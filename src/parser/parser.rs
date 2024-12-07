use dashu::Integer;
use dashu::Rational;

use crate::arena::*;
use crate::atom_table::*;
use crate::forms::Number;
use crate::machine::heap::*;
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::parser::lexer::*;
use crate::types::*;

use std::ops::Neg;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq)]
enum TokenType {
    Term { heap_loc: HeapCellValue },
    Open,
    OpenCT,
    OpenList,          // '['
    OpenCurly,         // '{'
    HeadTailSeparator, // '|'
    Comma,             // ','
    Close,
    CloseList,  // ']'
    CloseCurly, // '}'
    End,
}

impl TokenType {
    fn sep_to_atom(self) -> Option<Atom> {
        match self {
            TokenType::Open | TokenType::OpenCT => Some(atom!("(")),
            TokenType::Close => Some(atom!(")")),
            TokenType::OpenList => Some(atom!("[")),
            TokenType::CloseList => Some(atom!("]")),
            TokenType::OpenCurly => Some(atom!("{")),
            TokenType::CloseCurly => Some(atom!("}")),
            TokenType::HeadTailSeparator => Some(atom!("|")),
            TokenType::Comma => Some(atom!(",")),
            TokenType::End => Some(atom!(".")),
            _ => None,
        }
    }
}

/*
Specifies whether the token sequence should be read from the lexer or
provided via the Provided variant.
*/
#[derive(Debug)]
pub enum Tokens {
    Default,
    Provided(Vec<Token>, usize),
}

impl TokenType {
    fn is_sep(self) -> bool {
        matches!(
            self,
            TokenType::HeadTailSeparator
                | TokenType::OpenCT
                | TokenType::Open
                | TokenType::Close
                | TokenType::OpenList
                | TokenType::CloseList
                | TokenType::OpenCurly
                | TokenType::CloseCurly
                | TokenType::Comma
        )
    }
}

#[derive(Debug, Clone, Copy)]
struct TokenDesc {
    tt: TokenType,
    priority: usize,
    spec: u32,
    unfold_bounds: usize,
}

pub fn get_op_desc(name: Atom, op_dir: &CompositeOpDir) -> Option<CompositeOpDesc> {
    let mut op_desc = CompositeOpDesc {
        pre: 0,
        inf: 0,
        post: 0,
        spec: 0,
    };

    if let Some(cell) = op_dir.get(name, Fixity::Pre) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.pre = pri as usize;
            op_desc.spec |= spec as u32;
        } else if name == atom!("-") {
            // used to denote a negative sign that should be treated as an atom and not an operator
            op_desc.spec |= NEGATIVE_SIGN;
        }
    }

    if let Some(cell) = op_dir.get(name, Fixity::Post) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.post = pri as usize;
            op_desc.spec |= spec as u32;
        }
    }

    if let Some(cell) = op_dir.get(name, Fixity::In) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.inf = pri as usize;
            op_desc.spec |= spec as u32;
        }
    }

    if op_desc.pre + op_desc.post + op_desc.inf == 0 && !is_negate!(op_desc.spec) {
        None
    } else {
        Some(op_desc)
    }
}

fn affirm_xfx(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool {
    d2.priority <= priority
        && is_term!(d3.spec)
        && is_term!(d1.spec)
        && d3.priority < d2.priority
        && d1.priority < d2.priority
}

fn affirm_yfx(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool {
    d2.priority <= priority
        && ((is_term!(d3.spec) && d3.priority < d2.priority)
            || (is_lterm!(d3.spec) && d3.priority == d2.priority))
        && is_term!(d1.spec)
        && d1.priority < d2.priority
}

fn affirm_xfy(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool {
    d2.priority < priority
        && is_term!(d3.spec)
        && d3.priority < d2.priority
        && is_term!(d1.spec)
        && d1.priority <= d2.priority
}

fn affirm_yf(d1: TokenDesc, d2: TokenDesc) -> bool {
    let is_valid_lterm = is_lterm!(d2.spec) && d2.priority == d1.priority;
    (is_term!(d2.spec) && d2.priority < d1.priority) || is_valid_lterm
}

fn affirm_xf(d1: TokenDesc, d2: TokenDesc) -> bool {
    is_term!(d2.spec) && d2.priority < d1.priority
}

fn affirm_fy(priority: usize, d1: TokenDesc, d2: TokenDesc) -> bool {
    d2.priority < priority && is_term!(d1.spec) && d1.priority <= d2.priority
}

fn affirm_fx(priority: usize, d1: TokenDesc, d2: TokenDesc) -> bool {
    d2.priority <= priority && is_term!(d1.spec) && d1.priority < d2.priority
}

#[derive(Debug, Clone, Copy)]
pub struct CompositeOpDesc {
    pub pre: usize,
    pub inf: usize,
    pub post: usize,
    pub spec: Specifier,
}

#[derive(Debug)]
struct Parser<'a> {
    tokens: Vec<Token>,
    stack: Vec<TokenDesc>,
    terms: HeapWriter<'a>,
    arena: &'a mut Arena,
    flags: MachineFlags,
    line_num: &'a mut usize,
    col_num: &'a mut usize,
    var_locs: VarLocs,
    inverse_var_locs: InverseVarLocs,
}

pub fn read_tokens<R: CharRead>(
    lexer: &mut LexerParser<R>,
) -> Result<(Vec<Token>, usize), ParserError> {
    let mut tokens = vec![];
    let mut term_size = 0;

    loop {
        match lexer.next_token() {
            Ok(token) => {
                let at_end = token.is_end();
                term_size += token.byte_size(lexer.machine_st.flags);
                tokens.push(token);

                if at_end {
                    break;
                }
            }
            Err(e) if e.is_unexpected_eof() && !tokens.is_empty() => {
                return Err(ParserError::IncompleteReduction(lexer.loc_to_err_src()));
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    tokens.reverse();

    Ok((tokens, term_size))
}

pub(crate) fn as_partial_string(
    heap: &impl SizedHeap,
    head: HeapCellValue,
    tail: HeapCellValue,
) -> Option<(String, Option<HeapCellValue>)> {
    let head = heap_bound_store(heap, heap_bound_deref(heap, head));
    let mut tail = heap_bound_store(heap, heap_bound_deref(heap, tail));

    let mut string = read_heap_cell!(head,
       (HeapCellValueTag::Atom, (atom, arity)) => {
           if arity == 0 {
               if let Some(c) = atom.as_char() {
                   c.to_string()
               } else {
                   return None;
               }
           } else {
               return None;
           }
       }
       _ => {
           return None;
       }
    );

    loop {
        read_heap_cell!(tail,
           (HeapCellValueTag::Lis, l) => {
               read_heap_cell!(heap[l],
                   (HeapCellValueTag::Atom, (atom, arity)) => {
                       if arity == 0 {
                           if let Some(c) = atom.as_char() {
                               string.push(c);
                           } else {
                               return None;
                           }
                       } else {
                           break;
                       }
                   }
                   _ => {
                       return None;
                   }
               );

               tail = heap[l+1];
           }
           (HeapCellValueTag::PStrLoc, l) => {
               let HeapStringScan { string: pstr, tail_idx } = heap.scan_slice_to_str(l);
               string += pstr;
               tail = heap[tail_idx];
           }
           (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
               if heap[h] != tail {
                   tail = heap[h];
               } else {
                   break;
               }
           }
           _ => {
               // Anon
               break;
           }
        );
    }

    read_heap_cell!(tail,
       (HeapCellValueTag::Var) => {
           Some((string, Some(tail)))
       }
       (HeapCellValueTag::Atom, (atom, arity)) => {
           if atom == atom!("[]") && arity == 0 {
               Some((string, None))
           } else {
               Some((string, Some(tail)))
           }
       }
       _ => {
           Some((string, Some(tail)))
       }
    )
}

impl<'a> Parser<'a> {
    fn get_term_name(&self, td: TokenDesc) -> Option<Atom> {
        match td.tt {
            TokenType::HeadTailSeparator => Some(atom!("|")),
            TokenType::Comma => Some(atom!(",")),
            TokenType::Term { heap_loc } => {
                if heap_loc.is_ref() {
                    term_predicate_key(&self.terms, heap_loc.get_value() as usize).map(|key| key.0)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn push_binary_op(
        &mut self,
        op: TokenDesc,
        operand_1: TokenDesc,
        operand_2: TokenDesc,
        spec: Specifier,
    ) {
        if let TokenDesc {
            tt: TokenType::Term { heap_loc: arg2 },
            ..
        } = operand_2
        {
            if let TokenDesc {
                tt: TokenType::Term { heap_loc: arg1 },
                ..
            } = operand_1
            {
                if let Some(name) = self.get_term_name(op) {
                    let str_loc = self.terms.cell_len();

                    self.terms.write_with(|section| {
                        section.push_cell(atom_as_cell!(name, 2));
                        section.push_cell(arg1);
                        section.push_cell(arg2);

                        section.push_cell(str_loc_as_cell!(str_loc));
                    });

                    self.stack.push(TokenDesc {
                        tt: TokenType::Term {
                            heap_loc: heap_loc_as_cell!(str_loc + 3),
                        },
                        priority: op.priority,
                        spec,
                        unfold_bounds: 0,
                    });
                }
            }
        }
    }

    fn push_unary_op(&mut self, op: TokenDesc, operand: TokenDesc, spec: Specifier) {
        if let TokenDesc {
            tt: TokenType::Term { heap_loc: arg1 },
            ..
        } = operand
        {
            if let TokenDesc {
                tt: TokenType::Term { .. },
                ..
            } = op
            {
                if let Some(name) = self.get_term_name(op) {
                    let str_loc = self.terms.cell_len();

                    self.terms.write_with(|section| {
                        section.push_cell(atom_as_cell!(name, 1));
                        section.push_cell(arg1);
                        section.push_cell(str_loc_as_cell!(str_loc));
                    });

                    self.stack.push(TokenDesc {
                        tt: TokenType::Term {
                            heap_loc: heap_loc_as_cell!(str_loc + 2),
                        },
                        priority: op.priority,
                        spec,
                        unfold_bounds: 0,
                    });
                }
            }
        }
    }

    fn promote_atom_op(&mut self, atom: Atom, priority: usize, assoc: u32) {
        let h = self.terms.cell_len();
        self.terms
            .write_with(|section| section.push_cell(atom_as_cell!(atom)));
        self.stack.push(TokenDesc {
            tt: TokenType::Term {
                heap_loc: heap_loc_as_cell!(h),
            },
            priority,
            spec: assoc,
            unfold_bounds: 0,
        });
    }

    fn shift(&mut self, token: Token, priority: usize, spec: Specifier) {
        let heap_loc = heap_loc_as_cell!(self.terms.cell_len());

        let tt = match token {
            Token::String(s) if self.flags.double_quotes.is_codes() => {
                let mut list = empty_list_as_cell!();

                self.terms.write_with(|section| {
                    for c in s.as_str().chars().rev() {
                        let h = section.cell_len();

                        section.push_cell(fixnum_as_cell!(Fixnum::build_with(c as i64)));
                        section.push_cell(list);

                        list = list_loc_as_cell!(h);
                    }

                    section.push_cell(list);
                });

                TokenType::Term { heap_loc: list }
            }
            Token::String(s) => {
                debug_assert!(self.flags.double_quotes.is_chars());
                let mut pstr_cell = heap_loc;

                if s == "\u{0}" {
                    let h = self.terms.cell_len();

                    self.terms.write_with(|section| {
                        section.push_cell(char_as_cell!('\u{0}'));
                        section.push_cell(empty_list_as_cell!());
                        section.push_cell(list_loc_as_cell!(h));
                    });

                    TokenType::Term {
                        heap_loc: heap_loc_as_cell!(h + 2),
                    }
                } else {
                    self.terms
                        .write_with(|section| match section.push_pstr(&s) {
                            Some(pstr_loc_cell) => {
                                section.push_cell(empty_list_as_cell!());
                                let h = section.cell_len();
                                section.push_cell(pstr_loc_cell);
                                pstr_cell = heap_loc_as_cell!(h);
                            }
                            None => {
                                section.push_cell(empty_list_as_cell!());
                            }
                        });

                    TokenType::Term {
                        heap_loc: pstr_cell,
                    }
                }
            }
            Token::Literal(c) => {
                self.terms.write_with(|section| section.push_cell(c));
                TokenType::Term { heap_loc }
            }
            Token::Var(var_string) => {
                let var = Rc::new(var_string);

                match self.var_locs.get(&var).cloned() {
                    Some(heap_loc) => {
                        self.terms.write_with(|section| section.push_cell(heap_loc));
                        TokenType::Term { heap_loc }
                    }
                    None => {
                        self.terms.write_with(|section| section.push_cell(heap_loc));

                        // if var_string == "_", it not being present
                        // as a key of self.var_locs means it is
                        // anonymous.

                        if var.trim() != "_" {
                            self.var_locs.insert(var.clone(), heap_loc);
                            self.inverse_var_locs
                                .insert(heap_loc.get_value() as usize, var);
                        }

                        TokenType::Term { heap_loc }
                    }
                }
            }
            Token::Comma => TokenType::Comma,
            Token::Open => TokenType::Open,
            Token::Close => TokenType::Close,
            Token::OpenCT => TokenType::OpenCT,
            Token::HeadTailSeparator => TokenType::HeadTailSeparator,
            Token::OpenList => TokenType::OpenList,
            Token::CloseList => TokenType::CloseList,
            Token::OpenCurly => TokenType::OpenCurly,
            Token::CloseCurly => TokenType::CloseCurly,
            Token::End => TokenType::End,
        };

        self.stack.push(TokenDesc {
            tt,
            priority,
            spec,
            unfold_bounds: 0,
        });
    }

    fn reduce_op(&mut self, priority: usize) {
        loop {
            if let Some(desc1) = self.stack.pop() {
                if let Some(desc2) = self.stack.pop() {
                    if let Some(desc3) = self.stack.pop() {
                        if is_xfx!(desc2.spec) && affirm_xfx(priority, desc2, desc3, desc1)
                            || is_yfx!(desc2.spec) && affirm_yfx(priority, desc2, desc3, desc1)
                        {
                            self.push_binary_op(desc2, desc3, desc1, LTERM);
                            continue;
                        } else if is_xfy!(desc2.spec) && affirm_xfy(priority, desc2, desc3, desc1) {
                            self.push_binary_op(desc2, desc3, desc1, TERM);
                            continue;
                        } else {
                            self.stack.push(desc3);
                        }
                    }

                    if is_yf!(desc1.spec) && affirm_yf(desc1, desc2) {
                        self.push_unary_op(desc1, desc2, LTERM);
                        continue;
                    } else if is_xf!(desc1.spec) && affirm_xf(desc1, desc2) {
                        self.push_unary_op(desc1, desc2, LTERM);
                        continue;
                    } else if is_fy!(desc2.spec) && affirm_fy(priority, desc1, desc2) {
                        self.push_unary_op(desc2, desc1, TERM);
                        continue;
                    } else if is_fx!(desc2.spec) && affirm_fx(priority, desc1, desc2) {
                        self.push_unary_op(desc2, desc1, TERM);
                        continue;
                    } else {
                        self.stack.push(desc2);
                        self.stack.push(desc1);
                    }
                } else {
                    self.stack.push(desc1);
                }
            }

            break;
        }
    }

    fn compute_arity_in_brackets(&self) -> Option<usize> {
        let mut arity = 0;

        for (i, desc) in self.stack.iter().rev().enumerate() {
            if i % 2 == 0 {
                // expect a term or non-comma operator.
                if let TokenType::Comma = desc.tt {
                    return None;
                } else if is_term!(desc.spec) || is_op!(desc.spec) || is_negate!(desc.spec) {
                    arity += 1;
                } else {
                    return None;
                }
            } else {
                if desc.tt == TokenType::OpenCT {
                    return Some(arity);
                }

                if let TokenType::Comma = desc.tt {
                    continue;
                } else {
                    return None;
                }
            }
        }

        None
    }

    fn term_from_stack(&self, idx: usize) -> Option<HeapCellValue> {
        if let TokenType::Term { heap_loc } = self.stack[idx].tt {
            Some(heap_loc)
        } else {
            None
        }
    }

    fn reduce_term(&mut self) -> bool {
        if self.stack.is_empty() {
            return false;
        }

        self.reduce_op(999);

        let arity = match self.compute_arity_in_brackets() {
            Some(arity) => arity,
            None => return false,
        };

        if self.stack.len() > 2 * arity {
            let idx = self.stack.len() - 2 * arity - 1;

            if is_infix!(self.stack[idx].spec)
                && idx > 0
                && !is_op!(self.stack[idx - 1].spec)
                && !self.stack[idx - 1].tt.is_sep()
            {
                return false;
            }
        } else {
            return false;
        }

        if self.terms.cell_len() < arity {
            return false;
        }

        let stack_len = self.stack.len() - 2 * arity - 1;
        let term_idx = self.terms.cell_len();

        let push_structure = |parser: &mut Self, name: Atom| -> TokenType {
            parser
                .terms
                .write_with(|section| section.push_cell(atom_as_cell!(name, arity)));

            for idx in (stack_len + 2..parser.stack.len()).step_by(2) {
                let subterm = parser.term_from_stack(idx).unwrap();
                parser
                    .terms
                    .write_with(|section| section.push_cell(subterm));
            }

            let str_loc_idx = parser.terms.cell_len();
            parser
                .terms
                .write_with(|section| section.push_cell(str_loc_as_cell!(term_idx)));

            TokenType::Term {
                heap_loc: heap_loc_as_cell!(str_loc_idx),
            }
        };

        if let TokenDesc {
            tt: TokenType::Term { heap_loc },
            ..
        } = self.stack[stack_len]
        {
            let idx = heap_loc.get_value() as usize;

            if let Some((name, arity)) = term_predicate_key(&self.terms, idx) {
                // reduce the '.' functor to a cons cell if it applies.
                let new_tt = if name == atom!(".") && arity == 2 {
                    let head = self.term_from_stack(stack_len + 2).unwrap();
                    let tail = self.term_from_stack(stack_len + 4).unwrap();
                    let cell_len = self.terms.cell_len();

                    match as_partial_string(&self.terms, head, tail) {
                        Some((string_buf, tail_opt)) => {
                            let bytes_written = self.terms.write_with(|section| {
                                let pstr_cell = section.push_pstr(&string_buf).unwrap();
                                section.push_cell(tail_opt.unwrap_or(empty_list_as_cell!()));
                                section.push_cell(pstr_cell);
                            });

                            let heap_loc = cell_index!(bytes_written) - 1 + cell_len;

                            TokenType::Term {
                                heap_loc: heap_loc_as_cell!(heap_loc),
                            }
                        }
                        None => {
                            let bytes_written = self.terms.write_with(|section| {
                                section.push_cell(head);
                                section.push_cell(tail);
                                section.push_cell(list_loc_as_cell!(term_idx));
                            });

                            TokenType::Term {
                                heap_loc: heap_loc_as_cell!(
                                    cell_len + cell_index!(bytes_written) - 1
                                ),
                            }
                        }
                    }
                } else {
                    push_structure(self, name)
                };

                self.stack.truncate(stack_len + 1);

                if let Some(&mut TokenDesc {
                    ref mut tt,
                    ref mut priority,
                    ref mut spec,
                    ref mut unfold_bounds,
                }) = self.stack.last_mut()
                {
                    if *spec == BTERM {
                        return false;
                    }

                    *tt = new_tt;
                    *priority = 0;
                    *spec = TERM;
                    *unfold_bounds = 0;
                }
            } else {
                return false;
            };

            return true;
        }

        false
    }

    fn loc_to_err_src(&self) -> ParserErrorSrc {
        ParserErrorSrc {
            line_num: *self.line_num,
            col_num: *self.col_num,
        }
    }

    fn expand_comma_compacted_terms(&mut self, index: usize) -> usize {
        if let Some(term) = self.term_from_stack(index - 1) {
            let mut op_desc = self.stack[index - 1];
            let mut term = heap_bound_store(&self.terms, heap_bound_deref(&self.terms, term));

            if term.is_ref()
                && 0 < op_desc.priority
                && op_desc.priority < self.stack[index].priority
            {
                /* '|' is a head-tail separator here, not
                 * an operator, so expand the
                 * terms it compacted out again. */

                let focus = term.get_value() as usize;
                let key_opt = term_predicate_key(&self.terms, focus);

                if key_opt == Some((atom!(","), 2)) {
                    let terms = if op_desc.unfold_bounds == 0 {
                        unfold_by_str(&mut self.terms, term, atom!(","))
                    } else {
                        let mut terms = vec![];

                        while let Some(fst_loc) =
                            unfold_by_str_once(&mut self.terms, term, atom!(","))
                        {
                            let (_, snd) = subterm_index(&self.terms, fst_loc + 1);
                            let (_, fst) = subterm_index(&self.terms, fst_loc);

                            terms.push(fst);
                            term = snd;

                            op_desc.unfold_bounds -= 2;

                            if op_desc.unfold_bounds == 0 {
                                break;
                            }
                        }

                        terms.push(term);
                        terms
                    };

                    let arity = terms.len() - 1;
                    self.stack
                        .extend(terms.into_iter().map(|heap_loc| TokenDesc {
                            tt: TokenType::Term { heap_loc },
                            priority: 0,
                            spec: 0,
                            unfold_bounds: 0,
                        }));
                    return arity;
                }
            }
        }

        0
    }

    fn compute_arity_in_list(&self) -> Option<usize> {
        let mut arity = 0;

        for (i, desc) in self.stack.iter().rev().enumerate() {
            if i % 2 == 0 {
                // expect a term or non-comma operator.
                if let TokenType::Comma = desc.tt {
                    return None;
                } else if is_term!(desc.spec) || is_op!(desc.spec) || is_negate!(desc.spec) {
                    arity += 1;
                } else {
                    return None;
                }
            } else if desc.tt == TokenType::HeadTailSeparator {
                if arity == 1 {
                    continue;
                }
                return None;
            } else if desc.tt == TokenType::OpenList {
                return Some(arity);
            } else if desc.tt != TokenType::Comma {
                return None;
            }
        }

        None
    }

    fn reduce_list(&mut self) -> Result<bool, ParserError> {
        if self.stack.is_empty() {
            return Ok(false);
        }

        if let Some(ref mut td) = self.stack.last_mut() {
            // parsed an empty list token
            if td.tt == TokenType::OpenList {
                let h = self.terms.cell_len();
                self.terms
                    .write_with(|section| section.push_cell(empty_list_as_cell!()));

                td.spec = TERM;
                td.tt = TokenType::Term {
                    heap_loc: heap_loc_as_cell!(h),
                };
                td.priority = 0;

                return Ok(true);
            }
        }

        self.reduce_op(1000);

        let mut arity = match self.compute_arity_in_list() {
            Some(arity) => arity,
            None => return Ok(false),
        };

        // we know that self.stack.len() >= 2 by this point.
        let idx = self.stack.len() - 2;
        let list_start_idx = self.stack.len() - 2 * arity;

        let mut tail_term = if self.stack[idx].tt != TokenType::HeadTailSeparator {
            empty_list_as_cell!()
        } else {
            let tail_term = match self.term_from_stack(idx + 1) {
                Some(term) => term,
                None => {
                    return Err(ParserError::IncompleteReduction(self.loc_to_err_src()));
                }
            };

            self.stack.pop();

            if self.stack[idx].priority > 1000 {
                arity += self.expand_comma_compacted_terms(idx);
            }

            // decrement for the removal of tail term.
            arity -= 1;
            tail_term
        };

        if arity > self.terms.cell_len() {
            return Err(ParserError::IncompleteReduction(self.loc_to_err_src()));
        }

        let pre_terms_len = self.terms.cell_len();

        while let Some(token_desc) = self.stack.pop() {
            let subterm = match token_desc.tt {
                TokenType::Term { heap_loc } => heap_loc,
                _ => {
                    continue;
                }
            };

            arity -= 1;

            let link_cell = list_loc_as_cell!(self.terms.cell_len() + 1);

            self.terms.write_with(|section| {
                section.push_cell(link_cell);
                section.push_cell(subterm);
                section.push_cell(tail_term);
            });

            tail_term = link_cell;

            if arity == 0 {
                break;
            }
        }

        debug_assert_eq!(arity, 0);

        self.stack.truncate(list_start_idx);

        let list_loc = self.terms.cell_len() - 3;

        let head_term = self.terms[list_loc + 1];
        let tail_term = self.terms[list_loc + 2];

        let heap_loc = match as_partial_string(&self.terms, head_term, tail_term) {
            Some((string_buf, tail_opt)) => {
                self.terms.truncate(pre_terms_len);

                let bytes_written = self.terms.write_with(|section| {
                    let pstr_cell = section.push_pstr(&string_buf).unwrap();
                    section.push_cell(tail_opt.unwrap_or(empty_list_as_cell!()));
                    section.push_cell(pstr_cell);
                });

                heap_loc_as_cell!(pre_terms_len + cell_index!(bytes_written) - 1)
            }
            None => {
                heap_loc_as_cell!(list_loc) // head_term
            }
        };

        self.stack.push(TokenDesc {
            tt: TokenType::Term { heap_loc },
            priority: 0,
            spec: TERM,
            unfold_bounds: 0,
        });

        Ok(true)
    }

    fn reduce_curly(&mut self) -> Result<bool, ParserError> {
        if self.stack.is_empty() {
            return Ok(false);
        }

        if let Some(ref mut td) = self.stack.last_mut() {
            if td.tt == TokenType::OpenCurly {
                let h = self.terms.cell_len();

                self.terms
                    .write_with(|section| section.push_cell(atom_as_cell!(atom!("{}"))));

                td.tt = TokenType::Term {
                    heap_loc: heap_loc_as_cell!(h),
                };
                td.priority = 0;
                td.spec = TERM;

                return Ok(true);
            }
        }

        self.reduce_op(1201);

        if self.stack.len() > 1 {
            if let Some(td) = self.stack.pop() {
                if let Some(ref mut oc) = self.stack.last_mut() {
                    if !matches!(td.tt, TokenType::Term { .. }) {
                        return Ok(false);
                    }

                    if oc.tt == TokenType::OpenCurly {
                        if let TokenType::Term { heap_loc } = td.tt {
                            let curly_idx = self.terms.cell_len();

                            oc.tt = TokenType::Term {
                                heap_loc: heap_loc_as_cell!(curly_idx + 2),
                            };
                            oc.priority = 0;
                            oc.spec = TERM;

                            self.terms.write_with(|section| {
                                section.push_cell(atom_as_cell!(atom!("{}"), 1));
                                section.push_cell(heap_loc);
                                section.push_cell(str_loc_as_cell!(curly_idx));
                            });

                            /*
                            let term = match self.terms.pop() {
                                Some(term) => term,
                                _ => {
                                    return Err(ParserError::IncompleteReduction(
                                        self.lexer.line_num,
                                        self.lexer.col_num,
                                    ))
                                }
                            };

                            self.terms
                                .push(Term::Clause(Cell::default(), atom!("{}"), vec![term]));
                            */

                            return Ok(true);
                        }
                    }
                }
            }
        }

        Ok(false)
    }

    fn reduce_brackets(&mut self) -> bool {
        if self.stack.is_empty() {
            return false;
        }

        self.reduce_op(1400);

        if self.stack.len() <= 1 {
            return false;
        }

        match self.stack.last().map(|token| token.tt) {
            Some(TokenType::Open | TokenType::OpenCT) => return false,
            _ => {}
        }

        let idx = self.stack.len() - 2;
        let td = self.stack.remove(idx);

        match td.tt {
            TokenType::Open | TokenType::OpenCT => {
                if self.stack[idx].tt == TokenType::Comma {
                    return false;
                }

                let term = if self.stack[idx].tt.sep_to_atom().is_some() {
                    atom_as_cell!(atom!("|"))
                } else {
                    self.term_from_stack(idx).unwrap()
                };

                self.stack[idx].spec = BTERM;
                self.stack[idx].tt = TokenType::Term { heap_loc: term };
                self.stack[idx].priority = 0;

                true
            }
            _ => false,
        }
    }

    fn shift_op(&mut self, name: Atom, op_dir: &CompositeOpDir) -> Result<bool, ParserError> {
        if let Some(CompositeOpDesc {
            pre,
            inf,
            post,
            spec,
        }) = get_op_desc(name, op_dir)
        {
            if (pre > 0 && inf + post > 0) || is_negate!(spec) {
                match self
                    .tokens
                    .last()
                    .ok_or(ParserError::unexpected_eof(self.loc_to_err_src()))?
                {
                    // do this when layout hasn't been inserted,
                    // ie. why we don't match on Token::Open.
                    Token::OpenCT => {
                        // can't be prefix, so either inf == 0
                        // or post == 0.
                        self.reduce_op(inf + post);
                        self.promote_atom_op(
                            name,
                            inf + post,
                            spec & (XFX as u32 | XFY as u32 | YFX as u32 | YF as u32 | XF as u32),
                        );
                    }
                    _ => {
                        self.reduce_op(inf + post);

                        if let Some(TokenDesc { spec: pspec, .. }) = self.stack.last().cloned() {
                            // rterm.c: 412
                            if is_term!(pspec) {
                                self.promote_atom_op(
                                    name,
                                    inf + post,
                                    spec & (XFX as u32
                                        | XFY as u32
                                        | YFX as u32
                                        | XF as u32
                                        | YF as u32),
                                );

                                return Ok(true);
                            }
                        }

                        self.promote_atom_op(
                            name,
                            pre,
                            spec & (FX as u32 | FY as u32 | NEGATIVE_SIGN),
                        );
                    }
                }
            } else {
                self.reduce_op(pre + inf + post); // only one non-zero priority among these.
                self.promote_atom_op(name, pre + inf + post, spec);
            }

            Ok(true)
        } else {
            // not an operator.
            Ok(false)
        }
    }

    fn negate_number<N, Negator, ToLiteral>(&mut self, n: N, negator: Negator, constr: ToLiteral)
    where
        Negator: Fn(N, &mut Arena) -> N,
        ToLiteral: Fn(N, &mut Arena) -> HeapCellValue,
    {
        match self.stack.last().cloned() {
            Some(
                td @ TokenDesc {
                    tt: TokenType::Term { .. },
                    spec,
                    ..
                },
            ) => {
                if let Some(name) = self.get_term_name(td) {
                    if name == atom!("-") && (is_prefix!(spec) || is_negate!(spec)) {
                        self.stack.pop();

                        let arena = &mut self.arena;
                        let literal = constr(negator(n, arena), arena);

                        self.shift(Token::Literal(literal), 0, TERM);

                        return;
                    }
                }
            }
            _ => {}
        }

        let literal = constr(n, &mut self.arena);
        self.shift(Token::Literal(literal), 0, TERM);
    }

    fn shift_token(&mut self, token: Token, op_dir: &CompositeOpDir) -> Result<(), ParserError> {
        fn negate_int_rc(t: TypedArenaPtr<Integer>, arena: &mut Arena) -> TypedArenaPtr<Integer> {
            let i: Integer = (*t).clone();
            let data = i.neg();
            arena_alloc!(data, arena)
        }

        fn negate_rat_rc(t: TypedArenaPtr<Rational>, arena: &mut Arena) -> TypedArenaPtr<Rational> {
            let r: Rational = (*t).clone();
            let data = r.neg();
            arena_alloc!(data, arena)
        }

        match token {
            Token::String(string) => {
                self.shift(Token::String(string), 0, TERM);
            }
            Token::Literal(c) => match Number::try_from(c) {
                Ok(Number::Integer(n)) => {
                    self.negate_number(n, negate_int_rc, |n, _| typed_arena_ptr_as_cell!(n))
                }
                Ok(Number::Rational(n)) => {
                    self.negate_number(n, negate_rat_rc, |r, _| typed_arena_ptr_as_cell!(r))
                }
                Ok(Number::Float(n)) => {
                    use ordered_float::OrderedFloat;

                    self.negate_number(
                        n,
                        |n, _| -n,
                        |OrderedFloat(n), arena| HeapCellValue::from(float_alloc!(n, arena)),
                    )
                }
                Ok(Number::Fixnum(n)) => {
                    self.negate_number(n, |n, _| -n, |n, _| fixnum_as_cell!(n))
                }
                Err(_) => {
                    if let Some(name) = c.to_atom() {
                        if !self.shift_op(name, op_dir)? {
                            self.shift(Token::Literal(c), 0, TERM);
                        }
                    } else {
                        self.shift(Token::Literal(c), 0, TERM);
                    }
                }
            },
            Token::Var(v) => self.shift(Token::Var(v), 0, TERM),
            Token::Open => self.shift(Token::Open, 1300, DELIMITER),
            Token::OpenCT => self.shift(Token::OpenCT, 1300, DELIMITER),
            Token::Close => {
                if !self.reduce_term() && !self.reduce_brackets() {
                    return Err(ParserError::IncompleteReduction(self.loc_to_err_src()));
                }
            }
            Token::OpenList => self.shift(Token::OpenList, 1300, DELIMITER),
            Token::CloseList => {
                if !self.reduce_list()? {
                    return Err(ParserError::IncompleteReduction(self.loc_to_err_src()));
                }
            }
            Token::OpenCurly => self.shift(Token::OpenCurly, 1300, DELIMITER),
            Token::CloseCurly => {
                if !self.reduce_curly()? {
                    return Err(ParserError::IncompleteReduction(self.loc_to_err_src()));
                }
            }
            Token::HeadTailSeparator => {
                /* '|' as an operator must have priority > 1000 and can only be infix.
                 * See: http://www.complang.tuwien.ac.at/ulrich/iso-prolog/dtc2#Res_A78
                 */
                let (priority, spec) = get_op_desc(atom!("|"), op_dir)
                    .map(|CompositeOpDesc { inf, spec, .. }| (inf, spec))
                    .unwrap_or((1000, DELIMITER));

                let old_stack_len = self.stack.len();

                self.reduce_op(priority);

                let new_stack_len = self.stack.len();

                if let Some(term_desc) = self.stack.last_mut() {
                    term_desc.unfold_bounds = old_stack_len - new_stack_len;
                }

                self.shift(Token::HeadTailSeparator, priority, spec);
            }
            Token::Comma => {
                self.reduce_op(1000);
                self.shift(Token::Comma, 1000, XFY as u32);
            }
            Token::End => match self.stack.last().map(|t| t.tt) {
                Some(TokenType::Open)
                | Some(TokenType::OpenCT)
                | Some(TokenType::OpenList)
                | Some(TokenType::OpenCurly)
                | Some(TokenType::HeadTailSeparator)
                | Some(TokenType::Comma) => {
                    return Err(ParserError::IncompleteReduction(self.loc_to_err_src()))
                }
                _ => {}
            },
        }

        Ok(())
    }
}

impl<'a, R: CharRead> LexerParser<'a, R> {
    #[inline]
    pub fn line_num(&self) -> usize {
        self.line_num
    }

    pub fn loc_to_err_src(&self) -> ParserErrorSrc {
        ParserErrorSrc {
            line_num: self.line_num,
            col_num: self.col_num,
        }
    }

    // on success, returns the parsed term and the number of lines read.
    pub fn read_term(
        &mut self,
        op_dir: &CompositeOpDir,
        tokens: Tokens,
    ) -> Result<TermWriteResult, ParserError> {
        let (tokens, term_byte_size) = match tokens {
            Tokens::Default => read_tokens(self)?,
            Tokens::Provided(tokens, size) => (tokens, size),
        };

        // the parser uses conditional indirection in many places so
        // the reserved size should be at least 4 * term_byte_size
        // so all cells are accounted for.
        let writer = match self
            .machine_st
            .heap
            .reserve(cell_index!(4 * term_byte_size))
        {
            Ok(term) => term,
            Err(_err_loc) => {
                return Err(ParserError::ResourceError(self.loc_to_err_src()));
            }
        };

        let before_len = writer.cell_len();

        let mut parser_impl = Parser {
            tokens,
            stack: vec![],
            terms: writer,
            arena: &mut self.machine_st.arena,
            flags: self.machine_st.flags,
            line_num: &mut self.line_num,
            col_num: &mut self.col_num,
            var_locs: VarLocs::default(),
            inverse_var_locs: InverseVarLocs::default(),
        };

        while let Some(token) = parser_impl.tokens.pop() {
            parser_impl.shift_token(token, op_dir)?;
        }

        parser_impl.reduce_op(1400);

        let after_len = parser_impl.terms.cell_len();

        debug_assert!(after_len - before_len <= cell_index!(4 * term_byte_size));

        if parser_impl.stack.len() > 1 || parser_impl.terms.is_empty() {
            return Err(ParserError::IncompleteReduction(
                parser_impl.loc_to_err_src(),
            ));
        }

        match parser_impl.stack.pop() {
            Some(TokenDesc {
                tt: TokenType::Term { heap_loc },
                ..
            }) => Ok(TermWriteResult {
                focus: heap_loc.get_value() as usize,
                inverse_var_locs: parser_impl.inverse_var_locs,
            }),
            _ => Err(ParserError::IncompleteReduction(
                parser_impl.loc_to_err_src(),
            )),
        }
    }
}
