use dashu::Integer;
use dashu::Rational;

use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;
use crate::parser::char_reader::*;
use crate::parser::lexer::*;

use ordered_float::OrderedFloat;

use std::cell::Cell;
use std::mem;
use std::ops::Neg;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq)]
enum TokenType {
    Term,
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

/*
Specifies whether the token sequence should be read from the lexer or
provided via the Provided variant.
*/
#[derive(Debug)]
pub enum Tokens {
    Default,
    Provided(Vec<Token>),
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

pub(crate) fn as_partial_string(
    head: Term,
    mut tail: Term,
) -> Result<(String, Option<Box<Term>>), Term> {
    let mut string = match &head {
        Term::Literal(_, Literal::Atom(atom)) => {
            if let Some(c) = atom.as_char() {
                c.to_string()
            } else {
                return Err(Term::Cons(Cell::default(), Box::new(head), Box::new(tail)));
            }
        }
        _ => {
            return Err(Term::Cons(Cell::default(), Box::new(head), Box::new(tail)));
        }
    };

    let mut orig_tail = Box::new(tail);
    let mut tail_ref = &mut orig_tail;

    loop {
        match &mut **tail_ref {
            Term::Cons(_, prev, succ) => {
                match prev.as_ref() {
                    Term::Literal(_, Literal::Atom(atom)) => {
                        if let Some(c) = atom.as_char() {
                            string.push(c);
                        } else {
                            return Err(Term::Cons(Cell::default(), Box::new(head), orig_tail));
                        }
                    }
                    _ => {
                        tail = Term::Cons(
                            Cell::default(),
                            Box::new((**prev).clone()),
                            Box::new((**succ).clone()),
                        );
                        break;
                    }
                }

                tail_ref = succ;
            }
            Term::PartialString(_, pstr, tail) => {
                string += pstr;
                tail_ref = tail;
            }
            Term::CompleteString(_, cstr) => {
                string += &*cstr.as_str();
                tail = Term::Literal(Cell::default(), Literal::Atom(atom!("[]")));
                break;
            }
            tail_ref => {
                tail = mem::replace(tail_ref, Term::AnonVar);
                break;
            }
        }
    }

    match tail {
        Term::AnonVar | Term::Var(..) => Ok((string, Some(Box::new(tail)))),
        Term::Literal(_, Literal::Atom(atom!("[]"))) => Ok((string, None)),
        Term::CompleteString(_, tail) => {
            string += &tail;
            Ok((string, None))
        }
        Term::PartialString(_, tail_string, tail) => {
            string += &tail_string;
            Ok((string, Some(tail)))
        }
        _ => Ok((string, Some(Box::new(tail)))),
    }
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
pub struct Parser<'a, R> {
    pub lexer: Lexer<'a, R>,
    tokens: Vec<Token>,
    stack: Vec<TokenDesc>,
    terms: Vec<Term>,
}

pub fn read_tokens<R: CharRead>(lexer: &mut Lexer<'_, R>) -> Result<Vec<Token>, ParserError> {
    let mut tokens = vec![];

    loop {
        match lexer.next_token() {
            Ok(token) => {
                let at_end = token.is_end();
                tokens.push(token);

                if at_end {
                    break;
                }
            }
            Err(e) if e.is_unexpected_eof() && !tokens.is_empty() => {
                return Err(ParserError::IncompleteReduction(
                    lexer.line_num,
                    lexer.col_num,
                ));
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    tokens.reverse();
    Ok(tokens)
}

fn atomize_term(term: &Term) -> Option<Atom> {
    match term {
        &Term::Literal(_, Literal::Atom(c)) => Some(c),
        _ => None,
    }
}

impl TokenType {
    fn sep_to_atom(&mut self) -> Option<Atom> {
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

impl<'a, R: CharRead> Parser<'a, R> {
    pub fn new(stream: R, machine_st: &'a mut MachineState) -> Self {
        Parser {
            lexer: Lexer::new(stream, machine_st),
            tokens: vec![],
            stack: vec![],
            terms: vec![],
        }
    }

    pub fn from_lexer(lexer: Lexer<'a, R>) -> Self {
        Parser {
            lexer,
            tokens: vec![],
            stack: vec![],
            terms: vec![],
        }
    }

    fn get_term_name(&mut self, td: TokenDesc) -> Option<Atom> {
        match td.tt {
            TokenType::HeadTailSeparator => Some(atom!("|")),
            TokenType::Comma => Some(atom!(",")),
            TokenType::Term => match self.terms.pop() {
                Some(Term::Literal(_, Literal::Atom(atom))) => Some(atom),
                Some(term) => {
                    self.terms.push(term);
                    None
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn push_binary_op(&mut self, td: TokenDesc, spec: Specifier) {
        if let Some(arg2) = self.terms.pop() {
            if let Some(name) = self.get_term_name(td) {
                if let Some(arg1) = self.terms.pop() {
                    let term = Term::Clause(Cell::default(), name, vec![arg1, arg2]);

                    self.terms.push(term);
                    self.stack.push(TokenDesc {
                        tt: TokenType::Term,
                        priority: td.priority,
                        spec,
                        unfold_bounds: 0,
                    });
                }
            }
        }
    }

    fn push_unary_op(&mut self, td: TokenDesc, spec: Specifier, assoc: OpDeclSpec) {
        if let Some(mut arg1) = self.terms.pop() {
            if let Some(mut name) = self.terms.pop() {
                if assoc.is_postfix() {
                    mem::swap(&mut arg1, &mut name);
                }

                if let Term::Literal(_, Literal::Atom(name)) = name {
                    let term = Term::Clause(Cell::default(), name, vec![arg1]);

                    self.terms.push(term);
                    self.stack.push(TokenDesc {
                        tt: TokenType::Term,
                        priority: td.priority,
                        spec,
                        unfold_bounds: 0,
                    });
                }
            }
        }
    }

    fn promote_atom_op(&mut self, atom: Atom, priority: usize, assoc: u32) {
        self.terms
            .push(Term::Literal(Cell::default(), Literal::Atom(atom)));
        self.stack.push(TokenDesc {
            tt: TokenType::Term,
            priority,
            spec: assoc,
            unfold_bounds: 0,
        });
    }

    fn shift(&mut self, token: Token, priority: usize, spec: Specifier) {
        let tt = match token {
            Token::String(s) if self.lexer.machine_st.flags.double_quotes.is_codes() => {
                let mut list = Term::Literal(Cell::default(), Literal::Atom(atom!("[]")));

                for c in s.as_str().chars().rev() {
                    list = Term::Cons(
                        Cell::default(),
                        Box::new(Term::Literal(
                            Cell::default(),
                            Literal::Fixnum(Fixnum::build_with(c as i64)),
                        )),
                        Box::new(list),
                    );
                }

                self.terms.push(list);
                TokenType::Term
            }
            Token::String(s) => {
                debug_assert!(self.lexer.machine_st.flags.double_quotes.is_chars());
                self.terms
                    .push(Term::CompleteString(Cell::default(), Rc::new(s)));
                TokenType::Term
            }
            Token::Literal(c) => {
                self.terms.push(Term::Literal(Cell::default(), c));
                TokenType::Term
            }
            Token::Var(v) => {
                if v.trim() == "_" {
                    self.terms.push(Term::AnonVar);
                } else {
                    self.terms.push(Term::Var(Cell::default(), VarPtr::from(v)));
                }

                TokenType::Term
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
                            self.push_binary_op(desc2, LTERM);
                            continue;
                        } else if is_xfy!(desc2.spec) && affirm_xfy(priority, desc2, desc3, desc1) {
                            self.push_binary_op(desc2, TERM);
                            continue;
                        } else {
                            self.stack.push(desc3);
                        }
                    }

                    if is_yf!(desc1.spec) && affirm_yf(desc1, desc2) {
                        self.push_unary_op(desc1, LTERM, YF);
                        continue;
                    } else if is_xf!(desc1.spec) && affirm_xf(desc1, desc2) {
                        self.push_unary_op(desc1, LTERM, XF);
                        continue;
                    } else if is_fy!(desc2.spec) && affirm_fy(priority, desc1, desc2) {
                        self.push_unary_op(desc2, TERM, FY);
                        continue;
                    } else if is_fx!(desc2.spec) && affirm_fx(priority, desc1, desc2) {
                        self.push_unary_op(desc2, TERM, FX);
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

        if self.terms.len() < 1 + arity {
            return false;
        }

        let stack_len = self.stack.len() - 2 * arity - 1;
        let idx = self.terms.len() - arity;

        if TokenType::Term == self.stack[stack_len].tt
            && atomize_term(&self.terms[idx - 1]).is_some()
        {
            self.stack.truncate(stack_len + 1);

            let mut subterms: Vec<_> = self.terms.drain(idx..).collect();

            if let Some(name) = self.terms.pop().and_then(|t| atomize_term(&t)) {
                // reduce the '.' functor to a cons cell if it applies.
                if name == atom!(".") && subterms.len() == 2 {
                    let tail = subterms.pop().unwrap();
                    let head = subterms.pop().unwrap();

                    self.terms.push(match as_partial_string(head, tail) {
                        Ok((string_buf, Some(tail))) => {
                            Term::PartialString(Cell::default(), Rc::new(string_buf), tail)
                        }
                        Ok((string_buf, None)) => {
                            Term::CompleteString(Cell::default(), Rc::new(string_buf))
                        }
                        Err(term) => term,
                    });
                } else {
                    self.terms
                        .push(Term::Clause(Cell::default(), name, subterms));
                }

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

                    *tt = TokenType::Term;
                    *priority = 0;
                    *spec = TERM;
                    *unfold_bounds = 0;
                }

                return true;
            }
        }

        false
    }

    pub fn reset(&mut self) {
        self.stack.clear()
    }

    fn expand_comma_compacted_terms(&mut self, index: usize) -> usize {
        if let Some(mut term) = self.terms.pop() {
            let mut op_desc = self.stack[index - 1];

            if 0 < op_desc.priority && op_desc.priority < self.stack[index].priority {
                /* '|' is a head-tail separator here, not
                 * an operator, so expand the
                 * terms it compacted out again. */
                if let (Some(atom!(",")), 2) = (term.name(), term.arity()) {
                    let terms = if op_desc.unfold_bounds == 0 {
                        unfold_by_str(term, atom!(","))
                    } else {
                        let mut terms = vec![];

                        while let Some((fst, snd)) = unfold_by_str_once(&mut term, atom!(",")) {
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

                    self.terms.extend(terms);
                    return arity;
                }
            }

            self.terms.push(term);
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
            if td.tt == TokenType::OpenList {
                td.spec = TERM;
                td.tt = TokenType::Term;
                td.priority = 0;

                self.terms
                    .push(Term::Literal(Cell::default(), Literal::Atom(atom!("[]"))));
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
        let list_len = self.stack.len() - 2 * arity;

        let end_term = if self.stack[idx].tt != TokenType::HeadTailSeparator {
            Term::Literal(Cell::default(), Literal::Atom(atom!("[]")))
        } else {
            let term = match self.terms.pop() {
                Some(term) => term,
                _ => {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ))
                }
            };

            if self.stack[idx].priority > 1000 {
                arity += self.expand_comma_compacted_terms(idx);
            }

            arity -= 1;

            term
        };

        if arity > self.terms.len() {
            return Err(ParserError::IncompleteReduction(
                self.lexer.line_num,
                self.lexer.col_num,
            ));
        }

        let idx = self.terms.len() - arity;

        let list = self.terms.drain(idx..).rev().fold(end_term, |acc, t| {
            Term::Cons(Cell::default(), Box::new(t), Box::new(acc))
        });

        self.stack.truncate(list_len);

        self.stack.push(TokenDesc {
            tt: TokenType::Term,
            priority: 0,
            spec: TERM,
            unfold_bounds: 0,
        });

        self.terms.push(match list {
            Term::Cons(_, head, tail) => match as_partial_string(*head, *tail) {
                Ok((string_buf, Some(tail))) => {
                    Term::PartialString(Cell::default(), Rc::new(string_buf), tail)
                }
                Ok((string_buf, None)) => {
                    Term::CompleteString(Cell::default(), Rc::new(string_buf))
                }
                Err(term) => term,
            },
            term => term,
        });

        Ok(true)
    }

    fn reduce_curly(&mut self) -> Result<bool, ParserError> {
        if self.stack.is_empty() {
            return Ok(false);
        }

        if let Some(ref mut td) = self.stack.last_mut() {
            if td.tt == TokenType::OpenCurly {
                td.tt = TokenType::Term;
                td.priority = 0;
                td.spec = TERM;

                let term = Term::Literal(Cell::default(), Literal::Atom(atom!("{}")));

                self.terms.push(term);
                return Ok(true);
            }
        }

        self.reduce_op(1201);

        if self.stack.len() > 1 {
            if let Some(td) = self.stack.pop() {
                if let Some(ref mut oc) = self.stack.last_mut() {
                    if td.tt != TokenType::Term {
                        return Ok(false);
                    }

                    if oc.tt == TokenType::OpenCurly {
                        oc.tt = TokenType::Term;
                        oc.priority = 0;
                        oc.spec = TERM;

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

                        return Ok(true);
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

        if let Some(TokenType::Open | TokenType::OpenCT) = self.stack.last().map(|token| token.tt) {
            return false;
        }

        let idx = self.stack.len() - 2;
        let td = self.stack.remove(idx);

        match td.tt {
            TokenType::Open | TokenType::OpenCT => {
                if self.stack[idx].tt == TokenType::Comma {
                    return false;
                }

                if let Some(atom) = self.stack[idx].tt.sep_to_atom() {
                    self.terms
                        .push(Term::Literal(Cell::default(), Literal::Atom(atom)));
                }

                self.stack[idx].spec = BTERM;
                self.stack[idx].tt = TokenType::Term;
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
                match self.tokens.last().ok_or(ParserError::unexpected_eof())? {
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
        ToLiteral: Fn(N, &mut Arena) -> Literal,
    {
        if let Some(desc) = self.stack.last().cloned() {
            if let Some(term) = self.terms.last().cloned() {
                match term {
                    Term::Literal(_, Literal::Atom(name))
                        if name == atom!("-")
                            && (is_prefix!(desc.spec) || is_negate!(desc.spec)) =>
                    {
                        self.stack.pop();
                        self.terms.pop();

                        let arena = &mut self.lexer.machine_st.arena;
                        let literal = constr(negator(n, arena), arena);

                        self.shift(Token::Literal(literal), 0, TERM);

                        return;
                    }
                    _ => {}
                }
            }
        }

        let literal = constr(n, &mut self.lexer.machine_st.arena);
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
            Token::Literal(Literal::Integer(n)) => {
                self.negate_number(n, negate_int_rc, |n, _| Literal::Integer(n))
            }
            Token::Literal(Literal::Rational(n)) => {
                self.negate_number(n, negate_rat_rc, |r, _| Literal::Rational(r))
            }
            Token::Literal(Literal::Float(n)) => self.negate_number(
                **n.as_ptr(),
                |n, _| -n,
                |n, arena| Literal::from(float_alloc!(n, arena)),
            ),
            Token::Literal(Literal::Fixnum(n)) => {
                self.negate_number(n, |n, _| -n, |n, _| Literal::Fixnum(n))
            }
            Token::Literal(c) => {
                if let Literal::Atom(name) = c {
                    if !self.shift_op(name, op_dir)? {
                        self.shift(Token::Literal(c), 0, TERM);
                    }
                } else {
                    self.shift(Token::Literal(c), 0, TERM);
                }
            }
            Token::Var(v) => self.shift(Token::Var(v), 0, TERM),
            Token::Open => self.shift(Token::Open, 1300, DELIMITER),
            Token::OpenCT => self.shift(Token::OpenCT, 1300, DELIMITER),
            Token::Close => {
                if !self.reduce_term() && !self.reduce_brackets() {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ));
                }
            }
            Token::OpenList => self.shift(Token::OpenList, 1300, DELIMITER),
            Token::CloseList => {
                if !self.reduce_list()? {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ));
                }
            }
            Token::OpenCurly => self.shift(Token::OpenCurly, 1300, DELIMITER),
            Token::CloseCurly => {
                if !self.reduce_curly()? {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ));
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
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ))
                }
                _ => {}
            },
        }

        Ok(())
    }

    #[inline]
    pub fn add_lines_read(&mut self, lines_read: usize) {
        self.lexer.line_num += lines_read;
    }

    #[inline]
    pub fn lines_read(&self) -> usize {
        self.lexer.line_num
    }

    // on success, returns the parsed term and the number of lines read.
    pub fn read_term(
        &mut self,
        op_dir: &CompositeOpDir,
        tokens: Tokens,
    ) -> Result<Term, ParserError> {
        self.tokens = match tokens {
            Tokens::Default => read_tokens(&mut self.lexer)?,
            Tokens::Provided(tokens) => tokens,
        };

        while let Some(token) = self.tokens.pop() {
            self.shift_token(token, op_dir)?;
        }

        self.reduce_op(1400);

        if self.terms.len() > 1 || self.stack.len() > 1 {
            return Err(ParserError::IncompleteReduction(
                self.lexer.line_num,
                self.lexer.col_num,
            ));
        }

        match self.terms.pop() {
            Some(term) => {
                if self.terms.is_empty() {
                    Ok(term)
                } else {
                    Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ))
                }
            }
            _ => Err(ParserError::IncompleteReduction(
                self.lexer.line_num,
                self.lexer.col_num,
            )),
        }
    }
}
