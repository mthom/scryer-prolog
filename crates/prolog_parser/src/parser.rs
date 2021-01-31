use ast::*;
use lexer::*;
use tabled_rc::*;

use ordered_float::OrderedFloat;

use rug::ops::NegAssign;

use std::cell::Cell;
use std::io::Read;
use std::mem::swap;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq)]
enum TokenType {
    Term,
    Open,
    OpenCT,
    OpenList,       // '['
    OpenCurly,      // '{'
    HeadTailSeparator, // '|'
    Comma,          // ','
    Close,
    CloseList,      // ']'
    CloseCurly,     // '}'
    End
}

impl TokenType {
    fn is_sep(self) -> bool {
        match self {
            TokenType::HeadTailSeparator | TokenType::OpenCT | TokenType::Open |
            TokenType::Close | TokenType::OpenList | TokenType::CloseList |
            TokenType::OpenCurly | TokenType::CloseCurly | TokenType::Comma
                => true,
            _   => false
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct TokenDesc {
    tt: TokenType,
    priority: usize,
    spec: u32
}

pub
fn get_clause_spec(name: ClauseName, arity: usize, op_dir: CompositeOp) -> Option<SharedOpDesc>
{
    match arity {
        1 => {
            /* This is a clause with an operator principal functor. Prefix operators
            are supposed over post.
             */
            if let Some(OpDirValue(cell, _)) = op_dir.get(name.clone(), Fixity::Pre) {
                return Some(cell);
            }

            if let Some(OpDirValue(cell, _)) = op_dir.get(name, Fixity::Post) {
                return Some(cell);
            }
        },
        2 =>
            if let Some(OpDirValue(cell, _)) = op_dir.get(name, Fixity::In) {
                return Some(cell);
            },
        _ => {}
    };

    None
}

pub fn get_desc(name: ClauseName, op_dir: CompositeOp) -> Option<OpDesc>
{
    let mut op_desc = OpDesc { pre: 0, inf: 0, post: 0, spec: 0 };

    if let Some(OpDirValue(cell, _)) = op_dir.get(name.clone(), Fixity::Pre) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.pre = pri;
            op_desc.spec |= spec;
        } else if name.as_str() == "-" {
            op_desc.spec |= NEGATIVE_SIGN;
        }
    }

    if let Some(OpDirValue(cell, _)) = op_dir.get(name.clone(), Fixity::Post) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.post = pri;
            op_desc.spec |= spec;
        }
    }

    if let Some(OpDirValue(cell, _)) = op_dir.get(name.clone(), Fixity::In) {
        let (pri, spec) = cell.get();

        if pri > 0 {
            op_desc.inf = pri;
            op_desc.spec |= spec;
        }
    }

    if op_desc.pre + op_desc.post + op_desc.inf == 0 && !is_negate!(op_desc.spec) {
        None
    } else {
        Some(op_desc)
    }
}

fn affirm_xfx(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool
{
    d2.priority <= priority
        && is_term!(d3.spec)
        && is_term!(d1.spec)
        && d3.priority < d2.priority
        && d1.priority < d2.priority
}

fn affirm_yfx(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool
{
    d2.priority <= priority
        &&    ((is_term!(d3.spec) && d3.priority < d2.priority)
           ||  (is_lterm!(d3.spec) && d3.priority == d2.priority))
        && is_term!(d1.spec)
        && d1.priority < d2.priority
}


fn affirm_xfy(priority: usize, d2: TokenDesc, d3: TokenDesc, d1: TokenDesc) -> bool
{
    d2.priority < priority
        && is_term!(d3.spec)
        && d3.priority < d2.priority
        && is_term!(d1.spec)
        && d1.priority <= d2.priority
}

fn affirm_yf(d1: TokenDesc, d2: TokenDesc) -> bool
{
    let is_valid_lterm = is_lterm!(d2.spec) && d2.priority == d1.priority;
    (is_term!(d2.spec) && d2.priority < d1.priority) || is_valid_lterm
}

fn affirm_xf(d1: TokenDesc, d2: TokenDesc) -> bool
{
    is_term!(d2.spec) && d2.priority < d1.priority
}

fn affirm_fy(priority: usize, d1: TokenDesc, d2: TokenDesc) -> bool
{
    d2.priority < priority && is_term!(d1.spec) && d1.priority <= d2.priority
}

fn affirm_fx(priority: usize, d1: TokenDesc, d2: TokenDesc) -> bool
{
    d2.priority <= priority && is_term!(d1.spec) && d1.priority < d2.priority
}

fn sep_to_atom(tt: TokenType) -> Option<ClauseName>
{
    match tt {
        TokenType::Open | TokenType::OpenCT =>
            Some(clause_name!("(")),
        TokenType::Close =>
            Some(clause_name!(")")),
        TokenType::OpenList =>
            Some(clause_name!("[")),
        TokenType::CloseList =>
            Some(clause_name!("]")),
        TokenType::OpenCurly =>
            Some(clause_name!("{")),
        TokenType::CloseCurly =>
            Some(clause_name!("}")),
        TokenType::HeadTailSeparator =>
            Some(clause_name!("|")),
        TokenType::Comma =>
            Some(clause_name!(",")),
        TokenType::End =>
            Some(clause_name!(".")),
        _ => None
    }
}

#[derive(Debug, Clone, Copy)]
pub struct OpDesc {
    pub pre: usize,
    pub inf: usize,
    pub post: usize,
    pub spec: Specifier
}

#[derive(Debug)]
pub struct Parser<'a, R: Read> {
    lexer: Lexer<'a, R>,
    tokens: Vec<Token>,
    stack: Vec<TokenDesc>,
    terms: Vec<Term>,
}

fn read_tokens<'a, R: Read>(lexer: &mut Lexer<'a, R>) -> Result<Vec<Token>, ParserError>
{
    let mut tokens = vec![];

    loop {
        let token = lexer.next_token()?;
        let at_end = Token::End == token;

        tokens.push(token);

        if at_end {
            break;
        }
    }

    tokens.reverse();

    Ok(tokens)
}

impl<'a, R: Read> Parser<'a, R> {
    pub fn new(
        stream: &'a mut ParsingStream<R>,
        atom_tbl: TabledData<Atom>,
        flags: MachineFlags,
    ) -> Self {
        Parser { lexer: Lexer::new(atom_tbl, flags, stream),
                 tokens: vec![],
                 stack:  Vec::new(),
                 terms:  Vec::new() }
    }

    #[inline]
    pub fn line_num(&self) -> usize {
        self.lexer.line_num
    }

    #[inline]
    pub fn col_num(&self) -> usize {
        self.lexer.col_num
    }

    #[inline]
    pub fn get_atom_tbl(&self) -> TabledData<Atom> {
        self.lexer.atom_tbl.clone()
    }

    #[inline]
    pub fn set_atom_tbl(&mut self, atom_tbl: TabledData<Atom>) {
        self.lexer.atom_tbl = atom_tbl;
    }

    fn get_term_name(&mut self, td: TokenDesc) -> Option<(ClauseName, Option<SharedOpDesc>)> {
        match td.tt {
            TokenType::HeadTailSeparator => {
                Some((clause_name!("|"), Some(SharedOpDesc::new(td.priority, td.spec))))
            }
            TokenType::Comma => {
                Some((clause_name!(","), Some(SharedOpDesc::new(1000, XFY))))
            }
            TokenType::Term => {
                match self.terms.pop() {
                    Some(Term::Constant(_, Constant::Atom(atom, spec))) =>
                        Some((atom, spec)),
                    Some(term) => {
                        self.terms.push(term);
                        None
                    },
                    _ => None
                }
            }
            _ => {
                None
            }
        }
    }

    fn push_binary_op(&mut self, td: TokenDesc, spec: Specifier)
    {
        if let Some(arg2) = self.terms.pop() {
            if let Some((name, shared_op_desc)) = self.get_term_name(td) {
                if let Some(arg1) = self.terms.pop() {
                    let term = Term::Clause(Cell::default(),
                                            name,
                                            vec![Box::new(arg1), Box::new(arg2)],
                                            shared_op_desc);

                    self.terms.push(term);
                    self.stack.push(TokenDesc { tt: TokenType::Term,
                                                priority: td.priority,
                                                spec });
                }
            }
        }
    }

    fn push_unary_op(&mut self, td: TokenDesc, spec: Specifier, assoc: u32)
    {
        if let Some(mut arg1) = self.terms.pop() {
            if let Some(mut name) = self.terms.pop() {
                if is_postfix!(assoc) {
                    swap(&mut arg1, &mut name);
                }

                if let Term::Constant(_, Constant::Atom(name, shared_op_desc)) = name {
                    let term = Term::Clause(Cell::default(), name, vec![Box::new(arg1)],
                                            shared_op_desc);

                    self.terms.push(term);
                    self.stack.push(TokenDesc { tt: TokenType::Term,
                                                priority: td.priority,
                                                spec });
                }
            }
        }
    }

    fn promote_atom_op(&mut self, atom: ClauseName, priority: usize, assoc: u32,
                       op_dir_val: Option<OpDirValue>)
    {
        let spec = op_dir_val.map(|op_dir_val| op_dir_val.shared_op_desc());

        self.terms.push(Term::Constant(Cell::default(), Constant::Atom(atom, spec)));
        self.stack.push(TokenDesc { tt: TokenType::Term, priority, spec: assoc });
    }

    fn shift(&mut self, token: Token, priority: usize, spec: Specifier)
    {
        let tt = match token {
            Token::Constant(Constant::String(s))
                if self.lexer.flags.double_quotes.is_codes() => {
                    let mut list = Term::Constant(Cell::default(), Constant::EmptyList);

                    for c in s.chars().rev() {
                        list = Term::Cons(
                            Cell::default(),
                            Box::new(Term::Constant(
                                Cell::default(),
                                Constant::Fixnum(c as isize),
                            )),
                            Box::new(list),
                        );
                    }

                    self.terms.push(list);
                    TokenType::Term
                }
            Token::Constant(c) => {
                self.terms.push(Term::Constant(Cell::default(), c));
                TokenType::Term
            },
            Token::Var(v) => {
                if v.trim() == "_" {
                    self.terms.push(Term::AnonVar);
                } else {
                    self.terms.push(Term::Var(Cell::default(), v));
                }

                TokenType::Term
            },
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

        self.stack.push(TokenDesc { tt, priority, spec });
    }

    fn reduce_op(&mut self, priority: usize) {
        loop {
            if let Some(desc1) = self.stack.pop() {
                if let Some(desc2) = self.stack.pop() {
                    if let Some(desc3) = self.stack.pop() {
                        if is_xfx!(desc2.spec) && affirm_xfx(priority, desc2, desc3, desc1)
                        {
                            self.push_binary_op(desc2, LTERM);
                            continue;
                        }
                        else if is_yfx!(desc2.spec) && affirm_yfx(priority, desc2, desc3, desc1)
                        {
                            self.push_binary_op(desc2, LTERM);
                            continue;
                        }
                        else if is_xfy!(desc2.spec) && affirm_xfy(priority, desc2, desc3, desc1)
                        {
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

    fn compute_arity_in_brackets(&self) -> Option<usize>
    {
        let mut arity = 0;

        for (i, desc) in self.stack.iter().rev().enumerate() {
            if i % 2 == 0 { // expect a term or non-comma operator.
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

    fn reduce_term(&mut self, op_dir: CompositeOp) -> bool
    {
        if self.stack.is_empty() {
            return false;
        }

        self.reduce_op(999);

        let arity = match self.compute_arity_in_brackets() {
            Some(arity) => arity,
            None => return false
        };

        if self.stack.len() > 2 * arity {
            let idx = self.stack.len() - 2 * arity - 1;

            if is_infix!(self.stack[idx].spec) && idx > 0 {
                if !is_op!(self.stack[idx - 1].spec) && !self.stack[idx - 1].tt.is_sep() {
                    return false;
                }
            }

            if arity >= 2 && is_prefix!(self.stack[idx].spec) && self.stack[idx].priority > 0 {
                return false;
            }
        } else {
            return false;
        }

        let stack_len = self.stack.len() - 2 * arity - 1;
        let idx = self.terms.len() - arity;

        if TokenType::Term == self.stack[stack_len].tt {
            if self.atomize_term(&self.terms[idx - 1]).is_some() {
                self.stack.truncate(stack_len + 1);

                let mut subterms: Vec<_> = self.terms.drain(idx ..)
                    .map(|t| Box::new(t))
                    .collect();

                if let Some(name) = self.terms.pop().and_then(|t| self.atomize_term(&t)) {
                    // reduce the '.' functor to a cons cell if it applies.
                    if name.as_str() == "." && subterms.len() == 2 {
                        let tail = subterms.pop().unwrap();
                        let head = subterms.pop().unwrap();

                        self.terms.push(Term::Cons(Cell::default(), head, tail));
                    } else {
                        let spec = get_clause_spec(name.clone(), subterms.len(), op_dir);
                        self.terms.push(Term::Clause(Cell::default(), name, subterms, spec));
                    }

                    if let Some(&mut TokenDesc { ref mut priority, ref mut spec,
                                                 ref mut tt }) = self.stack.last_mut()
                    {
                        *tt = TokenType::Term;
                        *priority = 0;
                        *spec = TERM;
                    }

                    return true;
                }
            }
        }

        false
    }

    pub fn devour_whitespace(&mut self) -> Result<(), ParserError> {
	    self.lexer.scan_for_layout()?;
        Ok(())
    }

    pub fn reset(&mut self) {
        self.stack.clear()
    }

    fn expand_comma_compacted_terms(&mut self, index: usize) -> usize
    {
        if let Some(term) = self.terms.pop() {
            let op_desc = self.stack[index - 1];

            if 0 < op_desc.priority && op_desc.priority < self.stack[index].priority {
                /* '|' is a head-tail separator here, not
                 * an operator, so expand the
                 * terms it compacted out again. */
                match (term.name(), term.arity()) {
                    (Some(name), 2) if name.as_str() == "," => {
                        let terms = unfold_by_str(term, ",");
                        let arity = terms.len() - 1;

                        self.terms.extend(terms.into_iter());
                        return arity;
                    }
                    _ => {
                    }
                }
            }

            self.terms.push(term);
        }

        0
    }

    fn compute_arity_in_list(&self) -> Option<usize>
    {
        let mut arity = 0;

        for (i, desc) in self.stack.iter().rev().enumerate() {
            if i % 2 == 0 { // expect a term or non-comma operator.
                if let TokenType::Comma = desc.tt {
                    return None;
                } else if is_term!(desc.spec) || is_op!(desc.spec) {
                    arity += 1;
                } else {
                    return None;
                }
            } else {
                if desc.tt == TokenType::HeadTailSeparator {
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
        }

        None
    }

    fn reduce_list(&mut self) -> Result<bool, ParserError>
    {
        if self.stack.is_empty() {
            return Ok(false);
        }

        if let Some(ref mut td) = self.stack.last_mut() {
            if td.tt == TokenType::OpenList {
                td.spec = TERM;
                td.tt = TokenType::Term;
                td.priority = 0;

                self.terms.push(Term::Constant(Cell::default(), Constant::EmptyList));
                return Ok(true);
            }
        }

        self.reduce_op(1000);

        let mut arity = match self.compute_arity_in_list() {
            Some(arity) => arity,
            None => return Ok(false)
        };

        // we know that self.stack.len() >= 2 by this point.
        let idx = self.stack.len() - 2;
        let list_len = self.stack.len() - 2 * arity;

        let end_term = if self.stack[idx].tt != TokenType::HeadTailSeparator {
            Term::Constant(Cell::default(), Constant::EmptyList)
        } else {
            let term =
                match self.terms.pop() {
                    Some(term) => term,
                    _ => return Err(ParserError::IncompleteReduction(self.lexer.line_num,
                                                                     self.lexer.col_num))
                };

            if self.stack[idx].priority > 1000 {
                arity += self.expand_comma_compacted_terms(idx);
            }

            arity -= 1;

            term
        };

        let idx = self.terms.len() - arity;

        let list = self.terms.drain(idx ..)
            .rev()
            .fold(end_term, |acc, t| Term::Cons(Cell::default(),
                                                Box::new(t),
                                                Box::new(acc)));

        self.stack.truncate(list_len);

        self.stack.push(TokenDesc { tt: TokenType::Term, priority: 0, spec: TERM });
        self.terms.push(list);

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

                let term = Term::Constant(Cell::default(),
                                          atom!("{}", self.lexer.atom_tbl));
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
                            _ => return Err(ParserError::IncompleteReduction(self.lexer.line_num,
                                                                             self.lexer.col_num))
                        };

                        self.terms.push(Term::Clause(Cell::default(), clause_name!("{}"),
                                                     vec![Box::new(term)], None));

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

        if self.stack.len() == 1 {
            return false;
        }

        let idx = self.stack.len() - 2;

        match self.stack.remove(idx) {
            td =>
                match td.tt {
                    TokenType::Open | TokenType::OpenCT => {
                        if self.stack[idx].tt == TokenType::Comma {
                            return false;
                        }

                        if let Some(atom) = sep_to_atom(self.stack[idx].tt) {
                            self.terms.push(Term::Constant(Cell::default(), Constant::Atom(atom, None)));
                        }

                        self.stack[idx].spec = TERM;
                        self.stack[idx].tt = TokenType::Term;
                        self.stack[idx].priority = 0;
                        true
                    },
                    _ => false
                }
        }
    }

    fn shift_op(&mut self, name: ClauseName, op_dir: CompositeOp) -> Result<bool, ParserError> {
        if let Some(OpDesc { pre, inf, post, spec }) = get_desc(name.clone(), op_dir) {
            if (pre > 0 && inf + post > 0) || is_negate!(spec) {
                match self.tokens.last().ok_or(ParserError::UnexpectedEOF)? {
                    // do this when layout hasn't been inserted,
                    // ie. why we don't match on Token::Open.
                    &Token::OpenCT => {
                        // can't be prefix, so either inf == 0
                        // or post == 0.
                        self.reduce_op(inf + post);

                        let fixity = if inf > 0 { Fixity::In } else { Fixity::Post };
                        let op_dir_val = op_dir.get(name.clone(), fixity);

                        self.promote_atom_op(name, inf + post, spec & (XFX | XFY | YFX | YF | XF),
                                             op_dir_val);
                    },
                    _ => {
                        self.reduce_op(inf + post);

                        if let Some(TokenDesc { spec: pspec, .. }) = self.stack.last().cloned() {
                            // rterm.c: 412
                            if is_term!(pspec) {
                                let fixity = if inf > 0 { Fixity::In } else { Fixity::Post };
                                let op_dir_val = op_dir.get(name.clone(), fixity);

                                self.promote_atom_op(name, inf + post,
                                                     spec & (XFX | XFY | YFX | XF | YF),
                                                     op_dir_val);
                            } else {
                                let op_dir_val = op_dir.get(name.clone(), Fixity::Pre);
                                self.promote_atom_op(name, pre, spec & (FX | FY | NEGATIVE_SIGN), op_dir_val);
                            }
                        } else {
                            let op_dir_val = op_dir.get(name.clone(), Fixity::Pre);
                            self.promote_atom_op(name, pre, spec & (FX | FY | NEGATIVE_SIGN), op_dir_val);
                        }
                    }
                }
            } else {
                let op_dir_val = op_dir.get(name.clone(),
                                            if pre + inf == 0 {
                                                Fixity::Post
                                            } else if post + pre == 0 {
                                                Fixity::In
                                            } else {
                                                Fixity::Pre
                                            });

                self.reduce_op(pre + inf + post); // only one non-zero priority among these.
                self.promote_atom_op(name, pre + inf + post, spec, op_dir_val);
            }

            Ok(true)
        } else { // not an operator.
            Ok(false)
        }
    }

    fn atomize_term(&self, term: &Term) -> Option<ClauseName> {
        match term {
            &Term::Constant(_, ref c) => self.atomize_constant(c),
            _ => None
        }
    }

    fn atomize_constant(&self, c: &Constant) -> Option<ClauseName> {
        match c {
            &Constant::Atom(ref name, _) => Some(name.clone()),
            &Constant::Char(c) =>
                Some(clause_name!(c.to_string(), self.lexer.atom_tbl)),
            &Constant::EmptyList =>
                Some(clause_name!(c.to_string(), self.lexer.atom_tbl)),
            _ => None
        }
    }

    fn negate_number<N, Negator, ToConstant>(
        &mut self,
        n: N,
        negator: Negator,
        constr: ToConstant
    )
    where Negator: Fn(N) -> N,
          ToConstant: Fn(N) -> Constant
    {
        if let Some(desc) = self.stack.last().cloned() {
            if let Some(term) = self.terms.last().cloned() {
                match term {
                    Term::Constant(_, Constant::Atom(ref name, _))
                        if name.as_str() == "-" && (is_prefix!(desc.spec) || is_negate!(desc.spec)) => {
                            self.stack.pop();
                            self.terms.pop();

                            self.shift(Token::Constant(constr(negator(n))), 0, TERM);
                            return;
                        },
                    _ => {}
                }
            }
        }

        self.shift(Token::Constant(constr(n)), 0, TERM);
    }

    fn shift_token(&mut self, token: Token, op_dir: CompositeOp) -> Result<(), ParserError> {
        fn negate_rc<T: NegAssign>(mut t: Rc<T>) -> Rc<T> {
            match Rc::get_mut(&mut t) {
                Some(t) => {
                    t.neg_assign();
                }
                None => {
                }
            };

            t
        }

        match token {
            Token::Constant(Constant::Fixnum(n)) =>
                self.negate_number(n, |n| -n, Constant::Fixnum),
            Token::Constant(Constant::Integer(n)) =>
                self.negate_number(n, negate_rc, Constant::Integer),
            Token::Constant(Constant::Rational(n)) =>
                self.negate_number(n, negate_rc, Constant::Rational),
            Token::Constant(Constant::Float(n)) =>
                self.negate_number(
                    n,
                    |n| OrderedFloat(-n.into_inner()),
                    |n| Constant::Float(n)
                ),
            Token::Constant(c) =>
                if let Some(name) = self.atomize_constant(&c) {
                    if !self.shift_op(name, op_dir)? {
                        self.shift(Token::Constant(c), 0, TERM);
                    }
                } else {
                    self.shift(Token::Constant(c), 0, TERM);
                },
            Token::Var(v) => self.shift(Token::Var(v), 0, TERM),
            Token::Open   => self.shift(Token::Open, 1300, DELIMITER),
            Token::OpenCT => self.shift(Token::OpenCT, 1300, DELIMITER),
            Token::Close  =>
                if !self.reduce_term(op_dir) {
                    if !self.reduce_brackets() {
                        return Err(ParserError::IncompleteReduction(
                            self.lexer.line_num,
                            self.lexer.col_num,
                        ));
                    }
                },
            Token::OpenList  => self.shift(Token::OpenList, 1300, DELIMITER),
            Token::CloseList =>
                if !self.reduce_list()? {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ));
                },
            Token::OpenCurly => self.shift(Token::OpenCurly, 1300, DELIMITER),
            Token::CloseCurly =>
                if !self.reduce_curly()? {
                    return Err(ParserError::IncompleteReduction(
                        self.lexer.line_num,
                        self.lexer.col_num,
                    ));
                },
            Token::HeadTailSeparator => {
                /* '|' as an operator must have priority > 1000 and can only be infix.
                 * See: http://www.complang.tuwien.ac.at/ulrich/iso-prolog/dtc2#Res_A78
                 */
                let (priority, spec) = get_desc(clause_name!("|"), op_dir)
                    .map(|OpDesc { inf, spec, .. }| (inf, spec))
                    .unwrap_or((1000, DELIMITER));

                self.reduce_op(priority);
                self.shift(Token::HeadTailSeparator, priority, spec);
            },
            Token::Comma => {
                self.reduce_op(1000);
                self.shift(Token::Comma, 1000, XFY);
            },
            Token::End =>
                match self.stack.last().map(|t| t.tt) {
                    Some(TokenType::Open)
                  | Some(TokenType::OpenCT)
                  | Some(TokenType::OpenList)
                  | Some(TokenType::OpenCurly)
                  | Some(TokenType::HeadTailSeparator)
                  | Some(TokenType::Comma)
                      => return Err(ParserError::IncompleteReduction(self.lexer.line_num,
                                                                     self.lexer.col_num)),
                    _ => {}
                }
        }

        Ok(())
    }

    #[inline]
    pub fn eof(&mut self) -> Result<bool, ParserError> {
        self.lexer.eof()
    }

    pub fn read_term(&mut self, op_dir: CompositeOp) -> Result<Term, ParserError>
    {
        self.tokens = read_tokens(&mut self.lexer)?;

        while let Some(token) = self.tokens.pop() {
            self.shift_token(token, op_dir)?;
        }

        self.reduce_op(1400);

        if self.terms.len() > 1 || self.stack.len() > 1 {
            return Err(ParserError::IncompleteReduction(self.lexer.line_num, self.lexer.col_num));
        }

        match self.terms.pop() {
            Some(term) => if self.terms.is_empty() {
                Ok(term)
            } else {
                Err(ParserError::IncompleteReduction(self.lexer.line_num, self.lexer.col_num))
            },
            _ => Err(ParserError::IncompleteReduction(self.lexer.line_num, self.lexer.col_num))
        }
    }

    pub fn read(&mut self, op_dir: CompositeOp) -> Result<Vec<Term>, ParserError>
    {
        let mut terms = Vec::new();

        loop {
            terms.push(self.read_term(op_dir)?);

            if self.lexer.eof()? {
                break;
            }
        }

        Ok(terms)
    }
}
