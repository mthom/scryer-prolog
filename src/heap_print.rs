use prolog_parser::ast::*;
use prolog_parser::{
    alpha_numeric_char, capital_letter_char, clause_name, cut_char, decimal_digit_char,
    graphic_token_char, is_fx, is_infix, is_postfix, is_prefix, is_xf, is_xfx, is_xfy, is_yfx,
    semicolon_char, sign_char, single_quote_char, small_letter_char, solo_char,
    variable_indicator_char,
};

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::machine::heap::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::streams::*;
use crate::rug::{Integer, Rational};
use ordered_float::OrderedFloat;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::convert::TryFrom;
use std::iter::{once, FromIterator};
use std::net::{IpAddr, TcpListener};
use std::ops::{Range, RangeFrom};
use std::rc::Rc;

/* contains the location, name, precision and Specifier of the parent op. */
#[derive(Debug, Clone)]
pub(crate) enum DirectedOp {
    Left(ClauseName, SharedOpDesc),
    Right(ClauseName, SharedOpDesc),
}

impl DirectedOp {
    #[inline]
    fn as_str(&self) -> &str {
        match self {
            &DirectedOp::Left(ref name, _) | &DirectedOp::Right(ref name, _) => name.as_str(),
        }
    }

    #[inline]
    fn is_negative_sign(&self) -> bool {
        match self {
            &DirectedOp::Left(ref name, ref cell) | &DirectedOp::Right(ref name, ref cell) => {
                name.as_str() == "-" && is_prefix!(cell.assoc())
            }
        }
    }

    #[inline]
    fn is_left(&self) -> bool {
        if let &DirectedOp::Left(..) = self {
            true
        } else {
            false
        }
    }
}

fn needs_bracketing(child_spec: &SharedOpDesc, op: &DirectedOp) -> bool {
    match op {
        &DirectedOp::Left(ref name, ref cell) => {
            let (priority, spec) = cell.get();

            if name.as_str() == "-" {
                let child_assoc = child_spec.assoc();
                if is_prefix!(spec) && (is_postfix!(child_assoc) || is_infix!(child_assoc)) {
                    return true;
                }
            }

            let is_strict_right = is_yfx!(spec) || is_xfx!(spec) || is_fx!(spec);
            child_spec.prec() > priority || (child_spec.prec() == priority && is_strict_right)
        }
        &DirectedOp::Right(_, ref cell) => {
            let (priority, spec) = cell.get();
            let is_strict_left = is_xfx!(spec) || is_xfy!(spec) || is_xf!(spec);

            if child_spec.prec() > priority || (child_spec.prec() == priority && is_strict_left) {
                true
            } else if (is_postfix!(spec) || is_infix!(spec)) && !is_postfix!(child_spec.assoc()) {
                !SharedOpDesc::ptr_eq(&cell, &child_spec) && child_spec.prec() == priority
            } else {
                false
            }
        }
    }
}

impl<'a> HCPreOrderIterator<'a> {
    /*
     * descend into the subtree where the iterator is currently parked
     * and check that the leftmost leaf is a number, with every node
     * encountered on the way an infix or postfix operator, unblocked
     * by brackets.
     */
    fn leftmost_leaf_has_property<P>(&self, property_check: P) -> bool
    where
        P: Fn(Addr, &Heap) -> bool,
    {
        let mut addr = match self.state_stack.last().cloned() {
            Some(addr) => addr,
            None => return false,
        };

        let mut parent_spec = DirectedOp::Left(clause_name!("-"), SharedOpDesc::new(200, FY));

        loop {
            match self.machine_st.store(self.machine_st.deref(addr)) {
                Addr::Str(s) => match &self.machine_st.heap[s] {
                    &HeapCellValue::NamedStr(_, ref name, Some(ref spec))
                        if is_postfix!(spec.assoc()) || is_infix!(spec.assoc()) =>
                    {
                        if needs_bracketing(spec, &parent_spec) {
                            return false;
                        } else {
                            addr = Addr::HeapCell(s + 1);
                            parent_spec = DirectedOp::Right(name.clone(), spec.clone());
                        }
                    }
                    _ => {
                        return false;
                    }
                },
                addr => {
                    return property_check(addr, &self.machine_st.heap);
                }
            }
        }
    }

    fn immediate_leaf_has_property<P>(&self, property_check: P) -> bool
    where
        P: Fn(Addr, &Heap) -> bool,
    {
        let addr = match self.state_stack.last().cloned() {
            Some(addr) => addr,
            None => return false,
        };

        let addr = self.machine_st.store(self.machine_st.deref(addr));
        property_check(addr, &self.machine_st.heap)
    }
}

fn char_to_string(is_quoted: bool, c: char) -> String {
    match c {
        '\'' if is_quoted => "\\'".to_string(),
        '\n' if is_quoted => "\\n".to_string(),
        '\r' if is_quoted => "\\r".to_string(),
        '\t' if is_quoted => "\\t".to_string(),
        '\u{0b}' if is_quoted => "\\v".to_string(), // UTF-8 vertical tab
        '\u{0c}' if is_quoted => "\\f".to_string(), // UTF-8 form feed
        '\u{08}' if is_quoted => "\\b".to_string(), // UTF-8 backspace
        '\u{07}' if is_quoted => "\\a".to_string(), // UTF-8 alert
        '"' if is_quoted => "\\\"".to_string(),
        '\\' if is_quoted => "\\\\".to_string(),
        '\'' | '\n' | '\r' | '\t' | '\u{0b}' | '\u{0c}' | '\u{08}' | '\u{07}' | '"' | '\\' => {
            c.to_string()
        }
        '\u{a0}'..='\u{d6}' => c.to_string(),
        '\u{d8}'..='\u{f6}' => c.to_string(),
        '\u{f8}'..='\u{74f}' => c.to_string(),
        '\x20'..='\x7e' => c.to_string(),
        _ => format!("\\x{:x}\\", c as u32),
    }
}

#[derive(Debug, Clone)]
enum TokenOrRedirect {
    Atom(ClauseName),
    BarAsOp,
    Op(ClauseName, SharedOpDesc),
    NumberedVar(String),
    CompositeRedirect(usize, DirectedOp),
    FunctorRedirect(usize),
    IpAddr(IpAddr),
    Number(Number, Option<DirectedOp>),
    Open,
    Close,
    Comma,
    RawPtr(*const u8),
    Space,
    LeftCurly,
    RightCurly,
    OpenList(Rc<Cell<(bool, usize)>>),
    CloseList(Rc<Cell<(bool, usize)>>),
    HeadTailSeparator,
}

pub(crate) trait HCValueOutputter {
    type Output;

    fn new() -> Self;
    fn push_char(&mut self, c: char);
    fn append(&mut self, s: &str);
    fn begin_new_var(&mut self);
    fn insert(&mut self, index: usize, c: char);
    fn result(self) -> Self::Output;
    fn ends_with(&self, s: &str) -> bool;
    fn len(&self) -> usize;
    fn truncate(&mut self, len: usize);
    fn range(&self, range: Range<usize>) -> &str;
    fn range_from(&self, range: RangeFrom<usize>) -> &str;
}

#[derive(Debug)]
pub(crate) struct PrinterOutputter {
    contents: String,
}

impl HCValueOutputter for PrinterOutputter {
    type Output = String;

    fn new() -> Self {
        PrinterOutputter {
            contents: String::new(),
        }
    }

    fn append(&mut self, contents: &str) {
        if requires_space(&self.contents, contents) {
            self.push_char(' ');
        }

        self.contents += contents;
    }

    fn push_char(&mut self, c: char) {
        self.contents.push(c);
    }

    fn begin_new_var(&mut self) {
        if self.contents.len() != 0 {
            self.contents += ", ";
        }
    }

    fn insert(&mut self, idx: usize, c: char) {
        self.contents.insert(idx, c);
    }

    fn result(self) -> Self::Output {
        self.contents
    }

    fn ends_with(&self, s: &str) -> bool {
        self.contents.ends_with(s)
    }

    fn len(&self) -> usize {
        self.contents.len()
    }

    fn truncate(&mut self, len: usize) {
        self.contents.truncate(len);
    }

    fn range(&self, index: Range<usize>) -> &str {
        &self.contents.as_str()[index]
    }

    fn range_from(&self, index: RangeFrom<usize>) -> &str {
        &self.contents.as_str()[index]
    }
}

#[inline]
fn is_numbered_var(ct: &ClauseType, arity: usize) -> bool {
    arity == 1 && ct.name().as_str() == "$VAR"
}

#[inline]
fn negated_op_needs_bracketing(iter: &HCPreOrderIterator, op: &Option<DirectedOp>) -> bool {
    if let Some(ref op) = op {
        op.is_negative_sign()
            && iter.leftmost_leaf_has_property(|addr, heap| match Number::try_from((addr, heap)) {
                Ok(Number::Fixnum(n)) => n > 0,
                Ok(Number::Float(f)) => f > OrderedFloat(0f64),
                Ok(Number::Integer(n)) => &*n > &0,
                Ok(Number::Rational(n)) => &*n > &0,
                _ => false,
            })
    } else {
        false
    }
}

fn numbervar(n: Integer) -> Var {
    static CHAR_CODES: [char; 26] = [
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R',
        'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
    ];

    let i = n.mod_u(26) as usize;
    let j = n.div_rem_floor(Integer::from(26));
    let j = <(Integer, Integer)>::from(j).0;

    if j == 0 {
        CHAR_CODES[i].to_string()
    } else {
        format!("{}{}", CHAR_CODES[i], j)
    }
}

impl MachineState {
    pub(crate) fn numbervar(&self, offset: &Integer, addr: Addr) -> Option<Var> {
        let addr = self.store(self.deref(addr));

        match Number::try_from((addr, &self.heap)) {
            Ok(Number::Fixnum(n)) => {
                if n >= 0 {
                    Some(numbervar(Integer::from(offset + Integer::from(n))))
                } else {
                    None
                }
            }
            Ok(Number::Integer(n)) => {
                if &*n >= &0 {
                    Some(numbervar(Integer::from(offset + &*n)))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

type ReverseHeapVarDict = IndexMap<Addr, Rc<Var>>;

#[derive(Debug)]
pub(crate) struct HCPrinter<'a, Outputter> {
    outputter: Outputter,
    machine_st: &'a MachineState,
    op_dir: &'a OpDir,
    state_stack: Vec<TokenOrRedirect>,
    toplevel_spec: Option<DirectedOp>,
    heap_locs: ReverseHeapVarDict,
    printed_vars: IndexSet<Addr>,
    last_item_idx: usize,
    cyclic_terms: IndexMap<Addr, usize>,
    non_cyclic_terms: IndexSet<usize>,
    pub(crate) var_names: IndexMap<Addr, Var>,
    pub(crate) numbervars_offset: Integer,
    pub(crate) numbervars: bool,
    pub(crate) quoted: bool,
    pub(crate) ignore_ops: bool,
    pub(crate) print_strings_as_strs: bool,
    pub(crate) max_depth: usize,
}

macro_rules! push_space_if_amb {
    ($self:expr, $atom:expr, $action:block) => {
        if $self.ambiguity_check($atom) {
            $self.outputter.push_char(' ');
            $action;
        } else {
            $action;
        }
    };
}

pub(crate) fn requires_space(atom: &str, op: &str) -> bool {
    match atom.chars().last() {
        Some(ac) => op
            .chars()
            .next()
            .map(|oc| {
                if ac == '0' {
                    oc == '\'' || oc == '(' || alpha_numeric_char!(oc)
                } else if alpha_numeric_char!(ac) {
                    oc == '(' || alpha_numeric_char!(oc)
                } else if graphic_token_char!(ac) {
                    graphic_token_char!(oc)
                } else if variable_indicator_char!(ac) {
                    alpha_numeric_char!(oc)
                } else if capital_letter_char!(ac) {
                    alpha_numeric_char!(oc)
                } else if sign_char!(ac) {
                    sign_char!(oc) || decimal_digit_char!(oc)
                } else if single_quote_char!(ac) {
                    single_quote_char!(oc)
                } else {
                    false
                }
            })
            .unwrap_or(false),
        _ => false,
    }
}

fn non_quoted_graphic_token<Iter: Iterator<Item = char>>(mut iter: Iter, c: char) -> bool {
    if c == '/' {
        return match iter.next() {
            None => true,
            Some('*') => false, // if we start with comment token, we must quote.
            Some(c) => {
                if graphic_token_char!(c) {
                    iter.all(|c| graphic_token_char!(c))
                } else {
                    false
                }
            }
        };
    } else if c == '.' {
        return match iter.next() {
            None => false,
            Some(c) => {
                if graphic_token_char!(c) {
                    iter.all(|c| graphic_token_char!(c))
                } else {
                    false
                }
            }
        };
    } else {
        iter.all(|c| graphic_token_char!(c))
    }
}

pub(super) fn non_quoted_token<Iter: Iterator<Item = char>>(mut iter: Iter) -> bool {
    if let Some(c) = iter.next() {
        if small_letter_char!(c) {
            iter.all(|c| alpha_numeric_char!(c))
        } else if graphic_token_char!(c) {
            non_quoted_graphic_token(iter, c)
        } else if semicolon_char!(c) {
            iter.next().is_none()
        } else if cut_char!(c) {
            iter.next().is_none()
        } else if c == '[' {
            iter.next() == Some(']') && iter.next().is_none()
        } else if c == '{' {
            iter.next() == Some('}') && iter.next().is_none()
        } else if solo_char!(c) {
            !(c == '(' || c == ')' || c == '}' || c == ']' || c == ',' || c == '%' || c == '|')
        } else {
            false
        }
    } else {
        false
    }
}

#[inline]
fn functor_location(addr: &Addr) -> Option<usize> {
    Some(match addr {
        &Addr::Lis(l) => l,
        &Addr::Str(s) => s,
        &Addr::PStrLocation(h, _) => h,
        _ => {
            return None;
        }
    })
}

impl<'a, Outputter: HCValueOutputter> HCPrinter<'a, Outputter> {
    pub(crate) fn new(machine_st: &'a MachineState, op_dir: &'a OpDir, output: Outputter) -> Self {
        HCPrinter {
            outputter: output,
            machine_st,
            op_dir,
            state_stack: vec![],
            heap_locs: ReverseHeapVarDict::new(),
            toplevel_spec: None,
            printed_vars: IndexSet::new(),
            last_item_idx: 0,
            numbervars: false,
            numbervars_offset: Integer::from(0),
            quoted: false,
            ignore_ops: false,
            cyclic_terms: IndexMap::new(),
            non_cyclic_terms: IndexSet::new(),
            var_names: IndexMap::new(),
            print_strings_as_strs: false,
            max_depth: 0,
        }
    }

    #[inline]
    fn ambiguity_check(&self, atom: &str) -> bool {
        let tail = self.outputter.range_from(self.last_item_idx..);
        requires_space(tail, atom)
    }

    fn enqueue_op(
        &mut self,
        iter: &mut HCPreOrderIterator,
        mut max_depth: usize,
        ct: ClauseType,
        spec: SharedOpDesc,
    ) {
        if is_postfix!(spec.assoc()) {
            if self.check_max_depth(&mut max_depth) {
                iter.stack().pop();

                self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));

                return;
            }

            let right_directed_op = DirectedOp::Right(ct.name(), spec.clone());

            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                max_depth,
                right_directed_op,
            ));
        } else if is_prefix!(spec.assoc()) {
            match ct.name().as_str() {
                "-" | "\\" => {
                    self.format_prefix_op_with_space(iter, max_depth, ct.name(), spec);
                    return;
                }
                _ => {}
            };

            if self.check_max_depth(&mut max_depth) {
                iter.stack().pop();

                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));
                self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));

                return;
            }

            let left_directed_op = DirectedOp::Left(ct.name(), spec.clone());

            self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                max_depth,
                left_directed_op,
            ));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
        } else {
            match ct.name().as_str() {
                "|" => {
                    self.format_bar_separator_op(iter, max_depth, ct.name(), spec);
                    return;
                }
                _ => {}
            };

            if self.check_max_depth(&mut max_depth) {
                iter.stack().pop();
                iter.stack().pop();

                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));
                self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));

                return;
            }

            let left_directed_op = DirectedOp::Left(ct.name(), spec.clone());
            let right_directed_op = DirectedOp::Right(ct.name(), spec.clone());

            self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                max_depth,
                left_directed_op,
            ));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                max_depth,
                right_directed_op,
            ));
        }
    }

    fn format_struct(
        &mut self,
        iter: &mut HCPreOrderIterator,
        mut max_depth: usize,
        arity: usize,
        name: ClauseName,
    ) -> bool {
        if self.check_max_depth(&mut max_depth) {
            for _ in 0..arity {
                iter.stack().pop();
            }

            self.state_stack.push(TokenOrRedirect::Close);
            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            self.state_stack.push(TokenOrRedirect::Open);

            self.state_stack.push(TokenOrRedirect::Atom(name));

            return false;
        }

        self.state_stack.push(TokenOrRedirect::Close);

        for _ in 0..arity {
            self.state_stack
                .push(TokenOrRedirect::FunctorRedirect(max_depth));
            self.state_stack.push(TokenOrRedirect::Comma);
        }

        self.state_stack.pop();

        self.state_stack.push(TokenOrRedirect::Open);
        self.state_stack.push(TokenOrRedirect::Atom(name));

        true
    }

    fn format_prefix_op_with_space(
        &mut self,
        iter: &mut HCPreOrderIterator,
        mut max_depth: usize,
        name: ClauseName,
        spec: SharedOpDesc,
    ) {
        if self.check_max_depth(&mut max_depth) {
            iter.stack().pop();

            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            self.state_stack.push(TokenOrRedirect::Space);
            self.state_stack.push(TokenOrRedirect::Atom(name));

            return;
        }

        let op = DirectedOp::Left(name.clone(), spec);

        self.state_stack
            .push(TokenOrRedirect::CompositeRedirect(max_depth, op));
        self.state_stack.push(TokenOrRedirect::Space);
        self.state_stack.push(TokenOrRedirect::Atom(name));
    }

    fn format_bar_separator_op(
        &mut self,
        iter: &mut HCPreOrderIterator,
        mut max_depth: usize,
        name: ClauseName,
        spec: SharedOpDesc,
    ) {
        if self.check_max_depth(&mut max_depth) {
            iter.stack().pop();

            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            self.state_stack.push(TokenOrRedirect::BarAsOp);
            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));

            return;
        }

        let left_directed_op = DirectedOp::Left(name.clone(), spec.clone());
        let right_directed_op = DirectedOp::Right(name.clone(), spec.clone());

        self.state_stack.push(TokenOrRedirect::CompositeRedirect(
            max_depth,
            left_directed_op,
        ));
        self.state_stack.push(TokenOrRedirect::BarAsOp);
        self.state_stack.push(TokenOrRedirect::CompositeRedirect(
            max_depth,
            right_directed_op,
        ));
    }

    fn format_curly_braces(&mut self, iter: &mut HCPreOrderIterator, mut max_depth: usize) -> bool {
        if self.check_max_depth(&mut max_depth) {
            iter.stack().pop();

            self.state_stack.push(TokenOrRedirect::RightCurly);
            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            self.state_stack.push(TokenOrRedirect::LeftCurly);

            return false;
        }

        self.state_stack.push(TokenOrRedirect::RightCurly);
        self.state_stack
            .push(TokenOrRedirect::FunctorRedirect(max_depth));
        self.state_stack.push(TokenOrRedirect::LeftCurly);

        true
    }

    fn format_numbered_vars(&mut self, iter: &mut HCPreOrderIterator) -> bool {
        let addr = iter.stack().last().cloned().unwrap();

        // 7.10.4
        if let Some(var) = iter.machine_st().numbervar(&self.numbervars_offset, addr) {
            iter.stack().pop();
            self.state_stack.push(TokenOrRedirect::NumberedVar(var));
            return true;
        }

        false
    }

    fn format_clause(
        &mut self,
        iter: &mut HCPreOrderIterator,
        max_depth: usize,
        arity: usize,
        ct: ClauseType,
    ) -> bool {
        if self.numbervars && is_numbered_var(&ct, arity) {
            if self.format_numbered_vars(iter) {
                return true;
            }
        }

        if let Some(spec) = ct.spec() {
            if "." == ct.name().as_str() && is_infix!(spec.assoc()) {
                if !self.ignore_ops {
                    self.push_list(iter, max_depth);
                    return true;
                }
            }

            if !self.ignore_ops && spec.prec() > 0 {
                self.enqueue_op(iter, max_depth, ct, spec);
                return true;
            }
        }

        return match (ct.name().as_str(), arity) {
            ("{}", 1) if !self.ignore_ops => self.format_curly_braces(iter, max_depth),
            _ => self.format_struct(iter, max_depth, arity, ct.name()),
        };
    }

    #[inline]
    fn push_char(&mut self, c: char) {
        self.outputter.push_char(c);
        self.last_item_idx = self.outputter.len();
    }

    #[inline]
    fn append_str(&mut self, s: &str) {
        self.last_item_idx = self.outputter.len();
        self.outputter.append(s);
    }

    fn offset_as_string(&mut self, iter: &mut HCPreOrderIterator, addr: Addr) -> Option<Var> {
        if let Some(var) = self.var_names.get(&addr) {
            if addr.as_var().is_some() {
                return Some(format!("{}", var));
            } else {
                iter.stack().push(addr);
                return None;
            }
        }

        match addr {
            Addr::Lis(h) | Addr::Str(h) => Some(format!("{}", h)),
            _ => {
                if let Some(r) = addr.as_var() {
                    match r {
                        Ref::StackCell(fr, sc) => Some(format!("_s_{}_{}", fr, sc)),
                        Ref::HeapCell(h) | Ref::AttrVar(h) => Some(format!("_{}", h)),
                    }
                } else {
                    None
                }
            }
        }
    }

    fn record_children_as_non_cyclic(&mut self, addr: &Addr) {
        match addr {
            &Addr::Lis(l) => {
                let c1 = self
                    .machine_st
                    .store(self.machine_st.deref(Addr::HeapCell(l)));
                let c2 = self
                    .machine_st
                    .store(self.machine_st.deref(Addr::HeapCell(l + 1)));

                if let Some(c) = functor_location(&c1) {
                    self.non_cyclic_terms.insert(c);
                }

                if let Some(c) = functor_location(&c2) {
                    self.non_cyclic_terms.insert(c);
                }
            }
            &Addr::Str(s) => {
                let arity = match &self.machine_st.heap[s] {
                    HeapCellValue::NamedStr(arity, ..) => arity,
                    _ => {
                        unreachable!()
                    }
                };

                for i in 1..arity + 1 {
                    let c = self
                        .machine_st
                        .store(self.machine_st.deref(Addr::HeapCell(s + i)));

                    if let Some(c) = functor_location(&c) {
                        self.non_cyclic_terms.insert(c);
                    }
                }
            }
            &Addr::PStrLocation(h, _) => {
                let tail = self.machine_st.heap[h + 1].as_addr(h + 1);
                let tail = self.machine_st.store(self.machine_st.deref(tail));

                if let Some(c) = functor_location(&tail) {
                    self.non_cyclic_terms.insert(c);
                }
            }
            _ => {}
        }
    }

    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator) -> Option<Addr> {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            if let Some(var) = self.var_names.get(&addr) {
                self.heap_locs.insert(addr.clone(), Rc::new(var.clone()));
            }

            match self.heap_locs.get(&addr).cloned() {
                Some(var) if addr.is_ref() => {
                    iter.stack().pop();

                    push_space_if_amb!(self, &var, {
                        self.append_str(&var);
                    });

                    return None;
                }
                var_opt => {
                    let offset = match functor_location(&addr) {
                        Some(offset) => offset,
                        None => {
                            return iter.next();
                        }
                    };

                    if !self.non_cyclic_terms.contains(&offset) {
                        if let Some(reps) = self.cyclic_terms.get(&addr).cloned() {
                            if reps > 0 {
                                self.cyclic_terms.insert(addr, reps - 1);
                            } else {
                                match var_opt {
                                    Some(var) => {
                                        push_space_if_amb!(self, &var, {
                                            self.append_str(&var);
                                        });

                                        iter.stack().pop();
                                    }
                                    None => {
                                        push_space_if_amb!(self, "...", {
                                            self.append_str("...");
                                        });

                                        iter.stack().pop();
                                        self.cyclic_terms.insert(addr, 2);
                                    }
                                }

                                return None;
                            }
                        } else if self.machine_st.is_cyclic_term(addr.clone()) {
                            if var_opt.is_some() {
                                self.cyclic_terms.insert(addr, 0);
                            } else {
                                self.cyclic_terms.insert(addr, 2);
                            }
                        } else {
                            self.record_children_as_non_cyclic(&addr);
                            self.non_cyclic_terms.insert(offset);
                        }
                    } else {
                        self.record_children_as_non_cyclic(&addr);
                    }

                    iter.next()
                }
            }
        })
    }

    fn print_atom(&mut self, atom: &ClauseName) {
        let result = self.print_op_addendum(atom.as_str());

        push_space_if_amb!(self, result.as_str(), {
            self.append_str(&result);
        });
    }

    fn print_op_addendum(&mut self, atom: &str) -> String {
        if !self.quoted || non_quoted_token(atom.chars()) {
            atom.to_string()
        } else if atom == "''" {
            "''".to_string()
        } else {
            let mut result = String::new();

            if self.quoted {
                result.push('\'');
            }

            for c in atom.chars() {
                result += &char_to_string(self.quoted, c);
            }

            if self.quoted {
                result.push('\'');
            }

            result
        }
    }

    fn print_op(&mut self, atom: &str) {
        let result = if atom == "," {
            ",".to_string()
        } else {
            self.print_op_addendum(atom)
        };

        push_space_if_amb!(self, &result, {
            self.append_str(&result);
        });
    }

    #[inline]
    fn print_ip_addr(&mut self, ip: IpAddr) {
        self.push_char('\'');
        self.append_str(&format!("{}", ip));
        self.push_char('\'');
    }

    #[inline]
    fn print_raw_ptr(&mut self, ptr: *const u8) {
        self.append_str(&format!("0x{:x}", ptr as usize));
    }

    fn print_number(&mut self, n: Number, op: &Option<DirectedOp>) {
        let add_brackets = if let Some(op) = op {
            op.is_negative_sign() && n.is_positive()
        } else {
            false
        };

        if add_brackets {
            self.push_char('(');
        }

        match n {
            Number::Float(fl) => {
                if &fl == &OrderedFloat(0f64) {
                    push_space_if_amb!(self, "0.0", {
                        self.append_str("0.0");
                    });
                } else {
                    let OrderedFloat(fl) = fl;
                    let output_str = format!("{0:<20?}", fl);

                    push_space_if_amb!(self, &output_str, {
                        self.append_str(&output_str.trim());
                    });
                }
            }
            Number::Rational(r) => {
                self.print_rational(&r, add_brackets);
                return;
            }
            n => {
                let output_str = format!("{}", n);

                push_space_if_amb!(self, &output_str, {
                    self.append_str(&output_str);
                });
            }
        }

        if add_brackets {
            self.push_char(')');
        }
    }

    fn print_rational(&mut self, r: &Rational, add_brackets: bool) {
        match self.op_dir.get(&(clause_name!("rdiv"), Fixity::In)) {
            Some(OpDirValue(ref spec)) => {
                if add_brackets {
                    self.state_stack.push(TokenOrRedirect::Close);
                }

                let rdiv_ct = clause_name!("rdiv");

                let left_directed_op = if spec.prec() > 0 {
                    Some(DirectedOp::Left(rdiv_ct.clone(), spec.clone()))
                } else {
                    None
                };

                let right_directed_op = if spec.prec() > 0 {
                    Some(DirectedOp::Right(rdiv_ct.clone(), spec.clone()))
                } else {
                    None
                };

                if spec.prec() > 0 {
                    self.state_stack.push(TokenOrRedirect::Number(
                        Number::from(r.denom()),
                        left_directed_op,
                    ));

                    self.state_stack
                        .push(TokenOrRedirect::Op(rdiv_ct, spec.clone()));

                    self.state_stack.push(TokenOrRedirect::Number(
                        Number::from(r.numer()),
                        right_directed_op,
                    ));
                } else {
                    self.state_stack.push(TokenOrRedirect::Close);

                    self.state_stack
                        .push(TokenOrRedirect::Number(Number::from(r.denom()), None));

                    self.state_stack.push(TokenOrRedirect::Comma);

                    self.state_stack
                        .push(TokenOrRedirect::Number(Number::from(r.numer()), None));

                    self.state_stack.push(TokenOrRedirect::Open);
                    self.state_stack.push(TokenOrRedirect::Atom(rdiv_ct));
                }

                return;
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn print_char(&mut self, is_quoted: bool, c: char) {
        if non_quoted_token(once(c)) {
            let c = char_to_string(false, c);

            push_space_if_amb!(self, &c, {
                self.append_str(c.as_str());
            });
        } else {
            let mut result = String::new();

            if self.quoted {
                result.push('\'');
                result += &char_to_string(is_quoted, c);
                result.push('\'');
            } else {
                result += &char_to_string(is_quoted, c);
            }

            push_space_if_amb!(self, &result, {
                self.append_str(result.as_str());
            });
        }
    }

    fn print_proper_string(&mut self, buf: String, max_depth: usize) {
        self.push_char('"');

        let buf = if max_depth == 0 {
            String::from_iter(buf.chars().map(|c| char_to_string(self.quoted, c)))
        } else {
            let mut char_count = 0;
            let mut buf = String::from_iter(buf.chars().take(max_depth).map(|c| {
                char_count += 1;
                char_to_string(self.quoted, c)
            }));

            if char_count == max_depth {
                buf += " ...";
            }

            buf
        };

        self.append_str(&buf);
        self.push_char('"');
    }

    fn print_list_like(&mut self, iter: &mut HCPreOrderIterator, addr: Addr, mut max_depth: usize) {
        if self.check_max_depth(&mut max_depth) {
            iter.stack().pop();
            iter.stack().pop();

            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            return;
        }

        let mut heap_pstr_iter = self.machine_st.heap_pstr_iter(addr);

        let buf = heap_pstr_iter.to_string();

        if buf.is_empty() {
            self.push_list(iter, max_depth);
            return;
        }

        iter.stack().pop();
        iter.stack().pop();

        let end_addr = heap_pstr_iter.focus();

        let at_cdr = self.at_cdr(",");

        if !at_cdr && Addr::EmptyList == end_addr {
            if !self.ignore_ops {
                self.print_proper_string(buf, max_depth);
                return;
            }
        }

        let buf_len = buf.len();

        let buf_iter: Box<dyn Iterator<Item = char>> = if self.max_depth == 0 {
            Box::new(buf.chars())
        } else {
            Box::new(buf.chars().take(max_depth))
        };

        let mut byte_len = 0;

        if self.ignore_ops {
            let mut char_count = 0;

            for c in buf_iter {
                self.append_str("'.'");
                self.push_char('(');

                self.print_char(self.quoted, c);
                self.push_char(',');

                char_count += 1;
                byte_len += c.len_utf8();
            }

            for _ in 0..char_count {
                self.state_stack.push(TokenOrRedirect::Close);
            }

            if self.max_depth > 0 && buf_len > byte_len {
                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));
            } else {
                self.state_stack
                    .push(TokenOrRedirect::FunctorRedirect(max_depth));
                iter.stack().push(end_addr);
            }
        } else {
            let switch = if !at_cdr {
                self.push_char('[');
                true
            } else {
                false
            };

            for c in buf_iter {
                self.print_char(self.quoted, c);
                self.push_char(',');

                byte_len += c.len_utf8();
            }

            self.state_stack
                .push(TokenOrRedirect::CloseList(Rc::new(Cell::new((switch, 0)))));

            if self.max_depth > 0 && buf_len > byte_len {
                self.state_stack
                    .push(TokenOrRedirect::Atom(clause_name!("...")));
            } else {
                self.outputter
                    .truncate(self.outputter.len() - ','.len_utf8());
                self.state_stack
                    .push(TokenOrRedirect::FunctorRedirect(max_depth));

                iter.stack().push(end_addr);
            }

            self.state_stack.push(TokenOrRedirect::HeadTailSeparator);
        }
    }

    fn check_max_depth(&mut self, max_depth: &mut usize) -> bool {
        if self.max_depth > 0 && *max_depth == 0 {
            return true;
        }

        if *max_depth > 0 {
            *max_depth -= 1;
        }

        false
    }

    fn push_list(&mut self, iter: &mut HCPreOrderIterator, mut max_depth: usize) {
        if self.check_max_depth(&mut max_depth) {
            iter.stack().pop();
            iter.stack().pop();

            let cell = Rc::new(Cell::new((true, 0)));

            self.state_stack
                .push(TokenOrRedirect::CloseList(cell.clone()));
            self.state_stack
                .push(TokenOrRedirect::Atom(clause_name!("...")));
            self.state_stack.push(TokenOrRedirect::OpenList(cell));

            return;
        }

        let cell = Rc::new(Cell::new((true, max_depth)));

        self.state_stack
            .push(TokenOrRedirect::CloseList(cell.clone()));

        self.state_stack
            .push(TokenOrRedirect::FunctorRedirect(max_depth));
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
        self.state_stack
            .push(TokenOrRedirect::FunctorRedirect(max_depth));

        self.state_stack.push(TokenOrRedirect::OpenList(cell));
    }

    fn handle_op_as_struct(
        &mut self,
        name: ClauseName,
        arity: usize,
        iter: &mut HCPreOrderIterator,
        op: &Option<DirectedOp>,
        is_functor_redirect: bool,
        spec: SharedOpDesc,
        negated_operand: bool,
        max_depth: usize,
    ) {
        let add_brackets = if !self.ignore_ops {
            negated_operand
                || if let Some(ref op) = op {
                    if self.numbervars && arity == 1 && name.as_str() == "$VAR" {
                        !iter.immediate_leaf_has_property(|addr, heap| {
                            match heap.index_addr(&addr).as_ref() {
                                &HeapCellValue::Integer(ref n) => &**n >= &0,
                                &HeapCellValue::Addr(Addr::Fixnum(n)) => n >= 0,
                                &HeapCellValue::Addr(Addr::Float(f)) => f >= OrderedFloat(0f64),
                                &HeapCellValue::Rational(ref r) => &**r >= &0,
                                _ => false,
                            }
                        }) && needs_bracketing(&spec, op)
                    } else {
                        needs_bracketing(&spec, op)
                    }
                } else {
                    is_functor_redirect && spec.prec() >= 1000
                }
        } else {
            false
        };

        if add_brackets {
            self.state_stack.push(TokenOrRedirect::Close);
        }

        let ct = ClauseType::from(name.clone(), arity, Some(spec));

        if self.format_clause(iter, max_depth, arity, ct) {
            if add_brackets {
                self.state_stack.push(TokenOrRedirect::Open);

                if let Some(ref op) = &op {
                    if op.is_left() && requires_space(op.as_str(), "(") {
                        self.state_stack.push(TokenOrRedirect::Space);
                    }
                }
            }
        }
    }

    fn print_tcp_listener(
        &mut self,
        iter: &mut HCPreOrderIterator,
        tcp_listener: &TcpListener,
        max_depth: usize,
    ) {
        let (ip, port) = if let Some(addr) = tcp_listener.local_addr().ok() {
            (addr.ip(), Number::from(addr.port() as isize))
        } else {
            let disconnected_atom = clause_name!("$disconnected_tcp_listener");
            self.state_stack
                .push(TokenOrRedirect::Atom(disconnected_atom));

            return;
        };

        if self.format_struct(iter, max_depth, 1, clause_name!("$tcp_listener")) {
            let atom = self.state_stack.pop().unwrap();

            self.state_stack.pop();
            self.state_stack.pop();

            self.state_stack.push(TokenOrRedirect::Number(port, None));
            self.state_stack.push(TokenOrRedirect::Comma);
            self.state_stack.push(TokenOrRedirect::IpAddr(ip));

            self.state_stack.push(TokenOrRedirect::Open);
            self.state_stack.push(atom);
        }
    }

    fn print_stream(&mut self, iter: &mut HCPreOrderIterator, stream: &Stream, max_depth: usize) {
        if let Some(alias) = &stream.options().alias {
            self.print_atom(alias);
        } else {
            if self.format_struct(iter, max_depth, 1, clause_name!("$stream")) {
                let atom = if stream.is_stdout() || stream.is_stdin() || stream.is_stderr() {
                    TokenOrRedirect::Atom(clause_name!("user"))
                } else {
                    TokenOrRedirect::RawPtr(stream.as_ptr())
                };

                let stream_root = self.state_stack.pop().unwrap();

                self.state_stack.pop();
                self.state_stack.pop();

                self.state_stack.push(atom);
                self.state_stack.push(TokenOrRedirect::Open);
                self.state_stack.push(stream_root);
            }
        }
    }

    fn handle_heap_term(
        &mut self,
        iter: &mut HCPreOrderIterator,
        op: Option<DirectedOp>,
        is_functor_redirect: bool,
        max_depth: usize,
    ) {
        let negated_operand = negated_op_needs_bracketing(iter, &op);

        let addr = match self.check_for_seen(iter) {
            Some(addr) => addr,
            None => return,
        };

        match self.machine_st.heap.index_addr(&addr).as_ref() {
            &HeapCellValue::NamedStr(arity, ref name, ref spec) => {
                let spec =
                    fetch_op_spec_from_existing(name.clone(), arity, spec.clone(), self.op_dir);

                if let Some(spec) = spec {
                    self.handle_op_as_struct(
                        name.clone(),
                        arity,
                        iter,
                        &op,
                        is_functor_redirect,
                        spec.clone(),
                        negated_operand,
                        max_depth,
                    );
                } else {
                    push_space_if_amb!(self, name.as_str(), {
                        let ct = ClauseType::from(name.clone(), arity, spec);
                        self.format_clause(iter, max_depth, arity, ct);
                    });
                }
            }
            &HeapCellValue::Atom(ref atom, ref spec) => {
                if let Some(_) = fetch_atom_op_spec(atom.clone(), spec.clone(), self.op_dir) {
                    let mut result = String::new();

                    if let Some(ref op) = op {
                        if self.outputter.ends_with(&format!(" {}", op.as_str())) {
                            result.push(' ');
                        }

                        result.push('(');
                    }

                    result += &self.print_op_addendum(atom.as_str());

                    if op.is_some() {
                        result.push(')');
                    }

                    push_space_if_amb!(self, &result, {
                        self.append_str(&result);
                    });
                } else {
                    push_space_if_amb!(self, atom.as_str(), {
                        self.print_atom(&atom);
                    });
                }
            }
            &HeapCellValue::Addr(Addr::Char(c)) => {
                self.print_char(self.quoted, c);
            }
            &HeapCellValue::Addr(Addr::CutPoint(b)) => {
                self.append_str(&format!("{}", b));
            }
            &HeapCellValue::Addr(Addr::EmptyList) => {
                if !self.at_cdr("") {
                    self.append_str("[]");
                }
            }
            &HeapCellValue::Addr(Addr::Float(n)) => {
                self.print_number(Number::Float(n), &op);
            }
            &HeapCellValue::Addr(Addr::Fixnum(n)) => {
                self.print_number(Number::Fixnum(n), &op);
            }
            &HeapCellValue::Addr(Addr::Usize(u)) => {
                self.append_str(&format!("{}", u));
            }
            &HeapCellValue::Addr(Addr::PStrLocation(h, n)) => {
                self.print_list_like(iter, Addr::PStrLocation(h, n), max_depth);
            }
            &HeapCellValue::Addr(Addr::Lis(l)) => {
                if self.ignore_ops {
                    self.format_struct(iter, max_depth, 2, clause_name!("."));
                } else {
                    self.print_list_like(iter, Addr::Lis(l), max_depth);
                }
            }
            &HeapCellValue::Addr(addr) => {
                if let Some(offset_str) = self.offset_as_string(iter, addr) {
                    push_space_if_amb!(self, &offset_str, {
                        self.append_str(offset_str.as_str());
                    })
                }
            }
            &HeapCellValue::Integer(ref n) => {
                self.print_number(Number::Integer(n.clone()), &op);
            }
            &HeapCellValue::Rational(ref n) => {
                self.print_number(Number::Rational(n.clone()), &op);
            }
            &HeapCellValue::Stream(ref stream) => {
                self.print_stream(iter, stream, max_depth);
            }
            &HeapCellValue::TcpListener(ref tcp_listener) => {
                self.print_tcp_listener(iter, tcp_listener, max_depth);
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn at_cdr(&mut self, tr: &str) -> bool {
        let len = self.outputter.len();

        if self.outputter.ends_with("|") {
            self.outputter.truncate(len - "|".len());
            self.append_str(tr);

            true
        } else {
            false
        }
    }

    pub(crate) fn print(mut self, addr: Addr) -> Outputter {
        let mut iter = self.machine_st.pre_order_iter(addr);

        loop {
            if let Some(loc_data) = self.state_stack.pop() {
                match loc_data {
                    TokenOrRedirect::Atom(atom) => self.print_atom(&atom),
                    TokenOrRedirect::BarAsOp => self.append_str(" | "),
                    TokenOrRedirect::Op(atom, _) => self.print_op(atom.as_str()),
                    TokenOrRedirect::NumberedVar(num_var) => self.append_str(num_var.as_str()),
                    TokenOrRedirect::CompositeRedirect(max_depth, op) => {
                        self.handle_heap_term(&mut iter, Some(op), false, max_depth)
                    }
                    TokenOrRedirect::FunctorRedirect(max_depth) => {
                        self.handle_heap_term(&mut iter, None, true, max_depth)
                    }
                    TokenOrRedirect::Close => self.push_char(')'),
                    TokenOrRedirect::IpAddr(ip) => self.print_ip_addr(ip),
                    TokenOrRedirect::RawPtr(ptr) => self.print_raw_ptr(ptr),
                    TokenOrRedirect::Open => self.push_char('('),
                    TokenOrRedirect::OpenList(delimit) => {
                        if !self.at_cdr(",") {
                            self.push_char('[');
                        } else {
                            let (_, max_depth) = delimit.get();
                            delimit.set((false, max_depth));
                        }
                    }
                    TokenOrRedirect::CloseList(delimit) => {
                        if delimit.get().0 {
                            self.push_char(']');
                        }
                    }
                    TokenOrRedirect::HeadTailSeparator => self.append_str("|"),
                    TokenOrRedirect::Number(n, op) => self.print_number(n, &op),
                    TokenOrRedirect::Comma => self.append_str(","),
                    TokenOrRedirect::Space => self.push_char(' '),
                    TokenOrRedirect::LeftCurly => self.push_char('{'),
                    TokenOrRedirect::RightCurly => self.push_char('}'),
                }
            } else if !iter.stack().is_empty() {
                let spec = self.toplevel_spec.take();
                self.handle_heap_term(&mut iter, spec, false, self.max_depth);
            } else {
                break;
            }
        }

        self.outputter
    }
}
