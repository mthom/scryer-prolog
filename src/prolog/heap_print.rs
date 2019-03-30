use prolog_parser::ast::*;

use prolog::clause_types::*;
use prolog::heap_iter::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::num::*;
use prolog::ordered_float::OrderedFloat;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::ops::{Range, RangeFrom};
use std::rc::Rc;

/* contains the location, name, precision and Specifier of the parent op. */
#[derive(Clone)]
pub enum DirectedOp {
    Left(ClauseName, (usize, Specifier)),
    Right(ClauseName, (usize, Specifier)),
}

impl DirectedOp {
    #[inline]
    fn as_str(&self) -> &str {
        match self {
            &DirectedOp::Left(ref name, _) | &DirectedOp::Right(ref name, _) =>
                name.as_str()
        }
    }

    #[inline]
    fn is_negative_sign(&self) -> bool {
        match self {
            &DirectedOp::Left(ref name, (_, spec)) | &DirectedOp::Right(ref name, (_, spec)) =>
                name.as_str() == "-" && is_prefix!(spec)
        }
    }
}

fn needs_bracketing(child_spec: (usize, Specifier), op: &DirectedOp) -> bool
{
    match op {
        &DirectedOp::Left(_, (priority, spec)) => {
            let is_strict_right = is_yfx!(spec) || is_xfx!(spec) || is_fx!(spec);
            child_spec.0 > priority || (child_spec.0 == priority && is_strict_right)
        },
        &DirectedOp::Right(_, (priority, spec)) => {
            let is_strict_left = is_xfx!(spec) || is_xfy!(spec) || is_xf!(spec);
            child_spec.0 > priority || (child_spec.0 == priority && is_strict_left)
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
    fn leftmost_leaf_is_positive_number(&self) -> bool {
        let mut addr = match self.state_stack.last().cloned() {
            Some(addr) => addr,
            None => return false
        };

        let mut parent_spec = DirectedOp::Left(clause_name!("-"), (200, FY));

        loop {
            match self.machine_st.store(self.machine_st.deref(addr)) {
                Addr::Str(s) =>
                    match &self.machine_st.heap[s] {
                        &HeapCellValue::NamedStr(_, ref name, Some(spec))
                            if is_postfix!(spec.1) || is_infix!(spec.1) =>
                                if needs_bracketing(spec, &parent_spec) {
                                    return false;
                                } else {
                                    addr = Addr::HeapCell(s+1);
                                    parent_spec = DirectedOp::Right(name.clone(), spec);
                                },
                        _ =>
                            return false
                    },
                Addr::Con(Constant::Number(n)) =>
                    return n.is_positive(),
                _ =>
                    return false
            }
        }
    }
}

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(ClauseName),
    Op(ClauseName, (usize, Specifier)),
    NumberedVar(String),
    CompositeRedirect(DirectedOp),
    FunctorRedirect,
    Open,
    Close,
    Comma,
    Space,
    LeftCurly,
    RightCurly,
    OpenList(Rc<Cell<bool>>),
    CloseList(Rc<Cell<bool>>),
    HeadTailSeparator,
}

pub trait HCValueOutputter {
    type Output;

    fn new() -> Self;
    fn push_char(&mut self, char);
    fn append(&mut self, &str);
    fn begin_new_var(&mut self);
    fn insert(&mut self, usize, char);
    fn result(self) -> Self::Output;
    fn ends_with(&self, &str) -> bool;
    fn len(&self) -> usize;
    fn truncate(&mut self, usize);
    fn range(&self, Range<usize>) -> &str;
    fn range_from(&self, RangeFrom<usize>) -> &str;
}

pub struct PrinterOutputter {
    contents: String
}

impl HCValueOutputter for PrinterOutputter {
    type Output = String;

    fn new() -> Self {
        PrinterOutputter { contents: String::new() }
    }

    fn append(&mut self, contents: &str) {
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
    arity == 1 && if let &ClauseType::Named(ref name, ..) = ct {
        name.as_str() == "$VAR"
    } else {
        false
    }
}

#[inline]
fn negated_op_needs_bracketing(iter: &HCPreOrderIterator, op: &Option<DirectedOp>) -> bool
{
    if let &Some(ref op) = op {
        op.is_negative_sign() && iter.leftmost_leaf_is_positive_number()
    } else {
        false
    }
}

impl MachineState {
    pub fn numbervar(&self, offset: &BigInt, addr: Addr) -> Option<Var> {
        static CHAR_CODES: [char; 26] = ['A','B','C','D','E','F','G','H','I','J',
                                         'K','L','M','N','O','P','Q','R','S','T',
                                         'U','V','W','X','Y','Z'];

        match self.store(self.deref(addr)) {
            Addr::Con(Constant::Number(Number::Integer(ref n)))
                if !n.is_negative() => {
                    let n = offset + n.as_ref();

                    let i = n.mod_floor(&BigInt::from(26)).to_usize().unwrap();
                    let j = n.div_floor(&BigInt::from(26));

                    Some(if j.is_zero() {
                        CHAR_CODES[i].to_string()
                    } else {
                        format!("{}{}", CHAR_CODES[i], j)
                    })
                },
            _ => None
        }
    }
}

type ReverseHeapVarDict = HashMap<Addr, Rc<Var>>;

pub struct HCPrinter<'a, Outputter> {
    outputter:    Outputter,
    machine_st:   &'a MachineState,
    state_stack:  Vec<TokenOrRedirect>,
    toplevel_spec: Option<DirectedOp>,
    heap_locs:    ReverseHeapVarDict,
    printed_vars: HashSet<Addr>,
    last_item_idx: usize,
    pub(crate) numbervars_offset: BigInt,
    pub(crate) numbervars:   bool,
    pub(crate) quoted:       bool,
    pub(crate) ignore_ops:   bool
}

macro_rules! push_space_if_amb {
    ($self:expr, $atom:expr, $action:block) => (
        if $self.ambiguity_check($atom) {
            if $self.last_item_idx > 1 {
                if !$self.outputter.range(0 .. $self.last_item_idx).ends_with(" ") {
                    $self.outputter.insert($self.last_item_idx, ' ');
                }
            }

            $self.outputter.push_char(' ');
            $action;
        } else {
            $action;
        }
    )
}

fn continues_with_append(atom: &str, op: &str) -> bool {
    match atom.chars().last() {
        Some(ac) => op.chars().next().map(|oc| {
            if alpha_char!(ac) {
                alpha_numeric_char!(oc)
            } else if graphic_token_char!(ac) {
                graphic_char!(oc)
            } else if variable_indicator_char!(ac) {
                alpha_numeric_char!(oc)
            } else if capital_letter_char!(ac) {
                alpha_numeric_char!(oc)
            } else if sign_char!(ac) {
                sign_char!(oc) || decimal_digit_char!(oc)
            } else {
                false
            }
        }).unwrap_or(false),
        _ => false
    }
}

fn reverse_heap_locs<'a>(machine_st: &'a MachineState, heap_locs: &'a HeapVarDict)
                         -> ReverseHeapVarDict
{
    heap_locs.iter().map(|(var, var_addr)| {
        (machine_st.store(machine_st.deref(var_addr.clone())), var.clone())
    }).collect()
}

fn non_quoted_graphic_token<Iter: Iterator<Item=char>>(mut iter: Iter, c: char) -> bool {
    if c == '/' {
        return match iter.next() {
            None => true,
            Some('*') => false, // if we start with comment token, we must quote.
            Some(c) => if graphic_token_char!(c) {
                iter.all(|c| graphic_token_char!(c))
            } else {
                false
            }
        }
    } else if c == '.' {
        return match iter.next() {
            None => false,
            Some(c) => if graphic_token_char!(c) {
                iter.all(|c| graphic_token_char!(c))
            } else {
                false
            }
        }
    } else {
        iter.all(|c| graphic_token_char!(c))
    }
}

fn non_quoted_token<Iter: Iterator<Item=char>>(mut iter: Iter) -> bool {
    if let Some(c) = iter.next() {
        if small_letter_char!(c) {
            iter.all(|c| alpha_numeric_char!(c))
        } else if graphic_token_char!(c) {
            non_quoted_graphic_token(iter, c)
        } else if semicolon_char!(c) {
            iter.next().is_none()
        } else if cut_char!(c) {
            iter.next().is_none()
        } else if solo_char!(c) {
            !iter.next().is_none()
        } else if c == '[' {
            (iter.next() == Some(']') && iter.next().is_none())
        } else if c == '{' {
            (iter.next() == Some('}') && iter.next().is_none())
        } else {
            false
        }
    } else {
        false
    }
}

impl<'a, Outputter: HCValueOutputter> HCPrinter<'a, Outputter>
{
    pub fn new(machine_st: &'a MachineState, output: Outputter) -> Self
    {
        HCPrinter { outputter: output,
                    machine_st,
                    state_stack: vec![],
                    heap_locs: ReverseHeapVarDict::new(),
                    toplevel_spec: None,
                    printed_vars: HashSet::new(),
                    last_item_idx: 0,
                    numbervars: false,
                    numbervars_offset: BigInt::zero(),
                    quoted: false,
                    ignore_ops: false }
    }

    pub fn from_heap_locs(machine_st: &'a MachineState, output: Outputter,
                          heap_locs: &'a HeapVarDict)
                          -> Self
    {
        let mut printer = Self::new(machine_st, output);

        printer.toplevel_spec = Some(DirectedOp::Right(clause_name!("="), (700, XFX)));
        printer.heap_locs = reverse_heap_locs(machine_st, heap_locs);

        printer
    }

    #[inline]
    pub fn see_all_locs(&mut self) {
        for key in self.heap_locs.keys().cloned() {
            self.printed_vars.insert(key);
        }
    }

    #[inline]
    fn ambiguity_check(&self, atom: &str) -> bool
    {
        let tail = self.outputter.range_from(self.last_item_idx ..);
        continues_with_append(tail, atom)
    }

    // TODO: create a DirectedOp factory method. Use it here, and above.
    fn enqueue_op(&mut self, ct: ClauseType, spec: (usize, Specifier)) {
        if is_postfix!(spec.1) {
            let right_directed_op = DirectedOp::Right(ct.name(), spec);

            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack.push(TokenOrRedirect::CompositeRedirect(right_directed_op));
        } else if is_prefix!(spec.1) {
            if ct.name().as_str() == "-" {
                self.format_negated_operand();
                return;
            }

            let left_directed_op = DirectedOp::Left(ct.name(), spec);

            self.state_stack.push(TokenOrRedirect::CompositeRedirect(left_directed_op));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
        } else { // if is_infix!(spec.1)
            let left_directed_op  = DirectedOp::Left(ct.name(), spec);
            let right_directed_op = DirectedOp::Right(ct.name(), spec);

            self.state_stack.push(TokenOrRedirect::CompositeRedirect(left_directed_op));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack.push(TokenOrRedirect::CompositeRedirect(right_directed_op));
        }
    }

    fn format_struct(&mut self, arity: usize, name: ClauseName)
    {
        self.state_stack.push(TokenOrRedirect::Close);

        for _ in 0 .. arity {
            self.state_stack.push(TokenOrRedirect::FunctorRedirect);
            self.state_stack.push(TokenOrRedirect::Comma);
        }

        self.state_stack.pop();
        self.state_stack.push(TokenOrRedirect::Open);

        self.state_stack.push(TokenOrRedirect::Atom(name));
    }

    fn format_negated_operand(&mut self)
    {
        let op = DirectedOp::Left(clause_name!("-"), (200, FY));

        self.state_stack.push(TokenOrRedirect::CompositeRedirect(op));
        self.state_stack.push(TokenOrRedirect::Space);
        self.state_stack.push(TokenOrRedirect::Atom(clause_name!("-")));
    }

    fn format_curly_braces(&mut self)
    {
        self.state_stack.push(TokenOrRedirect::RightCurly);
        self.state_stack.push(TokenOrRedirect::FunctorRedirect);
        self.state_stack.push(TokenOrRedirect::LeftCurly);
    }

    fn format_clause(&mut self, iter: &mut HCPreOrderIterator, arity: usize, ct: ClauseType)
    {
        if let Some(spec) = ct.spec() {
            if !self.ignore_ops {
                return self.enqueue_op(ct, spec);
            }
        } else if self.numbervars && is_numbered_var(&ct, arity) {
            let addr = iter.stack().last().cloned().unwrap();

            // 7.10.4
            if let Some(var) = iter.machine_st().numbervar(&self.numbervars_offset, addr) {
                iter.stack().pop();
                self.state_stack.push(TokenOrRedirect::NumberedVar(var));
                return;
            }
        }

        match (ct.name().as_str(), arity) {
            ("-", 1) => self.format_negated_operand(),
            ("{}", 1) => self.format_curly_braces(),
            _ =>  self.format_struct(arity, ct.name())
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

    fn offset_as_string(&self, addr: Addr) -> Option<String> {
        match addr {
            Addr::AttrVar(h) =>
                Some(format!("_{}", h + 1)),
            Addr::HeapCell(h) | Addr::Lis(h) | Addr::Str(h) =>
                Some(format!("_{}", h)),
            Addr::StackCell(fr, sc) =>
                Some(format!("_s_{}_{}", fr, sc)),
            _ => None
        }
    }

    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator) -> Option<HeapCellValue>
    {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            match self.heap_locs.get(&addr).cloned() {
                Some(var) => if !self.printed_vars.contains(&addr) {
                    self.printed_vars.insert(addr);
                    return iter.next();
                } else {
                    iter.stack().pop();
                    push_space_if_amb!(self, &var, {
                        self.append_str(&var);
                    });

                    return None;
                },
                None => if self.machine_st.is_cyclic_term(addr.clone()) {
                    if self.printed_vars.contains(&addr) {
                        iter.stack().pop();

                        if let Some(offset_str) = self.offset_as_string(addr) {
                            push_space_if_amb!(self, &offset_str, {
                                self.append_str(offset_str.as_str());
                            });
                        }

                        None
                    } else {
                        if let Some(s) = self.offset_as_string(addr.clone()) {
                            let var = Rc::new(s);
                            self.heap_locs.insert(addr.clone(), var);
                        }

                        self.printed_vars.insert(addr);
                        iter.next()
                    }
                } else {
                    iter.next()
                }
            }
        })
    }

    fn print_atom(&mut self, atom: &ClauseName, spec: Option<(usize, Specifier)>) {
        push_space_if_amb!(self, atom.as_str(), {
            match atom.as_str() {
                "" => self.append_str("''"),
                ";" | "!" => self.append_str(atom.as_str()),
                s => if spec.is_some() || !self.quoted || non_quoted_token(s.chars()) {
                    self.append_str(atom.as_str());
                } else {
                    if self.quoted {
                        self.push_char('\'');
                    }

                    for c in atom.as_str().chars() {
                        self.print_char(c);
                    }

                    if self.quoted {
                        self.push_char('\'');
                    }
                }
            }
        });
    }

    fn print_char(&mut self, c: char) {
        match c {
            '\n' => self.append_str("\\n"),
            '\r' => self.append_str("\\r"),
            '\t' => self.append_str("\\t"),
            '\u{0b}' => self.append_str("\\v"), // UTF-8 vertical tab
            '\u{0c}' => self.append_str("\\f"), // UTF-8 form feed
            '\u{08}' => self.append_str("\\b"), // UTF-8 backspace
            '\u{07}' => self.append_str("\\a"), // UTF-8 alert
            '\x20' ... '\x7e' => self.push_char(c),
            _ => self.append_str(&format!("\\x{:x}\\", c as u32))
        };
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
            Number::Float(fl) =>
                if &fl == &OrderedFloat(0f64) {
                    push_space_if_amb!(self, "0", {
                        self.append_str("0");
                    });
                } else {
                    let OrderedFloat(fl) = fl;
                    let output_str = format!("{0:<20?}", fl);

                    push_space_if_amb!(self, &output_str, {
                        self.append_str(&output_str.trim());
                    });
                },
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

    fn print_constant(&mut self, c: Constant, op: &Option<DirectedOp>) {
        match c {
            Constant::Atom(ref atom, Some(spec)) => {
                if let Some(ref op) = op {
                    if self.outputter.ends_with(&format!(" {}", op.as_str())) {
                        self.push_char(' ');
                    }

                    self.push_char('(');
                }

                self.print_atom(atom, Some(spec));

                if op.is_some() {
                    self.push_char(')');
                }
            },
            Constant::Atom(ref atom, None) =>
                push_space_if_amb!(self, atom.as_str(), {
                    self.print_atom(atom, None);
                }),
            Constant::Char(c) if non_quoted_token(once(c)) =>
                self.print_char(c),
            Constant::Char(c) =>
                if self.quoted {
                    self.push_char('\'');
                    self.print_char(c);
                    self.push_char('\'');
                } else {
                    self.print_char(c);
                },
            Constant::EmptyList =>
                self.append_str("[]"),
            Constant::Number(n) =>
                self.print_number(n, op),
            Constant::String(s) =>
                if self.machine_st.machine_flags().double_quotes.is_chars() {
                    if !s.is_empty() {
                        if self.ignore_ops {
                            self.format_struct(2, clause_name!("."));
                        } else {
                            self.push_list();
                        }
                    } else if s.is_expandable() {
                        if !self.at_cdr(" | _") {
                            self.push_char('_');
                        }
                    } else if !self.at_cdr("") {
                        self.append_str("[]");
                    }
                } else { // for now, == DoubleQuotes::Atom
                    let borrowed_str = s.borrow();

                    self.push_char('"');
                    self.append_str(&borrowed_str[s.cursor() ..]);
                    self.push_char('"');
                },
            Constant::Usize(i) =>
                self.append_str(&format!("u{}", i))
        }
    }

    fn push_list(&mut self) {
        let cell = Rc::new(Cell::new(true));

        self.state_stack.push(TokenOrRedirect::CloseList(cell.clone()));

        self.state_stack.push(TokenOrRedirect::FunctorRedirect);
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
        self.state_stack.push(TokenOrRedirect::FunctorRedirect);

        self.state_stack.push(TokenOrRedirect::OpenList(cell));
    }

    fn handle_heap_term(&mut self, iter: &mut HCPreOrderIterator, op: Option<DirectedOp>,
                        is_functor_redirect: bool)
    {
        let add_brackets = negated_op_needs_bracketing(iter, &op);

        let heap_val = match self.check_for_seen(iter) {
            Some(heap_val) => heap_val,
            None => return
        };

        match heap_val {
            HeapCellValue::NamedStr(arity, ref name, Some(spec)) => {
                let add_brackets = if !self.ignore_ops {
                    add_brackets || if let Some(ref op) = &op {
                        needs_bracketing(spec, op)
                    } else {
                        is_functor_redirect && spec.0 >= 1000
                    }
                } else {
                    false
                };

                if add_brackets {
                    self.state_stack.push(TokenOrRedirect::Close);
                }

                let ct = ClauseType::from(name.clone(), arity, Some(spec));
                self.format_clause(iter, arity, ct);

                if add_brackets {
                    self.state_stack.push(TokenOrRedirect::Open);
                }
            },
            HeapCellValue::NamedStr(0, name, fixity) =>
                push_space_if_amb!(self, name.as_str(), {
                    let ct = ClauseType::from(name, 0, fixity);
                    self.format_clause(iter, 0, ct);
                }),
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let ct = ClauseType::from(name, arity, fixity);
                self.format_clause(iter, arity, ct);
            },
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) =>
                if !self.at_cdr("") {
                    self.append_str("[]");
                },
            HeapCellValue::Addr(Addr::Con(c)) =>
                self.print_constant(c, &op),
            HeapCellValue::Addr(Addr::Lis(_)) =>
                if self.ignore_ops {
                    self.format_struct(2, clause_name!("."));
                } else {
                    self.push_list();
                },
            HeapCellValue::Addr(addr) =>
                if let Some(offset_str) = self.offset_as_string(addr) {
                    push_space_if_amb!(self, &offset_str, {
                        self.append_str(offset_str.as_str());
                    })
                }
        }
    }

    fn at_cdr(&mut self, tr: &str) -> bool {
        let len = self.outputter.len();

        if self.outputter.ends_with(" | ") {
            self.outputter.truncate(len - " | ".len());
            self.append_str(tr);

            true
        } else {
            false
        }
    }

    pub fn print(mut self, addr: Addr) -> Outputter {
        let mut iter = self.machine_st.pre_order_iter(addr);

        loop {
            if let Some(loc_data) = self.state_stack.pop() {
                match loc_data {
                    TokenOrRedirect::Atom(atom) =>
                        self.print_atom(&atom, None),
                    TokenOrRedirect::Op(atom, spec) =>
                        self.print_atom(&atom, Some(spec)),
                    TokenOrRedirect::NumberedVar(num_var) =>
                        self.append_str(num_var.as_str()),
                    TokenOrRedirect::CompositeRedirect(op) =>
                        self.handle_heap_term(&mut iter, Some(op), false),
                    TokenOrRedirect::FunctorRedirect =>
                        self.handle_heap_term(&mut iter, None, true),
                    TokenOrRedirect::Close =>
                        self.push_char(')'),
                    TokenOrRedirect::Open =>
                        self.push_char('('),
                    TokenOrRedirect::OpenList(delimit) =>
                        if !self.at_cdr(", ") {
                            self.push_char('[');
                        } else {
                            delimit.set(false);
                        },
                    TokenOrRedirect::CloseList(delimit) =>
                        if delimit.get() {
                            self.push_char(']');
                        },
                    TokenOrRedirect::HeadTailSeparator =>
                        self.append_str(" | "),
                    TokenOrRedirect::Comma =>
                        self.append_str(", "),
                    TokenOrRedirect::Space =>
                        self.push_char(' '),
                    TokenOrRedirect::LeftCurly =>
                        self.push_char('{'),
                    TokenOrRedirect::RightCurly =>
                        self.push_char('}'),
                }
            } else if !iter.stack().is_empty() {
                let spec = self.toplevel_spec.take();
                self.handle_heap_term(&mut iter, spec, false);
            } else {
                break;
            }
        }

        self.outputter
    }
}
