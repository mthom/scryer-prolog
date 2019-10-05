use prolog_parser::ast::*;
use prolog_parser::string_list::*;

use prolog::clause_types::*;
use prolog::forms::*;
use prolog::heap_iter::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::ordered_float::OrderedFloat;
use prolog::rug::Integer;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::iter::once;
use std::ops::{Range, RangeFrom};
use std::rc::Rc;

/* contains the location, name, precision and Specifier of the parent op. */
#[derive(Clone)]
pub enum DirectedOp {
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
        P: Fn(Constant) -> bool,
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
                    _ => return false,
                },
                Addr::Con(Constant::Integer(n)) => return property_check(Constant::Integer(n)),
                Addr::Con(Constant::Float(n)) => return property_check(Constant::Float(n)),
                Addr::Con(Constant::Rational(n)) => return property_check(Constant::Rational(n)),
                _ => return false,
            }
        }
    }

    fn immediate_leaf_has_property<P>(&self, property_check: P) -> bool
    where
        P: Fn(Constant) -> bool,
    {
        let addr = match self.state_stack.last().cloned() {
            Some(addr) => addr,
            None => return false,
        };

        match self.machine_st.store(self.machine_st.deref(addr)) {
            Addr::Con(c) => property_check(c),
            _ => false,
        }
    }
}

fn char_to_string(c: char) -> String {
    match c {
        '\'' => "\\'".to_string(),
        '\n' => "\\n".to_string(),
        '\r' => "\\r".to_string(),
        '\t' => "\\t".to_string(),
        '\u{0b}' => "\\v".to_string(), // UTF-8 vertical tab
        '\u{0c}' => "\\f".to_string(), // UTF-8 form feed
        '\u{08}' => "\\b".to_string(), // UTF-8 backspace
        '\u{07}' => "\\a".to_string(), // UTF-8 alert
        '\x20'...'\x7e' => c.to_string(),
        _ => format!("\\x{:x}\\", c as u32),
    }
}

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(ClauseName),
    Op(ClauseName, SharedOpDesc),
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
    if let &Some(ref op) = op {
        op.is_negative_sign()
            && iter.leftmost_leaf_has_property(|c| match c {
                Constant::Integer(n) => n > 0,
                Constant::Float(f) => f > OrderedFloat(0f64),
                Constant::Rational(r) => r > 0,
                _ => false,
            })
    } else {
        false
    }
}

impl MachineState {
    pub fn numbervar(&self, offset: &Integer, addr: Addr) -> Option<Var> {
        static CHAR_CODES: [char; 26] = [
            'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q',
            'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
        ];

        match self.store(self.deref(addr)) {
            Addr::Con(Constant::Integer(ref n)) if n >= &0 => {
                let n = Integer::from(offset + n);

                let i = n.mod_u(26) as usize;
                let j = n.div_rem_floor(Integer::from(26));
                let j = <(Integer, Integer)>::from(j).1;

                Some(if j == 0 {
                    CHAR_CODES[i].to_string()
                } else {
                    format!("{}{}", CHAR_CODES[i], j)
                })
            }
            _ => None,
        }
    }
}

type ReverseHeapVarDict = IndexMap<Addr, Rc<Var>>;

pub struct HCPrinter<'a, Outputter> {
    outputter: Outputter,
    machine_st: &'a MachineState,
    op_dir: &'a OpDir,
    state_stack: Vec<TokenOrRedirect>,
    toplevel_spec: Option<DirectedOp>,
    heap_locs: ReverseHeapVarDict,
    printed_vars: IndexSet<Addr>,
    last_item_idx: usize,
    cyclic_terms: IndexMap<Addr, usize>,
    pub(crate) var_names: IndexMap<Addr, String>,
    pub(crate) numbervars_offset: Integer,
    pub(crate) numbervars: bool,
    pub(crate) quoted: bool,
    pub(crate) ignore_ops: bool,
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

pub fn requires_space(atom: &str, op: &str) -> bool {
    match atom.chars().last() {
        Some(ac) => op
            .chars()
            .next()
            .map(|oc| {
                if ac == '0' {
                    oc == 'b' || oc == 'x' || oc == 'o' || oc == '\''
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

fn reverse_heap_locs<'a>(machine_st: &'a MachineState) -> ReverseHeapVarDict {
    machine_st
        .heap_locs
        .iter()
        .map(|(var, var_addr)| {
            (
                machine_st.store(machine_st.deref(var_addr.clone())),
                var.clone(),
            )
        })
        .collect()
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

fn non_quoted_token<Iter: Iterator<Item = char>>(mut iter: Iter) -> bool {
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
            (iter.next() == Some(']') && iter.next().is_none())
        } else if c == '{' {
            (iter.next() == Some('}') && iter.next().is_none())
        } else if solo_char!(c) {
            !(c == ')' || c == '}' || c == ']' || c == ',' || c == '%' || c == '|')
        } else {
            false
        }
    } else {
        false
    }
}

impl<'a, Outputter: HCValueOutputter> HCPrinter<'a, Outputter> {
    pub fn new(machine_st: &'a MachineState, op_dir: &'a OpDir, output: Outputter) -> Self {
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
            var_names: IndexMap::new(),
        }
    }

    pub fn from_heap_locs(
        machine_st: &'a MachineState,
        op_dir: &'a OpDir,
        output: Outputter,
    ) -> Self {
        let mut printer = Self::new(machine_st, op_dir, output);

        printer.toplevel_spec = Some(DirectedOp::Right(
            clause_name!("="),
            SharedOpDesc::new(700, XFX),
        ));
        printer.heap_locs = reverse_heap_locs(machine_st);

        printer
    }

    pub fn drop_toplevel_spec(&mut self) {
        self.toplevel_spec = None;
    }

    #[inline]
    pub fn see_all_locs(&mut self) {
        for key in self.heap_locs.keys().cloned() {
            self.printed_vars.insert(key);
        }
    }

    #[inline]
    fn ambiguity_check(&self, atom: &str) -> bool {
        let tail = self.outputter.range_from(self.last_item_idx..);
        requires_space(tail, atom)
    }

    fn enqueue_op(&mut self, ct: ClauseType, spec: SharedOpDesc) {
        if is_postfix!(spec.assoc()) {
            let right_directed_op = DirectedOp::Right(ct.name(), spec.clone());

            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack
                .push(TokenOrRedirect::CompositeRedirect(right_directed_op));
        } else if is_prefix!(spec.assoc()) {
            match ct.name().as_str() {
                "-" | "\\" => {
                    self.format_prefix_op_with_space(ct.name(), spec);
                    return;
                }
                _ => {}
            };

            let left_directed_op = DirectedOp::Left(ct.name(), spec.clone());

            self.state_stack
                .push(TokenOrRedirect::CompositeRedirect(left_directed_op));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
        } else {
            // if is_infix!(spec.assoc())
            match ct.name().as_str() {
                "|" => {
                    self.format_bar_separator_op(ct.name(), spec);
                    return;
                }
                _ => {}
            };

            let left_directed_op = DirectedOp::Left(ct.name(), spec.clone());
            let right_directed_op = DirectedOp::Right(ct.name(), spec.clone());

            self.state_stack
                .push(TokenOrRedirect::CompositeRedirect(left_directed_op));
            self.state_stack.push(TokenOrRedirect::Op(ct.name(), spec));
            self.state_stack
                .push(TokenOrRedirect::CompositeRedirect(right_directed_op));
        }
    }

    fn format_struct(&mut self, arity: usize, name: ClauseName) {
        self.state_stack.push(TokenOrRedirect::Close);

        for _ in 0..arity {
            self.state_stack.push(TokenOrRedirect::FunctorRedirect);
            self.state_stack.push(TokenOrRedirect::Comma);
        }

        self.state_stack.pop();
        self.state_stack.push(TokenOrRedirect::Open);

        self.state_stack.push(TokenOrRedirect::Atom(name));
    }

    fn format_prefix_op_with_space(&mut self, name: ClauseName, spec: SharedOpDesc) {
        let op = DirectedOp::Left(name.clone(), spec);

        self.state_stack
            .push(TokenOrRedirect::CompositeRedirect(op));
        self.state_stack.push(TokenOrRedirect::Space);
        self.state_stack.push(TokenOrRedirect::Atom(name));
    }

    fn format_bar_separator_op(&mut self, name: ClauseName, spec: SharedOpDesc) {
        let left_directed_op = DirectedOp::Left(name.clone(), spec.clone());
        let right_directed_op = DirectedOp::Right(name.clone(), spec.clone());

        self.state_stack
            .push(TokenOrRedirect::CompositeRedirect(left_directed_op));
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator);
        self.state_stack
            .push(TokenOrRedirect::CompositeRedirect(right_directed_op));
    }

    fn format_curly_braces(&mut self) {
        self.state_stack.push(TokenOrRedirect::RightCurly);
        self.state_stack.push(TokenOrRedirect::FunctorRedirect);
        self.state_stack.push(TokenOrRedirect::LeftCurly);
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

    fn format_clause(&mut self, iter: &mut HCPreOrderIterator, arity: usize, ct: ClauseType) {
        if self.numbervars && is_numbered_var(&ct, arity) {
            if self.format_numbered_vars(iter) {
                return;
            }
        }

        if let Some(spec) = ct.spec() {
            if "." == ct.name().as_str() && is_infix!(spec.assoc()) {
                if !self.ignore_ops {
                    self.push_list();
                    return;
                }
            }

            if !self.ignore_ops && spec.prec() > 0 {
                return self.enqueue_op(ct, spec);
            }
        }

        match (ct.name().as_str(), arity) {
            ("{}", 1) if !self.ignore_ops => self.format_curly_braces(),
            _ => self.format_struct(arity, ct.name()),
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

    fn offset_as_string(&self, iter: &mut HCPreOrderIterator, addr: Addr) -> Option<String> {
        if let Some(var) = self.var_names.get(&addr) {
            if addr.as_var().is_some() {
                return Some(format!("{}", var));
            } else {
                iter.stack().push(addr);
                return None;
            }
        }

        match addr {
            Addr::AttrVar(h) => Some(format!("_{}", h + 1)),
            Addr::HeapCell(h) | Addr::Lis(h) | Addr::Str(h) => Some(format!("_{}", h)),
            Addr::StackCell(fr, sc) => Some(format!("_s_{}_{}", fr, sc)),
            _ => None,
        }
    }

    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator) -> Option<HeapCellValue> {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            match self.heap_locs.get(&addr).cloned() {
                Some(var) => {
                    if !self.printed_vars.contains(&addr) {
                        self.printed_vars.insert(addr);
                        return iter.next();
                    } else {
                        iter.stack().pop();
                        push_space_if_amb!(self, &var, {
                            self.append_str(&var);
                        });

                        return None;
                    }
                }
                None => {
                    if self.machine_st.is_cyclic_term(addr.clone()) {
                        match self.cyclic_terms.get(&addr).cloned() {
                            Some(reps) => {
                                if reps > 0 {
                                    self.cyclic_terms.insert(addr, reps - 1);
                                    iter.next()
                                } else {
                                    push_space_if_amb!(self, "...", {
                                        self.append_str("...");
                                    });

                                    iter.stack().pop();
                                    self.cyclic_terms.swap_remove(&addr);
                                    None
                                }
                            }
                            None => {
                                self.cyclic_terms.insert(addr, 2);
                                iter.next()
                            }
                        }
                    } else {
                        iter.next()
                    }
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
                result += &char_to_string(c);
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
                    push_space_if_amb!(self, "0", {
                        self.append_str("0");
                    });
                } else {
                    let OrderedFloat(fl) = fl;
                    let output_str = format!("{0:<20?}", fl);

                    push_space_if_amb!(self, &output_str, {
                        self.append_str(&output_str.trim());
                    });
                }
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

    fn print_constant(&mut self, c: Constant, op: &Option<DirectedOp>) {
        match c {
            Constant::Atom(atom, spec) => {
                if let Some(_) = fetch_atom_op_spec(atom.clone(), spec, self.op_dir) {
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
            Constant::Char(c) if non_quoted_token(once(c)) => {
                let c = char_to_string(c);

                push_space_if_amb!(self, &c, {
                    self.append_str(c.as_str());
                });
            }
            Constant::Char(c) => {
                let mut result = String::new();

                if self.quoted {
                    result.push('\'');
                    result += &char_to_string(c);
                    result.push('\'');
                } else {
                    result += &char_to_string(c);
                }

                push_space_if_amb!(self, &result, {
                    self.append_str(result.as_str());
                });
            }
            Constant::CharCode(c) => self.append_str(&format!("{}", c)),
            Constant::EmptyList => self.append_str("[]"),
            Constant::Integer(n) => self.print_number(Number::Integer(n), op),
            Constant::Float(n) => self.print_number(Number::Float(n), op),
            Constant::Rational(n) => self.print_number(Number::Rational(n), op),
            Constant::String(s) => self.print_string(s),
            Constant::Usize(i) => self.append_str(&format!("u{}", i)),
        }
    }

    fn print_string(&mut self, s: StringList) {
        match self.machine_st.machine_flags().double_quotes {
            DoubleQuotes::Chars | DoubleQuotes::Codes => {
                if !s.is_empty() {
                    if self.ignore_ops {
                        self.format_struct(2, clause_name!("."));
                    } else {
                        self.push_list();
                    }
                } else if s.is_expandable() {
                    if !self.at_cdr("|_") {
                        self.push_char('_');
                    }
                } else if !self.at_cdr("") {
                    self.append_str("[]");
                }
            }
            DoubleQuotes::Atom => {
                let borrowed_str = s.borrow();
                let mut atom = String::new();

                for c in borrowed_str[s.cursor()..].chars() {
                    atom += &char_to_string(c);
                }

                self.push_char('"');
                self.append_str(&atom);
                self.push_char('"');
            }
        }
    }

    fn push_list(&mut self) {
        let cell = Rc::new(Cell::new(true));

        self.state_stack
            .push(TokenOrRedirect::CloseList(cell.clone()));

        self.state_stack.push(TokenOrRedirect::FunctorRedirect);
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
        self.state_stack.push(TokenOrRedirect::FunctorRedirect);

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
    ) {
        let add_brackets = if !self.ignore_ops {
            negated_operand
                || if let Some(ref op) = op {
                    if self.numbervars && arity == 1 && name.as_str() == "$VAR" {
                        !iter.immediate_leaf_has_property(|c| match c {
                            Constant::Integer(n) => n >= 0,
                            Constant::Float(f) => f >= OrderedFloat(0f64),
                            Constant::Rational(r) => r >= 0,
                            _ => false,
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
        self.format_clause(iter, arity, ct);

        if add_brackets {
            self.state_stack.push(TokenOrRedirect::Open);

            if let Some(ref op) = &op {
                if op.is_left() && requires_space(op.as_str(), "(") {
                    self.state_stack.push(TokenOrRedirect::Space);
                }
            }
        }
    }

    fn handle_heap_term(
        &mut self,
        iter: &mut HCPreOrderIterator,
        op: Option<DirectedOp>,
        is_functor_redirect: bool,
    ) {
        let negated_operand = negated_op_needs_bracketing(iter, &op);

        let heap_val = match self.check_for_seen(iter) {
            Some(heap_val) => heap_val,
            None => return,
        };

        match heap_val {
            HeapCellValue::NamedStr(arity, name, spec) => {
                let spec = fetch_op_spec(name.clone(), arity, spec.clone(), self.op_dir);
                
                if let Some(spec) = spec {
                    self.handle_op_as_struct(
                        name,
                        arity,
                        iter,
                        &op,
                        is_functor_redirect,
                        spec,
                        negated_operand,
                    );
                } else {
                    push_space_if_amb!(self, name.as_str(), {
                        let ct = ClauseType::from(name, arity, spec);
                        self.format_clause(iter, arity, ct);
                    });
                }
            }
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) => {
                if !self.at_cdr("") {
                    self.append_str("[]");
                }
            }
            HeapCellValue::Addr(Addr::Con(c)) => self.print_constant(c, &op),
            HeapCellValue::Addr(Addr::Lis(_)) => {
                if self.ignore_ops {
                    self.format_struct(2, clause_name!("."));
                } else {
                    self.push_list();
                }
            }
            HeapCellValue::Addr(addr) => {
                if let Some(offset_str) = self.offset_as_string(iter, addr) {
                    push_space_if_amb!(self, &offset_str, {
                        self.append_str(offset_str.as_str());
                    })
                }
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

    pub fn print(mut self, addr: Addr) -> Outputter {
        let mut iter = self.machine_st.pre_order_iter(addr);

        loop {
            if let Some(loc_data) = self.state_stack.pop() {
                match loc_data {
                    TokenOrRedirect::Atom(atom) => self.print_atom(&atom),
                    TokenOrRedirect::Op(atom, _) => self.print_op(atom.as_str()),
                    TokenOrRedirect::NumberedVar(num_var) => self.append_str(num_var.as_str()),
                    TokenOrRedirect::CompositeRedirect(op) => {
                        self.handle_heap_term(&mut iter, Some(op), false)
                    }
                    TokenOrRedirect::FunctorRedirect => {
                        self.handle_heap_term(&mut iter, None, true)
                    }
                    TokenOrRedirect::Close => self.push_char(')'),
                    TokenOrRedirect::Open => self.push_char('('),
                    TokenOrRedirect::OpenList(delimit) => {
                        if !self.at_cdr(",") {
                            self.push_char('[');
                        } else {
                            delimit.set(false);
                        }
                    }
                    TokenOrRedirect::CloseList(delimit) => {
                        if delimit.get() {
                            self.push_char(']');
                        }
                    }
                    TokenOrRedirect::HeadTailSeparator => self.append_str("|"),
                    TokenOrRedirect::Comma => self.append_str(","),
                    TokenOrRedirect::Space => self.push_char(' '),
                    TokenOrRedirect::LeftCurly => self.push_char('{'),
                    TokenOrRedirect::RightCurly => self.push_char('}'),
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
