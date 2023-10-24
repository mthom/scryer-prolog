use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;
use crate::parser::dashu::{ibig, Integer, Rational};
use crate::parser::dashu::base::RemEuclid;
use crate::parser::dashu::integer::Sign;
use crate::{
    alpha_numeric_char, capital_letter_char, cut_char, decimal_digit_char, graphic_token_char,
    is_fx, is_infix, is_postfix, is_prefix, is_xf, is_xfx, is_xfy, is_yfx, semicolon_char,
    sign_char, single_quote_char, small_letter_char, solo_char, variable_indicator_char,
};

use crate::forms::*;
use crate::heap_iter::*;
use crate::machine::heap::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::pstr_loc_and_offset;
use crate::machine::partial_string::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::types::*;

use ordered_float::OrderedFloat;

use indexmap::IndexMap;

use std::cell::Cell;
use std::convert::TryFrom;
use std::iter::once;
use std::net::{IpAddr, TcpListener};
use std::rc::Rc;
use std::sync::Arc;

/* contains the location, name, precision and Specifier of the parent op. */
#[derive(Debug, Copy, Clone)]
pub(crate) enum DirectedOp {
    Left(Atom, OpDesc),
    Right(Atom, OpDesc),
}

impl DirectedOp {
    #[inline]
    fn as_atom(&self) -> Atom {
        match self {
            &DirectedOp::Left(name, _) | &DirectedOp::Right(name, _) => name,
        }
    }

    #[inline]
    fn is_prefix(&self) -> bool {
        match self {
            &DirectedOp::Left(_name, cell) | &DirectedOp::Right(_name, cell) => {
                is_prefix!(cell.get_spec() as u32)
            }
        }
    }

    #[inline]
    fn is_negative_sign(&self) -> bool {
        match self {
            &DirectedOp::Left(name, cell) | &DirectedOp::Right(name, cell) => {
                name == atom!("-") && is_prefix!(cell.get_spec() as u32)
            }
        }
    }

    #[inline]
    fn is_left(&self) -> bool {
        matches!(self, DirectedOp::Left(..))
    }
}

fn needs_bracketing(child_desc: OpDesc, op: &DirectedOp) -> bool {
    match op {
        DirectedOp::Left(name, cell) => {
            let (priority, spec) = cell.get();

            if &*name.as_str() == "-" {
                let child_assoc = child_desc.get_spec();
                if is_prefix!(spec) && (is_postfix!(child_assoc) || is_infix!(child_assoc)) {
                    return true;
                }
            }

            let is_strict_right = is_yfx!(spec) || is_xfx!(spec) || is_fx!(spec);
            child_desc.get_prec() > priority
                || (child_desc.get_prec() == priority && is_strict_right)
        }
        DirectedOp::Right(_, cell) => {
            let (priority, spec) = cell.get();
            let is_strict_left = is_xfx!(spec) || is_xfy!(spec) || is_xf!(spec);

            if child_desc.get_prec() > priority
                || (child_desc.get_prec() == priority && is_strict_left)
            {
                true
            } else if (is_postfix!(spec) || is_infix!(spec)) && !is_postfix!(child_desc.get_spec())
            {
                *cell != child_desc && child_desc.get_prec() == priority
            } else {
                false
            }
        }
    }
}

impl<'a, ElideLists> StackfulPreOrderHeapIter<'a, ElideLists> {
    /*
     * descend into the subtree where the iterator is currently parked
     * and check that the leftmost leaf is a number, with every node
     * encountered on the way an infix or postfix operator, unblocked
     * by brackets.
     */
    fn leftmost_leaf_has_property<P>(&self, op_dir: &OpDir, property_check: P) -> bool
    where
        P: Fn(HeapCellValue) -> bool,
    {
        let mut h = match self.stack_last() {
            Some(h) => h,
            None => return false,
        };

        let mut parent_spec = DirectedOp::Left(atom!("-"), OpDesc::build_with(200, FY as u8));

        loop {
            let cell = self.read_cell(h);

            read_heap_cell!(cell,
                (HeapCellValueTag::Str, s) => {
                    read_heap_cell!(self.heap[s],
                        (HeapCellValueTag::Atom, (name, _arity)) => {
                            if let Some(spec) = fetch_atom_op_spec(name, None, op_dir) {
                                if is_postfix!(spec.get_spec() as u32) || is_infix!(spec.get_spec() as u32) {
                                    if needs_bracketing(spec, &parent_spec) {
                                        return false;
                                    } else {
                                        h = IterStackLoc::iterable_loc(s + 1, HeapOrStackTag::Heap);
                                        parent_spec = DirectedOp::Right(name, spec);
                                        continue;
                                    }
                                }
                            }

                            return false;
                        }
                        _ => {
                            return false;
                        }
                    )
                }
                _ => {
                    return property_check(cell);
                }
            )
        }
    }

    fn immediate_leaf_has_property<P>(&self, property_check: P) -> bool
    where
        P: Fn(HeapCellValue) -> bool,
    {
        let cell = match self.stack_last() {
            Some(h) => self.read_cell(h),
            None => return false,
        };

        property_check(cell)
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
        '\\' if is_quoted => "\\\\".to_string(),
        ' ' | '\'' | '\n' | '\r' | '\t' | '\u{0b}' | '\u{0c}' | '\u{08}' | '\u{07}' | '"'
        | '\\' => c.to_string(),
        _ => {
            if c.is_whitespace() || c.is_control() {
                // print all other control and whitespace characters in hex.
                format!("\\x{:x}\\", c as u32)
            } else {
                c.to_string()
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum NumberFocus {
    Unfocused(Number),
    Denominator(TypedArenaPtr<Rational>),
    Numerator(TypedArenaPtr<Rational>),
}

impl NumberFocus {
    fn is_negative(&self) -> bool {
        match self {
            NumberFocus::Unfocused(n) => n.is_negative(),
            NumberFocus::Denominator(r) | NumberFocus::Numerator(r) => **r < Rational::from(0),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct CommaSeparatedCharList {
    pstr: PartialString,
    offset: usize,
    max_depth: usize,
    end_cell: HeapCellValue,
    end_h: Option<usize>,
}

#[derive(Debug, Clone)]
enum TokenOrRedirect {
    Atom(Atom),
    BarAsOp,
    Char(char),
    Op(Atom, OpDesc),
    NumberedVar(String),
    CompositeRedirect(usize, DirectedOp),
    CurlyBracketRedirect(usize),
    FunctorRedirect(usize),
    #[allow(unused)]
    IpAddr(IpAddr),
    NumberFocus(usize, NumberFocus, Option<DirectedOp>),
    Open,
    Close,
    Comma,
    RawPtr(*const ArenaHeader),
    Space,
    LeftCurly,
    RightCurly,
    ChildOpenList,
    ChildCloseList,
    OpenList(Rc<Cell<(bool, usize)>>),
    CloseList(Rc<Cell<(bool, usize)>>),
    HeadTailSeparator,
    StackPop,
    CommaSeparatedCharList(CommaSeparatedCharList),
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

pub trait HCValueOutputter {
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
    fn as_str(&self) -> &str;
}

#[derive(Debug)]
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

    fn as_str(&self) -> &str {
        &self.contents
    }
}

#[inline(always)]
fn is_numbered_var(name: Atom, arity: usize) -> bool {
    arity == 1 && name == atom!("$VAR")
}

#[inline]
fn negated_op_needs_bracketing(
    iter: &StackfulPreOrderHeapIter<ListElider>,
    op_dir: &OpDir,
    op: &Option<DirectedOp>,
) -> bool {
    if let Some(ref op) = op {
        op.is_negative_sign()
            && iter.leftmost_leaf_has_property(op_dir, |addr| match Number::try_from(addr) {
                Ok(Number::Fixnum(n)) => n.get_num() > 0,
                Ok(Number::Float(f)) => f > OrderedFloat(0f64),
                Ok(Number::Integer(n)) => &*n > &Integer::from(0),
                Ok(Number::Rational(n)) => &*n > &Rational::from(0),
                _ => false,
            })
    } else {
        false
    }
}

macro_rules! push_char {
    ($self:ident, $c:expr) => {{
        $self.outputter.push_char($c);
        $self.last_item_idx = $self.outputter.len();
    }};
}

macro_rules! append_str {
    ($self:ident, $s:expr) => {{
        $self.last_item_idx = $self.outputter.len();
        $self.outputter.append($s);
    }};
}

macro_rules! print_char {
    ($self:ident, $is_quoted:expr, $c:expr) => {
        if non_quoted_token(once($c)) {
            let result = char_to_string(false, $c);

            push_space_if_amb!($self, &result, {
                append_str!($self, &result);
            });
        } else {
            let mut result = String::new();

            if $self.quoted {
                result.push('\'');
                result += &char_to_string($is_quoted, $c);
                result.push('\'');
            } else {
                result += &char_to_string($is_quoted, $c);
            }

            push_space_if_amb!($self, &result, {
                append_str!($self, result.as_str());
            });
        }
    };
}

pub fn fmt_float(mut fl: f64) -> String {
    if OrderedFloat(fl) == -0f64 {
        fl = 0f64;
    }

    let mut buffer = ryu::Buffer::new();
    let fl_str = buffer.format(fl);

    /* When printing floats with zero fractional parts in scientific notation, ryu
     * prints "{integer part}e{exponent}" without a ".0" preceding "e",
     * which is not valid ISO Prolog syntax. Add ".0" manually in this
     * case.
     */

    if let Some(e_index) = fl_str.find('e') {
        if !fl_str[0..e_index].contains('.') {
            return fl_str[0..e_index].to_string() + ".0" + &fl_str[e_index..];
        }
    }

    fl_str.to_string()
}

#[derive(Debug)]
pub struct HCPrinter<'a, Outputter> {
    outputter: Outputter,
    iter: StackfulPreOrderHeapIter<'a, ListElider>,
    atom_tbl: Arc<AtomTable>,
    op_dir: &'a OpDir,
    state_stack: Vec<TokenOrRedirect>,
    toplevel_spec: Option<DirectedOp>,
    last_item_idx: usize,
    parent_of_first_op: Option<(DirectedOp, usize)>,
    pub var_names: IndexMap<HeapCellValue, VarPtr>,
    pub numbervars_offset: Integer,
    pub numbervars: bool,
    pub quoted: bool,
    pub ignore_ops: bool,
    pub print_strings_as_strs: bool,
    pub max_depth: usize,
    pub double_quotes: bool,
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

pub(crate) fn numbervar(offset: &Integer, addr: HeapCellValue) -> Option<String> {
    fn numbervar(n: Integer) -> String {
        static CHAR_CODES: [char; 26] = [
            'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q',
            'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
        ];

        let i: usize = (&n).rem_euclid(ibig!(26)).try_into().unwrap();
        let j = n / ibig!(26);

        if j.is_zero() {
            CHAR_CODES[i].to_string()
        } else {
            format!("{}{}", CHAR_CODES[i], j)
        }
    }

    match Number::try_from(addr) {
        Ok(Number::Fixnum(n)) => {
            if n.get_num() >= 0 {
                Some(numbervar(offset + Integer::from(n.get_num())))
            } else {
                None
            }
        }
        Ok(Number::Integer(n)) => {
            if &*n >= &Integer::from(0) {
                Some(numbervar(Integer::from(offset + &*n)))
            } else {
                None
            }
        }
        _ => None,
    }
}

impl<'a, Outputter: HCValueOutputter> HCPrinter<'a, Outputter> {
    pub fn new(
        heap: &'a mut Heap,
        atom_tbl: Arc<AtomTable>,
        stack: &'a mut Stack,
        op_dir: &'a OpDir,
        output: Outputter,
        cell: HeapCellValue,
    ) -> Self {
        HCPrinter {
            outputter: output,
            iter: stackful_preorder_iter(heap, stack, cell),
            atom_tbl,
            op_dir,
            state_stack: vec![],
            toplevel_spec: None,
            last_item_idx: 0,
            parent_of_first_op: None,
            numbervars: false,
            numbervars_offset: Integer::from(0),
            quoted: false,
            ignore_ops: false,
            var_names: IndexMap::new(),
            print_strings_as_strs: false,
            max_depth: 0,
            double_quotes: false,
        }
    }

    #[inline]
    fn ambiguity_check(&self, atom: &str) -> bool {
        let tail = &self.outputter.as_str()[self.last_item_idx..];

        if atom == "," || !self.quoted || non_quoted_token(atom.chars()) {
            requires_space(tail, atom)
        } else {
            requires_space(tail, "'")
        }
    }

    fn set_parent_of_first_op(&mut self, parent_op: Option<DirectedOp>) {
        if let Some(op) = parent_op {
            if op.is_left() && op.is_prefix() {
                self.parent_of_first_op = Some((op, self.last_item_idx));
            }
        }
    }

    fn enqueue_op(&mut self, mut max_depth: usize, name: Atom, spec: OpDesc) {
        if is_postfix!(spec.get_spec()) {
            if self.max_depth_exhausted(max_depth) {
                self.iter.pop_stack();
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            } else if self.check_max_depth(&mut max_depth) {
                self.iter.pop_stack();

                self.state_stack.push(TokenOrRedirect::Op(name, spec));
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            } else {
                let right_directed_op = DirectedOp::Right(name, spec);

                self.state_stack.push(TokenOrRedirect::Op(name, spec));
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                    max_depth,
                    right_directed_op,
                ));
            }
        } else if is_prefix!(spec.get_spec()) {
            if self.max_depth_exhausted(max_depth) {
                self.iter.pop_stack();
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                return;
            } else if self.check_max_depth(&mut max_depth) {
                self.iter.pop_stack();

                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                self.state_stack.push(TokenOrRedirect::Op(name, spec));
            } else {
                let op = DirectedOp::Left(name, spec);

                self.state_stack
                    .push(TokenOrRedirect::CompositeRedirect(max_depth, op));
                self.state_stack.push(TokenOrRedirect::Op(name, spec));
            }
        } else {
            match &*name.as_str() {
                "|" => {
                    self.format_bar_separator_op(max_depth, name, spec);
                    return;
                }
                _ => {}
            };

            if self.max_depth_exhausted(max_depth) {
                self.iter.pop_stack();
                self.iter.pop_stack();

                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            } else if self.check_max_depth(&mut max_depth) {
                if is_xfy!(spec.get_spec()) {
                    let left_directed_op = DirectedOp::Left(name, spec);

                    self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                        0,
                        left_directed_op,
                    ));

                    self.state_stack.push(TokenOrRedirect::Op(name, spec));
                    self.state_stack.push(TokenOrRedirect::StackPop);
                } else { // is_yfx!
                    let right_directed_op = DirectedOp::Right(name, spec);

                    self.state_stack.push(TokenOrRedirect::StackPop);
                    self.state_stack.push(TokenOrRedirect::Op(name, spec));
                    self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                        0,
                        right_directed_op,
                    ));
                }
            } else {
                let left_directed_op = DirectedOp::Left(name, spec);
                let right_directed_op = DirectedOp::Right(name, spec);

                self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                    max_depth,
                    left_directed_op,
                ));

                self.state_stack.push(TokenOrRedirect::Op(name, spec));
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(
                    max_depth,
                    right_directed_op,
                ));
            }
        }
    }

    fn format_struct(&mut self, mut max_depth: usize, arity: usize, name: Atom) -> bool {
        if self.check_max_depth(&mut max_depth) {
            for _ in 0..arity {
                self.iter.pop_stack();
            }

            if arity > 0 {
                self.state_stack.push(TokenOrRedirect::Close);
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                self.state_stack.push(TokenOrRedirect::Open);
            }

            self.state_stack.push(TokenOrRedirect::Atom(name));

            return false;
        }

        if arity > 0 {
            self.state_stack.push(TokenOrRedirect::Close);

            for _ in 0..arity {
                self.state_stack
                    .push(TokenOrRedirect::FunctorRedirect(max_depth));
                self.state_stack.push(TokenOrRedirect::Comma);
            }

            self.state_stack.pop();

            self.state_stack.push(TokenOrRedirect::Open);
        }

        self.state_stack.push(TokenOrRedirect::Atom(name));

        true
    }

    fn format_bar_separator_op(&mut self, mut max_depth: usize, name: Atom, spec: OpDesc) {
        if self.check_max_depth(&mut max_depth) {
            self.iter.pop_stack();
            self.iter.pop_stack();

            let ellipsis_atom = atom!("...");

            self.state_stack.push(TokenOrRedirect::Atom(ellipsis_atom));
            self.state_stack.push(TokenOrRedirect::BarAsOp);
            self.state_stack.push(TokenOrRedirect::Atom(ellipsis_atom));

            return;
        }

        let left_directed_op = DirectedOp::Left(name, spec);
        let right_directed_op = DirectedOp::Right(name, spec);

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

    fn format_curly_braces(&mut self, mut max_depth: usize) -> bool {
        if self.check_max_depth(&mut max_depth) {
            self.iter.pop_stack();

            let ellipsis_atom = atom!("...");

            self.state_stack.push(TokenOrRedirect::RightCurly);
            self.state_stack.push(TokenOrRedirect::Atom(ellipsis_atom));
            self.state_stack.push(TokenOrRedirect::LeftCurly);

            return false;
        }

        self.state_stack.push(TokenOrRedirect::RightCurly);
        self.state_stack
            .push(TokenOrRedirect::CurlyBracketRedirect(max_depth));
        self.state_stack.push(TokenOrRedirect::LeftCurly);

        true
    }

    fn format_numbered_vars(&mut self) -> bool {
        let h = self.iter.stack_last().unwrap();

        let cell = self.iter.read_cell(h);
        let cell = heap_bound_store(&self.iter.heap, heap_bound_deref(&self.iter.heap, cell));

        // 7.10.4
        if let Some(var) = numbervar(&self.numbervars_offset, cell) {
            self.iter.pop_stack();
            self.state_stack.push(TokenOrRedirect::NumberedVar(var));
            return true;
        }

        false
    }

    fn format_clause(
        &mut self,
        max_depth: usize,
        arity: usize,
        name: Atom,
        op_desc: Option<OpDesc>,
    ) -> bool {
        if self.numbervars && is_numbered_var(name, arity) {
            if self.format_numbered_vars() {
                return true;
            }
        }

        let dot_atom = atom!(".");

        if let Some(spec) = op_desc {
            if dot_atom == name && is_infix!(spec.get_spec()) {
                if !self.ignore_ops {
                    self.push_list(max_depth);
                    return true;
                }
            }

            if !self.ignore_ops && spec.get_prec() > 0 {
                self.enqueue_op(max_depth, name, spec);
                return true;
            }
        }

        return match (name, arity) {
            (atom!("{}"), 1) if !self.ignore_ops => self.format_curly_braces(max_depth),
            _ => self.format_struct(max_depth, arity, name),
        };
    }

    fn offset_as_string(&mut self, h: IterStackLoc) -> Option<String> {
        let cell = self.iter.read_cell(h);

        if let Some(var) = self.var_names.get(&cell) {
            read_heap_cell!(cell,
               (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                   return Some(var.borrow().to_string());
               }
               _ => {
                   self.iter.push_stack(h);
                   return None;
               }
            );
        }

        read_heap_cell!(cell,
            (HeapCellValueTag::Lis | HeapCellValueTag::Str, h) => {
                Some(format!("{}", h))
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, h) => {
                Some(format!("_{}", h))
            }
            (HeapCellValueTag::StackVar, h) => {
                Some(format!("_s_{}", h))
            }
            _ => {
                None
            }
        )
    }

    fn check_for_seen(&mut self, max_depth: &mut usize) -> Option<HeapCellValue> {
        if let Some(mut orig_cell) = self.iter.next() {
            loop {
                let is_cyclic = orig_cell.get_forwarding_bit();

                let cell = heap_bound_store(self.iter.heap, heap_bound_deref(self.iter.heap, orig_cell));
                let cell = unmark_cell_bits!(cell);

                match self.var_names.get(&cell).cloned() {
                    Some(var) if cell.is_var() => {
                        // If cell is an unbound variable and maps to
                        // a name via heap_locs, append the name to
                        // the current output, and return None. None
                        // short-circuits handle_heap_term.
                        // self.iter.pop_stack();

                        let var_str = var.borrow().to_string();

                        push_space_if_amb!(self, &var_str, {
                            append_str!(self, &var_str);
                        });

                        return None;
                    }
                    var_opt => {
                        if is_cyclic && cell.is_compound(self.iter.heap) {
                            // self-referential variables are marked "cyclic".
                            read_heap_cell!(cell,
                                (HeapCellValueTag::Lis, vh) => {
                                    if self.iter.heap[vh].get_forwarding_bit() {
                                        self.iter.pop_stack();
                                    }

                                    if self.iter.heap[vh+1].get_forwarding_bit() {
                                        self.iter.pop_stack();
                                    }
                                }
                                _ => {}
                            );

                            match var_opt {
                                Some(var) => {
                                    // If the term is bound to a named variable,
                                    // print the variable's name to output.
                                    let var_str = var.borrow().to_string();

                                    push_space_if_amb!(self, &var_str, {
                                        append_str!(self, &var_str);
                                    });
                                }
                                None => {
                                    if self.max_depth == 0 || *max_depth == 0 {
                                        // otherwise, contract it to an ellipsis.
                                        push_space_if_amb!(self, "...", {
                                            append_str!(self, "...");
                                        });
                                    } else {
                                        debug_assert!(cell.is_ref());

                                        // as usual, the WAM's
                                        // optimization of the Lis tag
                                        // (conflating the location of
                                        // the list and that of its
                                        // first element) needs
                                        // special consideration here
                                        // lest we find ourselves in
                                        // an infinite loop.
                                        if cell.get_tag() == HeapCellValueTag::Lis {
                                            *max_depth -= 1;
                                        }

                                        let h = cell.get_value() as usize;
                                        self.iter.push_stack(IterStackLoc::iterable_loc(h, HeapOrStackTag::Heap));

                                        if let Some(cell) = self.iter.next() {
                                            orig_cell = cell;
                                            continue;
                                        }
                                    }
                                }
                            }

                            return None;
                        }

                        return Some(cell);
                    }
                }
            }
        } else {
            while let Some(_) = self.iter.pop_stack() {}
            None
        }
    }

    fn print_impromptu_atom(&mut self, atom: Atom) {
        let result = self.print_op_addendum(&*atom.as_str());

        push_space_if_amb!(self, result.as_str(), {
            append_str!(self, &result);
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
            append_str!(self, &result);
        });
    }

    #[inline]
    fn print_ip_addr(&mut self, ip: IpAddr) {
        push_char!(self, '\'');
        append_str!(self, &format!("{}", ip));
        push_char!(self, '\'');
    }

    #[inline]
    fn print_raw_ptr(&mut self, ptr: *const ArenaHeader) {
        append_str!(self, &format!("0x{:x}", ptr as *const u8 as usize));
    }

    fn print_number(&mut self, max_depth: usize, n: NumberFocus, op: &Option<DirectedOp>) {
        let (add_brackets, op_is_prefix) = if let Some(op) = op {
            (op.is_negative_sign() && !n.is_negative(), op.is_prefix())
        } else {
            (false, false)
        };

        if add_brackets {
            if op_is_prefix && !self.outputter.ends_with(" ") {
                push_char!(self, ' ');
            }

            push_char!(self, '(');
        }

        match n {
            NumberFocus::Unfocused(n) => match n {
                Number::Float(OrderedFloat(fl)) => {
                    let output_str = fmt_float(fl);

                    push_space_if_amb!(self, &output_str, {
                        append_str!(self, &output_str);
                    });
                }
                Number::Rational(r) => {
                    self.print_rational(max_depth, r, *op);
                }
                n => {
                    let output_str = format!("{}", n);

                    push_space_if_amb!(self, &output_str, {
                        append_str!(self, &output_str);
                    });
                }
            },
            NumberFocus::Denominator(r) => {
                let output_str = format!("{}", r.denominator());

                push_space_if_amb!(self, &output_str, {
                    append_str!(self, &output_str);
                });
            }
            NumberFocus::Numerator(r) => {
                let output_str = format!("{}", r.numerator());

                push_space_if_amb!(self, &output_str, {
                    append_str!(self, &output_str);
                });
            }
        }

        if add_brackets {
            push_char!(self, ')');
        }
    }

    fn print_rational(
        &mut self,
        mut max_depth: usize,
        r: TypedArenaPtr<Rational>,
        parent_op: Option<DirectedOp>,
    ) {
        if self.check_max_depth(&mut max_depth) {
            self.state_stack.push(TokenOrRedirect::Close);
            self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            self.state_stack.push(TokenOrRedirect::Open);

            self.state_stack.push(TokenOrRedirect::Atom(atom!("rdiv")));

            return;
        }

        match self.op_dir.get(&(atom!("rdiv"), Fixity::In)) {
            Some(op_desc) => {
                if r.is_int() {
                    let output_str = format!("{}", r);

                    push_space_if_amb!(self, &output_str, {
                        append_str!(self, &output_str);
                    });

                    return;
                }

                let rdiv_ct = atom!("rdiv");

                let left_directed_op = if op_desc.get_prec() > 0 {
                    Some(DirectedOp::Left(rdiv_ct, *op_desc))
                } else {
                    None
                };

                let right_directed_op = if op_desc.get_prec() > 0 {
                    Some(DirectedOp::Right(rdiv_ct, *op_desc))
                } else {
                    None
                };

                if !self.ignore_ops && op_desc.get_prec() > 0 {
                    self.state_stack.push(TokenOrRedirect::NumberFocus(
                        max_depth,
                        NumberFocus::Denominator(r),
                        left_directed_op,
                    ));
                    self.state_stack
                        .push(TokenOrRedirect::Op(rdiv_ct, *op_desc));
                    self.state_stack.push(TokenOrRedirect::NumberFocus(
                        max_depth,
                        NumberFocus::Numerator(r),
                        right_directed_op,
                    ));

                    self.set_parent_of_first_op(parent_op);
                } else {
                    self.state_stack.push(TokenOrRedirect::Close);

                    self.state_stack.push(TokenOrRedirect::NumberFocus(
                        max_depth,
                        NumberFocus::Denominator(r),
                        None,
                    ));

                    self.state_stack.push(TokenOrRedirect::Comma);

                    self.state_stack.push(TokenOrRedirect::NumberFocus(
                        max_depth,
                        NumberFocus::Numerator(r),
                        None,
                    ));

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

    // returns true if max_depth limit is reached and ellipsis is printed.
    fn print_string_as_functor(&mut self, focus: usize, max_depth: &mut usize) -> bool {
        let iter = HeapPStrIter::new(self.iter.heap, focus);

        for (char_count, c) in iter.chars().enumerate() {
            if self.check_max_depth(max_depth) {
                if char_count > 0 {
                    self.state_stack.push(TokenOrRedirect::Close);
                }

                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                return true;
            }

            append_str!(self, "'.'");
            push_char!(self, '(');

            print_char!(self, self.quoted, c);
            push_char!(self, ',');

            self.state_stack.push(TokenOrRedirect::Close);
        }

        false
    }

    // proper strings are terminal so there's no need for max_depth to
    // be a mutable ref here.
    fn print_proper_string(&mut self, focus: usize, max_depth: usize) {
        push_char!(self, '"');

        let iter = HeapPStrIter::new(self.iter.heap, focus);
        let char_to_string = |c: char| {
            // refrain from quoting characters other than '"' and '\'
            // unless self.quoted is true.
            match c {
                '\\' => "\\\\".to_string(),
                '"' => "\\\"".to_string(),
                _ => char_to_string(self.quoted, c),
            }
        };

        if max_depth == 0 {
            for c in iter.chars() {
                for c in char_to_string(c).chars() {
                    push_char!(self, c);
                }
            }
        } else {
            let mut char_count = 0;

            for c in iter.chars().take(max_depth) {
                char_count += 1;

                for c in char_to_string(c).chars() {
                    push_char!(self, c);
                }
            }

            if char_count == max_depth {
                append_str!(self, " ...");
            }
        }

        push_char!(self, '"');
    }

    fn remove_list_children(&mut self, h: usize) {
        match self.iter.heap[h].get_tag() {
            HeapCellValueTag::Lis => {
                self.iter.pop_stack();
                self.iter.pop_stack();
            }
            HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset => {
                self.iter.pop_stack();
            }
            HeapCellValueTag::CStr => {}
            _ => {
                unreachable!();
            }
        }
    }

    fn print_list_like(&mut self, mut max_depth: usize) {
        let focus = self.iter.focus();
        let mut heap_pstr_iter = HeapPStrIter::new(self.iter.heap, focus.value() as usize);

        if heap_pstr_iter.next().is_some() {
            while let Some(_) = heap_pstr_iter.next() {}
        } else {
            return self.push_list(max_depth);
        }

        let end_h = heap_pstr_iter.focus();
        let end_cell = heap_pstr_iter.focus;

        if self.check_max_depth(&mut max_depth) {
            self.remove_list_children(focus.value() as usize);
            self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            return;
        }

        let at_cdr = self.outputter.ends_with("|");

        if self.double_quotes {
            if !self.ignore_ops && end_cell.is_string_terminator(&self.iter.heap) {
                self.remove_list_children(focus.value() as usize);
                return self.print_proper_string(focus.value() as usize, max_depth);
            }
        }

        if self.ignore_ops {
            self.at_cdr(",");
            self.remove_list_children(focus.value() as usize);

            if !self.print_string_as_functor(focus.value() as usize, &mut max_depth) {
                if end_cell == empty_list_as_cell!() {
                    if !self.at_cdr("") {
                        append_str!(self, "[]");
                    }
                } else {
                    self.state_stack.push(TokenOrRedirect::FunctorRedirect(max_depth));
                    self.iter.push_stack(IterStackLoc::iterable_loc(end_h, HeapOrStackTag::Heap));
                }
            }
        } else {
            let value = heap_bound_store(
                self.iter.heap,
                heap_bound_deref(self.iter.heap, self.iter.read_cell(focus)),
            );

            read_heap_cell!(value,
                (HeapCellValueTag::Lis) => {
                    return self.push_list(max_depth);
                }
                _ => {
                    let switch = Rc::new(Cell::new((!at_cdr, 0)));
                    let switch = self.close_list(switch);

                    let (h, offset) = pstr_loc_and_offset(self.iter.heap, focus.value() as usize);

                    let offset = offset.get_num() as usize;
                    let tag = value.get_tag();

                    let end_h = if tag == HeapCellValueTag::PStrOffset {
                        // remove the fixnum offset from the iterator stack so we don't
                        // print an extraneous number. pstr offset value cells are never
                        // used by the iterator to mark cyclic terms so the removal is safe.
                        self.iter.pop_stack();
                        Some(end_h)
                    } else {
                        None
                    };

                    if !self.max_depth_exhausted(max_depth) {
                        let pstr = cell_as_string!(self.iter.heap[h]);
                        self.state_stack.push(TokenOrRedirect::CommaSeparatedCharList(CommaSeparatedCharList {
                            pstr, offset, max_depth, end_cell, end_h,
                        }));
                    } else {
                        self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                    }

                    self.open_list(switch);
                }
            );
        }
    }

    #[inline]
    fn max_depth_exhausted(&self, max_depth: usize) -> bool {
        self.max_depth > 0 && max_depth == 0
    }

    fn check_max_depth(&self, max_depth: &mut usize) -> bool {
        if self.max_depth > 0 && *max_depth == 0 {
            return true;
        }

        if *max_depth > 0 {
            *max_depth -= 1;
        }

        false
    }

    fn close_list(&mut self, switch: Rc<Cell<(bool, usize)>>) -> Option<Rc<Cell<(bool, usize)>>> {
        if let Some(TokenOrRedirect::Op(_, op_desc)) = self.state_stack.last() {
            if is_postfix!(op_desc.get_spec()) || is_infix!(op_desc.get_spec()) {
                self.state_stack.push(TokenOrRedirect::ChildCloseList);
                return None;
            }
        }

        self.state_stack
            .push(TokenOrRedirect::CloseList(switch.clone()));
        Some(switch)
    }

    fn open_list(&mut self, switch: Option<Rc<Cell<(bool, usize)>>>) {
        self.state_stack.push(match switch {
            Some(switch) => TokenOrRedirect::OpenList(switch),
            None => TokenOrRedirect::ChildOpenList,
        });
    }

    fn push_list(&mut self, mut max_depth: usize) {
        if self.max_depth_exhausted(max_depth) {
            self.iter.pop_stack();
            self.iter.pop_stack();

            self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));

            return;
        } else if self.check_max_depth(&mut max_depth) {
            self.iter.pop_stack();
            self.iter.pop_stack();

            let cell = Rc::new(Cell::new((true, 0)));

            let switch = self.close_list(cell);

            self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            self.open_list(switch);

            return;
        }

        let cell = Rc::new(Cell::new((true, max_depth)));

        let switch = self.close_list(cell);

        self.state_stack.push(TokenOrRedirect::FunctorRedirect(max_depth));
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
        self.state_stack.push(TokenOrRedirect::FunctorRedirect(max_depth + 1));

        self.open_list(switch);
    }

    fn handle_op_as_struct(
        &mut self,
        name: Atom,
        arity: usize,
        op: Option<DirectedOp>,
        is_functor_redirect: bool,
        op_desc: OpDesc,
        negated_operand: bool,
        max_depth: usize,
    ) {
        let add_brackets = if !self.ignore_ops {
            negated_operand
                || if let Some(ref op) = op {
                    if self.numbervars && arity == 1 && name == atom!("$VAR") {
                        !self.iter.immediate_leaf_has_property(|addr| {
                            match Number::try_from(addr) {
                                Ok(Number::Integer(n)) => (*n).sign() == Sign::Positive,
                                Ok(Number::Fixnum(n)) => n.get_num() >= 0,
                                Ok(Number::Float(f)) => f >= OrderedFloat(0f64),
                                Ok(Number::Rational(r)) => (*r).sign() == Sign::Positive,
                                _ => false,
                            }
                        }) && needs_bracketing(op_desc, op)
                    } else {
                        needs_bracketing(op_desc, op)
                    }
                } else {
                    is_functor_redirect && op_desc.get_prec() >= 1000
                }
        } else {
            false
        };

        if add_brackets {
            self.state_stack.push(TokenOrRedirect::Close);
            self.format_clause(max_depth, arity, name, Some(op_desc));
            self.state_stack.push(TokenOrRedirect::Open);

            if !self.outputter.ends_with(" ") {
                let parent_op = self
                    .parent_of_first_op
                    .and_then(|(parent_op, last_item_idx)| {
                        // if parent_op isn't printed to the output string
                        // already, then it doesn't border the present op
                        // and we should return None.
                        if self.last_item_idx == last_item_idx {
                            Some(parent_op)
                        } else {
                            None
                        }
                    });

                for op in &[op, parent_op] {
                    if let Some(ref op) = &op {
                        if op.is_left()
                            && (op.is_prefix() || requires_space(&*op.as_atom().as_str(), "("))
                        {
                            self.state_stack.push(TokenOrRedirect::Space);
                            return;
                        }
                    }
                }
            }
        } else {
            self.format_clause(max_depth, arity, name, Some(op_desc));
        }
    }

    #[allow(dead_code)]
    fn print_tcp_listener(&mut self, tcp_listener: &TcpListener, max_depth: usize) {
        let (ip, port) = if let Some(addr) = tcp_listener.local_addr().ok() {
            (addr.ip(), addr.port())
        } else {
            let disconnected_atom = atom!("$disconnected_tcp_listener");
            self.state_stack
                .push(TokenOrRedirect::Atom(disconnected_atom));

            return;
        };

        let tcp_listener_atom = atom!("$tcp_listener");

        if self.format_struct(max_depth, 1, tcp_listener_atom) {
            let atom = self.state_stack.pop().unwrap();

            self.state_stack.pop();
            self.state_stack.pop();

            self.state_stack.push(TokenOrRedirect::NumberFocus(
                max_depth,
                NumberFocus::Unfocused(Number::Fixnum(Fixnum::build_with(port as i64))),
                None,
            ));
            self.state_stack.push(TokenOrRedirect::Comma);
            self.state_stack.push(TokenOrRedirect::IpAddr(ip));

            self.state_stack.push(TokenOrRedirect::Open);
            self.state_stack.push(atom);
        }
    }

    fn print_index_ptr(&mut self, index_ptr: IndexPtr, max_depth: usize) {
        if self.format_struct(max_depth, 1, atom!("$index_ptr")) {
            let atom = self.state_stack.pop().unwrap();

            self.state_stack.pop();
            self.state_stack.pop();

            let offset = if index_ptr.is_undefined() || index_ptr.is_dynamic_undefined() {
                TokenOrRedirect::Atom(atom!("undefined"))
            } else {
                let idx = index_ptr.p() as i64;

                TokenOrRedirect::NumberFocus(
                    max_depth,
                    NumberFocus::Unfocused(Number::Fixnum(Fixnum::build_with(idx))),
                    None,
                )
            };

            self.state_stack.push(offset);
            self.state_stack.push(TokenOrRedirect::Open);
            self.state_stack.push(atom);
        }
    }

    fn print_stream(&mut self, stream: Stream, max_depth: usize) {
        if let Some(alias) = stream.options().get_alias() {
            self.print_impromptu_atom(alias);
        } else {
            let stream_atom = atom!("$stream");

            if self.format_struct(max_depth, 1, stream_atom) {
                let atom = if stream.is_stdout() || stream.is_stdin() {
                    TokenOrRedirect::Atom(atom!("user"))
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

    fn print_comma_separated_char_list(&mut self, char_list: CommaSeparatedCharList) {
        let CommaSeparatedCharList { pstr, offset, max_depth, end_cell, end_h } = char_list;
        let pstr_str = pstr.as_str_from(offset);

        if let Some(c) = pstr_str.chars().next() {
            let offset = offset + c.len_utf8();

            if !self.max_depth_exhausted(max_depth) {
                self.state_stack.push(TokenOrRedirect::CommaSeparatedCharList(CommaSeparatedCharList {
                    pstr,
                    offset,
                    max_depth: max_depth.saturating_sub(1),
                    end_cell,
                    end_h,
                }));

                let max_depth_allows = self.max_depth == 0 || max_depth > 1;

                if max_depth_allows && pstr_str.chars().skip(1).next().is_some() {
                    self.state_stack.push(TokenOrRedirect::Comma);
                }

                self.state_stack.push(TokenOrRedirect::Char(c));
            } else {
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                self.state_stack.push(TokenOrRedirect::HeadTailSeparator);
            }
        } else if self.max_depth_exhausted(max_depth) {
            self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            self.state_stack.push(TokenOrRedirect::HeadTailSeparator);
        } else if end_cell != empty_list_as_cell!() {
            if let Some(end_h) = end_h {
                self.iter.push_stack(IterStackLoc::iterable_loc(end_h, HeapOrStackTag::Heap));
            }

            self.state_stack.push(TokenOrRedirect::FunctorRedirect(max_depth + 1));
            self.state_stack.push(TokenOrRedirect::HeadTailSeparator);
        }
    }

    fn handle_heap_term(
        &mut self,
        op: Option<DirectedOp>,
        is_functor_redirect: bool,
        mut max_depth: usize,
    ) {
        let negated_operand = negated_op_needs_bracketing(&self.iter, self.op_dir, &op);

        let addr = match self.check_for_seen(&mut max_depth) {
            Some(addr) => addr,
            None => return,
        };

        let print_struct = |printer: &mut Self, name: Atom, arity: usize| {
            if name == atom!("[]") && arity == 0 {
                match printer.state_stack.last() {
                    Some(TokenOrRedirect::CloseList(_) | TokenOrRedirect::ChildCloseList) => {
                        if printer.at_cdr("") {
                            return;
                        }
                    }
                    _ => {}
                }

                append_str!(printer, "[]");
            } else if arity > 0 {
                if let Some(spec) = fetch_op_spec(name, arity, printer.op_dir) {
                    printer.handle_op_as_struct(
                        name,
                        arity,
                        op,
                        is_functor_redirect,
                        spec,
                        negated_operand,
                        max_depth,
                    );
                } else {
                    push_space_if_amb!(printer, &*name.as_str(), {
                        printer.format_clause(max_depth, arity, name, None);
                    });
                }
            } else if fetch_op_spec(name, arity, printer.op_dir).is_some() {
                let mut result = String::new();

                if let Some(ref op) = op {
                    let op_is_prefix = op.is_prefix() && op.is_left();

                    if op_is_prefix
                        || printer
                            .outputter
                            .ends_with(&format!(" {}", op.as_atom().as_str()))
                    {
                        result.push(' ');
                    }

                    result.push('(');
                }

                result += &printer.print_op_addendum(&*name.as_str());

                if op.is_some() {
                    result.push(')');
                }

                push_space_if_amb!(printer, &result, {
                    append_str!(printer, &result);
                });
            } else {
                push_space_if_amb!(printer, &*name.as_str(), {
                    printer.print_impromptu_atom(name);
                });
            }
        };

        if !addr.is_var()
            && !addr.is_compound(&self.iter.heap)
            && self.max_depth_exhausted(max_depth)
        {
            if !(addr == atom_as_cell!(atom!("[]")) && self.at_cdr("")) {
                self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
            }

            return;
        }

        read_heap_cell!(addr,
            (HeapCellValueTag::Atom, (name, arity)) => {
                print_struct(self, name, arity);
            }
            (HeapCellValueTag::Char, c) => {
                let name = AtomTable::build_with(&self.atom_tbl, &String::from(c));
                print_struct(self, name, 0);
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.iter.heap[s])
                    .get_name_and_arity();

                if let Some(spec) = fetch_op_spec(name, arity, self.op_dir) {
                    self.handle_op_as_struct(
                        name,
                        arity,
                        op,
                        is_functor_redirect,
                        spec,
                        negated_operand,
                        max_depth,
                    );
                } else {
                    push_space_if_amb!(self, &*name.as_str(), {
                        self.format_clause(max_depth, arity, name, None);
                    });
                }
            }
            (HeapCellValueTag::Fixnum | HeapCellValueTag::CutPoint, n) => {
                self.print_number(max_depth, NumberFocus::Unfocused(Number::Fixnum(n)), &op);
            }
            (HeapCellValueTag::F64, f) => {
                self.print_number(max_depth, NumberFocus::Unfocused(Number::Float(*f)), &op);
            }
            (HeapCellValueTag::CStr | HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset) => {
                self.print_list_like(max_depth);
            }
            (HeapCellValueTag::Lis) => {
                if self.ignore_ops {
                    let period_atom = atom!(".");
                    self.format_struct(max_depth, 2, period_atom);
                } else {
                    self.print_list_like(max_depth);
                }
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let h = self.iter.focus();

                if let Some(offset_str) = self.offset_as_string(h) {
                    push_space_if_amb!(self, &offset_str, {
                        append_str!(self, offset_str.as_str());
                    })
                }
            }
            (HeapCellValueTag::Cons, c) => {
                match_untyped_arena_ptr!(c,
                   (ArenaHeaderTag::Integer, n) => {
                       self.print_number(max_depth, NumberFocus::Unfocused(Number::Integer(n)), &op);
                   }
                   (ArenaHeaderTag::Rational, r) => {
                       self.print_number(max_depth, NumberFocus::Unfocused(Number::Rational(r)), &op);
                   }
                   (ArenaHeaderTag::Stream, stream) => {
                       self.print_stream(stream, max_depth);
                   }
                   (ArenaHeaderTag::Dropped, _value) => {
                       self.print_impromptu_atom(atom!("$dropped_value"));
                   }
                   (ArenaHeaderTag::IndexPtr, index_ptr) => {
                       self.print_index_ptr(*index_ptr, max_depth);
                   }
                   _ => {
                   }
               );
            }
            _ => {
                unreachable!()
            }
        );
    }

    fn at_cdr(&mut self, tr: &str) -> bool {
        let len = self.outputter.len();

        if self.outputter.ends_with("|") {
            self.outputter.truncate(len - "|".len());
            append_str!(self, tr);
            true
        } else {
            false
        }
    }

    pub fn print(mut self) -> Outputter {
        let spec = self.toplevel_spec.take();
        self.handle_heap_term(spec, false, self.max_depth);

        while let Some(loc_data) = self.state_stack.pop() {
            match loc_data {
                TokenOrRedirect::Atom(atom) => self.print_impromptu_atom(atom),
                TokenOrRedirect::BarAsOp => append_str!(self, " | "),
                TokenOrRedirect::Char(c) => print_char!(self, self.quoted, c),
                TokenOrRedirect::Op(atom, op) => {
                    self.print_op(&*atom.as_str());

                    if is_prefix!(op.get_spec()) {
                        self.set_parent_of_first_op(Some(DirectedOp::Left(atom, op)));
                    }
                }
                TokenOrRedirect::NumberedVar(num_var) => append_str!(self, &num_var),
                TokenOrRedirect::CompositeRedirect(max_depth, op) => {
                    self.handle_heap_term(Some(op), false, max_depth)
                }
                TokenOrRedirect::CurlyBracketRedirect(max_depth) => {
                    self.handle_heap_term(None, false, max_depth)
                }
                TokenOrRedirect::FunctorRedirect(max_depth) => {
                    self.handle_heap_term(None, true, max_depth)
                }
                TokenOrRedirect::Close => push_char!(self, ')'),
                TokenOrRedirect::IpAddr(ip) => self.print_ip_addr(ip),
                TokenOrRedirect::RawPtr(ptr) => self.print_raw_ptr(ptr),
                TokenOrRedirect::Open => push_char!(self, '('),
                TokenOrRedirect::ChildOpenList => {
                    push_char!(self, '[');
                }
                TokenOrRedirect::ChildCloseList => {
                    push_char!(self, ']');
                }
                TokenOrRedirect::OpenList(delimit) => {
                    if !self.at_cdr(",") {
                        push_char!(self, '[');
                    } else {
                        let (_, max_depth) = delimit.get();
                        delimit.set((false, max_depth));
                    }
                }
                TokenOrRedirect::CloseList(delimit) => {
                    if delimit.get().0 {
                        push_char!(self, ']');
                    }
                }
                TokenOrRedirect::HeadTailSeparator => append_str!(self, "|"),
                TokenOrRedirect::NumberFocus(max_depth, n, op) => {
                    self.print_number(max_depth, n, &op);
                }
                TokenOrRedirect::Comma => append_str!(self, ","),
                TokenOrRedirect::Space => push_char!(self, ' '),
                TokenOrRedirect::LeftCurly => push_char!(self, '{'),
                TokenOrRedirect::RightCurly => push_char!(self, '}'),
                TokenOrRedirect::StackPop => {
                    self.iter.pop_stack();
                    self.state_stack.push(TokenOrRedirect::Atom(atom!("...")));
                }
                TokenOrRedirect::CommaSeparatedCharList(char_list) => {
                    self.print_comma_separated_char_list(char_list);
                }
            }
        }

        self.outputter
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::machine::mock_wam::*;

    #[test]
    fn term_printing_tests() {
        let mut wam = MockWAM::new();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");
        let c_atom = atom!("c");

        wam.machine_st
            .heap
            .extend(functor!(f_atom, [atom(a_atom), atom(b_atom)]));

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "f(a,b)");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        wam.machine_st.heap.extend(functor!(
            f_atom,
            [
                atom(a_atom),
                atom(b_atom),
                atom(a_atom),
                cell(str_loc_as_cell!(0))
            ]
        ));

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "f(a,b,a,...)");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        // print L = [L|L].
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(1));

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "[...|...]");

            let mut printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            printer
                .var_names
                .insert(list_loc_as_cell!(1), VarPtr::from("L"));

            let output = printer.print();

            assert_eq!(output.result(), "[L|L]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let functor = functor!(f_atom, [atom(a_atom), atom(b_atom), atom(b_atom)]);

        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(str_loc_as_cell!(5));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(str_loc_as_cell!(5));
        wam.machine_st.heap.push(empty_list_as_cell!());

        wam.machine_st.heap.extend(functor);

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "[f(a,b,b),f(a,b,b)]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap[4] = list_loc_as_cell!(1);

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "[f(a,b,b),f(a,b,b)|...]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        {
            let mut printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            printer
                .var_names
                .insert(list_loc_as_cell!(1), VarPtr::from("L"));

            let output = printer.print();

            assert_eq!(output.result(), "[f(a,b,b),f(a,b,b)|L]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        // issue #382
        wam.machine_st.heap.clear();
        wam.machine_st.heap.push(list_loc_as_cell!(1));

        for idx in 0..3000 {
            wam.machine_st.heap.push(heap_loc_as_cell!(2 * idx + 1));
            wam.machine_st.heap.push(list_loc_as_cell!(2 * idx + 2 + 1));
        }

        wam.machine_st.heap.push(empty_list_as_cell!());

        {
            let mut printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            printer.max_depth = 5;

            let output = printer.print();

            assert_eq!(output.result(), "[_1,_3,_5,_7,_9|...]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        put_partial_string(&mut wam.machine_st.heap, "abc", &wam.machine_st.atom_tbl);

        {
            let printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                pstr_loc_as_cell!(0),
            );

            let output = printer.print();

            assert_eq!(output.result(), "[a,b,c|_1]");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.pop();

        wam.machine_st.heap.push(list_loc_as_cell!(2));

        wam.machine_st.heap.push(atom_as_cell!(a_atom));
        wam.machine_st.heap.push(list_loc_as_cell!(4));
        wam.machine_st.heap.push(atom_as_cell!(b_atom));
        wam.machine_st.heap.push(list_loc_as_cell!(6));
        wam.machine_st.heap.push(atom_as_cell!(c_atom));
        wam.machine_st.heap.push(empty_list_as_cell!());

        {
            let mut printer = HCPrinter::new(
                &mut wam.machine_st.heap,
                Arc::clone(&wam.machine_st.atom_tbl),
                &mut wam.machine_st.stack,
                &wam.op_dir,
                PrinterOutputter::new(),
                heap_loc_as_cell!(0),
            );

            printer.double_quotes = true;

            let output = printer.print();

            assert_eq!(output.result(), "\"abcabc\"");
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        assert_eq!(
            &wam.parse_and_print_term("=(X,[a,b,c|X]).").unwrap(),
            "=(X,[a,b,c|X])"
        );

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(
            &wam.parse_and_print_term("[a,b,\"a\",[a,b,c]].").unwrap(),
            "[a,b,[a],[a,b,c]]"
        );

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(
            &wam.parse_and_print_term("[\"abc\",e,f,[g,e,h,Y,v|[X,Y]]].")
                .unwrap(),
            "[[a,b,c],e,f,[g,e,h,Y,v,X,Y]]"
        );

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(&wam.parse_and_print_term("f((a,b)).").unwrap(), "f((a,b))");

        all_cells_unmarked(&wam.machine_st.heap);

        wam.op_dir
            .insert((atom!("+"), Fixity::In), OpDesc::build_with(500, YFX as u8));
        wam.op_dir
            .insert((atom!("*"), Fixity::In), OpDesc::build_with(400, YFX as u8));

        assert_eq!(
            &wam.parse_and_print_term("[a|[] + b].").unwrap(),
            "[a|[]+b]"
        );

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(
            &wam.parse_and_print_term("[a|[b|c]*d].").unwrap(),
            "[a|[b|c]*d]"
        );

        all_cells_unmarked(&wam.machine_st.heap);

        wam.op_dir
            .insert((atom!("fy"), Fixity::Pre), OpDesc::build_with(9, FY as u8));

        wam.op_dir
            .insert((atom!("yf"), Fixity::Post), OpDesc::build_with(9, YF as u8));

        assert_eq!(
            &wam.parse_and_print_term("(fy (fy 1)yf)yf.").unwrap(),
            "(fy (fy 1)yf)yf"
        );

        assert_eq!(
            &wam.parse_and_print_term("fy(fy(yf(fy(1)))).").unwrap(),
            "fy fy (fy 1)yf"
        );
    }
}
