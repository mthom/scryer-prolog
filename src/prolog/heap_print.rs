use prolog_parser::ast::*;

use prolog::instructions::*;
use prolog::machine::machine_state::*;
use prolog::num::*;
use prolog::heap_iter::*;
use prolog::ordered_float::OrderedFloat;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::rc::Rc;

#[derive(Clone)]
pub enum DirectedOp {
    Left(ClauseName),
    Right(ClauseName)
}

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(ClauseName),
    Op(ClauseName, Fixity),
    NumberedVar(String),
    CompositeRedirect(DirectedOp),
    Redirect,
    Open,
    Close,
    Comma,
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
    fn result(self) -> Self::Output;
    fn ends_with(&self, &str) -> bool;
    fn len(&self) -> usize;
    fn truncate(&mut self, usize);
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
}

#[inline]
fn is_numbered_var(ct: &ClauseType, arity: usize) -> bool {
    arity == 1 && if let &ClauseType::Named(ref name, _) = ct {
        name.as_str() == "$VAR"
    } else {
        false
    }
}

impl MachineState {
    pub fn numbervar(&self, addr: Addr) -> Option<Var> {
        static CHAR_CODES: [char; 26] = ['A','B','C','D','E','F','G','H','I','J',
                                         'K','L','M','N','O','P','Q','R','S','T',
                                         'U','V','W','X','Y','Z'];

        match self.store(self.deref(addr)) {
            Addr::Con(Constant::Number(Number::Integer(ref n)))
                if !n.is_negative() => {
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

type ReverseHeapVarDict<'a> = HashMap<Addr, Rc<Var>>;

pub struct HCPrinter<'a, Outputter> {
    outputter:    Outputter,
    machine_st:   &'a MachineState,
    state_stack:  Vec<TokenOrRedirect>,
    heap_locs:    ReverseHeapVarDict<'a>,
    printed_vars: HashSet<Addr>,
    pub(crate) numbervars:   bool,
    pub(crate) quoted:       bool,
    pub(crate) ignore_ops:   bool
}

macro_rules! push_space_if_amb {
    ($self:expr, $atom:expr, $op:expr, $action:block) => (
        match ambiguity_check($atom, $op) {
            Some(DirectedOp::Left(_)) => {
                $self.outputter.push_char(' ');
                $action;
            },
            Some(DirectedOp::Right(_)) => {
                $action;
                $self.outputter.push_char(' ');
            },
            None => $action
        };
    )
}

fn continues_with_append(atom: &str, op: &str) -> bool {
    match atom.chars().next() {
        Some(ac) => op.chars().next().map(|oc| {
            if alpha_char!(ac) {
                alpha_numeric_char!(oc)
            } else if graphic_token_char!(ac) {
                graphic_char!(oc)
            } else if variable_indicator_char!(ac) {
                alpha_numeric_char!(oc)
            } else if capital_letter_char!(ac) {
                alpha_numeric_char!(oc)
            } else {
                false
            }
        }).unwrap_or(false),
        _ => false
    }
}

fn reverse_heap_locs<'a>(machine_st: &'a MachineState, heap_locs: &'a HeapVarDict)
                         -> ReverseHeapVarDict<'a>
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

// return op itself if there is an ambiguity to indicate the direction the op
// lies, None otherwise.
fn ambiguity_check(atom: &str, op: &Option<DirectedOp>) -> Option<DirectedOp>
{
    match op {
        &Some(DirectedOp::Left(ref lop)) if continues_with_append(lop.as_str(), atom) =>
            Some(DirectedOp::Left(lop.clone())),
        &Some(DirectedOp::Right(ref rop)) if continues_with_append(atom, rop.as_str()) =>
            Some(DirectedOp::Right(rop.clone())),
        _ =>
            None
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
                    printed_vars: HashSet::new(),
                    numbervars: false,
                    quoted: false,
                    ignore_ops: false }
    }

    pub fn from_heap_locs(machine_st: &'a MachineState, output: Outputter,
                          heap_locs: &'a HeapVarDict)
                          -> Self
    {
        let mut printer = Self::new(machine_st, output);

        printer.heap_locs = reverse_heap_locs(machine_st, heap_locs);
        printer
    }

    fn enqueue_op(&mut self, ct: ClauseType, fixity: Fixity) {
        match fixity {
            Fixity::Post => {
                self.state_stack.push(TokenOrRedirect::Op(ct.name(), fixity));
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(DirectedOp::Right(ct.name())));
            },
            Fixity::Pre => {
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(DirectedOp::Left(ct.name())));
                self.state_stack.push(TokenOrRedirect::Op(ct.name(), fixity));
            },
            Fixity::In => {
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(DirectedOp::Left(ct.name())));
                self.state_stack.push(TokenOrRedirect::Op(ct.name(), fixity));
                self.state_stack.push(TokenOrRedirect::CompositeRedirect(DirectedOp::Right(ct.name())));
            }
        }
    }

    fn format_struct(&mut self, arity: usize, name: ClauseName)
    {
        self.state_stack.push(TokenOrRedirect::Close);

        for _ in 0 .. arity {
            self.state_stack.push(TokenOrRedirect::Redirect);
            self.state_stack.push(TokenOrRedirect::Comma);
        }

        self.state_stack.pop();
        self.state_stack.push(TokenOrRedirect::Open);

        self.state_stack.push(TokenOrRedirect::Atom(name));
    }

    fn format_clause(&mut self, iter: &mut HCPreOrderIterator, arity: usize, ct: ClauseType)
    {
        if let Some(fixity) = ct.fixity() {
            if !self.ignore_ops {
                return self.enqueue_op(ct, fixity);
            }
        } else if self.numbervars && is_numbered_var(&ct, arity) {
            let addr = iter.stack().last().cloned().unwrap();

            // 7.10.4
            if let Some(var) = iter.machine_st.numbervar(addr) {
                iter.stack().pop();
                self.state_stack.push(TokenOrRedirect::NumberedVar(var));
                return;
            }
        }

        self.format_struct(arity, ct.name());
    }

    fn offset_as_string(&self, addr: Addr) -> Option<String> {
        match addr {
            Addr::HeapCell(h) | Addr::Lis(h) | Addr::Str(h) =>
                Some(format!("_{}", h)),
            Addr::StackCell(fr, sc) =>
                Some(format!("_s_{}_{}", fr, sc)),
            _ => None
        }
    }

    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator, op: &Option<DirectedOp>)
                      -> Option<HeapCellValue>
    {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            match self.heap_locs.get(&addr).cloned() {
                Some(var) => if !self.printed_vars.contains(&addr) {
                    self.printed_vars.insert(addr);
                    return iter.next();
                } else {
                    iter.stack().pop();
                    push_space_if_amb!(self, &var, op, {
                        self.outputter.append(&var);
                    });

                    return None;
                },
                None => if self.machine_st.is_cyclic_term(addr.clone()) {
                    if self.printed_vars.contains(&addr) {
                        iter.stack().pop();

                        if let Some(offset_str) = self.offset_as_string(addr) {
                            push_space_if_amb!(self, &offset_str, op, {
                                self.outputter.append(offset_str.as_str());
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

    fn print_atom(&mut self, atom: &ClauseName, fixity: Option<Fixity>) {
        match atom.as_str() {
            "" => self.outputter.append("''"),
            ";" | "!" => self.outputter.append(atom.as_str()),
            s => if fixity.is_some() || !self.quoted || non_quoted_token(s.chars()) {
                self.outputter.append(atom.as_str())
            } else {
                if self.quoted {
                    self.outputter.push_char('\'');
                }

                for c in atom.as_str().chars() {
                    self.print_char(c);
                }

                if self.quoted {
                    self.outputter.push_char('\'');
                }
            }
        }
    }

    fn print_char(&mut self, c: char) {
        match c {
            '\n' => self.outputter.append("\\n"),
            '\r' => self.outputter.append("\\r"),
            '\t' => self.outputter.append("\\t"),
            '\u{0b}' => self.outputter.append("\\v"), // UTF-8 vertical tab
            '\u{0c}' => self.outputter.append("\\f"), // UTF-8 form feed
            '\u{08}' => self.outputter.append("\\b"), // UTF-8 backspace
            '\u{07}' => self.outputter.append("\\a"), // UTF-8 alert
            '\x20' ... '\x7e' => self.outputter.push_char(c),
            _ => self.outputter.append(&format!("\\x{:x}", c as u32))
        };
    }

    fn print_constant(&mut self, c: Constant, op: &Option<DirectedOp>) {
        match c {
            Constant::Atom(ref atom, Some(fixity)) => {
                if op.is_some() {
                    self.outputter.push_char('(');
                }

                self.print_atom(atom, Some(fixity));

                if op.is_some() {
                    self.outputter.push_char(')');
                }
            },
            Constant::Atom(ref atom, None) =>
                push_space_if_amb!(self, atom.as_str(), &op, {
                    self.print_atom(atom, None);
                }),
            Constant::Char(c) if non_quoted_token(once(c)) =>
                self.print_char(c),
            Constant::Char(c) =>
                if self.quoted {
                    self.outputter.push_char('\'');
                    self.print_char(c);
                    self.outputter.push_char('\'');
                } else {
                    self.print_char(c);
                },
            Constant::EmptyList =>
                self.outputter.append("[]"),
            Constant::Number(Number::Float(fl)) =>
                if &fl == &OrderedFloat(0f64) {
                    push_space_if_amb!(self, "0", &op, {
                        self.outputter.append("0");
                    });
                } else {
                    let output_str = format!("{}", fl);

                    push_space_if_amb!(self, &output_str, &op, {
                        self.outputter.append(&output_str);
                    });
                },
            Constant::Number(n) => {
                let output_str = format!("{}", n);

                push_space_if_amb!(self, &output_str, &op, {
                    self.outputter.append(&output_str);
                });
            },
            Constant::String(s) =>
                if self.machine_st.machine_flags().double_quotes.is_chars() {
                    if !s.is_empty() {
                        self.push_list();
                    } else if s.is_expandable() {
                        if !self.at_cdr(" | _") {
                            self.outputter.push_char('_');
                        }
                    } else if !self.at_cdr("") {
                        self.outputter.append("[]");
                    }
                } else { // for now, == DoubleQuotes::Atom
                    let borrowed_str = s.borrow();

                    self.outputter.append("\"");
                    self.outputter.append(&borrowed_str[s.cursor() ..]);
                    self.outputter.append("\"");
                },
            Constant::Usize(i) =>
                self.outputter.append(&format!("u{}", i))
        }
    }

    fn push_list(&mut self) {
        let cell = Rc::new(Cell::new(true));

        self.state_stack.push(TokenOrRedirect::CloseList(cell.clone()));

        self.state_stack.push(TokenOrRedirect::Redirect);
        self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
        self.state_stack.push(TokenOrRedirect::Redirect);

        self.state_stack.push(TokenOrRedirect::OpenList(cell));
    }

    fn handle_heap_term(&mut self, iter: &mut HCPreOrderIterator, op: Option<DirectedOp>)
    {
        let heap_val = match self.check_for_seen(iter, &op) {
            Some(heap_val) => heap_val,
            None => return
        };

        match heap_val {
            HeapCellValue::NamedStr(arity, ref name, Some(fixity)) if name.as_str() != "," => {
                if op.is_some() {
                    self.state_stack.push(TokenOrRedirect::Close);
                }

                let ct = ClauseType::from(name.clone(), arity, Some(fixity));
                self.format_clause(iter, arity, ct);

                if op.is_some() {
                    self.state_stack.push(TokenOrRedirect::Open);
                }
            },
            HeapCellValue::NamedStr(arity, name, fixity) =>
                push_space_if_amb!(self, name.as_str(), &op, {
                    let ct = ClauseType::from(name, arity, fixity);
                    self.format_clause(iter, arity, ct);
                }),
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) =>
                if !self.at_cdr("") {
                    self.outputter.append("[]");
                },
            HeapCellValue::Addr(Addr::Con(c)) =>
                self.print_constant(c, &op),
            HeapCellValue::Addr(Addr::Lis(_)) =>
                self.push_list(),
            HeapCellValue::Addr(addr) =>
                if let Some(offset_str) = self.offset_as_string(addr) {
                    push_space_if_amb!(self, &offset_str, &op, {
                        self.outputter.append(offset_str.as_str());
                    })
                }
        }
    }

    fn at_cdr(&mut self, tr: &str) -> bool {
        let len = self.outputter.len();

        if self.outputter.ends_with(" | ") {
            self.outputter.truncate(len - 3);
            self.outputter.append(tr);

            true
        } else {
            false
        }
    }

    pub fn print(mut self, addr: Addr) -> Outputter {
        let mut iter = HCPreOrderIterator::new(&self.machine_st, addr);

        loop {
            if let Some(loc_data) = self.state_stack.pop() {
                match loc_data {
                    TokenOrRedirect::Atom(atom) =>
                        self.print_atom(&atom, None),
                    TokenOrRedirect::Op(atom, fixity) =>
                        self.print_atom(&atom, Some(fixity)),
                    TokenOrRedirect::NumberedVar(num_var) =>
                        self.outputter.append(num_var.as_str()),
                    TokenOrRedirect::CompositeRedirect(op) =>
                        self.handle_heap_term(&mut iter, Some(op)),
                    TokenOrRedirect::Redirect =>
                        self.handle_heap_term(&mut iter, None),
                    TokenOrRedirect::Close =>
                        self.outputter.append(")"),
                    TokenOrRedirect::Open =>
                        self.outputter.append("("),
                    TokenOrRedirect::OpenList(delimit) =>
                        if self.ignore_ops {
                            self.format_struct(2, clause_name!("."));
                        } else if !self.at_cdr(", ") {
                            self.outputter.append("[");
                        } else {
                            delimit.set(false);
                        },
                    TokenOrRedirect::CloseList(delimit) =>
                        if !self.ignore_ops && delimit.get() {
                            self.outputter.append("]");
                        },
                    TokenOrRedirect::HeadTailSeparator =>
                        if !self.ignore_ops {
                            self.outputter.append(" | ");
                        },
                    TokenOrRedirect::Comma =>
                        self.outputter.append(", ")
                }
            } else if !iter.stack().is_empty() {
                self.handle_heap_term(&mut iter, None);
            } else {
                break;
            }
        }

        self.outputter
    }
}
