use prolog::ast::*;
use prolog::heap_iter::*;
use prolog::machine::machine_state::MachineState;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(ClauseName),
    Redirect,
    Open,
    Close,
    Comma,
    OpenList(Rc<Cell<bool>>),
    CloseList(Rc<Cell<bool>>),
    HeadTailSeparator,
    Space
}

pub trait HCValueFormatter {
    // this function belongs to the display predicate formatter, which it uses
    // to format all clauses.
    fn format_struct(&self, arity: usize, name: ClauseName, state_stack: &mut Vec<TokenOrRedirect>)
    {
        state_stack.push(TokenOrRedirect::Close);

        for _ in 0 .. arity {
            state_stack.push(TokenOrRedirect::Redirect);
            state_stack.push(TokenOrRedirect::Comma);
        }

        state_stack.pop();
        state_stack.push(TokenOrRedirect::Open);

        state_stack.push(TokenOrRedirect::Atom(name));
    }

    // this can be overloaded to handle special cases, falling back on the default of
    // format_struct when convenient.
    fn format_clause(&self, usize, ClauseType, &mut Vec<TokenOrRedirect>);
}

pub trait HCValueOutputter {
    type Output;

    fn new() -> Self;
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

// the 'classic' display corresponding to the display predicate.
pub struct DisplayFormatter {}

impl HCValueFormatter for DisplayFormatter {
    fn format_clause(&self, arity: usize, ct: ClauseType, state_stack: &mut Vec<TokenOrRedirect>)
    {
        if ct.fixity().is_some() {
            let mut new_name = String::from("'");
            new_name += ct.name().as_str();
            new_name += "'";

            self.format_struct(arity, ct.name(), state_stack);
        } else {
            self.format_struct(arity, ct.name(), state_stack);
        }
    }
}

pub struct TermFormatter {}

impl HCValueFormatter for TermFormatter {
    fn format_clause(&self, arity: usize, ct: ClauseType, state_stack: &mut Vec<TokenOrRedirect>)
    {
        if let Some(fixity) = ct.fixity() {
            match fixity {
                Fixity::Post => {
                    state_stack.push(TokenOrRedirect::Atom(ct.name()));
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Redirect);
                },
                Fixity::Pre => {
                    state_stack.push(TokenOrRedirect::Redirect);
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Atom(ct.name()));
                },
                Fixity::In => {
                    state_stack.push(TokenOrRedirect::Redirect);
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Atom(ct.name()));
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Redirect);
                }
            }
        } else {
            self.format_struct(arity, ct.name(), state_stack);
        }
    }
}

type ReverseHeapVarDict<'a> = HashMap<Addr, Rc<Var>>;

pub struct HCPrinter<'a, Formatter, Outputter> {
    formatter:    Formatter,
    outputter:    Outputter,
    machine_st:   &'a MachineState,
    state_stack:  Vec<TokenOrRedirect>,
    heap_locs:    ReverseHeapVarDict<'a>,
    printed_vars: HashSet<Addr>
}

fn reverse_heap_locs<'a>(machine_st: &'a MachineState, heap_locs: &'a HeapVarDict)
                         -> ReverseHeapVarDict<'a>
{
    heap_locs.iter().map(|(var, var_addr)| {
        (machine_st.store(machine_st.deref(var_addr.clone())), var.clone())
    }).collect()
}

impl<'a, Formatter: HCValueFormatter, Outputter: HCValueOutputter>
    HCPrinter<'a, Formatter, Outputter>
{
    pub fn new(machine_st: &'a MachineState, fmt: Formatter, output: Outputter) -> Self
    {
        HCPrinter { formatter: fmt,
                    outputter: output,
                    machine_st,
                    state_stack: vec![],
                    heap_locs: ReverseHeapVarDict::new(),
                    printed_vars: HashSet::new() }
    }

    pub fn from_heap_locs(machine_st: &'a MachineState, fmt: Formatter,
                          output: Outputter, heap_locs: &'a HeapVarDict)
                          -> Self
    {
        let mut printer = Self::new(machine_st, fmt, output);

        printer.heap_locs = reverse_heap_locs(machine_st, heap_locs);
        printer
    }

    fn offset_as_string(&self, addr: Addr) -> Option<String> {
        match addr {
            Addr::HeapCell(h) | Addr::Lis(h) | Addr::Str(h) =>
                Some(format!("_{}", h)),
            Addr::StackCell(fr, sc) =>
                Some(format!("s_{}_{}", fr, sc)),
            _ => None
        }
    }

    fn print_offset(&mut self, addr: Addr) {
        self.offset_as_string(addr).map(|s| self.outputter.append(s.as_str()));
    }

    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator) -> Option<HeapCellValue> {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            match self.heap_locs.get(&addr).cloned() {
                Some(var) => if !self.printed_vars.contains(&addr) {
                    self.printed_vars.insert(addr);
                    return iter.next();
                } else {
                    iter.stack().pop();
                    self.outputter.append(var.as_str());

                    return None;
                },
                None => if self.machine_st.is_cyclic_term(addr.clone()) {
                    if self.printed_vars.contains(&addr) {
                        iter.stack().pop();
                        self.print_offset(addr);

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

    fn handle_heap_term(&mut self, iter: &mut HCPreOrderIterator)
    {
        let heap_val = match self.check_for_seen(iter) {
            Some(heap_val) => heap_val,
            _ => return
        };

        match heap_val {
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let ct = ClauseType::from(name, arity, fixity);
                self.formatter.format_clause(arity, ct, &mut self.state_stack)
            },
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) =>
                if !self.at_cdr("") {
                    self.outputter.append("[]");
                },
            HeapCellValue::Addr(Addr::Con(c)) =>
                self.outputter.append(format!("{}", c).as_str()),
            HeapCellValue::Addr(Addr::Lis(_)) => {
                let cell = Rc::new(Cell::new(true));

                self.state_stack.push(TokenOrRedirect::CloseList(cell.clone()));

                self.state_stack.push(TokenOrRedirect::Redirect);
                self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
                self.state_stack.push(TokenOrRedirect::Redirect);

                self.state_stack.push(TokenOrRedirect::OpenList(cell));
            },
            HeapCellValue::Addr(addr) => self.print_offset(addr)
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
                    TokenOrRedirect::Space =>
                        self.outputter.append(" "),
                    TokenOrRedirect::Atom(atom) =>
                        self.outputter.append(atom.as_str()),
                    TokenOrRedirect::Redirect =>
                        self.handle_heap_term(&mut iter),
                    TokenOrRedirect::Close =>
                        self.outputter.append(")"),
                    TokenOrRedirect::Open =>
                        self.outputter.append("("),
                    TokenOrRedirect::OpenList(delimit) =>
                        if !self.at_cdr(", ") {
                            self.outputter.append("[");
                        } else {
                            delimit.set(false);
                        },
                    TokenOrRedirect::CloseList(delimit) =>
                        if delimit.get() {
                            self.outputter.append("]");
                        },
                    TokenOrRedirect::HeadTailSeparator =>
                        self.outputter.append(" | "),
                    TokenOrRedirect::Comma =>
                        self.outputter.append(", ")
                }
            } else if !iter.stack().is_empty() {
                self.handle_heap_term(&mut iter);
            } else {
                break;
            }
        }

        self.outputter
    }
}
