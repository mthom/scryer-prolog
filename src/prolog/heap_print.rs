use prolog::ast::*;
use prolog::heap_iter::*;
use prolog::machine::machine_state::MachineState;

use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashSet;
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

pub struct HCPrinter<'a, Formatter, Outputter> {
    formatter:    Formatter,
    outputter:    Outputter,
    machine_st:   &'a MachineState,
    state_stack:  Vec<TokenOrRedirect>,
    heap_locs:    Cow<'a, HeapVarDict>,
    printed_vars: HashSet<Addr>
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
                    heap_locs: Cow::default(),
                    printed_vars: HashSet::new() }
    }

    pub fn from_heap_locs(machine_st: &'a MachineState, fmt: Formatter,
                          output: Outputter, heap_locs: &'a HeapVarDict)
                          -> Self
    {
        let mut printer = Self::new(machine_st, fmt, output);

        printer.heap_locs = Cow::Borrowed(heap_locs);
        printer
    }

    pub fn from_heap_locs_as_seen(machine_st: &'a MachineState, fmt: Formatter,
                                  output: Outputter, heap_locs: &'a HeapVarDict)
                                  -> Self
    {
        let mut printer = Self::from_heap_locs(machine_st, fmt, output, heap_locs);

        for (_, addr) in heap_locs.iter() {
            let addr = machine_st.store(machine_st.deref(addr.clone()));
            printer.printed_vars.insert(addr.clone());
        }

        printer
    }

    fn print_offset(&mut self, addr: Addr) {
        match addr {
            Addr::HeapCell(h) | Addr::Lis(h) | Addr::Str(h) =>
                self.outputter.append(format!("_{}", h).as_str()),
            Addr::StackCell(fr, sc) =>
                self.outputter.append(format!("s_{}_{}", fr, sc).as_str()),
            _ => {}
        }
    }

    // returns a HeapCellValue iff the next element to come hasn't been seen previously.
    fn check_for_seen(&mut self, iter: &mut HCPreOrderIterator) -> Option<HeapCellValue> {
        iter.stack().last().cloned().and_then(|addr| {
            let addr = self.machine_st.store(self.machine_st.deref(addr));

            for (var, var_addr) in self.heap_locs.iter() {
                if &addr == &self.machine_st.store(self.machine_st.deref(var_addr.clone())) {
                    if !self.printed_vars.contains(&addr) {
                        self.printed_vars.insert(addr);
                        return iter.next();
                    } else {
                        iter.stack().pop();
                        self.outputter.append(var.as_str());

                        return None;
                    }
                }
            }

            if self.machine_st.is_cyclic_term(addr.clone()) {
                if self.printed_vars.contains(&addr) {
                    iter.stack().pop();
                    self.print_offset(addr);
                    
                    None
                } else {
                    self.printed_vars.insert(addr);
                    iter.next()
                }
            } else {
                iter.next()
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

    //TODO: idea: hand a mutable ref to iter to handle_heap_term,
    // and have it query the stack before getting the next thing.
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
