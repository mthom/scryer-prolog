use prolog::ast::*;
use prolog::num::*;
use prolog::heap_iter::*;
use prolog::machine::machine_state::MachineState;
use prolog::ordered_float::OrderedFloat;

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::rc::Rc;

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(ClauseName),
    Op(ClauseName),
    NumberedVar(String),    
    Redirect,
    Open,
    Close,
    Comma,
    OpenList(Rc<Cell<bool>>),
    CloseList(Rc<Cell<bool>>),
    HeadTailSeparator,
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
    fn format_clause(&self, &mut HCPreOrderIterator, usize, ClauseType, &mut Vec<TokenOrRedirect>);
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

// the 'classic' display corresponding to the display predicate.
pub struct WriteqFormatter {}

fn is_numbered_var(ct: &ClauseType, arity: usize) -> bool {
    arity == 1 && if let &ClauseType::Named(ref name, _) = ct {
        name.as_str() == "$VAR"
    } else {
        false
    }
}

fn print_op(ct: ClauseType, fixity: Fixity, state_stack: &mut Vec<TokenOrRedirect>) {
    match fixity {
        Fixity::Post => {
            state_stack.push(TokenOrRedirect::Op(ct.name()));
            state_stack.push(TokenOrRedirect::Redirect);
        },
        Fixity::Pre => {
            state_stack.push(TokenOrRedirect::Redirect);
            state_stack.push(TokenOrRedirect::Op(ct.name()));
        },
        Fixity::In => {
            state_stack.push(TokenOrRedirect::Redirect);
            state_stack.push(TokenOrRedirect::Op(ct.name()));
            state_stack.push(TokenOrRedirect::Redirect);
        }
    }    
}

impl HCValueFormatter for WriteqFormatter {
    fn format_clause(&self, iter: &mut HCPreOrderIterator, arity: usize,
                     ct: ClauseType, state_stack: &mut Vec<TokenOrRedirect>)
    {
        static CHAR_CODES: [char; 26] = ['A','B','C','D','E','F','G','H','I','J',
                                         'K','L','M','N','O','P','Q','R','S','T',
                                         'U','V','W','X','Y','Z'];

        if let Some(fixity) = ct.fixity() {
            return print_op(ct, fixity, state_stack);
        } else if is_numbered_var(&ct, arity) {
            let addr = iter.stack().last().cloned().unwrap();

            // 7.10.4
            match iter.machine_st.store(iter.machine_st.deref(addr)) {
                Addr::Con(Constant::Number(Number::Integer(ref n))) if !n.is_negative() => {
                    iter.stack().pop();
                    
                    let i = n.mod_floor(&BigInt::from(26)).to_usize().unwrap();
                    let j = n.div_floor(&BigInt::from(26));

                    let mut result = if j.is_zero() {
                        CHAR_CODES[i].to_string()
                    } else {
                        format!("{}{}", CHAR_CODES[i], j)
                    };
                    
                    state_stack.push(TokenOrRedirect::NumberedVar(result));
                    
                    return;
                }
                _ => {}
            };           
        }
        
        self.format_struct(arity, ct.name(), state_stack);        
    }
}

pub struct TermFormatter {}

impl HCValueFormatter for TermFormatter {
    fn format_clause(&self, _: &mut HCPreOrderIterator, arity: usize, ct: ClauseType,
                     state_stack: &mut Vec<TokenOrRedirect>)
    {
        if let Some(fixity) = ct.fixity() {
            print_op(ct, fixity, state_stack);
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
    
    fn print_atom(&mut self, atom: &ClauseName, is_op: bool) {
        match atom.as_str() {
            "" => self.outputter.append("''"),
            ";" | "!" => self.outputter.append(atom.as_str()),
            s => if is_op || non_quoted_token(s.chars()) {
                self.outputter.append(atom.as_str());
            } else {
                self.outputter.push_char('\'');

                for c in atom.as_str().chars() {
                    self.print_char(c);
                }
                
                self.outputter.push_char('\'');
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
            _ => self.outputter.push_char(c)
        };
    }
    
    fn print_constant(&mut self, c: Constant) {
        match c {            
            Constant::Atom(ref atom) =>
                self.print_atom(atom, false),
            Constant::Char(c) if non_quoted_token(once(c)) =>
                self.print_char(c),
            Constant::Char(c) => {
                self.outputter.push_char('\'');
                self.print_char(c);
                self.outputter.push_char('\'');
            },
            Constant::EmptyList =>
                self.outputter.append("[]"),
            Constant::Number(Number::Float(fl)) =>
                if &fl == &OrderedFloat(0f64) {
                    self.outputter.append("0");
                } else {
                    self.outputter.append(&format!("{}", fl));
                },
            Constant::Number(n) =>
                self.outputter.append(&format!("{}", n)),
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
    
    fn handle_heap_term(&mut self, iter: &mut HCPreOrderIterator)
    {
        let heap_val = match self.check_for_seen(iter) {
            Some(heap_val) => heap_val,
            _ => return
        };

        match heap_val {
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let ct = ClauseType::from(name, arity, fixity);
                self.formatter.format_clause(iter, arity, ct, &mut self.state_stack)
            },
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) =>
                if !self.at_cdr("") {
                    self.outputter.append("[]");
                },
            HeapCellValue::Addr(Addr::Con(c)) =>
                self.print_constant(c),
            HeapCellValue::Addr(Addr::Lis(_)) =>
                self.push_list(),
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
                    TokenOrRedirect::Atom(atom) =>
                        self.print_atom(&atom, false),
                    TokenOrRedirect::Op(atom) =>
                        self.print_atom(&atom, true),
                    TokenOrRedirect::NumberedVar(num_var) =>
                        self.outputter.append(num_var.as_str()),
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
