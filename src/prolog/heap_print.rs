use prolog::ast::*;
use prolog::builtins::*;
use prolog::heap_iter::*;

use std::cell::Cell;
use std::rc::Rc;

#[derive(Clone)]
pub enum TokenOrRedirect {
    Atom(Rc<Atom>),
    Redirect,
    Open,
    Close,
    Comma,
    OpenList(Rc<Cell<bool>>),
    CloseList(Rc<Cell<bool>>),
    HeadTailSeparator,
    Space
}

pub trait HeapCellValueFormatter {
    // this function belongs to the display predicate formatter, which it uses
    // to format all clauses.
    fn format_struct(&self, arity: usize, name: Rc<Atom>, state_stack: &mut Vec<TokenOrRedirect>)
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
    fn format_clause(&self, arity: usize, name: Rc<Atom>, state_stack: &mut Vec<TokenOrRedirect>);
}

// the 'classic' display corresponding to the display predicate.
pub struct DisplayFormatter {}

impl HeapCellValueFormatter for DisplayFormatter {
    fn format_clause(&self, arity: usize, name: Rc<Atom>, state_stack: &mut Vec<TokenOrRedirect>)
    {
        self.format_struct(arity, name, state_stack);
    }
}

pub struct TermFormatter<'a> {
    op_dir: &'a OpDir
}

impl<'a> TermFormatter<'a> {
    pub fn new(op_dir: &'a OpDir) -> Self {
        TermFormatter { op_dir }
    }        
}

impl<'a> HeapCellValueFormatter for TermFormatter<'a> {
    fn format_clause(&self, arity: usize, name: Rc<Atom>, state_stack: &mut Vec<TokenOrRedirect>) {
        if arity == 1 {
            match self.op_dir.get(&(name.clone(), Fixity::Post)) {
                Some(_) => {
                    state_stack.push(TokenOrRedirect::Atom(name));
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Redirect);
                },
                None => match self.op_dir.get(&(name.clone(), Fixity::Pre)) {
                    Some(_) => {
                        state_stack.push(TokenOrRedirect::Redirect);
                        state_stack.push(TokenOrRedirect::Space);
                        state_stack.push(TokenOrRedirect::Atom(name));
                    },
                    None => self.format_struct(arity, name, state_stack)
                }
            }
        } else if arity == 2 {
            match self.op_dir.get(&(name.clone(), Fixity::In)) {
                Some(_) => {
                    state_stack.push(TokenOrRedirect::Redirect);
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Atom(name));
                    state_stack.push(TokenOrRedirect::Space);
                    state_stack.push(TokenOrRedirect::Redirect);
                },
                None => self.format_struct(arity, name, state_stack)
            };
        } else {
            self.format_struct(arity, name, state_stack);
        }
    }
}

pub struct HeapCellPrinter<'a, Formatter> {
    formatter:   Formatter,
    iter:        HeapCellIterator<'a>,
    state_stack: Vec<TokenOrRedirect>
}

impl<'a, Formatter: HeapCellValueFormatter> HeapCellPrinter<'a, Formatter>
{
    pub fn new(iter: HeapCellIterator<'a>, formatter: Formatter) -> Self {
        HeapCellPrinter { formatter, iter, state_stack: vec![] }
    }

    fn handle_heap_term(&mut self, heap_val: HeapCellValue, result: &mut String) {
        match heap_val {
            HeapCellValue::NamedStr(arity, name) =>
                self.formatter.format_clause(arity, name, &mut self.state_stack),
            HeapCellValue::Addr(Addr::Con(Constant::EmptyList)) =>
                if !Self::at_cdr(result, "") {
                    *result += "[]";
                },
            HeapCellValue::Addr(Addr::Con(c)) =>
                *result += format!("{}", c).as_str(),
            HeapCellValue::Addr(Addr::Lis(_)) => {
                let cell = Rc::new(Cell::new(true));

                self.state_stack.push(TokenOrRedirect::CloseList(cell.clone()));

                self.state_stack.push(TokenOrRedirect::Redirect);
                self.state_stack.push(TokenOrRedirect::HeadTailSeparator); // bar
                self.state_stack.push(TokenOrRedirect::Redirect);

                self.state_stack.push(TokenOrRedirect::OpenList(cell));
            },
            HeapCellValue::Addr(Addr::HeapCell(h)) =>
                *result += format!("_{}", h).as_str(),
            HeapCellValue::Addr(Addr::StackCell(fr, sc)) =>
                *result += format!("s_{}_{}", fr, sc).as_str(),
            HeapCellValue::Addr(Addr::Str(_)) => {}
        }
    }

    fn at_cdr(result: &mut String, tr: &str) -> bool {
        let len = result.len();

        if result.ends_with(" | ") {
            result.truncate(len - 3);
            *result += tr;
            true
        } else {
            false
        }
    }

    pub fn print(&mut self) -> String {
        let mut result = String::new();

        loop {
            if let Some(loc_data) = self.state_stack.pop() {
                match loc_data {
                    TokenOrRedirect::Space =>
                        result += " ",
                    TokenOrRedirect::Atom(atom) =>
                        result += atom.as_str(),
                    TokenOrRedirect::Redirect => {
                        let heap_val = self.iter.next().unwrap();
                        self.handle_heap_term(heap_val, &mut result);
                    },
                    TokenOrRedirect::Close =>
                        result += ")",
                    TokenOrRedirect::Open =>
                        result += "(",
                    TokenOrRedirect::OpenList(delimit) =>
                        if !Self::at_cdr(&mut result, ", ") {
                            result += "[";
                        } else {
                            delimit.set(false);
                        },
                    TokenOrRedirect::CloseList(delimit) =>
                        if delimit.get() == true {
                            result += "]";
                        },
                    TokenOrRedirect::HeadTailSeparator =>
                        result += " | ",
                    TokenOrRedirect::Comma =>
                        result += ", "
                }
            } else if let Some(heap_val) = self.iter.next() {
                self.handle_heap_term(heap_val, &mut result);
            } else {
                break;
            }
        }

        result
    }
}
