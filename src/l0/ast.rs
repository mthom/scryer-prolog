use std::cell::{Cell};
use std::vec::{Vec};

pub type Var = String;

pub type Atom = String;

#[derive(Debug)]
pub enum TopLevel {
    Fact(Term),
    Query(Term)
}

#[derive(Debug)]
pub enum Term {
    Atom(Cell<usize>, Atom),
    Clause(Cell<usize>, Atom, Vec<Box<Term>>),
    Var(Cell<usize>, Var)
}

pub enum FactInstruction {
    GetStructure(Atom, usize, usize),
    UnifyVariable(usize),
    UnifyValue(usize)
}

pub enum QueryInstruction {    
    PutStructure(Atom, usize, usize),
    SetVariable(usize),
    SetValue(usize),    
}

pub type CompiledFact = Vec<FactInstruction>;

pub type CompiledQuery = Vec<QueryInstruction>;

#[derive(Clone, Copy, PartialEq)]
pub enum Addr {
    HeapCell(usize),
    RegNum(usize)
}

impl Term {
    pub fn set_cell(&self, cell_num: usize) {
        match self {
            &Term::Atom(ref cell, _) => cell.set(cell_num),
            &Term::Clause(ref cell, _, _) => cell.set(cell_num),
            &Term::Var(ref cell, _) => cell.set(cell_num)
        };
    }
}
