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
    Atom(Atom),
    Clause(Atom, Vec<Box<Term>>),
    Var(Var)
}

#[derive(Clone)]
pub enum MachineInstruction {
    GetStructure(Atom, usize, usize),
    PutStructure(Atom, usize, usize),
    SetVariable(usize),
    SetValue(usize),
    UnifyVariable(usize),
    UnifyValue(usize)
}

pub type Program = Vec<MachineInstruction>;

#[derive(Clone, Copy, PartialEq)]    
pub enum Addr {
    HeapCell(usize),
    RegNum(usize)
}

impl Addr {
    pub fn heap_offset(&self) -> usize {
        match self {
            &Addr::HeapCell(hc) => hc,
            &Addr::RegNum(reg)  => reg
        }
    }
}
