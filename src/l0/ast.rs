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

impl Term {
    pub fn name(&self) -> &Atom {
        match self {
            &Term::Atom(ref atom) => atom,
            &Term::Var(ref var)   => var,
            &Term::Clause(ref atom, _) => atom
        }
    }

    pub fn is_variable(&self) -> bool {
        if let &Term::Var(_) = self {
            return true;
        }

        return false;
    }
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
