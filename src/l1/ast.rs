use std::cell::Cell;
use std::fmt;
use std::vec::Vec;

pub type Var = String;

pub type Atom = String;

pub enum TopLevel {
    Fact(Term),
    Query(Term)
}

#[derive(Clone, Copy)]
pub enum Level {
    Shallow, Deep
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Level::Shallow => write!(f, "A"),
            &Level::Deep => write!(f, "X")
        }
    }
}

#[derive(Clone, Copy)]
pub enum Reg {
    ArgAndNorm(usize, usize),
    Norm(usize)
}

impl Reg {
    pub fn has_arg(&self) -> bool {
        match self {
            &Reg::ArgAndNorm(_, _) => true,
            _ => false
        }
    }

    pub fn norm(&self) -> usize {
        match self {
            &Reg::ArgAndNorm(_, norm) | &Reg::Norm(norm) => norm
        }
    }
}

pub enum Term {
    Atom(Cell<usize>, Atom),
    Clause(Cell<usize>, Atom, Vec<Box<Term>>),
    Var(Cell<Reg>, Var)
}

pub enum TermRef<'a> {
    Atom(Level, &'a Cell<usize>, &'a Atom),
    Clause(Level, &'a Cell<usize>, &'a Atom, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<Reg>, &'a Var)
}

#[derive(Clone)]
pub enum FactInstruction {
    GetStructure(Level, Atom, usize, usize),
    GetValue(usize, usize),
    GetVariable(usize, usize),
    Proceed,
    UnifyVariable(usize),
    UnifyValue(usize)
}

pub enum QueryInstruction {
    Call(Atom, usize),
    PutStructure(Level, Atom, usize, usize),
    PutValue(usize, usize),
    PutVariable(usize, usize),
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

#[derive(Clone)]
pub enum HeapCellValue {
    NamedStr(usize, Atom),
    Ref(usize),
    Str(usize),
}

pub type Heap = Vec<HeapCellValue>;

pub type Registers = Vec<HeapCellValue>;

impl Term {
    pub fn subterms(&self) -> usize {
        match self {
            &Term::Clause(_, _, ref terms) => terms.len(),
            _ => 1
        }
    }

    pub fn name(&self) -> &Atom {
        match self {
            &Term::Atom(_, ref atom)
            | &Term::Var(_, ref atom)
            | &Term::Clause(_, ref atom, _) => atom
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &Term::Atom(_, _) | &Term::Var(_, _) => 0,
            &Term::Clause(_, _, ref child_terms) => child_terms.len()
        }
    }
}
