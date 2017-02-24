use std::cell::Cell;
use std::fmt;
use std::ops::{Add, AddAssign};
use std::vec::Vec;

pub type Var = String;

pub type Atom = String;

pub enum TopLevel {
    Fact(Term),
    Rule(Rule),
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
pub enum RegType {
    Perm(usize),
    Temp(usize)
}

impl RegType {
    pub fn reg_num(self) -> usize {
        match self {
            RegType::Perm(reg_num) | RegType::Temp(reg_num) => reg_num
        }
    }

    pub fn is_perm(self) -> bool {
        match self {
            RegType::Perm(_) => true,
            _ => false
        }
    }
}

impl fmt::Display for VarReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VarReg::Norm(RegType::Perm(reg)) => write!(f, "Y{}", reg),
            &VarReg::Norm(RegType::Temp(reg)) => write!(f, "X{}", reg),
            &VarReg::ArgAndNorm(RegType::Perm(reg), arg) =>
                write!(f, "Y{} A{}", reg, arg),
            &VarReg::ArgAndNorm(RegType::Temp(reg), arg) =>
                write!(f, "X{} A{}", reg, arg)
        }
    }
}

impl From<RegType> for Addr {
    fn from(reg: RegType) -> Addr {
        match reg {
            RegType::Perm(reg) => Addr::StackCell(reg),
            RegType::Temp(reg) => Addr::RegNum(reg)
        }
    }
}

impl fmt::Display for RegType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RegType::Perm(val) => write!(f, "Y{}", val),
            &RegType::Temp(val) => write!(f, "X{}", val)
        }
    }
}

#[derive(Clone, Copy)]
pub enum VarReg {
    ArgAndNorm(RegType, usize),
    Norm(RegType)
}

impl VarReg {
    pub fn norm(self) -> RegType {
        match self {
            VarReg::ArgAndNorm(reg, _) | VarReg::Norm(reg) => reg
        }
    }

    pub fn root_register(self) -> usize {
        match self {
            VarReg::ArgAndNorm(_, root) => root,
            VarReg::Norm(root) => root.reg_num()
        }
    }
}

pub enum Term {
    Atom(Cell<RegType>, Atom),
    Clause(Cell<RegType>, Atom, Vec<Box<Term>>),
    Var(Cell<VarReg>, Var)
}

pub struct Rule {
    pub head: (Term, Term),
    pub clauses: Vec<Term>
}

pub enum TermRef<'a> {
    Atom(Level, &'a Cell<RegType>, &'a Atom),
    Clause(Level, &'a Cell<RegType>, &'a Atom, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

pub enum FactInstruction {
    GetStructure(Level, Atom, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),
    UnifyVariable(RegType),
    UnifyValue(RegType)
}

pub enum QueryInstruction {
    PutStructure(Level, Atom, usize, RegType),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetVariable(RegType),
    SetValue(RegType)
}

pub enum ControlInstruction {
    Allocate(usize),
    Call(Atom, usize),
    Deallocate,
    Proceed
}

pub type CompiledFact = Vec<FactInstruction>;

pub type CompiledQuery = Vec<QueryInstruction>;

pub enum Line {
    Control(ControlInstruction),    
    Fact(CompiledFact),
    Query(CompiledQuery)
}

pub type Code = Vec<Line>;

#[derive(Clone, Copy, PartialEq)]
pub enum Addr {
    HeapCell(usize),
    RegNum(usize),
    StackCell(usize),
}

#[derive(Clone, PartialEq)]
pub enum HeapCellValue {
    NamedStr(usize, Atom),
    Ref(usize),
    Str(usize)
}

impl HeapCellValue {
    pub fn as_ref(&self, focus: usize) -> HeapCellRef {
        match self {
            &HeapCellValue::Ref(r) => HeapCellRef::Ref(r),
            &HeapCellValue::Str(s) => HeapCellRef::Str(s),
            &HeapCellValue::NamedStr(_, _) => HeapCellRef::Str(focus)
        }
    }
}

#[derive(Copy, Clone)]
pub enum HeapCellRef {
    Ref(usize),
    Str(usize)
}

impl HeapCellRef {
    pub fn heap_offset(&self) -> usize {
        match self {
            &HeapCellRef::Ref(r) | &HeapCellRef::Str(r) => r
        }
    }        
}

impl From<HeapCellRef> for HeapCellValue {
    fn from(hcr: HeapCellRef) -> HeapCellValue {
        match hcr {
            HeapCellRef::Ref(r) => HeapCellValue::Ref(r),
            HeapCellRef::Str(s) => HeapCellValue::Str(s)
        }
    }
}

#[derive(Clone, Copy)]
pub enum CodePtr {
    DirEntry(usize),
    TopLevel
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;
    fn add(self, rhs: usize) -> Self::Output {
        match self {
            CodePtr::DirEntry(p) => CodePtr::DirEntry(p + rhs),
            CodePtr::TopLevel => CodePtr::TopLevel
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::DirEntry(ref mut p) => *p += rhs,
            _ => {}
        }
    }
}

pub type Heap = Vec<HeapCellValue>;

pub type Registers = Vec<HeapCellRef>;

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
