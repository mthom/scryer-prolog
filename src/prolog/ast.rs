use std::cell::Cell;
use std::collections::HashMap;
use std::ops::{Add, AddAssign};
use std::vec::Vec;

pub type Var = String;

pub type Atom = String;

pub enum PredicateClause {
    Fact(Term),
    Rule(Rule)
}

impl PredicateClause {
    pub fn name(&self) -> &Atom {
        match self {
            &PredicateClause::Fact(ref t) => t.name().unwrap(),
            &PredicateClause::Rule(ref rule) => rule.head.0.name().unwrap()
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref t) => t.arity(),
            &PredicateClause::Rule(ref rule) => rule.head.0.arity()
        }
    }
}

pub enum TopLevel {
    Fact(Term),
    Predicate(Vec<PredicateClause>),
    Query(Term),
    Rule(Rule)
}

#[derive(Clone, Copy)]
pub enum Level {
    Deep, Shallow
}

#[derive(Clone, Copy)]
pub enum RegType {
    Perm(usize),
    Temp(usize)
}

impl Default for RegType {
    fn default() -> Self {
        RegType::Temp(0)
    }
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

    pub fn is_temp(self) -> bool {
        !self.norm().is_perm()
    }
    
    pub fn root_register(self) -> usize {
        match self {
            VarReg::ArgAndNorm(_, root) => root,
            VarReg::Norm(root) => root.reg_num()
        }
    }
}

impl Default for VarReg {
    fn default() -> Self {
        VarReg::Norm(RegType::default())
    }
}

#[derive(Clone, PartialEq)]
pub enum Constant {
    Atom(Atom),
    EmptyList
}

pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, Atom, Vec<Box<Term>>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Constant(Cell<RegType>, Constant),
    Var(Cell<VarReg>, Var)
}

pub struct Rule {
    pub head: (Term, Term),
    pub clauses: Vec<Term>
}

impl Rule {
    pub fn last_clause(&self) -> &Term {
        match self.clauses.last() {
            None => &self.head.1,
            Some(clause) => clause
        }
    }
}

pub enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(Level, &'a Cell<RegType>, &'a Atom, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetStructure(Level, Atom, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),    
    UnifyConstant(Constant),
    UnifyVariable(RegType),
    UnifyValue(RegType),
    UnifyVoid(usize)
}

pub enum QueryInstruction {
    PutConstant(Level, Constant, RegType),
    PutList(Level, RegType),
    PutStructure(Level, Atom, usize, RegType),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetConstant(Constant),
    SetVariable(RegType),
    SetValue(RegType),
    SetVoid(usize)
}

pub enum ChoiceInstruction {
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

pub enum ControlInstruction {
    Allocate(usize),
    Call(Atom, usize, usize),
    Deallocate,
    Execute(Atom, usize),
    Proceed
}

pub type CompiledFact = Vec<FactInstruction>;

pub type CompiledQuery = Vec<QueryInstruction>;

pub enum Line {
    Choice(ChoiceInstruction),
    Control(ControlInstruction),
    Fact(CompiledFact),
    Query(CompiledQuery)
}

pub enum LineOrCodeOffset<'a> {
    Instruction(&'a Line),
    Offset(usize)
}

impl<'a> From<&'a Line> for LineOrCodeOffset<'a> {
    fn from(line: &'a Line) -> Self {
        LineOrCodeOffset::Instruction(line)
    }
}

pub type Code = Vec<Line>;

#[derive(Clone, PartialEq)]
pub enum Addr {
    Con(Constant),
    Lis(usize),
    HeapCell(usize),
    StackCell(usize, usize),
    Str(usize)
}

impl Addr {
    pub fn is_ref(&self) -> bool {
        match self {
            &Addr::HeapCell(_) | &Addr::StackCell(_, _) => true,
            _ => false
        }
    }

    pub fn as_ref(&self) -> Option<Ref> {
        match self {
            &Addr::HeapCell(hc) => Some(Ref::HeapCell(hc)),
            &Addr::StackCell(fr, sc) => Some(Ref::StackCell(fr, sc)),
            _ => None
        }
    }
}

impl From<Ref> for Addr {
    fn from(r: Ref) -> Self {
        match r {
            Ref::HeapCell(hc) => Addr::HeapCell(hc),
            Ref::StackCell(fr, sc) => Addr::StackCell(fr, sc)
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum Ref {
    HeapCell(usize),
    StackCell(usize, usize)
}

#[derive(Clone, PartialEq)]
pub enum HeapCellValue {
    Con(Constant),
    Lis(usize),
    NamedStr(usize, Atom),
    Ref(Ref),
    Str(usize)
}

impl From<Addr> for HeapCellValue {
    fn from(addr: Addr) -> HeapCellValue {
        match addr {
            Addr::Con(constant) =>
                HeapCellValue::Con(constant),
            Addr::HeapCell(hc) =>
                HeapCellValue::Ref(Ref::HeapCell(hc)),
            Addr::Lis(a) =>
                HeapCellValue::Lis(a),
            Addr::StackCell(fr, sc) =>
                HeapCellValue::Ref(Ref::StackCell(fr, sc)),
            Addr::Str(hc) =>
                HeapCellValue::Str(hc)
        }
    }
}

impl HeapCellValue {
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            &HeapCellValue::Con(ref c) => Addr::Con(c.clone()),
            &HeapCellValue::Lis(a) => Addr::Lis(a),
            &HeapCellValue::Ref(r) => Addr::from(r),
            &HeapCellValue::Str(s) => Addr::Str(s),
            &HeapCellValue::NamedStr(_, _) => Addr::Str(focus)
        }
    }
}

#[derive(Clone, Copy)]
pub enum CodePtr {
    DirEntry(usize),
    TopLevel
}

impl Default for CodePtr {
    fn default() -> Self {
        CodePtr::TopLevel
    }
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

pub type Registers = Vec<Addr>;

impl Term {
    pub fn subterms(&self) -> usize {
        match self {
            &Term::Clause(_, _, ref terms) => terms.len(),
            _ => 1
        }
    }

    pub fn name(&self) -> Option<&Atom> {
        match self {
            &Term::Constant(_, Constant::Atom(ref atom))
            | &Term::Var(_, ref atom)
            | &Term::Clause(_, ref atom, _) => Some(atom),
            _ => None
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &Term::Clause(_, _, ref child_terms) => child_terms.len(),
            _ => 0
        }
    }
}

pub type HeapVarDict = HashMap<Var, Addr>;

pub enum EvalResult {
    EntryFailure,
    EntrySuccess,
    InitialQuerySuccess(HeapVarDict),
    QueryFailure,
    SubsequentQuerySuccess,
}

impl EvalResult {
    #[allow(dead_code)]
    pub fn failed_query(&self) -> bool {
        if let &EvalResult::QueryFailure = self {
            true
        } else {
            false
        }
    }
}
