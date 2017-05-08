use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::ops::{Add, AddAssign};
use std::vec::Vec;

pub type Var = String;

pub type Atom = String;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum GenContext {
    Head, Mid(usize), Last(usize) // Mid & Last: chunk_num
}

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

    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &PredicateClause::Fact(ref t) => t.first_arg(),
            &PredicateClause::Rule(ref rule) => rule.head.0.first_arg()
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
    Query(Vec<TermOrCut>),
    Rule(Rule)
}

#[derive(Clone, Copy)]
pub enum Level {
    Deep, Shallow
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
}

impl Default for VarReg {
    fn default() -> Self {
        VarReg::Norm(RegType::default())
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
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

pub enum TermOrCut {
    Cut,
    Term(Term)
}

impl TermOrCut {
    pub fn arity(&self) -> usize {
        match self {
            &TermOrCut::Term(ref term) => term.arity(),
            _ => 0
        }
    }
}

pub struct Rule {
    pub head: (Term, TermOrCut),
    pub clauses: Vec<TermOrCut>
}

impl Rule {
    pub fn last_clause(&self) -> &TermOrCut {
        match self.clauses.last() {
            None => &self.head.1,
            Some(clause) => clause
        }
    }
}

#[derive(Clone, Copy)]
pub enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(Level, &'a Cell<RegType>, &'a Atom, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> TermRef<'a> {
    pub fn level(self) -> Level {
        match self {
            TermRef::AnonVar(lvl)
          | TermRef::Cons(lvl, _, _, _)
          | TermRef::Constant(lvl, _, _)
          | TermRef::Clause(lvl, _, _, _)
          | TermRef::Var(lvl, _, _) => lvl
        }
    }
}

pub enum TermOrCutRef<'a> {
    Cut, Term(&'a Term)
}

pub enum ChoiceInstruction {
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

pub enum Terminal {
    Terminal, Non
}

pub enum CutInstruction {
    Cut(Terminal),
    GetLevel,
    NeckCut(Terminal)
}

pub enum IndexedChoiceInstruction {
    Retry(usize),
    Trust(usize),
    Try(usize)
}

impl From<IndexedChoiceInstruction> for Line {
    fn from(i: IndexedChoiceInstruction) -> Self {
        Line::IndexedChoice(i)
    }
}

impl IndexedChoiceInstruction {
    pub fn offset(&self) -> usize {
        match self {
            &IndexedChoiceInstruction::Retry(offset) => offset,
            &IndexedChoiceInstruction::Trust(offset) => offset,
            &IndexedChoiceInstruction::Try(offset)   => offset
        }
    }
}

pub enum ControlInstruction {
    Allocate(usize),
    Call(Atom, usize, usize),
    Deallocate,
    Execute(Atom, usize),
    Proceed
}

impl ControlInstruction {
    pub fn is_jump_instr(&self) -> bool {
        match self {
            &ControlInstruction::Call(_, _, _) => true,
            &ControlInstruction::Execute(_, _) => true,
            _ => false
        }
    }
}

pub enum IndexingInstruction {
    SwitchOnTerm(usize, usize, usize, usize),
    SwitchOnConstant(usize, HashMap<Constant, usize>),
    SwitchOnStructure(usize, HashMap<(Atom, usize), usize>)
}

impl From<IndexingInstruction> for Line {
    fn from(i: IndexingInstruction) -> Self {
        Line::Indexing(i)
    }
}

pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetStructure(Level, Atom, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),
    UnifyConstant(Constant),
    UnifyLocalValue(RegType),
    UnifyVariable(RegType),
    UnifyValue(RegType),
    UnifyVoid(usize)
}

pub enum QueryInstruction {
    GetVariable(RegType, usize),
    PutConstant(Level, Constant, RegType),
    PutList(Level, RegType),
    PutStructure(Level, Atom, usize, RegType),
    PutUnsafeValue(usize, usize),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetConstant(Constant),
    SetLocalValue(RegType),
    SetVariable(RegType),
    SetValue(RegType),
    SetVoid(usize)
}

pub type CompiledFact = Vec<FactInstruction>;

pub type CompiledQuery = Vec<QueryInstruction>;

pub enum Line {
    Choice(ChoiceInstruction),
    Control(ControlInstruction),
    Cut(CutInstruction),
    Fact(CompiledFact),
    Indexing(IndexingInstruction),
    IndexedChoice(IndexedChoiceInstruction),
    Query(CompiledQuery)
}

pub type ThirdLevelIndex = Vec<IndexedChoiceInstruction>;

pub type Code = Vec<Line>;

pub type CodeDeque = VecDeque<Line>;

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

    pub fn is_protected(&self, e: usize) -> bool {
        match self {
            &Addr::StackCell(fr, _) if fr > e => false,
            _ => true
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

#[derive(Clone, Copy, PartialEq)]
pub enum CodePtr {
    DirEntry(usize),
    TopLevel(usize, usize) // chunk_num, offset.
}

impl PartialOrd<CodePtr> for CodePtr {
    fn partial_cmp(&self, other: &CodePtr) -> Option<Ordering> {
        match (self, other) {
            (&CodePtr::DirEntry(p1), &CodePtr::DirEntry(ref p2)) =>
                p1.partial_cmp(p2),
            (&CodePtr::DirEntry(_), &CodePtr::TopLevel(_, _)) =>
                Some(Ordering::Less),
            (&CodePtr::TopLevel(_, p1), &CodePtr::TopLevel(_, ref p2)) =>
                p1.partial_cmp(p2),
            _ => Some(Ordering::Greater)
        }
    }
}

impl Default for CodePtr {
    fn default() -> Self {
        CodePtr::TopLevel(0, 0)
    }
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            CodePtr::DirEntry(p) => CodePtr::DirEntry(p + rhs),
            CodePtr::TopLevel(cn, p) => CodePtr::TopLevel(cn, p + rhs)
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::DirEntry(ref mut p) |
            &mut CodePtr::TopLevel(_, ref mut p) => *p += rhs
        }
    }
}

pub type Heap = Vec<HeapCellValue>;

pub type Registers = Vec<Addr>;

impl Term {
    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &Term::Clause(_, _, ref terms) =>
                terms.first().map(|bt| bt.as_ref()),
            _ => None
        }
    }

    pub fn is_clause(&self) -> bool {
        if let &Term::Clause(_, _, _) = self {
            true
        } else {
            false
        }
    }

    pub fn is_callable(&self) -> bool {
        match self {
            &Term::Clause(_, _, _) | &Term::Constant(_, Constant::Atom(_)) =>
                true,
            _ => false
        }
    }

    pub fn subterms(&self) -> usize {
        match self {
            &Term::Clause(_, _, ref terms) => terms.len(),
            _ => 1
        }
    }

    pub fn name(&self) -> Option<&Atom> {
        match self {
            &Term::Constant(_, Constant::Atom(ref atom))
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
