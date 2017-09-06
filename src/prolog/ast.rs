use prolog::num::bigint::BigInt;

use prolog::ordered_float::*;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::io::Error as IOError;
use std::num::{ParseFloatError};
use std::ops::{Add, AddAssign};
use std::str::Utf8Error;
use std::vec::Vec;

pub type Atom = String;

pub type Var = String;

pub const LEXER_BUF_SIZE: usize = 4096;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum GenContext {
    Head, Mid(usize), Last(usize) // Mid & Last: chunk_num
}

impl GenContext {
    pub fn chunk_num(self) -> usize {
        match self {
            GenContext::Head => 0,
            GenContext::Mid(cn) | GenContext::Last(cn) => cn
        }
    }
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
    Query(Vec<QueryTerm>),
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

pub type Specifier = u32;

pub const XFX: u32 = 0x0001;
pub const XFY: u32 = 0x0002;
pub const YFX: u32 = 0x0004;
pub const XF: u32  = 0x0010;
pub const YF: u32  = 0x0020;
pub const FX: u32  = 0x0040;
pub const FY: u32  = 0x0080;
pub const DELIMITER: u32 = 0x0100;
pub const TERM: u32  = 0x1000;
pub const LTERM: u32 = 0x3000;

macro_rules! is_term {
    ($x:expr) => ( ($x & TERM) != 0 )
}

macro_rules! is_lterm {
    ($x:expr) => ( ($x & LTERM) != 0 )
}

macro_rules! is_op {
    ($x:expr) => ( $x & (XF | YF | FX | FY | XFX | XFY | YFX) != 0 )
}

macro_rules! is_infix {
    ($x:expr) => ( ($x & (XFX | XFY | YFX)) != 0 )
}

macro_rules! is_xfx {
    ($x:expr) => ( ($x & XFX) != 0 )
}

macro_rules! is_xfy {
    ($x:expr) => ( ($x & XFY) != 0 )
}

macro_rules! is_yfx {
    ($x:expr) => ( ($x & YFX) != 0 )
}

macro_rules! is_yf {
    ($x:expr) => ( ($x & YF) != 0 )
}

macro_rules! is_xf {
    ($x:expr) => ( ($x & XF) != 0 )
}

macro_rules! is_fx {
    ($x:expr) => ( ($x & FX) != 0 )
}

macro_rules! is_fy {
    ($x:expr) => ( ($x & FY) != 0 )
}

macro_rules! prefix {
    ($x:expr) => ($x & (FX | FY))
}

/* 'TokenTooLong' is hard to detect reliably if we don't process the
input one character at a time. It would be easy to detect if the regex
library supported matching on iterator inputs, but it currently does
not. This is fine, mostly; the typical Prolog program will not contain
tokens exceeding 4096 chars in length. */

#[derive(Debug)]
pub enum ParserError
{
    CommaArityMismatch,
    UnexpectedEOF,
    FailedMatch(String),
    IO(IOError),
    InadmissibleFact,
    InadmissibleQueryTerm,
    IncompleteReduction,
    InconsistentPredicate,
    ParseBigInt,
    ParseFloat(ParseFloatError),
    // TokenTooLong,
    Utf8Conversion(Utf8Error)
}

impl From<IOError> for ParserError {
    fn from(err: IOError) -> ParserError {
        ParserError::IO(err)
    }
}

impl From<Utf8Error> for ParserError {
    fn from(err: Utf8Error) -> ParserError {
        ParserError::Utf8Conversion(err)
    }
}

impl From<ParseFloatError> for ParserError {
    fn from(err: ParseFloatError) -> ParserError {
        ParserError::ParseFloat(err)
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub enum Fixity {
    In, Post, Pre
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Constant {
    Atom(Atom),
    Float(OrderedFloat<f64>),
    Integer(BigInt),
    String(String),
    Usize(usize),
    EmptyList
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Constant::Atom(ref atom) =>
                write!(f, "{}", atom),
            &Constant::EmptyList =>
                write!(f, "[]"),
            &Constant::Float(fl) =>
                write!(f, "{}", fl),
            &Constant::Integer(ref i) =>
                write!(f, "{}", i),
            &Constant::String(ref s) =>
                write!(f, "{}", s),
            &Constant::Usize(integer) =>
                write!(f, "u{}", integer)
        }
    }
}

pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, Atom, Vec<Box<Term>>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Constant(Cell<RegType>, Constant),
    Var(Cell<VarReg>, Var)
}

pub enum QueryTerm {
    CallN(Vec<Box<Term>>),
    Catch(Vec<Box<Term>>),
    Cut,
    Term(Term),
    Throw(Vec<Box<Term>>)
}

impl QueryTerm {
    pub fn to_ref(&self) -> QueryTermRef {
        match self {
            &QueryTerm::CallN(ref terms) =>
                QueryTermRef::CallN(terms),
            &QueryTerm::Catch(ref terms) =>
                QueryTermRef::Catch(terms),
            &QueryTerm::Cut =>
                QueryTermRef::Cut,
            &QueryTerm::Term(ref term) =>
                QueryTermRef::Term(term),
            &QueryTerm::Throw(ref t) =>
                QueryTermRef::Throw(t)
        }
    }
}

pub struct Rule {
    pub head: (Term, QueryTerm),
    pub clauses: Vec<QueryTerm>
}

#[derive(Clone, Copy)]
pub enum ClauseType<'a> {
    CallN,
    Catch,
    Deep(Level, &'a Cell<RegType>, &'a Atom),
    Root,
    Throw,
}

impl<'a> ClauseType<'a> {
    pub fn level_of_subterms(self) -> Level {
        match self {
            ClauseType::CallN | ClauseType::Catch | ClauseType::Throw => Level::Shallow,
            ClauseType::Deep(_, _, _) => Level::Deep,
            ClauseType::Root => Level::Shallow,
        }
    }
}

#[derive(Clone, Copy)]
pub enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(ClauseType<'a>, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> TermRef<'a> {
    pub fn level(self) -> Level {
        match self {
            TermRef::AnonVar(lvl)
          | TermRef::Cons(lvl, _, _, _)
          | TermRef::Constant(lvl, _, _)
          | TermRef::Var(lvl, _, _) => lvl,
            TermRef::Clause(ClauseType::Root, _) => Level::Shallow,
            TermRef::Clause(ClauseType::Deep(lvl, _, _), _) => lvl,
            TermRef::Clause(ClauseType::CallN, _) => Level::Shallow,
            TermRef::Clause(ClauseType::Throw, _) => Level::Shallow,
            TermRef::Clause(ClauseType::Catch, _) => Level::Shallow
        }
    }
}

#[derive(Clone, Copy)]
pub enum QueryTermRef<'a> {
    CallN(&'a Vec<Box<Term>>),
    Catch(&'a Vec<Box<Term>>),
    Cut,
    Term(&'a Term),
    Throw(&'a Vec<Box<Term>>)
}

impl<'a> QueryTermRef<'a> {
    pub fn arity(self) -> usize {
        match self {
            QueryTermRef::Catch(_) => 3,
            QueryTermRef::Throw(_) => 1,
            QueryTermRef::CallN(terms) => terms.len(),
            QueryTermRef::Cut => 0,
            QueryTermRef::Term(term) => term.arity(),
        }
    }
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

pub enum BuiltInInstruction {
    CleanUpBlock,
    DuplicateTerm,
    EraseBall,
    Fail,
    GetBall,
    GetCurrentBlock,
    InstallNewBlock,
    InternalCallN,
    IsAtomic,
    IsVar,
    ResetBlock,
    SetBall,
    Unify,
    UnwindStack
}

pub enum ControlInstruction {
    Allocate(usize),
    Call(Atom, usize, usize),
    CallN(usize),
    CatchCall,
    CatchExecute,
    Deallocate,
    Execute(Atom, usize),
    ExecuteN(usize),
    Goto(usize, usize),
    Proceed,
    ThrowCall,
    ThrowExecute
}

impl ControlInstruction {
    pub fn is_jump_instr(&self) -> bool {
        match self {
            &ControlInstruction::Call(_, _, _)  => true,
            &ControlInstruction::CatchCall => true,
            &ControlInstruction::CatchExecute => true,
            &ControlInstruction::Execute(_, _)  => true,
            &ControlInstruction::CallN(_) => true,
            &ControlInstruction::ExecuteN(_) => true,
            &ControlInstruction::ThrowCall => true,
            &ControlInstruction::ThrowExecute => true,
            &ControlInstruction::Goto(_, _) => true,
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
    BuiltIn(BuiltInInstruction),
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
