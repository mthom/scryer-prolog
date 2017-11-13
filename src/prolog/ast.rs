use prolog::num::bigint::BigInt;
use prolog::num::ToPrimitive;

use prolog::ordered_float::*;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::io::Error as IOError;
use std::num::{ParseFloatError};
use std::ops::{Add, AddAssign, Sub, Mul, Neg};
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
    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &PredicateClause::Fact(ref term) => term.first_arg(),
            &PredicateClause::Rule(ref rule) =>
                if let &QueryTerm::Term(ref term) = &rule.head.0 {
                    term.first_arg()
                } else {
                    None
                }
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term) => term.arity(),
            &PredicateClause::Rule(ref rule) => rule.head.0.arity()
        }
    }

    pub fn name(&self) -> Option<&Atom> {
        match self {
            &PredicateClause::Fact(ref term) => term.name(),
            &PredicateClause::Rule(ref rule) =>
                if let &QueryTerm::Term(ref term) = &rule.head.0 {
                    term.name()
                } else {
                    None
                }
        }
    }
}

pub enum Declaration {
    Op(usize, Specifier, Atom)
}

pub enum TopLevel {
    Declaration(Declaration),
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

macro_rules! is_postfix {
    ($x:expr) => ( $x & (XF | YF) != 0 )
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

#[derive(Debug, Clone, Copy)]
pub enum ArithmeticError {
    InvalidAtom,
    InvalidOp,
    InvalidTerm,
    UninstantiatedVar
}

/* 'TokenTooLong' is hard to detect reliably if we don't process the
input one character at a time. It would be easy to detect if the regex
library supported matching on iterator inputs, but it currently does
not. This is fine, mostly; the typical Prolog program will not contain
tokens exceeding 4096 chars in length. */

#[derive(Debug)]
pub enum ParserError
{
    Arithmetic(ArithmeticError),
    CommaArityMismatch,
    UnexpectedEOF,
    FailedMatch(String),
    IO(IOError),
    InadmissibleFact,
    InadmissibleQueryTerm,
    IncompleteReduction,
    InconsistentDeclaration,
    InconsistentPredicate,
    InvalidRuleHead,
    ParseBigInt,
    ParseFloat(ParseFloatError),
    // TokenTooLong,
    Utf8Conversion(Utf8Error)
}

impl From<ArithmeticError> for ParserError {
    fn from(err: ArithmeticError) -> ParserError {
        ParserError::Arithmetic(err)
    }
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

impl From<Number> for Constant {
    fn from(n: Number) -> Self {
        match n {
            Number::Integer(n) => Constant::Integer(n),
            Number::Float(f) => Constant::Float(f)
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

pub enum InlinedQueryTerm {    
    IsAtomic(Vec<Box<Term>>),
    IsVar(Vec<Box<Term>>)
}    

impl InlinedQueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &InlinedQueryTerm::IsAtomic(_) => 1,
            &InlinedQueryTerm::IsVar(_) => 1
        }
    }
}

pub enum QueryTerm {
    CallN(Vec<Box<Term>>),
    Catch(Vec<Box<Term>>),
    Cut,
    Is(Vec<Box<Term>>),
    Inlined(InlinedQueryTerm),
    Term(Term),
    Throw(Vec<Box<Term>>)
}

impl QueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &QueryTerm::Catch(_) => 3,
            &QueryTerm::Throw(_) => 1,
            &QueryTerm::Inlined(ref term) => term.arity(),
            &QueryTerm::Is(_) => 2,
            &QueryTerm::CallN(ref terms) => terms.len(),
            &QueryTerm::Cut => 0,
            &QueryTerm::Term(ref term) => term.arity(),
        }
    }
}

pub struct Rule {
    pub head: (QueryTerm, QueryTerm),
    pub clauses: Vec<QueryTerm>
}

#[derive(Clone, Copy)]
pub enum ClauseType<'a> {
    CallN,
    Catch,
    Deep(Level, &'a Cell<RegType>, &'a Atom),
    Is,
    Root,
    Throw,
}

impl<'a> ClauseType<'a> {
    pub fn level_of_subterms(self) -> Level {
        match self {
            ClauseType::Deep(_, _, _) => Level::Deep,
            _ => Level::Shallow
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
            TermRef::Clause(ClauseType::Deep(lvl, _, _), _) => lvl,
            _ => Level::Shallow
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

#[derive(Clone)]
pub enum Number {
    Float(OrderedFloat<f64>),
    Integer(BigInt)
}

impl Add<Number> for Number {
    type Output = Number;

    fn add(self, rhs: Number) -> Self::Output {
        match (self, rhs) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Number::Integer(n1 + n2),
            (Number::Float(n1), Number::Float(n2)) =>
                Number::Float(OrderedFloat(n1.into_inner() + n2.into_inner())),
            (Number::Integer(n1), Number::Float(n2))
          | (Number::Float(n2), Number::Integer(n1)) =>
                match n1.to_f64() {
                    Some(n1) => Number::Float(OrderedFloat(n1 + n2.into_inner())),
                    None     => Number::Integer(n1)
                }
        }
    }
}

impl Sub<Number> for Number {
    type Output = Number;

    fn sub(self, rhs: Number) -> Self::Output {
        match (self, rhs) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Number::Integer(n1 - n2),
            (Number::Float(n1), Number::Float(n2)) =>
                Number::Float(OrderedFloat(n1.into_inner() - n2.into_inner())),
            (Number::Integer(n1), Number::Float(n2))
          | (Number::Float(n2), Number::Integer(n1)) =>
                match n1.to_f64() {
                    Some(n1) => Number::Float(OrderedFloat(n1 - n2.into_inner())),
                    None     => Number::Integer(n1)
                }
        }
    }
}

impl Mul<Number> for Number {
    type Output = Number;

    fn mul(self, rhs: Number) -> Self::Output {
        match (self, rhs) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Number::Integer(n1 * n2),
            (Number::Float(n1), Number::Float(n2)) =>
                Number::Float(OrderedFloat(n1.into_inner() * n2.into_inner())),
            (Number::Integer(n1), Number::Float(n2))
          | (Number::Float(n2), Number::Integer(n1)) =>
                match n1.to_f64() {
                    Some(n1) => Number::Float(OrderedFloat(n1 * n2.into_inner())),
                    None     => Number::Integer(n1)
                }
        }
    }
}

/*TODO: reserved for proper division.
impl Div<Number> for Number {
    type Output = Number;

    fn div(self, rhs: Number) -> Self::Output {
        match (self, rhs) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Number::Integer(n1 / n2),
            (Number::Float(n1), Number::Float(n2)) =>
                Number::Float(OrderedFloat(n1.into_inner() / n2.into_inner())),
            (Number::Integer(n1), Number::Float(n2))
          | (Number::Float(n2), Number::Integer(n1)) =>
                match n1.to_f64() {
                    Some(n1) => Number::Float(OrderedFloat(n1 / n2.into_inner())),
                    None     => Number::Integer(n1)
                }
        }
    }
}
*/

impl Neg for Number {
    type Output = Number;

    fn neg(self) -> Self::Output {
        match self {
            Number::Integer(n) => Number::Integer(-n),
            Number::Float(f) => Number::Float(OrderedFloat(-1.0 * f.into_inner()))
        }
    }
}

#[derive(Clone)]
pub enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Float(OrderedFloat<f64>),
    Integer(BigInt)
}

impl ArithmeticTerm {
    pub fn interm_or(&self, interm: usize) -> usize {
        if let &ArithmeticTerm::Interm(interm) = self {
            interm
        } else {
            interm
        }
    }
}

pub enum ArithmeticInstruction {
    Add(ArithmeticTerm, ArithmeticTerm, usize),
    Sub(ArithmeticTerm, ArithmeticTerm, usize),
    Mul(ArithmeticTerm, ArithmeticTerm, usize),
    IDiv(ArithmeticTerm, ArithmeticTerm, usize),
    Neg(ArithmeticTerm, usize)
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
    IsAtomic(RegType),
    IsVar(RegType),
    ResetBlock,
    SetBall,
    Succeed,
    Unify,
    UnwindStack
}

pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    Call(Atom, usize, usize), // name, arity, perm_vars after threshold.
    CallN(usize), // arity.
    CatchCall,
    CatchExecute,
    Deallocate,
    Execute(Atom, usize),
    ExecuteN(usize),
    Goto(usize, usize), // p, arity.
    IsCall(RegType),
    IsExecute(RegType),
    Proceed,
    ThrowCall,
    ThrowExecute,    
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
            &ControlInstruction::Proceed => true,
            &ControlInstruction::IsCall(_) => true,
            &ControlInstruction::IsExecute(_) => true,            
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
    Arithmetic(ArithmeticInstruction),
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

pub enum IteratorState<'a> {
    AnonVar(Level),
    Clause(usize, ClauseType<'a>, &'a Vec<Box<Term>>),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> IteratorState<'a> {
    pub fn to_state(lvl: Level, term: &'a Term) -> IteratorState<'a> {
        match term {
            &Term::AnonVar =>
                IteratorState::AnonVar(lvl),
            &Term::Clause(ref cell, ref atom, ref child_terms) =>
                IteratorState::Clause(0, ClauseType::Deep(lvl, cell, atom), child_terms),
            &Term::Cons(ref cell, ref head, ref tail) =>
                IteratorState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref()),
            &Term::Constant(ref cell, ref constant) =>
                IteratorState::Constant(lvl, cell, constant),
            &Term::Var(ref cell, ref var) =>
                IteratorState::Var(lvl, cell, var)
        }
    }
}
