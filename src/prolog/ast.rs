use prolog::num::bigint::BigInt;
use prolog::num::{Float, ToPrimitive, Zero};
use prolog::num::rational::Ratio;
use prolog::ordered_float::*;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::io::Error as IOError;
use std::num::{ParseFloatError};
use std::ops::{Add, AddAssign, Div, Index, IndexMut, Sub, Mul, Neg};
use std::rc::Rc;
use std::str::Utf8Error;
use std::vec::Vec;

pub const LEXER_BUF_SIZE: usize = 4096;

pub type Atom = String;

pub type Var = String;

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

    pub fn name(&self) -> Option<Rc<Atom>> {
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
    Op(usize, Specifier, Rc<Atom>)
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
    Atom(Rc<Atom>),
    Number(Number),    
    String(Rc<String>),
    Usize(usize),
    EmptyList
}

impl<'a> From<&'a str> for Constant {
    fn from(input: &str) -> Constant {
        Constant::Atom(Rc::new(String::from(input)))
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Constant::Atom(ref atom) =>
                write!(f, "{}", atom),
            &Constant::EmptyList =>
                write!(f, "[]"),
            &Constant::Number(ref n) =>
                write!(f, "{}", n),            
            &Constant::String(ref s) =>
                write!(f, "{}", s),
            &Constant::Usize(integer) =>
                write!(f, "u{}", integer)
        }
    }
}

pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, Rc<Atom>, Vec<Box<Term>>, Option<Fixity>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Constant(Cell<RegType>, Constant),
    Var(Cell<VarReg>, Rc<Var>)
}

pub enum InlinedQueryTerm {
    CompareNumber(CompareNumberQT, Vec<Box<Term>>),
    IsAtomic(Vec<Box<Term>>),
    IsVar(Vec<Box<Term>>),
    IsInteger(Vec<Box<Term>>)
}

impl InlinedQueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &InlinedQueryTerm::CompareNumber(_, _) => 2,
            &InlinedQueryTerm::IsAtomic(_) => 1,
            &InlinedQueryTerm::IsInteger(_) => 1,
            &InlinedQueryTerm::IsVar(_) => 1,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CompareNumberQT {
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    NotEqual,
    Equal
}

pub enum QueryTerm {
    Arg(Vec<Box<Term>>),
    CallN(Vec<Box<Term>>),
    Catch(Vec<Box<Term>>),    
    Cut,
    Display(Vec<Box<Term>>),
    Functor(Vec<Box<Term>>),
    Inlined(InlinedQueryTerm),
    Is(Vec<Box<Term>>),
    Term(Term),
    Throw(Vec<Box<Term>>)
}

impl QueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &QueryTerm::Arg(_) => 3,
            &QueryTerm::Catch(_) => 3,
            &QueryTerm::Throw(_) => 1,
            &QueryTerm::Display(_) => 1,
            &QueryTerm::Functor(_) => 3,
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
    Deep(Level, &'a Cell<RegType>, &'a Rc<Atom>, Option<Fixity>),
    Is,
    Root,
    Throw,
}

impl<'a> ClauseType<'a> {
    pub fn level_of_subterms(self) -> Level {
        match self {
            ClauseType::Deep(..) => Level::Deep,
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
          | TermRef::Cons(lvl, ..)
          | TermRef::Constant(lvl, ..)
          | TermRef::Var(lvl, ..) => lvl,
            TermRef::Clause(ClauseType::Deep(lvl, ..), ..) => lvl,
            _ => Level::Shallow
        }
    }
}

pub enum ChoiceInstruction {
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

pub enum CutInstruction {
    Cut,
    GetLevel,
    NeckCut
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Number {
    Float(OrderedFloat<f64>),
    Integer(Rc<BigInt>),
    Rational(Rc<Ratio<BigInt>>)
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Number::Float(fl) => write!(f, "{}", fl),
            &Number::Integer(ref bi) => write!(f, "{}", bi),
            &Number::Rational(ref r) => write!(f, "{}", r)            
        }
    }
}

impl Default for Number {
    fn default() -> Self {
        Number::Float(OrderedFloat(0f64))
    }
}

impl Number {
    pub fn is_zero(&self) -> bool {
        match self {
            &Number::Float(fl)       => fl.into_inner().is_zero(),
            &Number::Integer(ref bi) => bi.is_zero(),
            &Number::Rational(ref r) => r.is_zero()
        }
    }

    pub fn gt(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 > n2,
            NumberPair::Float(n1, n2) => n1 > n2,
            NumberPair::Rational(n1, n2) => n1 > n2
        }
    }
    
    pub fn gte(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 >= n2,
            NumberPair::Float(n1, n2) => n1 >= n2,
            NumberPair::Rational(n1, n2) => n1 >= n2
        }
    }

    pub fn lt(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 < n2,
            NumberPair::Float(n1, n2) => n1 < n2,
            NumberPair::Rational(n1, n2) => n1 < n2
        }
    }

    pub fn lte(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 <= n2,
            NumberPair::Float(n1, n2) => n1 <= n2,
            NumberPair::Rational(n1, n2) => n1 <= n2
        }
    }

    pub fn ne(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 != n2,
            NumberPair::Float(n1, n2) => n1 != n2,
            NumberPair::Rational(n1, n2) => n1 != n2
        }
    }

    pub fn eq(self, n2: Number) -> bool {
        match NumberPair::from(self, n2) {
            NumberPair::Integer(n1, n2) => n1 == n2,
            NumberPair::Float(n1, n2) => n1 == n2,
            NumberPair::Rational(n1, n2) => n1 == n2
        }
    }    
}

enum NumberPair {
    Float(OrderedFloat<f64>, OrderedFloat<f64>),
    Integer(Rc<BigInt>, Rc<BigInt>),
    Rational(Rc<Ratio<BigInt>>, Rc<Ratio<BigInt>>)
}

impl NumberPair {
    fn flip(self) -> NumberPair {
        match self {
            NumberPair::Float(f1, f2)    => NumberPair::Float(f2, f1),
            NumberPair::Integer(n1, n2)  => NumberPair::Integer(n2, n1),
            NumberPair::Rational(r1, r2) => NumberPair::Rational(r2, r1)
        }
    }

    fn integer_float_pair(n1: Rc<BigInt>, n2: OrderedFloat<f64>) -> NumberPair {
        match n1.to_f64() {
            Some(f1) => NumberPair::Float(OrderedFloat(f1), n2),
            None => if let Some(r) = Ratio::from_float(n2.into_inner()) {
                NumberPair::Rational(Rc::new(Ratio::from_integer((*n1).clone())),
                                     Rc::new(r))
            } else if n2.into_inner().is_sign_positive() {
                NumberPair::Float(OrderedFloat(f64::infinity()),
                                  OrderedFloat(f64::infinity()))
            } else {
                NumberPair::Float(OrderedFloat(f64::neg_infinity()),
                                  OrderedFloat(f64::neg_infinity()))
            }
        }
    }

    fn float_rational_pair(n1: OrderedFloat<f64>, n2: Rc<Ratio<BigInt>>) -> NumberPair {
        match (n2.numer().to_f64(), n2.denom().to_f64()) {
            (Some(num), Some(denom)) =>
                NumberPair::Float(n1, OrderedFloat(num / denom)),
            _ => if let Some(r) = Ratio::from_float(n1.into_inner()) {
                NumberPair::Rational(Rc::new(r), n2)
            } else if n1.into_inner().is_sign_positive() {
                NumberPair::Float(OrderedFloat(f64::infinity()),
                                  OrderedFloat(f64::infinity()))
            } else {
                NumberPair::Float(OrderedFloat(f64::neg_infinity()),
                                  OrderedFloat(f64::neg_infinity()))
            }
        }
    }

    fn from(n1: Number, n2: Number) -> NumberPair
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                NumberPair::Integer(n1, n2),
            (Number::Float(n1), Number::Float(n2)) =>
                NumberPair::Float(n1, n2),
            (Number::Rational(n1), Number::Rational(n2)) =>
                NumberPair::Rational(n1, n2),            
            (Number::Integer(n1), Number::Float(n2)) =>
                Self::integer_float_pair(n1, n2),
            (Number::Float(n1), Number::Integer(n2)) =>
                Self::integer_float_pair(n2, n1).flip(),
            (Number::Float(n1), Number::Rational(n2)) =>
                Self::float_rational_pair(n1, n2),
            (Number::Rational(n1), Number::Float(n2)) =>
                Self::float_rational_pair(n2, n1).flip(),
            (Number::Rational(n1), Number::Integer(n2)) =>
                NumberPair::Rational(n1, Rc::new(Ratio::from_integer((*n2).clone()))),
            (Number::Integer(n1), Number::Rational(n2)) =>
                NumberPair::Rational(Rc::new(Ratio::from_integer((*n1).clone())), n2)
        }
    }
}

impl Add<Number> for Number {
    type Output = Number;

    fn add(self, rhs: Number) -> Self::Output {
        match NumberPair::from(self, rhs) {
            NumberPair::Float(f1, f2) =>
                Number::Float(OrderedFloat(f1.into_inner() + f2.into_inner())),
            NumberPair::Integer(n1, n2) =>
                Number::Integer(Rc::new(&*n1 + &*n2)),
            NumberPair::Rational(r1, r2) =>
                Number::Rational(Rc::new(&*r1 + &*r2))
        }
    }
}

impl Sub<Number> for Number {
    type Output = Number;

    fn sub(self, rhs: Number) -> Self::Output {
        match NumberPair::from(self, rhs) {
            NumberPair::Float(f1, f2) =>
                Number::Float(OrderedFloat(f1.into_inner() - f2.into_inner())),
            NumberPair::Integer(n1, n2) =>
                Number::Integer(Rc::new(&*n1 - &*n2)),
            NumberPair::Rational(r1, r2) =>
                Number::Rational(Rc::new(&*r1 - &*r2))
        }
    }
}

impl Mul<Number> for Number {
    type Output = Number;

    fn mul(self, rhs: Number) -> Self::Output {
        match NumberPair::from(self, rhs) {
            NumberPair::Float(f1, f2) =>
                Number::Float(OrderedFloat(f1.into_inner() * f2.into_inner())),
            NumberPair::Integer(n1, n2) =>
                Number::Integer(Rc::new(&*n1 * &*n2)),
            NumberPair::Rational(r1, r2) =>
                Number::Rational(Rc::new(&*r1 * &*r2))
        }        
    }
}
    
impl Div<Number> for Number {
    type Output = Number;

    fn div(self, rhs: Number) -> Self::Output {
        match NumberPair::from(self, rhs) {
            NumberPair::Float(f1, f2) =>
                Number::Float(OrderedFloat(f1.into_inner() / f2.into_inner())),
            NumberPair::Integer(n1, n2) =>
                match n1.to_f64() {
                    Some(f1) => if let Some(f2) = n2.to_f64() {
                        Number::Float(OrderedFloat(f1 / f2))
                    } else {
                        let r1 = Ratio::from_integer((*n1).clone());
                        let r2 = Ratio::from_integer((*n2).clone());

                        Number::Rational(Rc::new(r1 / r2))
                    },
                    None => {
                        let r1 = Ratio::from_integer((*n1).clone());
                        let r2 = Ratio::from_integer((*n2).clone());

                        Number::Rational(Rc::new(r1 / r2))
                    },
                },
            NumberPair::Rational(r1, r2) =>
                Number::Rational(Rc::new(&*r1 / &*r2))
        }
    }
}

impl Neg for Number {
    type Output = Number;

    fn neg(self) -> Self::Output {
        match self {
            Number::Integer(n) => Number::Integer(Rc::new(-&*n)),
            Number::Float(f) => Number::Float(OrderedFloat(-1.0 * f.into_inner())),
            Number::Rational(r) => Number::Rational(Rc::new(- &*r))
        }
    }
}

#[derive(Clone)]
pub enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Number(Number)
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
    FIDiv(ArithmeticTerm, ArithmeticTerm, usize),
    RDiv(ArithmeticTerm, ArithmeticTerm, usize),
    Div(ArithmeticTerm, ArithmeticTerm, usize),
    Shl(ArithmeticTerm, ArithmeticTerm, usize),
    Shr(ArithmeticTerm, ArithmeticTerm, usize),
    Xor(ArithmeticTerm, ArithmeticTerm, usize),
    And(ArithmeticTerm, ArithmeticTerm, usize),
    Or(ArithmeticTerm, ArithmeticTerm, usize),
    Mod(ArithmeticTerm, ArithmeticTerm, usize),
    Rem(ArithmeticTerm, ArithmeticTerm, usize),
    Neg(ArithmeticTerm, usize)
}

pub enum BuiltInInstruction {
    CleanUpBlock,
    CompareNumber(CompareNumberQT, ArithmeticTerm, ArithmeticTerm),
    DuplicateTerm,
    EraseBall,
    Fail,
    GetArg,
    GetBall,
    GetCurrentBlock,
    GetCutPoint(RegType),
    InstallNewBlock,
    InternalCallN,
    IsAtomic(RegType),
    IsInteger(RegType),
    IsVar(RegType),
    ResetBlock,
    SetBall,
    SetCutPoint(RegType),
    Succeed,
    Unify,
    UnwindStack
}

pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    ArgCall,
    ArgExecute,
    Call(Rc<Atom>, usize, usize), // name, arity, perm_vars after threshold.
    CallN(usize), // arity.
    CatchCall,
    CatchExecute,
    Deallocate,
    DisplayCall,
    DisplayExecute,
    Execute(Rc<Atom>, usize),
    ExecuteN(usize),
    FunctorCall,
    FunctorExecute,
    Goto(usize, usize), // p, arity.
    IsCall(RegType, ArithmeticTerm),
    IsExecute(RegType, ArithmeticTerm),
    Proceed,
    ThrowCall,
    ThrowExecute,
}

impl ControlInstruction {
    pub fn is_jump_instr(&self) -> bool {
        match self {
            &ControlInstruction::ArgCall => true,
            &ControlInstruction::ArgExecute => true,
            &ControlInstruction::Call(_, _, _)  => true,
            &ControlInstruction::CatchCall => true,
            &ControlInstruction::CatchExecute => true,
            &ControlInstruction::DisplayCall => true,
            &ControlInstruction::DisplayExecute => true,
            &ControlInstruction::Execute(_, _)  => true,
            &ControlInstruction::CallN(_) => true,
            &ControlInstruction::ExecuteN(_) => true,
            &ControlInstruction::FunctorCall => true,
            &ControlInstruction::FunctorExecute => true,
            &ControlInstruction::ThrowCall => true,
            &ControlInstruction::ThrowExecute => true,
            &ControlInstruction::Goto(_, _) => true,
            &ControlInstruction::Proceed => true,
            &ControlInstruction::IsCall(_, _) => true,
            &ControlInstruction::IsExecute(_, _) => true,
            _ => false
        }
    }
}

pub enum IndexingInstruction {
    SwitchOnTerm(usize, usize, usize, usize),
    SwitchOnConstant(usize, HashMap<Constant, usize>),
    SwitchOnStructure(usize, HashMap<(Rc<Atom>, usize), usize>)
}

impl From<IndexingInstruction> for Line {
    fn from(i: IndexingInstruction) -> Self {
        Line::Indexing(i)
    }
}

pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetStructure(Level, Rc<Atom>, usize, RegType, Option<Fixity>),
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
    PutStructure(Level, Rc<Atom>, usize, RegType, Option<Fixity>),
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
       
    pub fn as_var(&self) -> Option<Ref> {
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
            Ref::HeapCell(hc)      => Addr::HeapCell(hc),
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
    Addr(Addr),
    NamedStr(usize, Rc<Atom>, Option<Fixity>), // arity, name.
}

impl HeapCellValue {
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            &HeapCellValue::Addr(ref a)    => a.clone(),
            &HeapCellValue::NamedStr(_, _, _) => Addr::Str(focus)
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

pub struct Heap {
    heap: Vec<HeapCellValue>,
    pub h: usize
}

impl Heap {
    pub fn with_capacity(cap: usize) -> Self {
        Heap { heap: Vec::with_capacity(cap), h: 0 }
    }
    
    pub fn push(&mut self, val: HeapCellValue) {
        self.heap.push(val);
        self.h += 1;
    }

    pub fn truncate(&mut self, h: usize) {
        self.h = h;
        self.heap.truncate(h);
    }

    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn append(&mut self, vals: Vec<HeapCellValue>) {
        let n = vals.len();
        
        self.heap.extend(vals.into_iter());
        self.h += n;
    }

    pub fn clear(&mut self) {
        self.heap.clear();
        self.h = 0;
    }
}

impl Index<usize> for Heap {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index]
    }
}

impl IndexMut<usize> for Heap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.heap[index]
    }
}

pub type Registers = Vec<Addr>;

impl Term {
    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &Term::Clause(_, _, ref terms, _) =>
                terms.first().map(|bt| bt.as_ref()),
            _ => None
        }
    }

    pub fn is_callable(&self) -> bool {
        match self {
            &Term::Clause(..) | &Term::Constant(_, Constant::Atom(_)) =>
                true,
            _ => false
        }
    }

    pub fn name(&self) -> Option<Rc<Atom>> {
        match self {
            &Term::Constant(_, Constant::Atom(ref atom))
          | &Term::Clause(_, ref atom, ..) => Some(atom.clone()),
            _ => None
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &Term::Clause(_, _, ref child_terms, ..) => child_terms.len(),
            _ => 0
        }
    }
}

pub enum TermIterState<'a> {
    AnonVar(Level),
    Clause(usize, ClauseType<'a>, &'a Vec<Box<Term>>),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> TermIterState<'a> {
    pub fn to_state(lvl: Level, term: &'a Term) -> TermIterState<'a> {
        match term {
            &Term::AnonVar =>
                TermIterState::AnonVar(lvl),
            &Term::Clause(ref cell, ref atom, ref child_terms, fixity) =>
                TermIterState::Clause(0, ClauseType::Deep(lvl, cell, atom, fixity), child_terms),
            &Term::Cons(ref cell, ref head, ref tail) =>
                TermIterState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref()),
            &Term::Constant(ref cell, ref constant) =>
                TermIterState::Constant(lvl, cell, constant),
            &Term::Var(ref cell, ref var) =>
                TermIterState::Var(lvl, cell, var)
        }
    }
}
