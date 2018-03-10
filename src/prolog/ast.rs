use prolog::num::bigint::BigInt;
use prolog::num::{Float, ToPrimitive, Zero};
use prolog::num::rational::Ratio;
use prolog::ordered_float::*;
use prolog::tabled_rc::*;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::Error as IOError;
use std::num::{ParseFloatError};
use std::ops::{Add, AddAssign, Div, Index, IndexMut, Sub, Mul, Neg};
use std::rc::Rc;
use std::str::Utf8Error;
use std::vec::Vec;

pub const LEXER_BUF_SIZE: usize = 4096;

pub type Atom = String;

pub type Var = String;

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

pub type Predicate = Vec<PredicateClause>;

pub enum PredicateClause {
    Fact(Term),
    Rule(Rule)
}

impl PredicateClause {
    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &PredicateClause::Fact(ref term) => term.first_arg(),
            &PredicateClause::Rule(ref rule) => rule.head.1.first().map(|bt| bt.as_ref()),
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term) => term.arity(),
            &PredicateClause::Rule(ref rule) => rule.head.1.len()
        }
    }

    pub fn name(&self) -> Option<ClauseName> {
        match self {
            &PredicateClause::Fact(ref term) => term.name(),
            &PredicateClause::Rule(ref rule) => Some(rule.head.0.clone()),
        }
    }
}

pub type OpDirKey = (ClauseName, Fixity);
// name and fixity -> operator type and precedence.
pub type OpDir = HashMap<OpDirKey, (Specifier, usize, ClauseName)>;

pub type CodeDir = HashMap<PredicateKey, (usize, ClauseName)>;

pub type PredicateKey = (ClauseName, usize); // name, arity.

pub struct ModuleDecl {
    pub name: ClauseName,
    pub exports: Vec<PredicateKey>
}

pub struct Module {
    pub module_decl: ModuleDecl,
    pub code_dir: CodeDir,
    pub op_dir: OpDir
}

impl Module {
    pub fn new(module_decl: ModuleDecl) -> Self {
        Module { module_decl,
                 code_dir: CodeDir::new(),
                 op_dir: OpDir::new() }
    }
}

impl SubModuleUser for Module {
    fn op_dir(&mut self) -> &mut OpDir {
        &mut self.op_dir
    }

    fn code_dir(&mut self) -> &mut CodeDir {
        &mut self.code_dir
    }    
}

pub trait SubModuleUser {
    fn op_dir(&mut self) -> &mut OpDir;
    fn code_dir(&mut self) -> &mut CodeDir;

    // returns true on successful import.
    fn import_decl(&mut self, name: ClauseName, arity: usize, submodule: &Module) -> bool {
        let name = name.defrock_brackets();
            
        if arity == 1 {
            if let Some(op_data) = submodule.op_dir.get(&(name.clone(), Fixity::Pre)) {
                self.op_dir().insert((name.clone(), Fixity::Pre), op_data.clone());
            }

            if let Some(op_data) = submodule.op_dir.get(&(name.clone(), Fixity::Post)) {
                self.op_dir().insert((name.clone(), Fixity::Post), op_data.clone());
            }
        } else if arity == 2 {
            if let Some(op_data) = submodule.op_dir.get(&(name.clone(), Fixity::In)) {
                self.op_dir().insert((name.clone(), Fixity::In), op_data.clone());
            }
        }

        if self.code_dir().contains_key(&(name.clone(), arity)) {
            println!("warning: overwriting {}/{}", &name, arity);
        }

        if let Some(code_data) = submodule.code_dir.get(&(name.clone(), arity)) {
            self.code_dir().insert((name, arity), code_data.clone());
            true
        } else {
            false
        }
    }
    
    fn use_qualified_module(&mut self, submodule: &Module, exports: Vec<PredicateKey>) -> EvalSession
    {
        for (name, arity) in exports {
            if !submodule.module_decl.exports.contains(&(name.clone(), arity)) {
                continue;
            }
            
            if !self.import_decl(name, arity, submodule) {
                return EvalSession::from(EvalError::ModuleDoesNotContainExport);
            }
        }

        EvalSession::EntrySuccess
    }
    
    fn use_module(&mut self, submodule: &Module) -> EvalSession {
        for (name, arity) in submodule.module_decl.exports.iter().cloned() {
            if !self.import_decl(name, arity, submodule) {
                return EvalSession::from(EvalError::ModuleDoesNotContainExport);
            }
        }
        
        EvalSession::EntrySuccess
    }
}

pub enum Declaration {
    Module(ModuleDecl),
    Op(OpDecl),
    UseModule(ClauseName),
    UseQualifiedModule(ClauseName, Vec<PredicateKey>)
}

pub enum TopLevel {
    Declaration(Declaration),
    Fact(Term),
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule)
}

impl TopLevel {
    pub fn name(&self) -> Option<ClauseName> {
        match self {
            &TopLevel::Declaration(_) => None,
            &TopLevel::Fact(ref term) => term.name(),
            &TopLevel::Predicate(ref clauses) =>
                if let Some(ref term) = clauses.first() {
                    term.name()
                } else {
                    None
                },
            &TopLevel::Query(_) => None,
            &TopLevel::Rule(Rule { ref head, .. }) =>
                Some(head.0.clone())
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &TopLevel::Declaration(_) => 0,
            &TopLevel::Fact(ref term) => term.arity(),
            &TopLevel::Predicate(ref clauses) =>
                clauses.first().map(|t| t.arity()).unwrap_or(0),
            &TopLevel::Query(_) => 0,
            &TopLevel::Rule(Rule { ref head, .. }) => head.1.len()
        }
    }
}

#[derive(Clone, Copy)]
pub enum Level {
    Deep, Root, Shallow
}

impl Level {
    pub fn child_level(self) -> Level {
        match self {
            Level::Root => Level::Shallow,
            _ => Level::Deep
        }
    }
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

#[derive(PartialEq, Eq, Clone, Copy)]
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

// labeled with chunk numbers.
pub enum VarStatus {
    Perm(usize), Temp(usize, TempVarData) // Perm(chunk_num) | Temp(chunk_num, _)
}

pub type OccurrenceSet = BTreeSet<(GenContext, usize)>;

// Perm: 0 initially, a stack register once processed.
// Temp: labeled with chunk_num and temp offset (unassigned if 0).
pub enum VarData {
    Perm(usize), Temp(usize, usize, TempVarData)
}

pub struct TempVarData {
    pub last_term_arity: usize,
    pub use_set: OccurrenceSet,
    pub no_use_set: BTreeSet<usize>,
    pub conflict_set: BTreeSet<usize>
}

pub type HeapVarDict  = HashMap<Rc<Var>, Addr>;
pub type AllocVarDict = HashMap<Rc<Var>, VarData>;

pub enum EvalError {
    ImpermissibleEntry(String),
    ModuleDoesNotContainExport,
    ModuleNotFound,
    NamelessEntry,
    OpIsInfixAndPostFix,
    ParserError(ParserError),
    QueryFailure,
    QueryFailureWithException(String)
}

pub enum EvalSession {
    EntrySuccess,
    Error(EvalError),
    InitialQuerySuccess(AllocVarDict, HeapVarDict),
    SubsequentQuerySuccess,
}

impl From<EvalError> for EvalSession {
    fn from(err: EvalError) -> Self {
        EvalSession::Error(err)
    }
}

impl From<ParserError> for EvalError {
    fn from(err: ParserError) -> Self {
        EvalError::ParserError(err)
    }
}

impl From<ParserError> for EvalSession {
    fn from(err: ParserError) -> Self {
        EvalSession::from(EvalError::ParserError(err))
    }
}

pub struct OpDecl(pub usize, pub Specifier, pub ClauseName);

impl OpDecl {
    pub fn submit(&self, module: ClauseName, op_dir: &mut OpDir) -> Result<(), EvalError>
    {
        let (prec, spec, name) = (self.0, self.1, self.2.clone());

        if is_infix!(spec) {
            match op_dir.get(&(name.clone(), Fixity::Post)) {
                Some(_) => return Err(EvalError::OpIsInfixAndPostFix),
                _ => {}
            };
        }

        if is_postfix!(spec) {
            match op_dir.get(&(name.clone(), Fixity::In)) {
                Some(_) => return Err(EvalError::OpIsInfixAndPostFix),
                _ => {}
            };
        }

        if prec > 0 {
            match spec {
                XFY | XFX | YFX => op_dir.insert((name.clone(), Fixity::In),
                                                 (spec, prec, module.clone())),
                XF | YF => op_dir.insert((name.clone(), Fixity::Post), (spec, prec, module.clone())),
                FX | FY => op_dir.insert((name.clone(), Fixity::Pre), (spec, prec, module.clone())),
                _ => None
            };
        } else {
            op_dir.remove(&(name.clone(), Fixity::Pre));
            op_dir.remove(&(name.clone(), Fixity::In));
            op_dir.remove(&(name.clone(), Fixity::Post));
        }

        Ok(())
    }
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
    BuiltInArityMismatch(&'static str),
    UnexpectedEOF,
    FailedMatch(String),
    IO(IOError),
    ExpectedRel,
    InadmissibleFact,
    InadmissibleQueryTerm,
    IncompleteReduction,
    InconsistentEntry, // was InconsistentDeclaration.
    InvalidModuleDecl,
    InvalidModuleExport,
    InvalidRuleHead,
    InvalidUseModuleDecl,
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
    Atom(ClauseName),
    Number(Number),
    String(Rc<String>),
    Usize(usize),
    EmptyList
}

impl Constant {
    pub fn to_atom(self) -> Option<ClauseName> {
        match self {
            Constant::Atom(a) => Some(a),
            _ => None
        }
    }

    pub fn to_integer(self) -> Option<Rc<BigInt>> {
        match self {
            Constant::Number(Number::Integer(b)) => Some(b),
            _ => None
        }
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

#[derive(PartialEq, Eq, Clone)]
pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, ClauseName, Vec<Box<Term>>, Option<Fixity>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Constant(Cell<RegType>, Constant),
    Var(Cell<VarReg>, Rc<Var>)
}

#[derive(Clone, Copy)]
pub enum InlinedClauseType {
    CompareNumber(CompareNumberQT),
    IsAtom,
    IsAtomic,
    IsCompound,
    IsInteger,
    IsRational,
    IsString,
    IsFloat,
    IsNonVar,
    IsVar,
}

impl InlinedClauseType {
    pub fn name(&self) -> &'static str {
        match self {
            &InlinedClauseType::CompareNumber(qt) => qt.name(),
            &InlinedClauseType::IsAtom => "atom",
            &InlinedClauseType::IsAtomic => "atomic",
            &InlinedClauseType::IsCompound => "compound",
            &InlinedClauseType::IsInteger  => "integer",
            &InlinedClauseType::IsRational => "rational",
            &InlinedClauseType::IsString => "string",
            &InlinedClauseType::IsFloat  => "float",
            &InlinedClauseType::IsNonVar => "nonvar",
            &InlinedClauseType::IsVar => "var"
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<Self> {
        match (name, arity) {
            (">", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThan)),
            ("<", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThan)),
            (">=", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThanOrEqual)),
            ("<=", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThanOrEqual)),
            ("=\\=", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::NotEqual)),
            ("=:=", 2) => Some(InlinedClauseType::CompareNumber(CompareNumberQT::Equal)),
            ("atom", 1) => Some(InlinedClauseType::IsAtom),
            ("atomic", 1) => Some(InlinedClauseType::IsAtomic),
            ("compound", 1) => Some(InlinedClauseType::IsCompound),
            ("integer", 1) => Some(InlinedClauseType::IsInteger),
            ("rational", 1) => Some(InlinedClauseType::IsRational),
            ("string", 1) => Some(InlinedClauseType::IsString),
            ("float", 1) => Some(InlinedClauseType::IsFloat),
            ("nonvar", 1) => Some(InlinedClauseType::IsNonVar),
            ("var", 1) => Some(InlinedClauseType::IsVar),
            _ => None
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

impl CompareNumberQT {
    fn name(self) -> &'static str {
        match self {
            CompareNumberQT::GreaterThan => ">",
            CompareNumberQT::LessThan => "<",
            CompareNumberQT::GreaterThanOrEqual => ">=",
            CompareNumberQT::LessThanOrEqual => "=<",
            CompareNumberQT::NotEqual => "=\\=",
            CompareNumberQT::Equal => "=:="
        }
    }
}

#[derive(Clone, Copy)]
pub enum CompareTermQT {
    LessThan,
    LessThanOrEqual,
    Equal,
    GreaterThanOrEqual,
    GreaterThan,
    NotEqual,
}

impl CompareTermQT {
    fn name<'a>(self) -> &'a str {
        match self {
            CompareTermQT::GreaterThan => "@>",
            CompareTermQT::LessThan => "@<",
            CompareTermQT::GreaterThanOrEqual => "@>=",
            CompareTermQT::LessThanOrEqual => "@=<",
            CompareTermQT::NotEqual => "\\=@=",
            CompareTermQT::Equal => "=@="
        }
    }
}

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub type JumpStub = Vec<Term>;

pub enum QueryTerm {
    Clause(Cell<RegType>, ClauseType, Vec<Box<Term>>),
    Cut,
    Jump(JumpStub)
}

impl QueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &QueryTerm::Clause(_, _, ref subterms) => subterms.len(),
            &QueryTerm::Cut => 0,
            &QueryTerm::Jump(ref vars) => vars.len()
        }
    }
}

pub struct Rule {
    pub head: (ClauseName, Vec<Box<Term>>, QueryTerm),
    pub clauses: Vec<QueryTerm>
}

#[derive(Clone)]
pub enum ClauseType {
    Arg,
    CallN,
    CallWithInferenceLimit,
    Catch,
    Compare,
    CompareTerm(CompareTermQT),
    Display,
    DuplicateTerm,
    Eq,
    Functor,
    Ground,
    Inlined(InlinedClauseType),
    Is,
    NotEq,
    Op(ClauseName, Fixity),
    Named(ClauseName),
    SetupCallCleanup,
    Throw,
}

impl ClauseType {
    pub fn fixity(&self) -> Option<Fixity> {
        match self {
            &ClauseType::Compare | &ClauseType::CompareTerm(_)
          | &ClauseType::Inlined(InlinedClauseType::CompareNumber(_))
          | &ClauseType::NotEq | &ClauseType::Is | &ClauseType::Eq => Some(Fixity::In),
            &ClauseType::Op(_, fixity) => Some(fixity),
            _ => None
        }
    }
}

#[derive(Clone)]
pub enum ClauseName {
    BuiltIn(&'static str),
    User(TabledRc<Atom>)
}

impl Hash for ClauseName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self.as_str()).hash(state)
    }
}

impl PartialEq for ClauseName {
    fn eq(&self, other: &ClauseName) -> bool {
        *self.as_str() == *other.as_str()
    }
}

impl Eq for ClauseName {}

impl Ord for ClauseName {
    fn cmp(&self, other: &ClauseName) -> Ordering {
        (*self.as_str()).cmp(other.as_str())
    }
}

impl PartialOrd for ClauseName {
    fn partial_cmp(&self, other: &ClauseName) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> From<&'a TabledRc<Atom>> for ClauseName {
    fn from(name: &'a TabledRc<Atom>) -> ClauseName {
        ClauseName::User(name.clone())
    }
}

impl ClauseName {
    pub fn as_str(&self) -> &str {
        match self {
            &ClauseName::BuiltIn(s) => s,
            &ClauseName::User(ref name) => name.as_ref()
        }
    }

    pub fn defrock_brackets(self) -> Self {
        fn defrock_brackets(s: &str) -> &str {
            if s.starts_with('(') && s.ends_with(')') {
                &s[1 .. s.len() - 1]
            } else {
                s
            }
        }
        
        match self {
            ClauseName::BuiltIn(s) =>
                ClauseName::BuiltIn(defrock_brackets(s)),
            ClauseName::User(s) =>
                ClauseName::User(tabled_rc!(defrock_brackets(s.as_str()).to_owned(),
                                            s.atom_tbl()))
        }
    }
}

impl ClauseType {
    pub fn name(&self) -> ClauseName {
        match self {
            &ClauseType::Arg => ClauseName::BuiltIn("arg"),
            &ClauseType::CallN => ClauseName::BuiltIn("call"),
            &ClauseType::CallWithInferenceLimit => ClauseName::BuiltIn("call_with_inference_limit"),
            &ClauseType::Catch => ClauseName::BuiltIn("catch"),
            &ClauseType::Compare => ClauseName::BuiltIn("compare"),
            &ClauseType::CompareTerm(qt) => ClauseName::BuiltIn(qt.name()),
            &ClauseType::Display => ClauseName::BuiltIn("display"),
            &ClauseType::DuplicateTerm => ClauseName::BuiltIn("duplicate_term"),
            &ClauseType::Eq => ClauseName::BuiltIn("=="),
            &ClauseType::Functor => ClauseName::BuiltIn("functor"),
            &ClauseType::Ground  => ClauseName::BuiltIn("ground"),
            &ClauseType::Inlined(inlined) => ClauseName::BuiltIn(inlined.name()),
            &ClauseType::Is => ClauseName::BuiltIn("is"),
            &ClauseType::NotEq => ClauseName::BuiltIn("\\=="),
            &ClauseType::Op(ref name, _) => name.clone(),
            &ClauseType::Named(ref name) => name.clone(),
            &ClauseType::SetupCallCleanup => ClauseName::BuiltIn("setup_call_cleanup"),
            &ClauseType::Throw => ClauseName::BuiltIn("throw")
        }
    }

    pub fn from(name: ClauseName, arity: usize, fixity: Option<Fixity>) -> Self {
        match (name.as_str(), arity) {
            ("arg", 3)   => ClauseType::Arg,
            ("call", _)  => ClauseType::CallN,
            ("call_with_inference_limit", 3) => ClauseType::CallWithInferenceLimit,
            ("catch", 3) => ClauseType::Catch,
            ("compare", 3) => ClauseType::Compare,
            ("@>", 2) => ClauseType::CompareTerm(CompareTermQT::GreaterThan),
            ("@<", 2) => ClauseType::CompareTerm(CompareTermQT::LessThan),
            ("@>=", 2) => ClauseType::CompareTerm(CompareTermQT::GreaterThanOrEqual),
            ("@<=", 2) => ClauseType::CompareTerm(CompareTermQT::LessThanOrEqual),
            ("\\=@=", 2) => ClauseType::CompareTerm(CompareTermQT::NotEqual),
            ("=@=", 2) => ClauseType::CompareTerm(CompareTermQT::Equal),
            ("display", 1) => ClauseType::Display,
            ("duplicate_term", 2) => ClauseType::DuplicateTerm,
            ("==", 2) => ClauseType::Eq,
            ("functor", 3) => ClauseType::Functor,
            ("ground", 1) => ClauseType::Ground,
            ("is", 2) => ClauseType::Is,
            ("\\==", 2) => ClauseType::NotEq,
            ("setup_call_cleanup", 3) => ClauseType::SetupCallCleanup,
            ("throw", 1) => ClauseType::Throw,
            _ => if let Some(fixity) = fixity {
                ClauseType::Op(name, fixity)
            } else {
                ClauseType::Named(name)
            }
        }
    }
}

impl From<InlinedClauseType> for ClauseType {
    fn from(inlined_ct: InlinedClauseType) -> Self {
        ClauseType::Inlined(inlined_ct)
    }
}

#[derive(Clone)]
pub enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(Level, &'a Cell<RegType>, ClauseType, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, Rc<Var>)
}

impl<'a> TermRef<'a> {
    pub fn level(self) -> Level {
        match self {
            TermRef::AnonVar(lvl)
          | TermRef::Cons(lvl, ..)
          | TermRef::Constant(lvl, ..)
          | TermRef::Var(lvl, ..)
          | TermRef::Clause(lvl, ..) => lvl
        }
    }
}

pub enum ChoiceInstruction {
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

pub enum CutInstruction {
    Cut(RegType),
    GetLevel(RegType),
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

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Number) -> Option<Ordering> {
        match NumberPair::from(self.clone(), other.clone()) {
            NumberPair::Integer(n1, n2) =>
                Some(n1.cmp(&n2)),
            NumberPair::Float(n1, n2) =>
                Some(n1.cmp(&n2)),
            NumberPair::Rational(n1, n2) =>
                Some(n1.cmp(&n2))
        }
    }
}

impl Ord for Number {
    fn cmp(&self, other: &Number) -> Ordering {
        match NumberPair::from(self.clone(), other.clone()) {
            NumberPair::Integer(n1, n2) =>
                n1.cmp(&n2),
            NumberPair::Float(n1, n2) =>
                n1.cmp(&n2),
            NumberPair::Rational(n1, n2) =>
                n1.cmp(&n2)
        }
    }
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

pub enum NumberPair {
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

    pub fn from(n1: Number, n2: Number) -> NumberPair
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
    DefaultRetryMeElse(usize),
    DefaultTrustMe,
    DefaultSetCutPoint(RegType),
    DynamicCompareNumber(CompareNumberQT),
    EraseBall,
    Fail,
    GetArgCall,
    GetArgExecute,
    GetBall,
    GetCurrentBlock,
    GetCutPoint(RegType),
    InferenceLevel(RegType, RegType),
    InstallCleaner,
    InstallInferenceCounter(RegType, RegType, RegType),
    InstallNewBlock,
    InternalCallN,
    IsAtom(RegType),
    IsAtomic(RegType),
    IsCompound(RegType),
    IsFloat(RegType),
    IsInteger(RegType),
    IsNonVar(RegType),
    IsRational(RegType),
    IsString(RegType),
    IsVar(RegType),
    RemoveCallPolicyCheck,
    RemoveInferenceCounter(RegType, RegType),
    ResetBlock,
    RestoreCutPolicy,
    SetBall,
    SetCutPoint(RegType),
    Succeed,
    Unify,
    UnwindStack
}

#[derive(Clone)]
pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    ArgCall,
    ArgExecute,
    Call(ClauseName, usize, usize), // name, arity, perm_vars after threshold.
    CallN(usize), // arity.
    CatchCall,
    CatchExecute,
    CheckCpExecute,
    CompareCall,
    CompareExecute,
    CompareTermCall(CompareTermQT),
    CompareTermExecute(CompareTermQT),
    DisplayCall,
    DisplayExecute,
    Deallocate,
    DuplicateTermCall,
    DuplicateTermExecute,
    DynamicIs,
    EqCall,
    EqExecute,
    Execute(ClauseName, usize),
    ExecuteN(usize),
    FunctorCall,
    FunctorExecute,
    GetCleanerCall,
    GotoCall(usize, usize),    // p, arity.
    GotoExecute(usize, usize), // p, arity.
    GroundCall,
    GroundExecute,
    JmpByCall(usize, usize),    // arity, global_offset.
    JmpByExecute(usize, usize),
    IsCall(RegType, ArithmeticTerm),
    IsExecute(RegType, ArithmeticTerm),
    NotEqCall,
    NotEqExecute,
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
            &ControlInstruction::CompareTermCall(..) => true,
            &ControlInstruction::CompareTermExecute(..) => true,
            &ControlInstruction::DisplayCall => true,
            &ControlInstruction::DisplayExecute => true,
            &ControlInstruction::DuplicateTermCall => true,
            &ControlInstruction::DuplicateTermExecute => true,
            &ControlInstruction::DynamicIs => true,
            &ControlInstruction::EqCall => true,
            &ControlInstruction::EqExecute => true,
            &ControlInstruction::Execute(_, _)  => true,
            &ControlInstruction::CallN(_) => true,
            &ControlInstruction::ExecuteN(_) => true,
            &ControlInstruction::FunctorCall => true,
            &ControlInstruction::FunctorExecute => true,
            &ControlInstruction::NotEqCall => true,
            &ControlInstruction::NotEqExecute => true,
            &ControlInstruction::ThrowCall => true,
            &ControlInstruction::ThrowExecute => true,
            &ControlInstruction::GetCleanerCall => true,
            &ControlInstruction::GotoCall(..) => true,
            &ControlInstruction::GotoExecute(..) => true,
            &ControlInstruction::GroundCall => true,
            &ControlInstruction::GroundExecute => true,
            &ControlInstruction::IsCall(..) => true,
            &ControlInstruction::IsExecute(..) => true,
            &ControlInstruction::JmpByCall(..) => true,
            &ControlInstruction::JmpByExecute(..) => true,
            &ControlInstruction::CompareCall => true,
            &ControlInstruction::CompareExecute => true,
            _ => false
        }
    }
}

pub enum IndexingInstruction {
    SwitchOnTerm(usize, usize, usize, usize),
    SwitchOnConstant(usize, HashMap<Constant, usize>),
    SwitchOnStructure(usize, HashMap<(ClauseName, usize), usize>)
}

impl From<IndexingInstruction> for Line {
    fn from(i: IndexingInstruction) -> Self {
        Line::Indexing(i)
    }
}

pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetStructure(ClauseType, usize, RegType),
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
    PutStructure(ClauseType, usize, RegType),
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

#[derive(Clone, PartialEq, Eq, Hash)]
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
    NamedStr(usize, ClauseName, Option<Fixity>), // arity, name, fixity if it has one.
}

impl HeapCellValue {
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            &HeapCellValue::Addr(ref a)    => a.clone(),
            &HeapCellValue::NamedStr(_, _, _) => Addr::Str(focus)
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum CodePtr {
    DirEntry(usize, ClauseName), // offset, resident module name.
    TopLevel(usize, usize) // chunk_num, offset.
}

impl CodePtr {    
    pub fn module_name(&self) -> ClauseName {
        match self {
            &CodePtr::DirEntry(_, ref name) => name.clone(),
            _ => ClauseName::BuiltIn("user")
        }
    }
}

impl PartialOrd<CodePtr> for CodePtr {
    fn partial_cmp(&self, other: &CodePtr) -> Option<Ordering> {
        match (self, other) {
            (&CodePtr::DirEntry(p1, _), &CodePtr::DirEntry(p2, _)) =>
                p1.partial_cmp(&p2),
            (&CodePtr::DirEntry(..), &CodePtr::TopLevel(_, _)) =>
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
            CodePtr::DirEntry(p, name) => CodePtr::DirEntry(p + rhs, name),
            CodePtr::TopLevel(cn, p) => CodePtr::TopLevel(cn, p + rhs)
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::DirEntry(ref mut p, _) |
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
    pub fn to_constant(self) -> Option<Constant> {
        match self {
            Term::Constant(_, c) => Some(c),
            _ => None
        }
    }

    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &Term::Clause(_, _, ref terms, _) =>
                terms.first().map(|bt| bt.as_ref()),
            _ => None
        }
    }

    pub fn name(&self) -> Option<ClauseName> {
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
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(Level, usize, &'a Cell<RegType>, ClauseType, &'a Vec<Box<Term>>),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Var(Level, &'a Cell<VarReg>, Rc<Var>)
}

impl<'a> TermIterState<'a> {
    pub fn subterm_to_state(lvl: Level, term: &'a Term) -> TermIterState<'a> {
        match term {
            &Term::AnonVar =>
                TermIterState::AnonVar(lvl),
            &Term::Clause(ref cell, ref name, ref subterms, fixity) => {
                let ct = if let Some(fixity) = fixity {
                    ClauseType::Op(name.clone(), fixity)
                } else {
                    ClauseType::Named(name.clone())
                };

                TermIterState::Clause(lvl, 0, cell, ct, subterms)
            },
            &Term::Cons(ref cell, ref head, ref tail) =>
                TermIterState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref()),
            &Term::Constant(ref cell, ref constant) =>
                TermIterState::Constant(lvl, cell, constant),
            &Term::Var(ref cell, ref var) =>
                TermIterState::Var(lvl, cell, (*var).clone())
        }
    }
}
