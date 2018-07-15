use prolog::num::bigint::BigInt;
use prolog::num::{Float, ToPrimitive, Zero};
use prolog::num::rational::Ratio;
use prolog::ordered_float::*;
use prolog::tabled_rc::*;

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::Error as IOError;
use std::ops::{Add, AddAssign, Div, Index, IndexMut, Sub, Mul, Neg};
use std::rc::Rc;
use std::str::Utf8Error;
use std::vec::Vec;

pub type Atom = String;

pub type Var = String;

pub type Specifier = u32;

pub const MAX_ARITY: usize = 63;

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

pub struct Predicate(pub Vec<PredicateClause>);

impl Predicate {
    pub fn clauses(self) -> Vec<PredicateClause> {
        self.0
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

pub type ModuleCodeDir = HashMap<PredicateKey, ModuleCodeIndex>;

pub type CodeDir = HashMap<PredicateKey, CodeIndex>;

pub type TermDir = HashMap<PredicateKey, Predicate>;

pub type ModuleDir = HashMap<ClauseName, Module>;

pub type PredicateKey = (ClauseName, usize); // name, arity.

pub struct ModuleDecl {
    pub name: ClauseName,
    pub exports: Vec<PredicateKey>
}

pub struct Module {
    pub module_decl: ModuleDecl,
    pub code_dir: ModuleCodeDir,
    pub op_dir: OpDir
}

pub fn default_op_dir() -> OpDir {
    let module_name = clause_name!("builtins");
    let mut op_dir = OpDir::new();

    op_dir.insert((clause_name!(":-"), Fixity::In),  (XFX, 1200, module_name.clone()));
    op_dir.insert((clause_name!(":-"), Fixity::Pre), (FX,  1200, module_name.clone()));
    op_dir.insert((clause_name!("?-"), Fixity::Pre), (FX,  1200, module_name.clone()));

    op_dir
}

pub static BUILTINS: &str = include_str!("./lib/builtins.pl");

impl Module {
    pub fn new(module_decl: ModuleDecl) -> Self {
        Module { module_decl,
                 code_dir: ModuleCodeDir::new(),
                 op_dir: default_op_dir() }
    }
}

pub fn as_module_code_dir(code_dir: CodeDir) -> ModuleCodeDir {
    code_dir.into_iter()
        .map(|(k, code_idx)| {
            let (idx, module_name) = code_idx.0.borrow().clone();
            (k, ModuleCodeIndex(idx, module_name))
        })
        .collect()
}

impl SubModuleUser for Module {
    fn op_dir(&mut self) -> &mut OpDir {
        &mut self.op_dir
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: ModuleCodeIndex) {
        self.code_dir.insert((name, arity), idx);
    }
}

pub trait SubModuleUser {
    fn op_dir(&mut self) -> &mut OpDir;
    fn insert_dir_entry(&mut self, ClauseName, usize, ModuleCodeIndex);

    // returns true on successful import.
    fn import_decl(&mut self, name: ClauseName, arity: usize, submodule: &Module) -> bool {
        let name = name.defrock_brackets();
        let mut found_op = false;

        {
            let mut insert_op_dir = |fix| {
                if let Some(op_data) = submodule.op_dir.get(&(name.clone(), fix)) {
                    self.op_dir().insert((name.clone(), fix), op_data.clone());
                    found_op = true;
                }
            };

            if arity == 1 {
                insert_op_dir(Fixity::Pre);
                insert_op_dir(Fixity::Post);
            } else if arity == 2 {
                insert_op_dir(Fixity::In);
            }
        }

        if let Some(code_data) = submodule.code_dir.get(&(name.clone(), arity)) {
            self.insert_dir_entry(name, arity, code_data.clone());
            true
        } else {
            found_op
        }
    }

    fn use_qualified_module(&mut self, submodule: &Module, exports: &Vec<PredicateKey>) -> EvalSession
    {
        for (name, arity) in exports.iter().cloned() {
            if !submodule.module_decl.exports.contains(&(name.clone(), arity)) {
                continue;
            }

            if !self.import_decl(name, arity, submodule) {
                return EvalSession::from(SessionError::ModuleDoesNotContainExport);
            }
        }

        EvalSession::EntrySuccess
    }

    fn use_module(&mut self, submodule: &Module) -> EvalSession {
        for (name, arity) in submodule.module_decl.exports.iter().cloned() {
            if !self.import_decl(name, arity, submodule) {
                return EvalSession::from(SessionError::ModuleDoesNotContainExport);
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
                clauses.0.first().and_then(|ref term| term.name()),
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
                clauses.0.first().map(|t| t.arity()).unwrap_or(0),
            &TopLevel::Query(_) => 0,
            &TopLevel::Rule(Rule { ref head, .. }) => head.1.len()
        }
    }

    pub fn as_predicate(self) -> Result<Predicate, TopLevel> {
        match self {
            TopLevel::Fact(term) => Ok(Predicate(vec![PredicateClause::Fact(term)])),
            TopLevel::Rule(rule) => Ok(Predicate(vec![PredicateClause::Rule(rule)])),
            TopLevel::Predicate(pred) => Ok(pred),
            _ => Err(self)
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

pub enum SessionError {
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
    Error(SessionError),
    InitialQuerySuccess(AllocVarDict, HeapVarDict),
    SubsequentQuerySuccess,
}

impl From<SessionError> for EvalSession {
    fn from(err: SessionError) -> Self {
        EvalSession::Error(err)
    }
}

impl From<ParserError> for SessionError {
    fn from(err: ParserError) -> Self {
        SessionError::ParserError(err)
    }
}

impl From<ParserError> for EvalSession {
    fn from(err: ParserError) -> Self {
        EvalSession::from(SessionError::ParserError(err))
    }
}

pub struct OpDecl(pub usize, pub Specifier, pub ClauseName);

impl OpDecl {
    pub fn submit(&self, module: ClauseName, op_dir: &mut OpDir) -> Result<(), SessionError>
    {
        let (prec, spec, name) = (self.0, self.1, self.2.clone());

        if is_infix!(spec) {
            match op_dir.get(&(name.clone(), Fixity::Post)) {
                Some(_) => return Err(SessionError::OpIsInfixAndPostFix),
                _ => {}
            };
        }

        if is_postfix!(spec) {
            match op_dir.get(&(name.clone(), Fixity::In)) {
                Some(_) => return Err(SessionError::OpIsInfixAndPostFix),
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

#[derive(Debug)]
pub enum ParserError
{
    Arithmetic(ArithmeticError),
    BackQuotedString,
    // BuiltInArityMismatch(&'static str),
    UnexpectedChar(char),
    UnexpectedEOF,
    IO(IOError),
    ExpectedRel,
    InadmissibleFact,
    InadmissibleQueryTerm,
    IncompleteReduction,
    InconsistentEntry,
    InvalidModuleDecl,
    InvalidModuleExport,
    InvalidRuleHead,
    InvalidUseModuleDecl,
    InvalidModuleResolution,
    MissingQuote,
    ParseBigInt,
    ParseFloat,
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

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub enum Fixity {
    In, Post, Pre
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Constant {
    Atom(ClauseName),
    Char(char),
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

#[derive(PartialEq, Eq, Clone)]
pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, ClauseName, Vec<Box<Term>>, Option<Fixity>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Constant(Cell<RegType>, Constant),
    Var(Cell<VarReg>, Rc<Var>)
}

#[derive(Clone, PartialEq)]
pub enum InlinedClauseType {
    CompareNumber(CompareNumberQT, ArithmeticTerm, ArithmeticTerm),
    IsAtom(RegType),
    IsAtomic(RegType),
    IsCompound(RegType),
    IsInteger(RegType),
    IsRational(RegType),
    IsString(RegType),
    IsFloat(RegType),
    IsNonVar(RegType),
    IsVar(RegType),
}

impl InlinedClauseType {
    pub fn name(&self) -> &'static str {
        match self {
            &InlinedClauseType::CompareNumber(qt, ..) => qt.name(),
            &InlinedClauseType::IsAtom(..) => "atom",
            &InlinedClauseType::IsAtomic(..) => "atomic",
            &InlinedClauseType::IsCompound(..) => "compound",
            &InlinedClauseType::IsInteger (..) => "integer",
            &InlinedClauseType::IsRational(..) => "rational",
            &InlinedClauseType::IsString(..) => "string",
            &InlinedClauseType::IsFloat (..) => "float",
            &InlinedClauseType::IsNonVar(..) => "nonvar",
            &InlinedClauseType::IsVar(..) => "var"
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<Self> {
        let r1 = temp_v!(1);
        let r2 = temp_v!(2);

        let a1 = ArithmeticTerm::Reg(r1);
        let a2 = ArithmeticTerm::Reg(r2);

        match (name, arity) {
            (">", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThan, a1, a2)),
            ("<", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThan, a1, a2)),
            (">=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThanOrEqual,a1, a2)),
            ("=<", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThanOrEqual, a1, a2)),
            ("=\\=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::NotEqual, a1, a2)),
            ("=:=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::Equal, a1, a2)),
            ("atom", 1) => Some(InlinedClauseType::IsAtom(r1)),
            ("atomic", 1) => Some(InlinedClauseType::IsAtomic(r1)),
            ("compound", 1) => Some(InlinedClauseType::IsCompound(r1)),
            ("integer", 1) => Some(InlinedClauseType::IsInteger(r1)),
            ("rational", 1) => Some(InlinedClauseType::IsRational(r1)),
            ("string", 1) => Some(InlinedClauseType::IsString(r1)),
            ("float", 1) => Some(InlinedClauseType::IsFloat(r1)),
            ("nonvar", 1) => Some(InlinedClauseType::IsNonVar(r1)),
            ("var", 1) => Some(InlinedClauseType::IsVar(r1)),
            _ => None
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
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

#[derive(Clone, Copy, PartialEq)]
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
    BlockedCut, // a cut which is 'blocked by letters', like the P term in P -> Q.
    UnblockedCut(Cell<VarReg>),
    GetLevelAndUnify(Cell<VarReg>, Rc<Var>),
    Jump(JumpStub)
}

impl QueryTerm {
    pub fn arity(&self) -> usize {
        match self {
            &QueryTerm::Clause(_, _, ref subterms) => subterms.len(),
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => 0,
            &QueryTerm::Jump(ref vars) => vars.len(),
            &QueryTerm::GetLevelAndUnify(..) => 1,
        }
    }
}

pub struct Rule {
    pub head: (ClauseName, Vec<Box<Term>>, QueryTerm),
    pub clauses: Vec<QueryTerm>
}

#[derive(Copy, Clone, PartialEq)]
pub enum SystemClauseType {
    CheckCutPoint,
    GetSCCCleaner,
    InstallSCCCleaner,
    InstallInferenceCounter,
    RemoveCallPolicyCheck,
    RemoveInferenceCounter,
    RestoreCutPolicy,
    SetCutPoint(RegType),
    InferenceLevel,
    CleanUpBlock,
    EraseBall,
    Fail,
    GetBall,
    GetCurrentBlock,
    GetCutPoint,
    InstallNewBlock,
    ResetBlock,
    SetBall,
    SkipMaxList,
    Succeed,
    UnwindStack
}

impl SystemClauseType {
    pub fn fixity(&self) -> Option<Fixity> {
        None
    }

    pub fn name(&self) -> ClauseName {
        match self {
            &SystemClauseType::CheckCutPoint => clause_name!("$check_cp"),
            &SystemClauseType::GetSCCCleaner => clause_name!("$get_scc_cleaner"),
            &SystemClauseType::InstallSCCCleaner => clause_name!("$install_scc_cleaner"),
            &SystemClauseType::InstallInferenceCounter =>
                clause_name!("$install_inference_counter"),
            &SystemClauseType::RemoveCallPolicyCheck =>
                clause_name!("$remove_call_policy_check"),
            &SystemClauseType::RemoveInferenceCounter =>
                clause_name!("$remove_inference_counter"),
            &SystemClauseType::RestoreCutPolicy => clause_name!("$restore_cut_policy"),
            &SystemClauseType::SetCutPoint(_) => clause_name!("$set_cp"),
            &SystemClauseType::InferenceLevel => clause_name!("$inference_level"),
            &SystemClauseType::CleanUpBlock => clause_name!("$clean_up_block"),
            &SystemClauseType::EraseBall => clause_name!("$erase_ball"),
            &SystemClauseType::Fail => clause_name!("$fail"),
            &SystemClauseType::GetBall => clause_name!("$get_ball"),
            &SystemClauseType::GetCutPoint => clause_name!("$get_cp"),
            &SystemClauseType::GetCurrentBlock => clause_name!("$get_current_block"),
            &SystemClauseType::InstallNewBlock => clause_name!("$install_new_block"),
            &SystemClauseType::ResetBlock => clause_name!("$reset_block"),
            &SystemClauseType::SetBall => clause_name!("$set_ball"),
            &SystemClauseType::SkipMaxList => clause_name!("$skip_max_list"),
            &SystemClauseType::Succeed => clause_name!("$succeed"),
            &SystemClauseType::UnwindStack => clause_name!("$unwind_stack"),
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            ("$check_cp", 1) => Some(SystemClauseType::CheckCutPoint),
            ("$get_scc_cleaner", 1) => Some(SystemClauseType::GetSCCCleaner),
            ("$install_scc_cleaner", 2) =>
                Some(SystemClauseType::InstallSCCCleaner),
            ("$install_inference_counter", 3) =>
                Some(SystemClauseType::InstallInferenceCounter),
            ("$remove_call_policy_check", 1) =>
                Some(SystemClauseType::RemoveCallPolicyCheck),
            ("$remove_inference_counter", 1) =>
                Some(SystemClauseType::RemoveInferenceCounter),
            ("$restore_cut_policy", 0) => Some(SystemClauseType::RestoreCutPolicy),
            ("$set_cp", 1) => Some(SystemClauseType::SetCutPoint(temp_v!(1))),
            ("$inference_level", 2) => Some(SystemClauseType::InferenceLevel),
            ("$clean_up_block", 1) => Some(SystemClauseType::CleanUpBlock),
            ("$erase_ball", 0) => Some(SystemClauseType::EraseBall),
            ("$fail", 0) => Some(SystemClauseType::Fail),
            ("$get_ball", 1) => Some(SystemClauseType::GetBall),
            ("$get_current_block", 1) => Some(SystemClauseType::GetCurrentBlock),
            ("$get_cp", 1) => Some(SystemClauseType::GetCutPoint),
            ("$install_new_block", 1) => Some(SystemClauseType::InstallNewBlock),
            ("$reset_block", 1) => Some(SystemClauseType::ResetBlock),
            ("$set_ball", 1) => Some(SystemClauseType::SetBall),
            ("$skip_max_list", 4) => Some(SystemClauseType::SkipMaxList),
            ("$unwind_stack", 0) => Some(SystemClauseType::UnwindStack),
            _ => None
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum BuiltInClauseType {
    AcyclicTerm,
    Arg,
    Compare,
    CompareTerm(CompareTermQT),
    CyclicTerm,
    Writeq,
    DuplicateTerm,
    Eq,
    Functor,
    Ground,
    Is(RegType, ArithmeticTerm),
    KeySort,
    NotEq,
    Sort,
}

#[derive(Clone)]
pub enum ClauseType {
    BuiltIn(BuiltInClauseType),
    CallN,
    Inlined(InlinedClauseType),
    Named(ClauseName, CodeIndex),
    Op(ClauseName, Fixity, CodeIndex),    
    System(SystemClauseType)
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

impl BuiltInClauseType {
    fn fixity(&self) -> Option<Fixity> {
        match self {
            &BuiltInClauseType::Compare | &BuiltInClauseType::CompareTerm(_)
          | &BuiltInClauseType::NotEq   | &BuiltInClauseType::Is(..) | &BuiltInClauseType::Eq
                => Some(Fixity::In),
            _ => None
        }
    }

    pub fn name(&self) -> ClauseName {
        match self {
            &BuiltInClauseType::AcyclicTerm => clause_name!("acyclic_term"),
            &BuiltInClauseType::Arg => clause_name!("arg"),
            &BuiltInClauseType::Compare => clause_name!("compare"),
            &BuiltInClauseType::CompareTerm(qt) => clause_name!(qt.name()),
            &BuiltInClauseType::CyclicTerm => clause_name!("cyclic_term"),
            &BuiltInClauseType::Writeq => clause_name!("writeq"),
            &BuiltInClauseType::DuplicateTerm => clause_name!("duplicate_term"),
            &BuiltInClauseType::Eq => clause_name!("=="),
            &BuiltInClauseType::Functor => clause_name!("functor"),
            &BuiltInClauseType::Ground  => clause_name!("ground"),
            &BuiltInClauseType::Is(..)  => clause_name!("is"),
            &BuiltInClauseType::KeySort => clause_name!("keysort"),
            &BuiltInClauseType::NotEq => clause_name!("\\=="),
            &BuiltInClauseType::Sort => clause_name!("sort"),
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &BuiltInClauseType::AcyclicTerm => 1,
            &BuiltInClauseType::Arg => 3,
            &BuiltInClauseType::Compare => 2,
            &BuiltInClauseType::CompareTerm(_) => 2,
            &BuiltInClauseType::CyclicTerm => 1,
            &BuiltInClauseType::Writeq => 1,
            &BuiltInClauseType::DuplicateTerm => 2,
            &BuiltInClauseType::Eq => 2,
            &BuiltInClauseType::Functor => 3,
            &BuiltInClauseType::Ground  => 1,
            &BuiltInClauseType::Is(..) => 2,
            &BuiltInClauseType::KeySort => 2,
            &BuiltInClauseType::NotEq => 2,
            &BuiltInClauseType::Sort => 2,
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<Self> {
        match (name, arity) {
            ("acyclic_term", 1) => Some(BuiltInClauseType::AcyclicTerm),
            ("arg", 3) => Some(BuiltInClauseType::Arg),
            ("compare", 3) => Some(BuiltInClauseType::Compare),
            ("cyclic_term", 1) => Some(BuiltInClauseType::CyclicTerm),
            ("@>", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThan)),
            ("@<", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::LessThan)),
            ("@>=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThanOrEqual)),
            ("@=<", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::LessThanOrEqual)),
            ("\\=@=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::NotEqual)),
            ("=@=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::Equal)),
            ("writeq", 1) => Some(BuiltInClauseType::Writeq),
            ("duplicate_term", 2) => Some(BuiltInClauseType::DuplicateTerm),
            ("==", 2) => Some(BuiltInClauseType::Eq),
            ("functor", 3) => Some(BuiltInClauseType::Functor),
            ("ground", 1) => Some(BuiltInClauseType::Ground),
            ("is", 2) => Some(BuiltInClauseType::Is(temp_v!(1), ArithmeticTerm::Reg(temp_v!(2)))),
            ("keysort", 2) => Some(BuiltInClauseType::KeySort),
            ("\\==", 2) => Some(BuiltInClauseType::NotEq),
            ("sort", 2) => Some(BuiltInClauseType::Sort),
            _ => None
        }
    }
}

impl ClauseType {
    pub fn fixity(&self) -> Option<Fixity> {
        match self {
            &ClauseType::BuiltIn(ref built_in) => built_in.fixity(),
            &ClauseType::Inlined(InlinedClauseType::CompareNumber(..)) => Some(Fixity::In),
            &ClauseType::Op(_, fixity, _) => Some(fixity),
            &ClauseType::System(ref system) => system.fixity(),
            _ => None
        }
    }

    pub fn name(&self) -> ClauseName {
        match self {
            &ClauseType::CallN => clause_name!("call"),
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
            &ClauseType::Inlined(ref inlined) => clause_name!(inlined.name()),
            &ClauseType::Op(ref name, ..) => name.clone(),
            &ClauseType::Named(ref name, ..) => name.clone(),
            &ClauseType::System(ref system) => system.name(),
        }
    }

    pub fn from(name: ClauseName, arity: usize, fixity: Option<Fixity>) -> Self {
        InlinedClauseType::from(name.as_str(), arity)
            .map(ClauseType::Inlined)
            .unwrap_or_else(|| {
                BuiltInClauseType::from(name.as_str(), arity)
                    .map(ClauseType::BuiltIn)
                    .unwrap_or_else(|| {
                        SystemClauseType::from(name.as_str(), arity)
                            .map(ClauseType::System)
                            .unwrap_or_else(|| {
                                if let Some(fixity) = fixity {
                                    ClauseType::Op(name, fixity, CodeIndex::default())
                                } else if name.as_str() == "call" {
                                    ClauseType::CallN
                                } else {
                                    ClauseType::Named(name, CodeIndex::default())
                                }
                            })
                    })
            })
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

#[derive(Clone)]
pub enum ChoiceInstruction {
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

#[derive(Clone)]
pub enum CutInstruction {
    Cut(RegType),
    GetLevel(RegType),
    GetLevelAndUnify(RegType),
    NeckCut
}

#[derive(Clone)]
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

#[derive(Clone, PartialEq)]
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

#[derive(Clone)]
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

#[derive(Clone)]
pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    CallClause(ClauseType, usize, usize, bool), // name, arity, perm_vars after threshold, last call.
    Deallocate,
    JmpBy(usize, usize, usize, bool), // arity, global_offset, perm_vars after threshold, last call.
    Proceed
}

impl ControlInstruction {
    pub fn is_jump_instr(&self) -> bool {
        match self {
            &ControlInstruction::CallClause(..)  => true,
            &ControlInstruction::JmpBy(..) => true,
            _ => false
        }
    }
}

#[derive(Clone)]
pub enum IndexingInstruction {
    SwitchOnTerm(usize, usize, usize, usize),
    SwitchOnConstant(usize, Rc<HashMap<Constant, usize>>),
    SwitchOnStructure(usize, Rc<HashMap<(ClauseName, usize), usize>>)
}

impl From<IndexingInstruction> for Line {
    fn from(i: IndexingInstruction) -> Self {
        Line::Indexing(i)
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
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

#[derive(Clone)]
pub enum Line {
    Arithmetic(ArithmeticInstruction),
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

impl PartialEq<Ref> for Addr {
    fn eq(&self, r: &Ref) -> bool {
        self.as_var() == Some(*r)
    }
}

// for use in MachineState::bind.
impl PartialOrd<Ref> for Addr {
    fn partial_cmp(&self, r: &Ref) -> Option<Ordering> {
        match self {
            &Addr::StackCell(fr, sc) =>
                match *r {
                    Ref::HeapCell(_) => Some(Ordering::Greater),
                    Ref::StackCell(fr1, sc1) =>
                        if fr1 < fr || (fr1 == fr && sc1 < sc) {
                            Some(Ordering::Greater)
                        } else if fr1 == fr && sc1 == sc {
                            Some(Ordering::Equal)
                        } else {
                            Some(Ordering::Less)
                        }
                },
            &Addr::HeapCell(h) =>
                match r {
                    &Ref::StackCell(..) => Some(Ordering::Less),
                    &Ref::HeapCell(h1) => h.partial_cmp(&h1)
                },
            _ => None
        }
    }
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
            &Addr::StackCell(addr, _) if addr >= e => false,
            _ => true
        }
    }
}

impl Add<usize> for Addr {
    type Output = Addr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            Addr::Lis(a) => Addr::Lis(a + rhs),
            Addr::HeapCell(hc) => Addr::HeapCell(hc + rhs),
            Addr::Str(s) => Addr::Str(s + rhs),
            _ => self
        }
    }
}

impl Sub<usize> for Addr {
    type Output = Addr;

    fn sub(self, rhs: usize) -> Self::Output {
        match self {
            Addr::Lis(a) => Addr::Lis(a - rhs),
            Addr::HeapCell(hc) => Addr::HeapCell(hc - rhs),
            Addr::Str(s) => Addr::Str(s - rhs),
            _ => self
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

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub enum Ref {
    HeapCell(usize),
    StackCell(usize, usize)
}

impl Ref {
    pub fn as_addr(self) -> Addr {
        match self {
            Ref::HeapCell(h)       => Addr::HeapCell(h),
            Ref::StackCell(fr, sc) => Addr::StackCell(fr, sc)
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum HeapCellValue {
    Addr(Addr),
    NamedStr(usize, ClauseName, Option<Fixity>), // arity, name, fixity if it has one.
}

impl HeapCellValue {
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            &HeapCellValue::Addr(ref a) => a.clone(),
            &HeapCellValue::NamedStr(_, _, _) => Addr::Str(focus)
        }
    }
}

#[derive(Clone, Copy,PartialEq)]
pub enum IndexPtr {
    Undefined, Index(usize),
    Module // This is a resolved module call. The module
    // targeted is in the wrapping CodeIndex, and the name is in the ClauseType.
}

#[derive(Clone)]
pub struct CodeIndex(pub Rc<RefCell<(IndexPtr, ClauseName)>>);

impl CodeIndex {
    pub fn is_undefined(&self) -> bool {
        let index_ptr = &self.0.borrow().0;

        if let IndexPtr::Undefined = index_ptr {
            true
        } else {
            false
        }
    }
}

#[derive(Clone)]
pub struct ModuleCodeIndex(pub IndexPtr, pub ClauseName);

impl From<ModuleCodeIndex> for CodeIndex {
    fn from(value: ModuleCodeIndex) -> Self {
        CodeIndex(Rc::new(RefCell::new((value.0, value.1))))
    }
}

impl Default for CodeIndex {
    fn default() -> Self {
        CodeIndex(Rc::new(RefCell::new((IndexPtr::Undefined, clause_name!("")))))
    }
}

impl From<(usize, ClauseName)> for CodeIndex {
    fn from(value: (usize, ClauseName)) -> Self {
        CodeIndex(Rc::new(RefCell::new((IndexPtr::Index(value.0), value.1))))
    }
}

#[derive(Clone, PartialEq)]
pub enum CodePtr {
    BuiltInClause(BuiltInClauseType, LocalCodePtr), // local is the successor call.
    CallN(usize, LocalCodePtr), // arity, local.
    Local(LocalCodePtr)
}

impl CodePtr {
    pub fn local(&self) -> LocalCodePtr {
        match self {
            &CodePtr::BuiltInClause(_, ref local)
          | &CodePtr::CallN(_, ref local)
          | &CodePtr::Local(ref local) => local.clone()
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum LocalCodePtr {
    DirEntry(usize, ClauseName), // offset, resident module name.
    TopLevel(usize, usize) // chunk_num, offset.
}

impl LocalCodePtr {
    pub fn assign_if_local(&mut self, cp: CodePtr) {
        match cp {
            CodePtr::Local(local) => *self = local,
            _ => {}
        }
    }
}

impl PartialOrd<CodePtr> for CodePtr {
    fn partial_cmp(&self, other: &CodePtr) -> Option<Ordering> {
        match (self, other) {
            (&CodePtr::Local(ref l1), &CodePtr::Local(ref l2)) => l1.partial_cmp(l2),
            _ => Some(Ordering::Greater)
        }
    }
}

impl PartialOrd<LocalCodePtr> for LocalCodePtr {
    fn partial_cmp(&self, other: &LocalCodePtr) -> Option<Ordering> {
        match (self, other) {
            (&LocalCodePtr::DirEntry(p1, _), &LocalCodePtr::DirEntry(p2, _)) =>
                p1.partial_cmp(&p2),
            (&LocalCodePtr::DirEntry(..), &LocalCodePtr::TopLevel(_, _)) =>
                Some(Ordering::Less),
            (&LocalCodePtr::TopLevel(_, p1), &LocalCodePtr::TopLevel(_, ref p2)) =>
                p1.partial_cmp(p2),
            _ => Some(Ordering::Greater)
        }
    }
}

impl Default for CodePtr {
    fn default() -> Self {
        CodePtr::Local(LocalCodePtr::default())
    }
}

impl Default for LocalCodePtr {
    fn default() -> Self {
        LocalCodePtr::TopLevel(0, 0)
    }
}

impl Add<usize> for LocalCodePtr {
    type Output = LocalCodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            LocalCodePtr::DirEntry(p, name) => LocalCodePtr::DirEntry(p + rhs, name),
            LocalCodePtr::TopLevel(cn, p) => LocalCodePtr::TopLevel(cn, p + rhs)
        }
    }
}

impl AddAssign<usize> for LocalCodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut LocalCodePtr::DirEntry(ref mut p, _) |
            &mut LocalCodePtr::TopLevel(_, ref mut p) => *p += rhs
        }
    }
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            CodePtr::Local(local) => CodePtr::Local(local + rhs),
            CodePtr::CallN(_, local) | CodePtr::BuiltInClause(_, local) => CodePtr::Local(local + rhs),
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::Local(ref mut local) => *local += rhs,
            _ => *self = CodePtr::Local(self.local() + rhs)
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
                    ClauseType::Op(name.clone(), fixity, CodeIndex::default())
                } else {
                    ClauseType::Named(name.clone(), CodeIndex::default())
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
