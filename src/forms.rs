use crate::arena::*;
use crate::atom_table::*;
use crate::functor_macro::*;
use crate::instructions::*;
use crate::machine::disjuncts::VarData;
use crate::machine::loader::PredicateQueue;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::offset_table::*;
use crate::parser::ast::*;
use crate::parser::dashu::{Integer, Rational};
use crate::parser::parser::CompositeOpDesc;
use crate::types::*;

use dashu::base::Signed;
use fxhash::FxBuildHasher;

use indexmap::{IndexMap, IndexSet};
use num_order::NumOrd;
use ordered_float::OrderedFloat;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::num::NonZero;
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::LazyLock;

pub type PredicateKey = (Atom, usize); // name, arity.

#[derive(Debug, Clone, Copy)]
pub enum AppendOrPrepend {
    Append,
    Prepend,
}

impl AppendOrPrepend {
    #[inline]
    pub(crate) fn is_append(self) -> bool {
        match self {
            AppendOrPrepend::Append => true,
            AppendOrPrepend::Prepend => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Deep,
    Root,
    Shallow,
}

impl Level {
    pub(crate) fn child_level(self) -> Level {
        match self {
            Level::Root => Level::Shallow,
            _ => Level::Deep,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum CallPolicy {
    Default,
    Counted,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GenContext {
    Head,
    Mid(usize),
    Last(usize), // Mid & Last: chunk_num
}

impl GenContext {
    #[inline]
    pub fn chunk_num(&self) -> usize {
        match self {
            GenContext::Head => 0,
            &GenContext::Mid(cn) | &GenContext::Last(cn) => cn,
        }
    }

    #[inline]
    pub fn is_last(self) -> bool {
        matches!(self, GenContext::Last(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChunkType {
    Head,
    Mid,
    Last,
}

#[derive(Debug)]
pub enum RootIterationPolicy {
    Iterated,
    NotIterated,
}

impl RootIterationPolicy {
    #[inline(always)]
    pub fn iterable(&self) -> bool {
        matches!(self, RootIterationPolicy::Iterated)
    }
}

impl ChunkType {
    #[inline(always)]
    pub fn to_gen_context(self, chunk_num: usize) -> GenContext {
        match self {
            ChunkType::Head => GenContext::Head,
            ChunkType::Mid => GenContext::Mid(chunk_num),
            ChunkType::Last => GenContext::Last(chunk_num),
        }
    }

    #[inline(always)]
    pub fn is_last(self) -> bool {
        self == ChunkType::Last
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub(crate) struct BranchNumber(pub(crate) Arc<BranchNumberInner>);

impl Default for BranchNumber {
    fn default() -> Self {
        static DEFAULT_BRANCH_NUMBER: LazyLock<BranchNumber> = LazyLock::new(|| {
            BranchNumber(Arc::new(BranchNumberInner {
                branch_num: Rational::from(0),
                delta: Rational::from(1u64 << 31),
            }))
        });
        DEFAULT_BRANCH_NUMBER.clone()
    }
}

impl Deref for BranchNumber {
    type Target = BranchNumberInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl BranchNumber {
    pub(crate) fn split(&self) -> Self {
        Self(Arc::new(self.0.split()))
    }

    pub(crate) fn incr_by_delta(&self) -> Self {
        Self(Arc::new(self.0.incr_by_delta()))
    }

    pub(crate) fn halve_delta(&self) -> Self {
        Self(Arc::new(self.0.halve_delta()))
    }
}

#[derive(Debug)]
pub(crate) struct BranchNumberInner {
    pub(crate) branch_num: Rational,
    pub(crate) delta: Rational,
}

impl PartialEq for BranchNumberInner {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.branch_num == rhs.branch_num
    }
}

impl Eq for BranchNumberInner {}

impl Hash for BranchNumberInner {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.branch_num.hash(hasher)
    }
}

impl PartialOrd<BranchNumberInner> for BranchNumberInner {
    #[inline]
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        self.branch_num.partial_cmp(&rhs.branch_num)
    }
}

impl BranchNumberInner {
    pub(crate) fn has_as_subbranch(&self, other: &Self) -> bool {
        other.delta <= self.delta
            && other.branch_num >= self.branch_num
            && other.branch_num < &self.branch_num + &self.delta
    }

    pub(crate) fn split(&self) -> BranchNumberInner {
        BranchNumberInner {
            branch_num: self.branch_num.clone() + &self.delta / Rational::from(2),
            delta: &self.delta / Rational::from(4),
        }
    }

    pub(crate) fn incr_by_delta(&self) -> BranchNumberInner {
        BranchNumberInner {
            branch_num: self.branch_num.clone() + &self.delta,
            delta: self.delta.clone(),
        }
    }

    pub(crate) fn halve_delta(&self) -> BranchNumberInner {
        BranchNumberInner {
            branch_num: self.branch_num.clone(),
            delta: &self.delta / Rational::from(2),
        }
    }
}

#[derive(Debug)]
pub enum ChunkedTerms {
    Branch {
        branch_nums: Vec<BranchNumber>,
        arms: Vec<VecDeque<ChunkedTerms>>,
    },
    Chunk {
        terms: VecDeque<QueryTerm>,
    },
}

#[derive(Debug)]
pub struct ChunkedTermVec {
    pub chunk_vec: VecDeque<ChunkedTerms>,
}

impl Deref for ChunkedTermVec {
    type Target = VecDeque<ChunkedTerms>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.chunk_vec
    }
}

impl DerefMut for ChunkedTermVec {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.chunk_vec
    }
}

impl ChunkedTermVec {
    #[allow(clippy::new_without_default)]
    #[inline]
    pub fn new() -> Self {
        Self {
            chunk_vec: VecDeque::new(),
        }
    }

    pub fn reserve_branch(&mut self, capacity: usize) {
        self.chunk_vec.push_back(ChunkedTerms::Branch {
            branch_nums: Vec::with_capacity(capacity),
            arms: Vec::with_capacity(capacity),
        });
    }

    #[inline]
    pub fn add_chunk(&mut self) {
        self.chunk_vec.push_back(ChunkedTerms::Chunk {
            terms: VecDeque::from(vec![]),
        });
    }

    pub fn push_chunk_term(&mut self, term: QueryTerm) {
        match self.chunk_vec.back_mut() {
            Some(ChunkedTerms::Branch { .. }) => {
                let chunk = ChunkedTerms::Chunk {
                    terms: VecDeque::from(vec![term]),
                };

                self.chunk_vec.push_back(chunk);
            }
            Some(ChunkedTerms::Chunk { terms, .. }) => {
                terms.push_back(term);
            }
            None => {
                let chunk = ChunkedTerms::Chunk {
                    terms: VecDeque::from(vec![term]),
                };

                self.chunk_vec.push_back(chunk);
            }
        }
    }
}

#[derive(Debug)]
pub enum QueryTerm {
    // register, clause type, subterms, clause call policy.
    Clause(Cell<RegType>, ClauseType, Vec<Term>, CallPolicy),
    Fail,
    LocalCut { var_num: usize, cut_prev: bool }, // var_num
    GlobalCut(usize),                            // var_num
    GetCutPoint { var_num: usize, prev_b: bool },
    GetLevel(usize), // var_num
}

impl QueryTerm {
    pub(crate) fn arity(&self) -> usize {
        match self {
            QueryTerm::Clause(_, _, subterms, ..) => subterms.len(),
            &QueryTerm::GetLevel(_) | &QueryTerm::GetCutPoint { .. } => 1,
            _ => 0,
        }
    }
}

#[derive(Debug)]
pub struct Fact {
    pub(crate) head: Term,
}

#[derive(Debug)]
pub struct Rule {
    pub(crate) head: (Atom, Vec<Term>),
    pub(crate) clauses: ChunkedTermVec,
}

#[derive(Clone, Debug, Hash)]
pub enum ListingSource {
    DynamicallyGenerated,
    File(Atom, PathBuf), // filename, path
    User,
}

impl ListingSource {
    pub(crate) fn from_file_and_path(filename: Atom, path_buf: PathBuf) -> Self {
        ListingSource::File(filename, path_buf)
    }
}

pub trait ClauseInfo {
    fn is_consistent(&self, clauses: &PredicateQueue) -> bool {
        match clauses.first() {
            Some(cl) => {
                self.name() == ClauseInfo::name(cl) && self.arity() == ClauseInfo::arity(cl)
            }
            None => true,
        }
    }

    fn name(&self) -> Option<Atom>;
    fn arity(&self) -> usize;
}

impl ClauseInfo for PredicateKey {
    #[inline]
    fn name(&self) -> Option<Atom> {
        Some(self.0)
    }

    #[inline]
    fn arity(&self) -> usize {
        self.1
    }
}

impl ClauseInfo for Term {
    fn name(&self) -> Option<Atom> {
        match self {
            Term::Clause(_, name, terms) => {
                match name {
                    atom!(":-") => {
                        match terms.len() {
                            1 => None, // a declaration.
                            2 => terms[0].name(),
                            _ => Some(*name),
                        }
                    }
                    _ => Some(*name), //str_buf),
                }
            }
            Term::Literal(_, Literal::Atom(name)) => Some(*name),
            _ => None,
        }
    }

    fn arity(&self) -> usize {
        match self {
            Term::Clause(_, name, terms) => match &*name.as_str() {
                ":-" => match terms.len() {
                    1 => 0,
                    2 => terms[0].arity(),
                    _ => terms.len(),
                },
                _ => terms.len(),
            },
            _ => 0,
        }
    }
}

impl ClauseInfo for Rule {
    fn name(&self) -> Option<Atom> {
        Some(self.head.0)
    }

    fn arity(&self) -> usize {
        self.head.1.len()
    }
}

impl ClauseInfo for PredicateClause {
    fn name(&self) -> Option<Atom> {
        match self {
            PredicateClause::Fact(term, ..) => term.head.name(),
            PredicateClause::Rule(rule, ..) => rule.name(),
        }
    }

    fn arity(&self) -> usize {
        match self {
            PredicateClause::Fact(term, ..) => term.head.arity(),
            PredicateClause::Rule(rule, ..) => rule.arity(),
        }
    }
}

#[derive(Debug)]
pub enum PredicateClause {
    Fact(Fact, VarData),
    Rule(Rule, VarData),
}

impl PredicateClause {
    pub(crate) fn args(&self) -> &[Term] {
        match self {
            PredicateClause::Fact(term, ..) => match &term.head {
                Term::Clause(_, _, args) => args,
                _ => &[],
            },
            PredicateClause::Rule(rule, ..) => {
                if rule.head.1.is_empty() {
                    &[]
                } else {
                    &rule.head.1
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct ClauseSpan {
    pub left: usize,
    pub right: usize,
    pub instantiated_arg_index: Option<NonZero<usize>>,
}

#[derive(Debug, Clone)]
pub enum ModuleSource {
    Library(Atom),
    File(Atom),
}

impl ModuleSource {
    pub(crate) fn as_functor_stub(&self) -> MachineStub {
        match *self {
            ModuleSource::Library(name) => {
                functor!(atom!("library"), [atom_as_cell(name)])
            }
            ModuleSource::File(name) => {
                functor!(name)
            }
        }
    }
}

#[derive(Clone, Copy, Hash, Debug)]
pub enum MetaSpec {
    Minus,
    Plus,
    Either,
    Colon,
    RequiresExpansionWithArgument(usize),
}

#[derive(Clone, Copy, Debug, Default)]
pub enum IndexingSpec {
    #[default]
    InstOnly,     // +
    NoIndexing,   // -
}

impl IndexingSpec {
    pub fn as_atom(self) -> Atom {
        match self {
            IndexingSpec::InstOnly => atom!("+"),
            IndexingSpec::NoIndexing => atom!("-"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Dynamic(Atom, usize),
    Indexing(Atom, Vec<IndexingSpec>),
    MetaPredicate(Atom, Atom, Vec<MetaSpec>), // module name, name, meta-specs
    Module(ModuleDecl),
    NonCountedBacktracking(Atom, usize), // name, arity
    Op(OpDecl),
    UseModule(ModuleSource),
    UseQualifiedModule(ModuleSource, IndexSet<ModuleExport>),
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub struct OpDecl {
    pub(crate) op_desc: OpDesc,
    pub(crate) name: Atom,
}

impl OpDecl {
    #[inline]
    pub(crate) fn new(op_desc: OpDesc, name: Atom) -> Self {
        Self { op_desc, name }
    }

    #[inline]
    pub(crate) fn remove(&mut self, op_dir: &mut OpDir) {
        let prec = self.op_desc.get_prec();
        self.op_desc.set(0, self.op_desc.get_spec());

        self.insert_into_op_dir(op_dir);
        self.op_desc.set(prec, self.op_desc.get_spec());
    }

    pub(crate) fn insert_into_op_dir(&self, op_dir: &mut OpDir) -> Option<OpDesc> {
        let key = (self.name, self.op_desc.get_spec().fixity());

        if let Some(cell) = op_dir.get_mut(&key) {
            let (old_prec, old_spec) = cell.get();
            cell.set(self.op_desc.get_prec(), self.op_desc.get_spec());
            return Some(OpDesc::build_with(old_prec, old_spec));
        }

        op_dir.insert(key, self.op_desc)
    }

    pub(crate) fn submit(
        &self,
        existing_desc: Option<CompositeOpDesc>,
        op_dir: &mut OpDir,
    ) -> Result<(), SessionError> {
        let (spec, name) = (self.op_desc.get_spec(), self.name);

        if spec.is_infix()
            && let Some(desc) = existing_desc
            && desc.post > 0
        {
            return Err(SessionError::OpIsInfixAndPostFix(name));
        }

        if spec.is_postfix()
            && let Some(desc) = existing_desc
            && desc.inf > 0
        {
            return Err(SessionError::OpIsInfixAndPostFix(name));
        }

        self.insert_into_op_dir(op_dir);
        Ok(())
    }
}

#[derive(Debug)]
pub enum AtomOrString {
    Atom(Atom),
    String(String),
}

impl AtomOrString {
    #[inline]
    pub fn as_atom(&self, atom_tbl: &AtomTable) -> Atom {
        match self {
            &AtomOrString::Atom(atom) => atom,
            AtomOrString::String(string) => AtomTable::build_with(atom_tbl, string),
        }
    }

    #[inline]
    pub fn as_str(&self) -> AtomString<'_> {
        match self {
            AtomOrString::Atom(atom) if atom == &atom!("[]") => AtomString::Static(""),
            AtomOrString::Atom(atom) => atom.as_str(),
            AtomOrString::String(string) => AtomString::Static(string.as_str()),
        }
    }
}

impl From<AtomOrString> for String {
    fn from(val: AtomOrString) -> Self {
        match val {
            AtomOrString::Atom(atom) => atom.as_str().to_owned(),
            AtomOrString::String(string) => string,
        }
    }
}

pub(crate) fn fetch_atom_op_spec(
    name: Atom,
    spec: Option<OpDesc>,
    op_dir: &OpDir,
) -> Option<OpDesc> {
    fetch_op_spec_from_existing(name, 2, spec, op_dir)
        .or_else(|| fetch_op_spec_from_existing(name, 1, spec, op_dir))
}

pub(crate) fn fetch_op_spec_from_existing(
    name: Atom,
    arity: usize,
    op_desc: Option<OpDesc>,
    op_dir: &OpDir,
) -> Option<OpDesc> {
    if let Some(op_desc) = &op_desc
        && op_desc.arity() != arity
    {
        /* it's possible to extend operator functors with
         * additional terms. When that happens,
         * void the op_spec by returning None. */
        return None;
    }

    op_desc.or_else(|| fetch_op_spec(name, arity, op_dir))
}

pub(crate) fn fetch_op_spec(name: Atom, arity: usize, op_dir: &OpDir) -> Option<OpDesc> {
    match arity {
        2 => op_dir.get(&(name, Fixity::In)).and_then(|op_desc| {
            if op_desc.get_prec() > 0 {
                Some(*op_desc)
            } else {
                None
            }
        }),
        1 => {
            if let Some(op_desc) = op_dir.get(&(name, Fixity::Pre))
                && op_desc.get_prec() > 0
            {
                return Some(*op_desc);
            }

            op_dir.get(&(name, Fixity::Post)).and_then(|op_desc| {
                if op_desc.get_prec() > 0 {
                    Some(*op_desc)
                } else {
                    None
                }
            })
        }
        0 => fetch_atom_op_spec(name, None, op_dir),
        _ => None,
    }
}

pub(crate) type ModuleDir = IndexMap<Atom, Module, FxBuildHasher>;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum ModuleExport {
    OpDecl(OpDecl),
    PredicateKey(PredicateKey),
}

#[derive(Debug, Clone)]
pub struct ModuleDecl {
    pub(crate) name: Atom,
    pub(crate) exports: Vec<ModuleExport>,
}

#[derive(Debug)]
pub struct Module {
    pub(crate) module_decl: ModuleDecl,
    pub(crate) code_dir: CodeDir,
    pub(crate) op_dir: OpDir,
    pub(crate) meta_predicates: MetaPredicateDir,
    pub(crate) extensible_predicates: ExtensiblePredicates,
    pub(crate) local_extensible_predicates: LocalExtensiblePredicates,
    pub(crate) listing_src: ListingSource,
    pub(super) indexing_specs: IndexingSpecDir,
}

// Module's and related types are defined in forms.
impl Module {
    pub(crate) fn new(module_decl: ModuleDecl, listing_src: ListingSource) -> Self {
        Module {
            module_decl,
            code_dir: CodeDir::with_hasher(FxBuildHasher::default()),
            op_dir: default_op_dir(),
            meta_predicates: MetaPredicateDir::with_hasher(FxBuildHasher::default()),
            extensible_predicates: ExtensiblePredicates::with_hasher(FxBuildHasher::default()),
            local_extensible_predicates: LocalExtensiblePredicates::with_hasher(
                FxBuildHasher::default(),
            ),
            listing_src,
            indexing_specs: IndexingSpecDir::with_hasher(FxBuildHasher::default()),
        }
    }

    pub(crate) fn new_in_situ(module_decl: ModuleDecl) -> Self {
        Module {
            module_decl,
            code_dir: CodeDir::with_hasher(FxBuildHasher::default()),
            op_dir: OpDir::with_hasher(FxBuildHasher::default()),
            meta_predicates: MetaPredicateDir::with_hasher(FxBuildHasher::default()),
            extensible_predicates: ExtensiblePredicates::with_hasher(FxBuildHasher::default()),
            local_extensible_predicates: LocalExtensiblePredicates::with_hasher(
                FxBuildHasher::default(),
            ),
            listing_src: ListingSource::DynamicallyGenerated,
            indexing_specs: IndexingSpecDir::with_hasher(FxBuildHasher::default()),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Number {
    Float(OrderedFloat<f64>),
    Integer(TypedArenaPtr<Integer>),
    Rational(TypedArenaPtr<Rational>),
    Fixnum(Fixnum),
}

impl Default for Number {
    fn default() -> Self {
        Number::Fixnum(Fixnum::build_with(0))
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Number::Float(fl) => write!(f, "{fl}"),
            Number::Integer(n) => write!(f, "{n}"),
            Number::Rational(r) => write!(f, "{r}"),
            Number::Fixnum(n) => write!(f, "{}", n.get_num()),
        }
    }
}

pub trait ArenaFrom<T> {
    fn arena_from(value: T, arena: &mut Arena) -> Self;
}

impl ArenaFrom<Integer> for Number {
    #[inline]
    fn arena_from(value: Integer, arena: &mut Arena) -> Number {
        Number::Integer(arena_alloc!(value, arena))
    }
}

impl ArenaFrom<Rational> for Number {
    #[inline]
    fn arena_from(value: Rational, arena: &mut Arena) -> Number {
        Number::Rational(arena_alloc!(value, arena))
    }
}

impl ArenaFrom<usize> for Number {
    #[inline]
    fn arena_from(value: usize, arena: &mut Arena) -> Number {
        match i64::try_from(value) {
            Ok(value) => Fixnum::build_with_checked(value)
                .map(Number::Fixnum)
                .unwrap_or_else(|_| Number::Integer(arena_alloc!(Integer::from(value), arena))),
            Err(_) => Number::Integer(arena_alloc!(Integer::from(value), arena)),
        }
    }
}

impl ArenaFrom<u64> for Number {
    #[inline]
    fn arena_from(value: u64, arena: &mut Arena) -> Number {
        match i64::try_from(value) {
            Ok(value) => Fixnum::build_with_checked(value)
                .map(Number::Fixnum)
                .unwrap_or_else(|_| Number::Integer(arena_alloc!(Integer::from(value), arena))),
            Err(_) => Number::Integer(arena_alloc!(Integer::from(value), arena)),
        }
    }
}

impl ArenaFrom<i64> for Number {
    #[inline]
    fn arena_from(value: i64, arena: &mut Arena) -> Number {
        Fixnum::build_with_checked(value)
            .map(Number::Fixnum)
            .unwrap_or_else(|_| Number::Integer(arena_alloc!(Integer::from(value), arena)))
    }
}

impl ArenaFrom<isize> for Number {
    #[inline]
    fn arena_from(value: isize, arena: &mut Arena) -> Number {
        Fixnum::build_with_checked(value as i64)
            .map(Number::Fixnum)
            .unwrap_or_else(|_| Number::Integer(arena_alloc!(Integer::from(value), arena)))
    }
}

impl ArenaFrom<u32> for Number {
    #[inline]
    fn arena_from(value: u32, _arena: &mut Arena) -> Number {
        Number::Fixnum(Fixnum::build_with(value))
    }
}

impl ArenaFrom<i32> for Number {
    #[inline]
    fn arena_from(value: i32, _arena: &mut Arena) -> Number {
        Number::Fixnum(Fixnum::build_with(value))
    }
}

/*
impl ArenaFrom<Number> for Literal {
    #[inline]
    fn arena_from(value: Number, arena: &mut Arena) -> Literal {
        match value {
            Number::Fixnum(n) => Literal::Fixnum(n),
            Number::Integer(n) => Literal::Integer(n),
            Number::Float(OrderedFloat(f)) => Literal::from(float_alloc!(f, arena)),
            Number::Rational(r) => Literal::Rational(r),
        }
    }
}
*/

impl ArenaFrom<u64> for HeapCellValue {
    #[inline]
    fn arena_from(value: u64, arena: &mut Arena) -> HeapCellValue {
        HeapCellValue::from(fixnum!(Literal, value as i64, arena))
    }
}

impl ArenaFrom<usize> for HeapCellValue {
    #[inline]
    fn arena_from(value: usize, arena: &mut Arena) -> HeapCellValue {
        HeapCellValue::arena_from(value as u64, arena)
    }
}

impl ArenaFrom<Number> for HeapCellValue {
    #[inline]
    fn arena_from(value: Number, arena: &mut Arena) -> HeapCellValue {
        match value {
            Number::Fixnum(n) => fixnum_as_cell!(n),
            Number::Integer(n) => typed_arena_ptr_as_cell!(n),
            Number::Float(n) => HeapCellValue::from(arena.f64_tbl.build_with(n)),
            Number::Rational(n) => typed_arena_ptr_as_cell!(n),
        }
    }
}

impl Number {
    pub(crate) fn sign(&self) -> Number {
        match self {
            Number::Float(f) if *f == 0.0 => Number::Float(OrderedFloat(0f64)),
            Number::Float(f) => Number::Float(OrderedFloat(f.signum())),
            _ => {
                if self.is_positive() {
                    if self.is_zero() {
                        Number::Fixnum(Fixnum::build_with(0))
                    } else {
                        Number::Fixnum(Fixnum::build_with(1))
                    }
                } else if self.is_negative() {
                    Number::Fixnum(Fixnum::build_with(-1))
                } else {
                    Number::Fixnum(Fixnum::build_with(0))
                }
            }
        }
    }

    #[inline]
    pub(crate) fn is_positive(&self) -> bool {
        match self {
            Number::Fixnum(n) => n.get_num() > 0,
            Number::Integer(n) => n.is_positive(),
            Number::Float(f) => f.is_sign_positive(),
            Number::Rational(r) => r.is_positive(),
        }
    }

    #[inline]
    pub(crate) fn is_negative(&self) -> bool {
        match self {
            Number::Fixnum(n) => n.get_num() < 0,
            Number::Integer(n) => n.is_negative(),
            &Number::Float(OrderedFloat(f)) => f.is_sign_negative() && f != -0f64,
            Number::Rational(r) => r.is_negative(),
        }
    }

    #[inline]
    pub(crate) fn is_zero(&self) -> bool {
        match self {
            Number::Fixnum(n) => n.get_num() == 0,
            Number::Integer(n) => n.is_zero(),
            &Number::Float(OrderedFloat(f)) => f == 0.0 || f == -0.0,
            Number::Rational(r) => r.is_zero(),
        }
    }

    #[inline]
    pub(crate) fn is_integer(&self) -> bool {
        matches!(self, Number::Fixnum(_) | Number::Integer(_))
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) enum OptArgIndexKey {
    None,
    Literal(HeapCellValue), // opt arg, alternative
    List,
    Structure(Atom, usize), // name, arity
}

impl From<&'_ Term> for OptArgIndexKey {
    fn from(term: &'_ Term) -> OptArgIndexKey {
        match term {
            &Term::Clause(_, atom!("."), ref terms) if terms.len() == 2 => {
                OptArgIndexKey::List
            }
            &Term::Cons(..) | &Term::PartialString(..) | &Term::CompleteString(..) => {
                OptArgIndexKey::List
            }
            &Term::Clause(_, name, ref terms) => {
                OptArgIndexKey::Structure(name, terms.len())
            }
            &Term::Literal(_, constant) => {
                let literal = HeapCellValue::from(constant);
                OptArgIndexKey::Literal(literal)
            }
            &Term::Var(..) | &Term::AnonVar => {
                OptArgIndexKey::None
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct PredicateInfo {
    pub(crate) is_extensible: bool,
    pub(crate) is_discontiguous: bool,
    pub(crate) is_dynamic: bool,
    pub(crate) is_multifile: bool,
    pub(crate) has_clauses: bool,
}

impl PredicateInfo {
    #[inline]
    pub(crate) fn compile_incrementally(&self) -> bool {
        let base = self.is_extensible && self.has_clauses;
        base && (self.is_discontiguous || self.is_multifile)
    }

    #[inline]
    pub(crate) fn must_retract_local_clauses(&self, is_cross_module_clause: bool) -> bool {
        self.is_extensible
            && self.has_clauses
            && !self.is_discontiguous
            && !(self.is_multifile && is_cross_module_clause)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ClauseIndex {
    pub(crate) clause_start: usize, // start of the clause *after* the IndexingLine if one exists & at the choice point if it doesn't.
    pub(crate) index_loc: Option<usize>, // location of IndexingLine. if None, doesn't exist!
}

impl ClauseIndex {
    #[inline]
    pub(crate) fn add_to_index_loc(&mut self, clause_loc: usize) {
        if let &mut Some(index_loc) = &mut self.index_loc {
            self.index_loc = Some(index_loc + clause_loc);
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LocalPredicateSkeleton {
    pub(crate) is_discontiguous: bool,
    pub(crate) is_dynamic: bool,
    pub(crate) is_multifile: bool,
    pub(crate) prepend_append_margin: usize,
    pub(crate) clause_indices: VecDeque<usize>,
}

impl LocalPredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            is_discontiguous: false,
            is_dynamic: false,
            is_multifile: false,
            prepend_append_margin: 0,
            clause_indices: VecDeque::new(),
        }
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        self.clause_indices.clear();
        self.prepend_append_margin = 0;
    }

    #[inline]
    pub(crate) fn predicate_info(&self) -> PredicateInfo {
        PredicateInfo {
            is_extensible: true,
            is_discontiguous: self.is_discontiguous,
            is_dynamic: self.is_dynamic,
            is_multifile: self.is_multifile,
            has_clauses: !self.clause_indices.is_empty(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PredicateSkeleton {
    pub(crate) core: LocalPredicateSkeleton,
    pub(crate) clause_indices: VecDeque<ClauseIndex>, // sorted in clause order, descending/ascending around prepend_append_margin    
}

impl PredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            core: LocalPredicateSkeleton::new(),
            clause_indices: VecDeque::new(),
        }
    }

    pub(crate) fn target_pos_of_clause_clause_loc(
        &mut self,
        clause_index_loc: usize,
    ) -> Option<usize> {
        let search_result = self.core.clause_indices.make_contiguous()
            [0..self.core.prepend_append_margin]
            .binary_search_by(|loc| clause_index_loc.cmp(loc));

        match search_result {
            Ok(loc) => Some(loc),
            Err(_) => self.core.clause_indices.make_contiguous()
                [self.core.prepend_append_margin..]
                .binary_search_by(|loc| loc.cmp(&clause_index_loc))
                .map(|loc| loc + self.core.prepend_append_margin)
                .ok(),
        }
    }
}

impl HeapCellValue {
    // syntactic_hash and syntactic_eq are for hashing and comparing
    // HeapCellValue's as syntactic values shallowly for
    // indexing. particularly, different integer types with overlapping
    // values.
    pub fn syntactic_hash<H: Hasher>(self, f64_tbl: &F64Table, mut hasher: H) -> u64 {
        read_heap_cell!(self,
            (HeapCellValueTag::F64Offset, offset) => {
                f64_tbl.get_entry(offset).hash(&mut hasher);
            }
            (HeapCellValueTag::Fixnum, n) => {
                let n = n.get_num();

                if n.is_negative() {
                    hasher.write_i8(-1);
                }

                hasher.write_u64(n.abs() as u64);
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                hasher.write_u64(name.index);
                hasher.write_usize(arity);
            }
            (HeapCellValueTag::Lis) => {
                hasher.write_u64(atom!(".").index);
                hasher.write_usize(2);
            }
            (HeapCellValueTag::Cons, c) => {
                let signed_int_hasher = |hasher: &mut H, sign, words: &[u64]| {
                    if matches!(sign, dashu::base::Sign::Negative) {
                        hasher.write_i8(-1);
                    }

                    for word in words.iter().copied() {
                        hasher.write_u64(word);
                    }
                };

                match_untyped_arena_ptr!(c,
                   (ArenaHeaderTag::Integer, n) => {
                       let (sign, words) = n.as_sign_words();
                       signed_int_hasher(&mut hasher, sign, words);
                   }
                   (ArenaHeaderTag::Rational, r) => {
                       let (sign, words) = r.numerator().as_sign_words();
                       signed_int_hasher(&mut hasher, sign, words);

                       // ensure a Rational hashes exactly the equivalent integer
                       // if its denominator is 1
                       if !r.denominator().num_eq(&1) {
                           let words = r.denominator().as_words();
                           signed_int_hasher(&mut hasher, dashu::base::Sign::Positive, words);
                       }
                   }
                   _ => {
                       // we shouldn't be hashing pointer-based types like
                       // streams, load states, etc. This hash is meant only
                       // to index syntactic values.
                   }
                )
            }
            _ => {}
        );

        hasher.finish()
    }

    pub fn syntactic_eq(self, f64_tbl: &F64Table, cell_2: HeapCellValue) -> bool {
        read_heap_cell!(self,
            (HeapCellValueTag::F64Offset, offset) => {
                let val_1 = f64_tbl.get_entry(offset);

                read_heap_cell!(cell_2,
                    (HeapCellValueTag::F64Offset, offset) => {
                        let val_2 = f64_tbl.get_entry(offset);
                        val_1 == val_2
                    }
                    _ => {
                        false
                    }
                )
            }
            (HeapCellValueTag::Fixnum, n) => {
                let n = n.get_num();

                match Number::try_from((cell_2, f64_tbl)) {
                    Ok(Number::Integer(bigint)) => bigint.num_eq(&n),
                    Ok(Number::Fixnum(fixnum)) => n.num_eq(&fixnum.get_num()),
                    _ => false,
                }
            }
            (HeapCellValueTag::Atom, (name_1, arity_1)) => {
                read_heap_cell!(cell_2,
                    (HeapCellValueTag::Atom, (name_2, arity_2)) => {
                        name_1.index == name_2.index && arity_1 == arity_2
                    }
                    (HeapCellValueTag::Lis) => {
                        name_1.index == atom!(".").index && arity_1 == 2
                    }
                    _ => {
                        false
                    }
                )
            }
            (HeapCellValueTag::Lis) => {
                read_heap_cell!(cell_2,
                    (HeapCellValueTag::Atom, (name_2, arity_2)) => {
                        atom!(".").index == name_2.index && 2 == arity_2
                    }
                    (HeapCellValueTag::Lis) => {
                        true
                    }
                    _ => {
                        false
                    }
                )
            }
            (HeapCellValueTag::Cons) => {
                Number::try_from((self, f64_tbl)) == Number::try_from((cell_2, f64_tbl))
            }
            _ => {
                false
            }
        )
    }
}
