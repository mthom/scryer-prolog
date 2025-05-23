use crate::arena::*;
use crate::atom_table::*;
use crate::instructions::*;
use crate::functor_macro::*;
use crate::machine::disjuncts::VarData;
use crate::machine::heap::*;
// use crate::machine::loader::PredicateQueue;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::parser::ast::*;
use crate::parser::dashu::{Integer, Rational};
use crate::parser::parser::CompositeOpDesc;
use crate::types::*;

use dashu::base::Signed;
use fxhash::FxBuildHasher;

use indexmap::{IndexMap, IndexSet};
use ordered_float::OrderedFloat;

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt;
use std::ops::{AddAssign, Deref, DerefMut};
use std::path::PathBuf;

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

#[derive(Debug, Clone, Copy)]
pub enum VarComparison {
    Indistinct,
    Distinct,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Deep,
    Root,
    Shallow,
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
    pub fn chunk_type(&self) -> ChunkType {
        match self {
            GenContext::Head    => ChunkType::Head,
            GenContext::Mid(_)  => ChunkType::Mid,
            GenContext::Last(_) => ChunkType::Last,
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

#[derive(Debug)]
pub enum ChunkedTerms {
    Branch(Vec<VecDeque<ChunkedTerms>>),
    Chunk { chunk_num: usize, terms: VecDeque<QueryTerm> },
}

#[derive(Debug)]
pub struct ChunkedTermVec {
    pub chunk_vec: VecDeque<ChunkedTerms>,
    pub current_chunk_num: usize,
    pub current_chunk_type: ChunkType,
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
            current_chunk_num: 0,
            current_chunk_type: ChunkType::Mid,
        }
    }

    pub fn reserve_branch(&mut self, capacity: usize) {
        self.chunk_vec
            .push_back(ChunkedTerms::Branch(Vec::with_capacity(capacity)));
    }

    pub fn try_set_chunk_at_inlined_boundary(&mut self) -> bool {
        if self.current_chunk_type.is_last() {
            self.current_chunk_type = ChunkType::Mid;
            self.current_chunk_num += 1;
            true
        } else {
            false
        }
    }

    pub fn try_set_chunk_at_call_boundary(&mut self) -> bool {
        if self.current_chunk_type.is_last() {
            self.current_chunk_num += 1;
            true
        } else {
            self.current_chunk_type = ChunkType::Last;
            false
        }
    }

    #[inline]
    pub fn add_chunk(&mut self) {
        let chunk = ChunkedTerms::Chunk {
            chunk_num: self.current_chunk_num,
            terms: VecDeque::from(vec![]),
        };
        self.chunk_vec.push_back(chunk);
    }

    pub fn current_gen_context(&self) -> GenContext {
        self.current_chunk_type.to_gen_context(self.current_chunk_num)
    }

    pub fn push_chunk_term(&mut self, term: QueryTerm) {
        match self.chunk_vec.back_mut() {
            Some(ChunkedTerms::Branch(_)) => {
                let chunk = ChunkedTerms::Chunk {
                    chunk_num: self.current_chunk_num,
                    terms: VecDeque::from(vec![term]),
                };

                self.chunk_vec.push_back(chunk);
            }
            Some(ChunkedTerms::Chunk { terms, .. }) => {
                terms.push_back(term);
            }
            None => {
                let chunk = ChunkedTerms::Chunk {
                    chunk_num: self.current_chunk_num,
                    terms: VecDeque::from(vec![term]),
                };

                self.chunk_vec.push_back(chunk);
            }
        }
    }
}

#[derive(Debug)]
pub struct QueryClause {
    pub ct: ClauseType,
    pub term: HeapCellValue,
    pub code_indices: IndexMap<usize, CodeIndex, FxBuildHasher>,
    pub call_policy: CallPolicy,
}

impl QueryClause {
    pub fn term_loc(&self) -> usize {
        self.term.get_value() as usize
    }
}

#[derive(Debug)]
pub enum QueryTerm {
    Clause(QueryClause),
    Fail,
    Succeed,
    LocalCut { var_num: usize, cut_prev: bool },
    GlobalCut(usize), // var_num
    GetCutPoint { var_num: usize, prev_b: bool },
    GetLevel(usize), // var_num
}

#[derive(Clone, Copy, Debug)]
pub struct Fact {
    pub(crate) term_loc: usize,
}

#[derive(Debug)]
pub struct Rule {
    pub(crate) term_loc: usize,
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

pub fn clause_predicate_key_from_heap(
    heap: &impl SizedHeap,
    value: HeapCellValue,
) -> Option<PredicateKey> {
    read_heap_cell!(value,
        (HeapCellValueTag::Atom, (name, _arity)) => {
            debug_assert_eq!(_arity, 0);
            Some((name, 0))
        }
        _ => {
            if value.is_ref() {
                clause_predicate_key(heap, value.get_value() as usize)
            } else {
                None
            }
        }
    )
}

pub fn clause_predicate_key(heap: &impl SizedHeap, term_loc: usize) -> Option<PredicateKey> {
    let key_opt = term_predicate_key(heap, term_loc);

    if Some((atom!(":-"), 2)) == key_opt {
        term_nth_arg(heap, term_loc, 1).and_then(|arg_loc| {
            term_predicate_key(heap, arg_loc)
        })
    } else {
        key_opt
    }
}

#[derive(Debug)]
pub enum PredicateClause {
    Fact(Fact, VarData),
    Rule(Rule, VarData),
}

impl PredicateClause {
    pub(crate) fn args<'a>(&self, heap: &'a Heap) -> Option<std::ops::RangeInclusive<usize>> {
        let focus = match self {
            &PredicateClause::Fact(Fact { term_loc }, _) => term_loc,
            &PredicateClause::Rule(Rule { term_loc, .. }, _) => {
                term_nth_arg(heap, term_loc, 1).unwrap()
            }
        };

        let arity = clause_predicate_key(heap, focus)
            .map(|(_name, arity)| arity)
            .unwrap_or(0);

        read_heap_cell!(heap_bound_store(heap, heap_bound_deref(heap, heap[focus])),
            (HeapCellValueTag::Str, s) => {
                Some(s+1 ..= s+arity)
            }
            _ => {
                None
            }
        )
    }
}

#[derive(Debug)]
pub struct ClauseSpan {
    pub left: usize,
    pub right: usize,
    pub instantiated_arg_index: usize,
}

#[derive(Debug, Clone)]
pub enum ModuleSource {
    Library(Atom),
    File(Atom),
}

impl ModuleSource {
    pub(crate) fn as_functor_stub(&self) -> MachineStub {
        match self {
            &ModuleSource::Library(name) => {
                functor!(atom!("library"), [atom_as_cell(name)])
            }
            &ModuleSource::File(name) => {
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

#[derive(Debug, Clone)]
pub enum Declaration {
    Dynamic(Atom, usize),
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

        if spec.is_infix() {
            if let Some(desc) = existing_desc {
                if desc.post > 0 {
                    return Err(SessionError::OpIsInfixAndPostFix(name));
                }
            }
        }

        if spec.is_postfix() {
            if let Some(desc) = existing_desc {
                if desc.inf > 0 {
                    return Err(SessionError::OpIsInfixAndPostFix(name));
                }
            }
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
    if let Some(ref op_desc) = &op_desc {
        if op_desc.arity() != arity {
            /* it's possible to extend operator functors with
             * additional terms. When that happens,
             * void the op_spec by returning None. */
            return None;
        }
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
            if let Some(op_desc) = op_dir.get(&(name, Fixity::Pre)) {
                if op_desc.get_prec() > 0 {
                    return Some(*op_desc);
                }
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
            Number::Float(fl) => write!(f, "{}", fl),
            Number::Integer(n) => write!(f, "{}", n),
            Number::Rational(r) => write!(f, "{}", r),
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
        Number::Fixnum(Fixnum::build_with(value as i64))
    }
}

impl ArenaFrom<i32> for Number {
    #[inline]
    fn arena_from(value: i32, _arena: &mut Arena) -> Number {
        Number::Fixnum(Fixnum::build_with(value as i64))
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
        fixnum!(value as i64, arena)
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
            Number::Float(OrderedFloat(n)) => HeapCellValue::from(float_alloc!(n, arena)),
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
            Number::Integer(ref n) => n.is_positive(),
            Number::Float(f) => f.is_sign_positive(),
            Number::Rational(ref r) => r.is_positive(),
        }
    }

    #[inline]
    pub(crate) fn is_negative(&self) -> bool {
        match self {
            Number::Fixnum(n) => n.get_num() < 0,
            Number::Integer(ref n) => n.is_negative(),
            &Number::Float(OrderedFloat(f)) => f.is_sign_negative() && f != -0f64,
            Number::Rational(ref r) => r.is_negative(),
        }
    }

    #[inline]
    pub(crate) fn is_zero(&self) -> bool {
        match self {
            Number::Fixnum(n) => n.get_num() == 0,
            Number::Integer(ref n) => n.is_zero(),
            &Number::Float(OrderedFloat(f)) => f == 0.0 || f == -0.0,
            Number::Rational(ref r) => r.is_zero(),
        }
    }

    #[inline]
    pub(crate) fn is_integer(&self) -> bool {
        matches!(self, Number::Fixnum(_) | Number::Integer(_))
    }
}

#[derive(Debug, Clone)]
pub(crate) enum OptArgIndexKey {
    Literal(usize, usize, HeapCellValue, Vec<HeapCellValue>), // index, IndexingCode location, opt arg, alternatives
    List(usize, usize),                                       // index, IndexingCode location
    None,
    Structure(usize, usize, Atom, usize), // index, IndexingCode location, name, arity
}

impl OptArgIndexKey {
    #[inline]
    pub(crate) fn take(&mut self) -> OptArgIndexKey {
        std::mem::replace(self, OptArgIndexKey::None)
    }

    #[inline]
    pub(crate) fn arg_num(&self) -> usize {
        match &self {
            OptArgIndexKey::Literal(arg_num, ..)
            | OptArgIndexKey::Structure(arg_num, ..)
            | OptArgIndexKey::List(arg_num, _) => {
                // these are always at least 1.
                *arg_num
            }
            OptArgIndexKey::None => 0,
        }
    }

    #[inline]
    pub(crate) fn is_some(&self) -> bool {
        self.switch_on_term_loc().is_some()
    }

    #[inline]
    pub(crate) fn switch_on_term_loc(&self) -> Option<usize> {
        match &self {
            OptArgIndexKey::Literal(_, loc, ..)
            | OptArgIndexKey::Structure(_, loc, ..)
            | OptArgIndexKey::List(_, loc) => Some(*loc),
            OptArgIndexKey::None => None,
        }
    }

    #[inline]
    pub(crate) fn set_switch_on_term_loc(&mut self, value: usize) {
        match self {
            OptArgIndexKey::Literal(_, ref mut loc, ..)
            | OptArgIndexKey::Structure(_, ref mut loc, ..)
            | OptArgIndexKey::List(_, ref mut loc) => {
                *loc = value;
            }
            OptArgIndexKey::None => {}
        }
    }
}

impl AddAssign<usize> for OptArgIndexKey {
    #[inline]
    fn add_assign(&mut self, n: usize) {
        match self {
            OptArgIndexKey::Literal(_, ref mut o, ..)
            | OptArgIndexKey::List(_, ref mut o)
            | OptArgIndexKey::Structure(_, ref mut o, ..) => {
                *o += n;
            }
            OptArgIndexKey::None => {}
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ClauseIndexInfo {
    pub(crate) clause_start: usize,
    pub(crate) opt_arg_index_key: OptArgIndexKey,
}

impl ClauseIndexInfo {
    #[inline]
    pub(crate) fn new(clause_start: usize) -> Self {
        Self {
            clause_start,
            opt_arg_index_key: OptArgIndexKey::None,
            // index_locs: vec![],
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

#[derive(Clone, Debug)]
pub(crate) struct LocalPredicateSkeleton {
    pub(crate) is_discontiguous: bool,
    pub(crate) is_dynamic: bool,
    pub(crate) is_multifile: bool,
    pub(crate) clause_clause_locs: VecDeque<usize>,
    pub(crate) clause_assert_margin: usize,
    pub(crate) retracted_dynamic_clauses: Option<Vec<ClauseIndexInfo>>, // always None if non-dynamic.
}

impl LocalPredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            is_discontiguous: false,
            is_dynamic: false,
            is_multifile: false,
            clause_clause_locs: VecDeque::new(),
            clause_assert_margin: 0,
            retracted_dynamic_clauses: Some(vec![]),
        }
    }

    #[inline]
    pub(crate) fn predicate_info(&self) -> PredicateInfo {
        PredicateInfo {
            is_extensible: true,
            is_discontiguous: self.is_discontiguous,
            is_dynamic: self.is_dynamic,
            is_multifile: self.is_multifile,
            has_clauses: !self.clause_clause_locs.is_empty(),
        }
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        self.clause_clause_locs.clear();
        self.clause_assert_margin = 0;
    }

    #[inline]
    pub(crate) fn add_retracted_dynamic_clause_info(&mut self, clause_info: ClauseIndexInfo) {
        debug_assert!(self.is_dynamic);

        if self.retracted_dynamic_clauses.is_none() {
            self.retracted_dynamic_clauses = Some(vec![]);
        }

        self.retracted_dynamic_clauses
            .as_mut()
            .unwrap()
            .push(clause_info);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PredicateSkeleton {
    pub(crate) core: LocalPredicateSkeleton,
    pub(crate) clauses: VecDeque<ClauseIndexInfo>,
}

impl PredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        PredicateSkeleton {
            core: LocalPredicateSkeleton::new(),
            clauses: VecDeque::new(),
        }
    }

    #[inline]
    pub(crate) fn predicate_info(&self) -> PredicateInfo {
        PredicateInfo {
            is_extensible: true,
            is_discontiguous: self.core.is_discontiguous,
            is_dynamic: self.core.is_dynamic,
            is_multifile: self.core.is_multifile,
            has_clauses: !self.clauses.is_empty(),
        }
    }

    pub(crate) fn target_pos_of_clause_clause_loc(
        &mut self,
        clause_clause_loc: usize,
    ) -> Option<usize> {
        let search_result = self.core.clause_clause_locs.make_contiguous()
            [0..self.core.clause_assert_margin]
            .binary_search_by(|loc| clause_clause_loc.cmp(loc));

        match search_result {
            Ok(loc) => Some(loc),
            Err(_) => self.core.clause_clause_locs.make_contiguous()
                [self.core.clause_assert_margin..]
                .binary_search_by(|loc| loc.cmp(&clause_clause_loc))
                .map(|loc| loc + self.core.clause_assert_margin)
                .ok(),
        }
    }
}
