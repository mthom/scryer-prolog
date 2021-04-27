use prolog_parser::ast::*;
use prolog_parser::parser::OpDesc;
use prolog_parser::{clause_name, is_infix, is_postfix};

use crate::clause_types::*;
use crate::machine::loader::PredicateQueue;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::rug::{Integer, Rational};
use ordered_float::OrderedFloat;

use indexmap::{IndexMap, IndexSet};

use slice_deque::*;

use std::cell::Cell;
use std::ops::AddAssign;
use std::path::PathBuf;
use std::rc::Rc;

pub(crate) type PredicateKey = (ClauseName, usize); // name, arity.

pub(crate) type Predicate = Vec<PredicateClause>;

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub(crate) type JumpStub = Vec<Term>;

#[derive(Debug, Clone)]
pub(crate) enum TopLevel {
    Fact(Term), // Term, line_num, col_num
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule), // Rule, line_num, col_num
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum AppendOrPrepend {
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
pub(crate) enum Level {
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

#[derive(Debug, Clone)]
pub(crate) enum QueryTerm {
    // register, clause type, subterms, use default call policy.
    Clause(Cell<RegType>, ClauseType, Vec<Box<Term>>, bool),
    BlockedCut, // a cut which is 'blocked by letters', like the P term in P -> Q.
    UnblockedCut(Cell<VarReg>),
    GetLevelAndUnify(Cell<VarReg>, Rc<Var>),
    Jump(JumpStub),
}

impl QueryTerm {
    pub(crate) fn set_default_caller(&mut self) {
        match self {
            &mut QueryTerm::Clause(_, _, _, ref mut use_default_cp) => *use_default_cp = true,
            _ => {}
        }
    }

    pub(crate) fn arity(&self) -> usize {
        match self {
            &QueryTerm::Clause(_, _, ref subterms, ..) => subterms.len(),
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => 0,
            &QueryTerm::Jump(ref vars) => vars.len(),
            &QueryTerm::GetLevelAndUnify(..) => 1,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Rule {
    pub(crate) head: (ClauseName, Vec<Box<Term>>, QueryTerm),
    pub(crate) clauses: Vec<QueryTerm>,
}

#[derive(Clone, Debug, Hash)]
pub(crate) enum ListingSource {
    DynamicallyGenerated,
    File(ClauseName, PathBuf), // filename, path
    User,
}

impl ListingSource {
    pub(crate) fn from_file_and_path(filename: ClauseName, path_buf: PathBuf) -> Self {
        ListingSource::File(filename, path_buf)
    }
}

pub(crate) trait ClauseInfo {
    fn is_consistent(&self, clauses: &PredicateQueue) -> bool {
        match clauses.first() {
            Some(cl) => {
                self.name() == ClauseInfo::name(cl) && self.arity() == ClauseInfo::arity(cl)
            }
            None => true,
        }
    }

    fn name(&self) -> Option<ClauseName>;
    fn arity(&self) -> usize;
}

impl ClauseInfo for PredicateKey {
    #[inline]
    fn name(&self) -> Option<ClauseName> {
        Some(self.0.clone())
    }

    #[inline]
    fn arity(&self) -> usize {
        self.1
    }
}

impl ClauseInfo for Term {
    fn name(&self) -> Option<ClauseName> {
        match self {
            Term::Clause(_, ref name, ref terms, _) => {
                match name.as_str() {
                    ":-" => {
                        match terms.len() {
                            1 => None, // a declaration.
                            2 => terms[0].name(),
                            _ => Some(clause_name!(":-")),
                        }
                    }
                    _ => Some(name.clone()),
                }
            }
            Term::Constant(_, Constant::Atom(ref name, _)) => Some(name.clone()),
            _ => None,
        }
    }

    fn arity(&self) -> usize {
        match self {
            Term::Clause(_, ref name, ref terms, _) => match name.as_str() {
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
    fn name(&self) -> Option<ClauseName> {
        Some(self.head.0.clone())
    }

    fn arity(&self) -> usize {
        self.head.1.len()
    }
}

impl ClauseInfo for PredicateClause {
    fn name(&self) -> Option<ClauseName> {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.name(),
            &PredicateClause::Rule(ref rule, ..) => rule.name(),
        }
    }

    fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.arity(),
            &PredicateClause::Rule(ref rule, ..) => rule.arity(),
        }
    }
}

// pub(crate) type CompiledResult = (Predicate, VecDeque<TopLevel>);

#[derive(Debug, Clone)]
pub(crate) enum PredicateClause {
    Fact(Term),
    Rule(Rule),
}

impl PredicateClause {
    // TODO: add this to `Term` in `prolog_parser` like `first_arg`.
    pub(crate) fn args(&self) -> Option<&[Box<Term>]> {
        match *self {
            PredicateClause::Fact(ref term, ..) => match term {
                Term::Clause(_, _, args, _) => Some(&args),
                _ => None,
            },
            PredicateClause::Rule(ref rule, ..) => {
                if rule.head.1.is_empty() {
                    None
                } else {
                    Some(&rule.head.1)
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum ModuleSource {
    Library(ClauseName),
    File(ClauseName),
}

impl ModuleSource {
    pub(crate) fn as_functor_stub(&self) -> MachineStub {
        match self {
            ModuleSource::Library(ref name) => {
                functor!("library", [clause_name(name.clone())])
            }
            ModuleSource::File(ref name) => {
                functor!(clause_name(name.clone()))
            }
        }
    }
}

// pub(crate) type ScopedPredicateKey = (ClauseName, PredicateKey); // module name, predicate indicator.

/*
#[derive(Debug, Clone)]
pub(crate) enum MultiFileIndicator {
    LocalScoped(ClauseName, usize), // name, arity
    ModuleScoped(ScopedPredicateKey),
}
*/

#[derive(Clone, Copy, Hash, Debug)]
pub(crate) enum MetaSpec {
    Minus,
    Plus,
    Either,
    RequiresExpansionWithArgument(usize),
}

#[derive(Debug, Clone)]
pub(crate) enum Declaration {
    Dynamic(ClauseName, usize),
    MetaPredicate(ClauseName, ClauseName, Vec<MetaSpec>), // module name, name, meta-specs
    Module(ModuleDecl),
    NonCountedBacktracking(ClauseName, usize), // name, arity
    Op(OpDecl),
    UseModule(ModuleSource),
    UseQualifiedModule(ModuleSource, IndexSet<ModuleExport>),
}

#[derive(Debug, Clone, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub(crate) struct OpDecl {
    pub(crate) prec: usize,
    pub(crate) spec: Specifier,
    pub(crate) name: ClauseName,
}

impl OpDecl {
    #[inline]
    pub(crate) fn new(prec: usize, spec: Specifier, name: ClauseName) -> Self {
        Self { prec, spec, name }
    }

    #[inline]
    pub(crate) fn remove(&mut self, op_dir: &mut OpDir) {
        let prec = self.prec;
        self.prec = 0;

        self.insert_into_op_dir(op_dir);
        self.prec = prec;
    }

    #[inline]
    pub(crate) fn fixity(&self) -> Fixity {
        match self.spec {
            XFY | XFX | YFX => Fixity::In,
            XF | YF => Fixity::Post,
            FX | FY => Fixity::Pre,
            _ => unreachable!(),
        }
    }

    pub(crate) fn insert_into_op_dir(&self, op_dir: &mut OpDir) -> Option<(usize, Specifier)> {
        let key = (self.name.clone(), self.fixity());

        match op_dir.get(&key) {
            Some(cell) => {
                return Some(cell.shared_op_desc().replace((self.prec, self.spec)));
            }
            None => {}
        }

        op_dir
            .insert(key, OpDirValue::new(self.spec, self.prec))
            .map(|op_dir_value| op_dir_value.shared_op_desc().get())
    }

    pub(crate) fn submit(
        &self,
        existing_desc: Option<OpDesc>,
        op_dir: &mut OpDir,
    ) -> Result<(), SessionError> {
        let (spec, name) = (self.spec, self.name.clone());

        if is_infix!(spec) {
            if let Some(desc) = existing_desc {
                if desc.post > 0 {
                    return Err(SessionError::OpIsInfixAndPostFix(name));
                }
            }
        }

        if is_postfix!(spec) {
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

pub(crate) fn fetch_atom_op_spec(
    name: ClauseName,
    spec: Option<SharedOpDesc>,
    op_dir: &OpDir,
) -> Option<SharedOpDesc> {
    fetch_op_spec_from_existing(name.clone(), 1, spec.clone(), op_dir)
        .or_else(|| fetch_op_spec_from_existing(name, 2, spec, op_dir))
}

pub(crate) fn fetch_op_spec_from_existing(
    name: ClauseName,
    arity: usize,
    spec: Option<SharedOpDesc>,
    op_dir: &OpDir,
) -> Option<SharedOpDesc> {
    if let Some(ref op_desc) = &spec {
        if op_desc.arity() != arity {
            /* it's possible to extend operator functors with
             * additional terms. When that happens,
             * void the op_spec by returning None. */
            return None;
        }
    }

    spec.or_else(|| fetch_op_spec(name, arity, op_dir))
}

pub(crate) fn fetch_op_spec(
    name: ClauseName,
    arity: usize,
    op_dir: &OpDir,
) -> Option<SharedOpDesc> {
    match arity {
        2 => op_dir
            .get(&(name, Fixity::In))
            .and_then(|OpDirValue(spec)| {
                if spec.prec() > 0 {
                    Some(spec.clone())
                } else {
                    None
                }
            }),
        1 => {
            if let Some(OpDirValue(spec)) = op_dir.get(&(name.clone(), Fixity::Pre)) {
                if spec.prec() > 0 {
                    return Some(spec.clone());
                }
            }

            op_dir
                .get(&(name.clone(), Fixity::Post))
                .and_then(|OpDirValue(spec)| {
                    if spec.prec() > 0 {
                        Some(spec.clone())
                    } else {
                        None
                    }
                })
        }
        _ => None,
    }
}

pub(crate) type ModuleDir = IndexMap<ClauseName, Module>;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub(crate) enum ModuleExport {
    OpDecl(OpDecl),
    PredicateKey(PredicateKey),
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleDecl {
    pub(crate) name: ClauseName,
    pub(crate) exports: Vec<ModuleExport>,
}

#[derive(Debug)]
pub(crate) struct Module {
    pub(crate) module_decl: ModuleDecl,
    pub(crate) code_dir: CodeDir,
    pub(crate) op_dir: OpDir,
    pub(crate) meta_predicates: MetaPredicateDir,
    pub(crate) extensible_predicates: ExtensiblePredicates,
    pub(crate) local_extensible_predicates: LocalExtensiblePredicates,
    pub(crate) is_impromptu_module: bool,
    pub(crate) listing_src: ListingSource,
}

// Module's and related types are defined in forms.
impl Module {
    pub(crate) fn new(module_decl: ModuleDecl, listing_src: ListingSource) -> Self {
        Module {
            module_decl,
            code_dir: CodeDir::new(),
            op_dir: default_op_dir(),
            meta_predicates: MetaPredicateDir::new(),
            is_impromptu_module: false,
            extensible_predicates: ExtensiblePredicates::new(),
            local_extensible_predicates: LocalExtensiblePredicates::new(),
            listing_src,
        }
    }

    pub(crate) fn new_in_situ(module_decl: ModuleDecl) -> Self {
        Module {
            module_decl,
            code_dir: CodeDir::new(),
            op_dir: OpDir::new(),
            meta_predicates: MetaPredicateDir::new(),
            is_impromptu_module: false,
            extensible_predicates: ExtensiblePredicates::new(),
            local_extensible_predicates: LocalExtensiblePredicates::new(),
            listing_src: ListingSource::DynamicallyGenerated,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Number {
    Float(OrderedFloat<f64>),
    Integer(Rc<Integer>),
    Rational(Rc<Rational>),
    Fixnum(isize),
}

impl From<Integer> for Number {
    #[inline]
    fn from(n: Integer) -> Self {
        Number::Integer(Rc::new(n))
    }
}

impl From<Rational> for Number {
    #[inline]
    fn from(n: Rational) -> Self {
        Number::Rational(Rc::new(n))
    }
}

impl From<isize> for Number {
    #[inline]
    fn from(n: isize) -> Self {
        Number::Fixnum(n)
    }
}

impl Default for Number {
    fn default() -> Self {
        Number::Float(OrderedFloat(0f64))
    }
}

impl Into<Constant> for Number {
    #[inline]
    fn into(self) -> Constant {
        match self {
            Number::Fixnum(n) => Constant::Fixnum(n),
            Number::Integer(n) => Constant::Integer(n),
            Number::Float(f) => Constant::Float(f),
            Number::Rational(r) => Constant::Rational(r),
        }
    }
}

impl Into<HeapCellValue> for Number {
    #[inline]
    fn into(self) -> HeapCellValue {
        match self {
            Number::Fixnum(n) => HeapCellValue::Addr(Addr::Fixnum(n)),
            Number::Integer(n) => HeapCellValue::Integer(n),
            Number::Float(f) => HeapCellValue::Addr(Addr::Float(f)),
            Number::Rational(r) => HeapCellValue::Rational(r),
        }
    }
}

impl Number {
    #[inline]
    pub(crate) fn is_positive(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n > 0,
            &Number::Integer(ref n) => &**n > &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_positive(),
            &Number::Rational(ref r) => &**r > &0,
        }
    }

    #[inline]
    pub(crate) fn is_negative(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n < 0,
            &Number::Integer(ref n) => &**n < &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_negative(),
            &Number::Rational(ref r) => &**r < &0,
        }
    }

    #[inline]
    pub(crate) fn is_zero(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n == 0,
            &Number::Integer(ref n) => &**n == &0,
            &Number::Float(f) => f == OrderedFloat(0f64),
            &Number::Rational(ref r) => &**r == &0,
        }
    }

    #[inline]
    pub(crate) fn abs(self) -> Self {
        match self {
            Number::Fixnum(n) => {
                if let Some(n) = n.checked_abs() {
                    Number::from(n)
                } else {
                    Number::from(Integer::from(n).abs())
                }
            }
            Number::Integer(n) => Number::from(Integer::from(n.abs_ref())),
            Number::Float(f) => Number::Float(OrderedFloat(f.abs())),
            Number::Rational(r) => Number::from(Rational::from(r.abs_ref())),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum OptArgIndexKey {
    Constant(usize, usize, Constant, Vec<Constant>), // index, IndexingCode location, opt arg, alternatives
    List(usize, usize),                              // index, IndexingCode location
    None,
    Structure(usize, usize, ClauseName, usize), // index, IndexingCode location, name, arity
}

impl OptArgIndexKey {
    #[inline]
    pub(crate) fn take(&mut self) -> OptArgIndexKey {
        std::mem::replace(self, OptArgIndexKey::None)
    }

    #[inline]
    pub(crate) fn arg_num(&self) -> usize {
        match &self {
            OptArgIndexKey::Constant(arg_num, ..)
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
            OptArgIndexKey::Constant(_, loc, ..)
            | OptArgIndexKey::Structure(_, loc, ..)
            | OptArgIndexKey::List(_, loc) => Some(*loc),
            OptArgIndexKey::None => None,
        }
    }

    #[inline]
    pub(crate) fn set_switch_on_term_loc(&mut self, value: usize) {
        match self {
            OptArgIndexKey::Constant(_, ref mut loc, ..)
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
            OptArgIndexKey::Constant(_, ref mut o, ..)
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

#[derive(Clone, Copy, Debug)]
pub(crate) struct PredicateInfo {
    pub(crate) is_extensible: bool,
    pub(crate) is_discontiguous: bool,
    pub(crate) is_dynamic: bool,
    pub(crate) is_multifile: bool,
    pub(crate) has_clauses: bool,
}

impl Default for PredicateInfo {
    #[inline]
    fn default() -> Self {
        PredicateInfo {
            is_extensible: false,
            is_discontiguous: false,
            is_dynamic: false,
            is_multifile: false,
            has_clauses: false,
        }
    }
}

impl PredicateInfo {
    #[inline]
    pub(crate) fn compile_incrementally(&self) -> bool {
        let base = self.is_extensible && self.has_clauses;
        base && (self.is_discontiguous || self.is_multifile)
    }

    #[inline]
    pub(crate) fn must_retract_local_clauses(&self) -> bool {
        self.is_extensible && self.has_clauses && !self.is_discontiguous
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LocalPredicateSkeleton {
    pub(crate) is_discontiguous: bool,
    pub(crate) is_dynamic: bool,
    pub(crate) is_multifile: bool,
    pub(crate) clause_clause_locs: SliceDeque<usize>,
    pub(crate) clause_assert_margin: usize,
}

impl LocalPredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            is_discontiguous: false,
            is_dynamic: false,
            is_multifile: false,
            clause_clause_locs: sdeq![],
            clause_assert_margin: 0,
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
}

#[derive(Clone, Debug)]
pub(crate) struct PredicateSkeleton {
    pub(crate) core: LocalPredicateSkeleton,
    pub(crate) clauses: SliceDeque<ClauseIndexInfo>,
}

impl PredicateSkeleton {
    #[inline]
    pub(crate) fn new() -> Self {
        PredicateSkeleton {
            core: LocalPredicateSkeleton::new(),
            clauses: sdeq![],
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

    #[inline]
    pub(crate) fn reset(&mut self) {
        self.core.clause_clause_locs.clear();
        self.core.clause_assert_margin = 0;
        self.clauses.clear();
    }

    pub(crate) fn target_pos_of_clause_clause_loc(
        &self,
        clause_clause_loc: usize,
    ) -> Option<usize> {
        let search_result = self.core.clause_clause_locs[0..self.core.clause_assert_margin]
            .binary_search_by(|loc| clause_clause_loc.cmp(&loc));

        match search_result {
            Ok(loc) => Some(loc),
            Err(_) => self.core.clause_clause_locs[self.core.clause_assert_margin..]
                .binary_search_by(|loc| loc.cmp(&clause_clause_loc))
                .map(|loc| loc + self.core.clause_assert_margin)
                .ok(),
        }
    }
}
