use prolog_parser::ast::*;
use prolog_parser::parser::OpDesc;
use prolog_parser::{clause_name, is_infix, is_postfix};

use crate::clause_types::*;
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

pub type PredicateKey = (ClauseName, usize); // name, arity.

pub type Predicate = Vec<PredicateClause>;

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub type JumpStub = Vec<Term>;

#[derive(Debug, Clone)]
pub enum TopLevel {
    Declaration(Declaration),
    Fact(Term), // Term, line_num, col_num
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule), // Rule, line_num, col_num
}

#[derive(Debug, Clone, Copy)]
pub enum AppendOrPrepend {
    Append,
    Prepend,
}

impl AppendOrPrepend {
    #[inline]
    pub fn is_append(self) -> bool {
        match self {
            AppendOrPrepend::Append => true,
            AppendOrPrepend::Prepend => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Level {
    Deep,
    Root,
    Shallow,
}

impl Level {
    pub fn child_level(self) -> Level {
        match self {
            Level::Root => Level::Shallow,
            _ => Level::Deep,
        }
    }
}

#[derive(Debug, Clone)]
pub enum QueryTerm {
    // register, clause type, subterms, use default call policy.
    Clause(Cell<RegType>, ClauseType, Vec<Box<Term>>, bool),
    BlockedCut, // a cut which is 'blocked by letters', like the P term in P -> Q.
    UnblockedCut(Cell<VarReg>),
    GetLevelAndUnify(Cell<VarReg>, Rc<Var>),
    Jump(JumpStub),
}

impl QueryTerm {
    pub fn set_default_caller(&mut self) {
        match self {
            &mut QueryTerm::Clause(_, _, _, ref mut use_default_cp) => *use_default_cp = true,
            _ => {}
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &QueryTerm::Clause(_, _, ref subterms, ..) => subterms.len(),
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => 0,
            &QueryTerm::Jump(ref vars) => vars.len(),
            &QueryTerm::GetLevelAndUnify(..) => 1,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Rule {
    pub head: (ClauseName, Vec<Box<Term>>, QueryTerm),
    pub clauses: Vec<QueryTerm>,
}

#[derive(Clone, Debug, Hash)]
pub enum ListingSource {
    DynamicallyGenerated,
    File(ClauseName, PathBuf), // filename, path
    User,
}

impl ListingSource {
    pub fn from_file_and_path(filename: ClauseName, path_buf: PathBuf) -> Self {
        ListingSource::File(filename, path_buf)
    }
}

pub trait ClauseInfo {
    fn is_consistent(&self, clauses: &Vec<PredicateClause>) -> bool {
        match clauses.first() {
            Some(cl) => self.name() == cl.name() && self.arity() == cl.arity(),
            None => true,
        }
    }

    fn name(&self) -> Option<ClauseName>;
    fn arity(&self) -> usize;
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

// pub type CompiledResult = (Predicate, VecDeque<TopLevel>);

#[derive(Debug, Clone)]
pub enum PredicateClause {
    Fact(Term),
    Rule(Rule),
}

impl PredicateClause {
    // TODO: add this to `Term` in `prolog_parser` like `first_arg`.
    pub fn args(&self) -> Option<&[Box<Term>]> {
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

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.arity(),
            &PredicateClause::Rule(ref rule, ..) => {
                if rule.head.0.as_str() == ":" && rule.head.1.len() == 2 {
                    match (rule.head.1)[0].as_ref() {
                        &Term::Constant(_, Constant::Atom(..)) => {}
                        _ => {
                            return 2;
                        }
                    }

                    (rule.head.1)[1].arity()
                } else {
                    rule.head.1.len()
                }
            }
        }
    }

    pub fn name(&self) -> Option<ClauseName> {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.name(),
            &PredicateClause::Rule(ref rule, ..) => Some(rule.head.0.clone()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ModuleSource {
    Library(ClauseName),
    File(ClauseName),
}

impl ModuleSource {
    pub fn as_functor_stub(&self) -> MachineStub {
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

// pub type ScopedPredicateKey = (ClauseName, PredicateKey); // module name, predicate indicator.

/*
#[derive(Debug, Clone)]
pub enum MultiFileIndicator {
    LocalScoped(ClauseName, usize), // name, arity
    ModuleScoped(ScopedPredicateKey),
}
*/

#[derive(Clone, Copy, Hash, Debug)]
pub enum MetaSpec {
    Minus,
    Plus,
    Either,
    RequiresExpansionWithArgument(usize),
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Dynamic(ClauseName, usize),
    MetaPredicate(ClauseName, ClauseName, Vec<MetaSpec>), // module name, name, meta-specs
    Module(ModuleDecl),
    NonCountedBacktracking(ClauseName, usize), // name, arity
    Op(OpDecl),
    UseModule(ModuleSource),
    UseQualifiedModule(ModuleSource, IndexSet<ModuleExport>),
}

#[derive(Debug, Clone, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub struct OpDecl {
    pub prec: usize,
    pub spec: Specifier,
    pub name: ClauseName,
}

impl OpDecl {
    #[inline]
    pub fn new(prec: usize, spec: Specifier, name: ClauseName) -> Self {
        Self { prec, spec, name }
    }

    #[inline]
    pub fn remove(&mut self, op_dir: &mut OpDir) {
        let prec = self.prec;
        self.prec = 0;

        self.insert_into_op_dir(op_dir);
        self.prec = prec;
    }

    #[inline]
    pub fn fixity(&self) -> Fixity {
        match self.spec {
            XFY | XFX | YFX => Fixity::In,
            XF | YF => Fixity::Post,
            FX | FY => Fixity::Pre,
            _ => unreachable!(),
        }
    }

    pub fn insert_into_op_dir(&self, op_dir: &mut OpDir) -> Option<(usize, Specifier)> {
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

    pub fn submit(
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

pub fn fetch_atom_op_spec(
    name: ClauseName,
    spec: Option<SharedOpDesc>,
    op_dir: &OpDir,
) -> Option<SharedOpDesc> {
    fetch_op_spec_from_existing(name.clone(), 1, spec.clone(), op_dir)
        .or_else(|| fetch_op_spec_from_existing(name, 2, spec, op_dir))
}

pub fn fetch_op_spec_from_existing(
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

pub fn fetch_op_spec(name: ClauseName, arity: usize, op_dir: &OpDir) -> Option<SharedOpDesc> {
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

pub type ModuleDir = IndexMap<ClauseName, Module>;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum ModuleExport {
    OpDecl(OpDecl),
    PredicateKey(PredicateKey),
}

#[derive(Debug, Clone)]
pub struct ModuleDecl {
    pub name: ClauseName,
    pub exports: Vec<ModuleExport>,
}

#[derive(Debug)]
pub struct Module {
    pub module_decl: ModuleDecl,
    pub code_dir: CodeDir,
    pub op_dir: OpDir,
    pub meta_predicates: MetaPredicateDir,
    pub extensible_predicates: IndexMap<PredicateKey, PredicateSkeleton>,
    pub is_impromptu_module: bool,
    pub listing_src: ListingSource,
    pub clause_assert_margin: usize,
}

// Module's and related types are defined in forms.
impl Module {
    pub fn new(module_decl: ModuleDecl, listing_src: ListingSource) -> Self {
        Module {
            module_decl,
            code_dir: CodeDir::new(),
            op_dir: default_op_dir(),
            meta_predicates: MetaPredicateDir::new(),
            is_impromptu_module: false,
            extensible_predicates: IndexMap::new(),
            listing_src,
            clause_assert_margin: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Number {
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
    pub fn is_positive(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n > 0,
            &Number::Integer(ref n) => &**n > &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_positive(),
            &Number::Rational(ref r) => &**r > &0,
        }
    }

    #[inline]
    pub fn is_negative(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n < 0,
            &Number::Integer(ref n) => &**n < &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_negative(),
            &Number::Rational(ref r) => &**r < &0,
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            &Number::Fixnum(n) => n == 0,
            &Number::Integer(ref n) => &**n == &0,
            &Number::Float(f) => f == OrderedFloat(0f64),
            &Number::Rational(ref r) => &**r == &0,
        }
    }

    #[inline]
    pub fn abs(self) -> Self {
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
pub enum OptArgIndexKey {
    Constant(usize, usize, Constant, Vec<Constant>), // index, IndexingCode location, opt arg, alternatives
    List(usize, usize),                              // index, IndexingCode location
    None,
    Structure(usize, usize, ClauseName, usize), // index, IndexingCode location, name, arity
}

impl OptArgIndexKey {
    #[inline]
    pub fn take(&mut self) -> OptArgIndexKey {
        std::mem::replace(self, OptArgIndexKey::None)
    }

    #[inline]
    pub fn arg_num(&self) -> usize {
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
    pub fn is_some(&self) -> bool {
        self.switch_on_term_loc().is_some()
    }

    #[inline]
    pub fn switch_on_term_loc(&self) -> Option<usize> {
        match &self {
            OptArgIndexKey::Constant(_, loc, ..)
            | OptArgIndexKey::Structure(_, loc, ..)
            | OptArgIndexKey::List(_, loc) => Some(*loc),
            OptArgIndexKey::None => None,
        }
    }

    #[inline]
    pub fn set_switch_on_term_loc(&mut self, value: usize) {
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

#[derive(Debug)]
pub struct ClauseIndexInfo {
    pub clause_start: usize,
    pub opt_arg_index_key: OptArgIndexKey,
}

impl ClauseIndexInfo {
    #[inline]
    pub fn new(clause_start: usize) -> Self {
        Self {
            clause_start,
            opt_arg_index_key: OptArgIndexKey::None,
            // index_locs: vec![],
        }
    }
}

#[derive(Debug)]
pub struct PredicateSkeleton {
    pub is_discontiguous: bool,
    pub is_dynamic: bool,
    pub is_multifile: bool,
    pub clauses: SliceDeque<ClauseIndexInfo>,
    pub clause_clause_locs: SliceDeque<usize>,
}

impl PredicateSkeleton {
    #[inline]
    pub fn new() -> Self {
        PredicateSkeleton {
            is_discontiguous: false,
            is_dynamic: false,
            is_multifile: false,
            clauses: sdeq![],
            clause_clause_locs: sdeq![],
        }
    }

    /*
    #[inline]
    pub fn set_discontiguous(self, is_discontiguous: bool) -> Self {
        PredicateSkeleton {
            is_discontiguous,
            is_dynamic: self.is_dynamic,
            is_multifile: self.is_multifile,
            clauses: self.clauses,
        }
    }
    */

    #[inline]
    pub fn set_dynamic(self, is_dynamic: bool) -> Self {
        PredicateSkeleton {
            is_discontiguous: self.is_discontiguous,
            is_dynamic,
            is_multifile: self.is_multifile,
            clauses: self.clauses,
            clause_clause_locs: self.clause_clause_locs,
        }
    }

    /*
    #[inline]
    pub fn set_multifile(self, is_multifile: bool) -> Self {
        PredicateSkeleton {
           is_discontiguous: self.is_discontiguous,
            is_dynamic: self.is_dynamic,
            is_multifile,
            clauses: self.clauses,
        }
    }
    */
}
