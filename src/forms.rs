use crate::prolog_parser::ast::*;
use crate::prolog_parser::parser::OpDesc;
use crate::prolog_parser::tabled_rc::*;

use crate::clause_types::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::ordered_float::OrderedFloat;
use crate::rug::{Integer, Rational};

use crate::indexmap::IndexMap;

use std::cell::Cell;
use std::collections::VecDeque;
use std::path::PathBuf;
use std::rc::Rc;

pub type PredicateKey = (ClauseName, usize); // name, arity.

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub type JumpStub = Vec<Term>;

#[derive(Debug, Clone)]
pub enum TopLevel {
    Declaration(Declaration),
    Fact(Term, usize, usize), // Term, line_num, col_num
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule, usize, usize), // Rule, line_num, col_num
}

impl TopLevel {
    pub fn is_end_of_file_atom(&self) -> bool {
        match self {
            &TopLevel::Fact(Term::Constant(_, Constant::Atom(ref name, _)), ..) => {
                return name.as_str() == "end_of_file"
            }
            _ => false,
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

#[derive(Debug, Clone)]
pub struct Predicate(pub Vec<PredicateClause>);

impl Predicate {
    #[inline]
    pub fn new() -> Self {
        Predicate(vec![])
    }

    #[inline]
    pub fn clauses(self) -> Vec<PredicateClause> {
        self.0
    }

    #[inline]
    pub fn predicate_indicator(&self) -> Option<(ClauseName, usize)> {
        self.0
            .first()
            .and_then(|clause| clause.name().map(|name| (name, clause.arity())))
    }
}

#[derive(Debug, Clone)]
pub enum ListingSource {
    File(ClauseName, PathBuf), // filename, path
    User,
}

impl ListingSource {
    pub fn from_file_and_path(filename: ClauseName, path_buf: PathBuf) -> Self {
        ListingSource::File(filename, path_buf)
    }

    pub fn name(&self) -> ClauseName {
        match self {
            ListingSource::File(ref filename, _) => filename.clone(),
            ListingSource::User => clause_name!("[user]")
        }
    }

    pub fn path(&self) -> PathBuf {
        match self {
            ListingSource::File(_, ref path) => path.clone(),
            ListingSource::User => std::env::current_dir().unwrap(),
        }
    }
}

fn resolved_term_and_module(term: &Term) -> Option<(ClauseName, ClauseName)>
{
    match term {
        Term::Clause(_, ref name, ref terms, _) => {
            if name.as_str() == ":" && terms.len() == 2 {
                let module_name = match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Atom(ref module_name, _)) => {
                        module_name.clone()
                    }
                    _ => {
                        return Some((name.owning_module(), name.clone()));
                    }
                };

                match terms[1].as_ref() {
                    Term::Clause(_, ref name, ..)
                  | Term::Constant(_, Constant::Atom(ref name, ..)) => {
                        return Some((module_name, name.clone()));
                    }
                    _ => {
                    }
                }

                Some((name.owning_module(), name.clone()))
            } else {
                Some((name.owning_module(), name.clone()))
            }
        }
        Term::Constant(_, Constant::Atom(ref name, _)) => {
            Some((name.owning_module(), name.clone()))
        }
        _ => {
            None
        }
    }
}

fn resolved_term_arity(term: &Term) -> usize
{
    match term {
        Term::Clause(_, ref name, ref terms, _) => {
            if name.as_str() == ":" && terms.len() == 2 {
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Atom(..)) => {
                    }
                    _ => {
                        return 2;
                    }
                }

                match terms[1].as_ref() {
                    Term::Clause(_, _, ref terms, _) => {
                        terms.len()
                    }
                    Term::Constant(_, Constant::Atom(..)) => {
                        0
                    }
                    _ => {
                        2
                    }
                }
            } else {
                terms.len()
            }
        }
        _ => {
            0
        }
    }
}

pub trait ClauseConsistency {
    fn is_consistent(&self, clauses: &Vec<PredicateClause>) -> bool {
        match clauses.first() {
            Some(ref cl) => {
                self.name_and_module() == cl.name_and_module() && self.arity() == cl.arity()
            }
            None => {
                true
            }
        }
    }

    fn name_and_module(&self) -> Option<(ClauseName, ClauseName)>;
    fn arity(&self) -> usize;
}

/* Of course '$current_module$' isn't the name of the current
 * module. It'll do if no module is explicitly specified through
 * (:)/2.
 */
impl ClauseConsistency for Term {
    fn name_and_module(&self) -> Option<(ClauseName, ClauseName)>
    {
        match self {
            Term::Clause(_, ref name, ref terms, _) =>
                match name.as_str() {
                    ":-" => {
                        match terms.len() {
                            1 => None, // a declaration.
                            2 => resolved_term_and_module(&terms[0]),
                            _ => Some((name.owning_module(), clause_name!(":-"))),
                        }
                    }
                    _ => {
                        resolved_term_and_module(self)
                    }
                },
            Term::Constant(_, Constant::Atom(ref name, _)) => {
                Some((name.owning_module(), name.clone()))
            }
            _ => {
                None
            }
        }
    }

    fn arity(&self) -> usize {
        match self {
            Term::Clause(_, ref name, ref terms, _) =>
                match name.as_str() {
                    ":-" => {
                        match terms.len() {
                            1 => 0,
                            2 => resolved_term_arity(&terms[0]),
                            _ => terms.len(),
                        }
                    }
                    _ => {
                        resolved_term_arity(self)
                    }
                },
            _ => {
                0
            }
        }
    }
}

impl ClauseConsistency for Rule {
    fn name_and_module(&self) -> Option<(ClauseName, ClauseName)> {
        Some((self.head.0.owning_module(), self.head.0.clone()))
    }

    fn arity(&self) -> usize {
        self.head.1.len()
    }
}

impl ClauseConsistency for PredicateClause {
    fn name_and_module(&self) -> Option<(ClauseName, ClauseName)> {
        match self {
            &PredicateClause::Fact(ref term, ..) => {
                term.name_and_module()
                    .map(|(_, name)| (name.owning_module(), name))
            }
            &PredicateClause::Rule(ref rule, ..) => {
                rule.name_and_module()
            }
        }
    }

    fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term, ..) => {
                term.arity()
            }
            &PredicateClause::Rule(ref rule, ..) => {
                rule.arity()
            }
        }
    }
}

impl ClauseConsistency for Predicate {
    fn name_and_module(&self) -> Option<(ClauseName, ClauseName)> {
        self.0.first().and_then(|clause| clause.name_and_module())
    }

    fn arity(&self) -> usize {
        self.0.first().map(|clause| clause.arity()).unwrap_or(0)
    }
}

pub type CompiledResult = (Predicate, VecDeque<TopLevel>);

#[derive(Debug, Clone)]
pub enum PredicateClause {
    Fact(Term, usize, usize), // Term, line number, column number.
    Rule(Rule, usize, usize), // Term, line number, column number.
}

impl PredicateClause {
    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.first_arg(),
            &PredicateClause::Rule(ref rule, ..) => rule.head.1.first().map(|bt| bt.as_ref()),
        }
    }

    // TODO: add this to `Term` in `prolog_parser` like `first_arg`.
    pub fn args(&self) -> Option<&[Box<Term>]> {
        match *self {
            PredicateClause::Fact(ref term, ..) => {
                match term {
                    Term::Clause(_, _, args, _) => Some(&args),
                    _ => None,
                }
            },
            PredicateClause::Rule(ref rule, ..) => Some(&rule.head.1),
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term, ..) => {
                term.arity()
            }
            &PredicateClause::Rule(ref rule, ..) => {
                if rule.head.0.as_str() == ":" && rule.head.1.len() == 2 {
                    match (rule.head.1)[0].as_ref() {
                        &Term::Constant(_, Constant::Atom(..)) => {
                        }
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

pub type ScopedPredicateKey = (ClauseName, PredicateKey); // module name, predicate indicator.

#[derive(Debug, Clone)]
pub enum MultiFileIndicator {
    LocalScoped(ClauseName, usize), // name, arity
    ModuleScoped(ScopedPredicateKey),
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Dynamic(ClauseName, usize), // name, arity
    EndOfFile,
    Hook(CompileTimeHook, PredicateClause, VecDeque<TopLevel>),
    ModuleInitialization(Vec<QueryTerm>, VecDeque<TopLevel>), // goal
    Module(ModuleDecl),
    MultiFile(MultiFileIndicator),
    NonCountedBacktracking(ClauseName, usize), // name, arity
    Op(OpDecl),
    SetPrologFlag(DoubleQuotes),
    UseModule(ModuleSource),
    UseQualifiedModule(ModuleSource, Vec<ModuleExport>),
}

impl Declaration {
    #[inline]
    pub fn is_module_decl(&self) -> bool {
        if let &Declaration::Module(_) = self {
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn is_end_of_file(&self) -> bool {
        if let &Declaration::EndOfFile = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OpDecl(pub usize, pub Specifier, pub ClauseName);

impl OpDecl {
    #[inline]
    pub fn name(&self) -> ClauseName {
        self.2.clone()
    }

    #[inline]
    pub fn remove(&self, op_dir: &mut OpDir) {
        self.insert_into_op_dir(clause_name!(""), op_dir, 0);
    }

    #[inline]
    pub fn fixity(&self) -> Fixity {
        match self.1 {
            XFY | XFX | YFX => Fixity::In,
            XF | YF => Fixity::Post,
            FX | FY => Fixity::Pre,
            _ => unreachable!()
        }
    }

    pub fn insert_into_op_dir(&self, module: ClauseName, op_dir: &mut OpDir, prec: usize) {
        let (spec, name) = (self.1, self.2.clone());

        let fixity = self.fixity();

        match op_dir.get(&(name.clone(), fixity)) {
            Some(cell) => {
                cell.shared_op_desc().set(prec, spec);
                return;
            }
            None => {}
        }

        op_dir.insert((name, fixity), OpDirValue::new(spec, prec, module));
    }

    pub fn submit(
        &self,
        module: ClauseName,
        existing_desc: Option<OpDesc>,
        op_dir: &mut OpDir,
    ) -> Result<(), SessionError> {
        let (prec, spec, name) = (self.0, self.1, self.2.clone());

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

        Ok(self.insert_into_op_dir(module, op_dir, prec))
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

pub fn fetch_op_spec(
    name: ClauseName,
    arity: usize,
    op_dir: &OpDir,
) -> Option<SharedOpDesc> {
    match arity {
        2 => op_dir
            .get(&(name, Fixity::In))
            .and_then(|OpDirValue(spec, _)| {
                if spec.prec() > 0 {
                    Some(spec.clone())
                } else {
                    None
                }
            }),
        1 => {
            if let Some(OpDirValue(spec, _)) = op_dir.get(&(name.clone(), Fixity::Pre)) {
                if spec.prec() > 0 {
                    return Some(spec.clone());
                }
            }

            op_dir
                .get(&(name, Fixity::Post))
                .and_then(|OpDirValue(spec, _)| {
                    if spec.prec() > 0 {
                        Some(spec.clone())
                    } else {
                        None
                    }
                })
        }
        _ => {
            None
        }
    }
}

pub type ModuleDir = IndexMap<ClauseName, Module>;

#[derive(Debug, Clone, PartialEq)]
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
    pub atom_tbl: TabledData<Atom>,
    pub module_decl: ModuleDecl,
    pub code_dir: CodeDir,
    pub op_dir: OpDir,
    pub term_dir: TermDir, // this contains multifile predicates.
    pub term_expansions: (Predicate, VecDeque<TopLevel>),
    pub goal_expansions: (Predicate, VecDeque<TopLevel>),
    pub user_term_expansions: (Predicate, VecDeque<TopLevel>), // term expansions inherited from the user scope.
    pub user_goal_expansions: (Predicate, VecDeque<TopLevel>), // same for goal_expansions.
    pub local_term_expansions: (Predicate, VecDeque<TopLevel>), // expansions local to the module.
    pub local_goal_expansions: (Predicate, VecDeque<TopLevel>),
    pub inserted_expansions: bool, // has the module been successfully inserted into toplevel??
    pub is_impromptu_module: bool,
    pub listing_src: ListingSource,
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
            Number::Fixnum(n) =>
                if let Some(n) = n.checked_abs() {
                    Number::from(n)
                } else {
                    Number::from(Integer::from(n).abs())
                }
            Number::Integer(n) => Number::from(Integer::from(n.abs_ref())),
            Number::Float(f) => Number::Float(OrderedFloat(f.abs())),
            Number::Rational(r) => Number::from(Rational::from(r.abs_ref())),
        }
    }
}
