use prolog_parser::ast::*;
use prolog_parser::parser::OpDesc;
use prolog_parser::tabled_rc::*;

use crate::prolog::clause_types::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::ordered_float::OrderedFloat;
use crate::prolog::rug::{Integer, Rational};

use indexmap::IndexMap;

use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

pub type PredicateKey = (ClauseName, usize); // name, arity.

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub type JumpStub = Vec<Term>;

#[derive(Clone)]
pub enum TopLevel {
    Declaration(Declaration),
    Fact(Term, usize, usize), // Term, line_num, col_num
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule, usize, usize), // Rule, line_num, col_num
}

impl TopLevel {
    pub fn name(&self) -> Option<ClauseName> {
        match self {
            &TopLevel::Declaration(_) => None,
            &TopLevel::Fact(ref term, ..) => term.name(),
            &TopLevel::Predicate(ref clauses) => clauses.0.first().and_then(|ref term| term.name()),
            &TopLevel::Query(_) => None,
            &TopLevel::Rule(Rule { ref head, .. }, ..) => Some(head.0.clone()),
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            &TopLevel::Declaration(_) => 0,
            &TopLevel::Fact(ref term, ..) => term.arity(),
            &TopLevel::Predicate(ref clauses) => clauses.0.first().map(|t| t.arity()).unwrap_or(0),
            &TopLevel::Query(_) => 0,
            &TopLevel::Rule(Rule { ref head, .. }, ..) => head.1.len(),
        }
    }

    pub fn is_end_of_file_atom(&self) -> bool {
        match self {
            &TopLevel::Fact(Term::Constant(_, Constant::Atom(ref name, _)), ..) => {
                return name.as_str() == "end_of_file"
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
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

#[derive(Clone)]
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

#[derive(Clone)]
pub struct Rule {
    pub head: (ClauseName, Vec<Box<Term>>, QueryTerm),
    pub clauses: Vec<QueryTerm>,
}

#[derive(Clone)]
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

pub type CompiledResult = (Predicate, VecDeque<TopLevel>);

#[derive(Clone)]
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

    pub fn arity(&self) -> usize {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.arity(),
            &PredicateClause::Rule(ref rule, ..) => rule.head.1.len(),
        }
    }

    pub fn name(&self) -> Option<ClauseName> {
        match self {
            &PredicateClause::Fact(ref term, ..) => term.name(),
            &PredicateClause::Rule(ref rule, ..) => Some(rule.head.0.clone()),
        }
    }
}

#[derive(Clone)]
pub enum ModuleSource {
    Library(ClauseName),
    File(ClauseName),
}

#[derive(Clone)]
pub enum Declaration {
    Dynamic(ClauseName, usize), // name, arity
    EndOfFile,
    Hook(CompileTimeHook, PredicateClause, VecDeque<TopLevel>),
    ModuleInitialization(Vec<QueryTerm>, VecDeque<TopLevel>), // goal
    Module(ModuleDecl),
    NonCountedBacktracking(ClauseName, usize), // name, arity
    Op(OpDecl),
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    fetch_op_spec(name.clone(), 1, spec.clone(), op_dir)
        .or_else(|| fetch_op_spec(name, 2, spec, op_dir))
}

pub fn fetch_op_spec(
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

    spec.or_else(|| match arity {
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
                .get(&(name.clone(), Fixity::Post))
                .and_then(|OpDirValue(spec, _)| {
                    if spec.prec() > 0 {
                        Some(spec.clone())
                    } else {
                        None
                    }
                })
        }
        _ => None,
    })
}

pub type ModuleDir = IndexMap<ClauseName, Module>;

#[derive(Clone, PartialEq)]
pub enum ModuleExport {
    OpDecl(OpDecl),
    PredicateKey(PredicateKey),    
}

#[derive(Clone)]
pub struct ModuleDecl {
    pub name: ClauseName,
    pub exports: Vec<ModuleExport>,
}

pub struct Module {
    pub atom_tbl: TabledData<Atom>,
    pub module_decl: ModuleDecl,
    pub code_dir: CodeDir,
    pub op_dir: OpDir,
    pub term_expansions: (Predicate, VecDeque<TopLevel>),
    pub goal_expansions: (Predicate, VecDeque<TopLevel>),
    pub user_term_expansions: (Predicate, VecDeque<TopLevel>), // term expansions inherited from the user scope.
    pub user_goal_expansions: (Predicate, VecDeque<TopLevel>), // same for goal_expansions.
    pub local_term_expansions: (Predicate, VecDeque<TopLevel>), // expansions local to the module.
    pub local_goal_expansions: (Predicate, VecDeque<TopLevel>),
    pub inserted_expansions: bool, // has the module been successfully inserted into toplevel??
    pub is_impromptu_module: bool,
 }

#[derive(Clone, PartialEq, Eq)]
pub enum Number {
    Float(OrderedFloat<f64>),
    Integer(Integer),
    Rational(Rational),
}

impl Default for Number {
    fn default() -> Self {
        Number::Float(OrderedFloat(0f64))
    }
}

impl Number {
    pub fn to_constant(self) -> Constant {
        match self {
            Number::Integer(n) => Constant::Integer(n),
            Number::Float(f) => Constant::Float(f),
            Number::Rational(r) => Constant::Rational(r),
        }
    }

    #[inline]
    pub fn is_positive(&self) -> bool {
        match self {
            &Number::Integer(ref n) => n > &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_positive(),
            &Number::Rational(ref r) => r > &0,
        }
    }

    #[inline]
    pub fn is_negative(&self) -> bool {
        match self {
            &Number::Integer(ref n) => n < &0,
            &Number::Float(OrderedFloat(f)) => f.is_sign_negative(),
            &Number::Rational(ref r) => r < &0,
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            &Number::Integer(ref n) => n == &0,
            &Number::Float(f) => f == OrderedFloat(0f64),
            &Number::Rational(ref r) => r == &0,
        }
    }

    #[inline]
    pub fn abs(self) -> Self {
        match self {
            Number::Integer(n) => Number::Integer(n.abs()),
            Number::Float(f) => Number::Float(OrderedFloat(f.abs())),
            Number::Rational(r) => Number::Rational(r.abs()),
        }
    }
}
