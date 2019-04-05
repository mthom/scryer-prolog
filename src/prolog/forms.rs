use prolog_parser::ast::*;
use prolog_parser::parser::OpDesc;
use prolog_parser::tabled_rc::*;

use prolog::clause_types::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;

use std::cell::Cell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

pub type PredicateKey = (ClauseName, usize); // name, arity.

// vars of predicate, toplevel offset.  Vec<Term> is always a vector
// of vars (we get their adjoining cells this way).
pub type JumpStub = Vec<Term>;

#[derive(Clone)]
pub enum TopLevel {
    Declaration(Declaration),
    Fact(Term),
    Predicate(Predicate),
    Query(Vec<QueryTerm>),
    Rule(Rule),
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

#[derive(Clone)]
pub enum QueryTerm {
    // register, clause type, subterms, use default call policy.
    Clause(Cell<RegType>, ClauseType, Vec<Box<Term>>, bool),
    BlockedCut, // a cut which is 'blocked by letters', like the P term in P -> Q.
    UnblockedCut(Cell<VarReg>),
    GetLevelAndUnify(Cell<VarReg>, Rc<Var>),
    Jump(JumpStub)
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
    pub clauses: Vec<QueryTerm>
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
        self.0.first()
            .and_then(|clause| clause.name().map(|name| (name, clause.arity())))
    }
}

pub type CompiledResult = (Predicate, VecDeque<TopLevel>);

#[derive(Clone)]
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

#[derive(Clone)]
pub enum Declaration {
    Dynamic(ClauseName, usize), // name, arity
    Hook(CompileTimeHook, PredicateClause, VecDeque<TopLevel>),
    Module(ModuleDecl),
    NonCountedBacktracking(ClauseName, usize), // name, arity
    Op(OpDecl),
    UseModule(ClauseName),
    UseQualifiedModule(ClauseName, Vec<PredicateKey>)
}

impl Declaration {
    #[inline]
    pub fn is_module_decl(&self) -> bool {
        if let &Declaration::Module(_) = self { true } else { false }
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
    
    fn insert_into_op_dir(&self, module: ClauseName, op_dir: &mut OpDir, prec: usize)
    {
        let (spec, name) = (self.1, self.2.clone());

        let fixity = match spec {
            XFY | XFX | YFX => Fixity::In,
            XF | YF => Fixity::Post,
            FX | FY => Fixity::Pre,
            _ => return
        };

        match op_dir.get(&(name.clone(), fixity)) {
            Some(cell) => {
                cell.shared_op_desc().set(prec, spec);
                return;
            }
            None => {}
        }

        op_dir.insert((name, fixity), OpDirValue::new(spec, prec, module));
    }

    pub fn submit(&self, module: ClauseName, existing_desc: Option<OpDesc>, op_dir: &mut OpDir)
                  -> Result<(), SessionError>
    {
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

pub type ModuleDir = HashMap<ClauseName, Module>;

#[derive(Clone)]
pub struct ModuleDecl {
    pub name: ClauseName,
    pub exports: Vec<PredicateKey>
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
    pub inserted_expansions: bool // has the module been successfully inserted into toplevel??
}
