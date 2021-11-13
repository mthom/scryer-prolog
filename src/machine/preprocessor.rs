use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;
use prolog_parser::{atom, clause_name, rc_atom};

use crate::forms::*;
use crate::iterators::*;
use crate::machine::load_state::*;
use crate::machine::machine_errors::*;
use crate::machine::*;

use indexmap::IndexSet;

use std::cell::Cell;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::rc::Rc;

/*
 *  The preprocessor fabricates if-then-else ( .. -> ... ; ...)
 *  clauses into nameless standalone predicates, which it queues for
 *  later preprocessing and compilation. Fabricated predicates inherit
 *  explicit "cut variables" from the handwritten predicate
 *  surrounding their source if-then-else. They must be specially
 *  handled.
 */

#[derive(Clone, Copy, Debug)]
pub(crate) enum CutContext {
    BlocksCuts,
    HasCutVariable,
}

pub(crate) fn fold_by_str<I>(terms: I, mut term: Term, sym: ClauseName) -> Term
where
    I: DoubleEndedIterator<Item = Term>,
{
    for prec in terms.rev() {
        term = Term::Clause(
            Cell::default(),
            sym.clone(),
            vec![Box::new(prec), Box::new(term)],
            None,
        );
    }

    term
}

pub(crate) fn to_op_decl(
    prec: usize,
    spec: &str,
    name: ClauseName,
) -> Result<OpDecl, CompilationError> {
    match spec {
        "xfx" => Ok(OpDecl::new(prec, XFX, name)),
        "xfy" => Ok(OpDecl::new(prec, XFY, name)),
        "yfx" => Ok(OpDecl::new(prec, YFX, name)),
        "fx" => Ok(OpDecl::new(prec, FX, name)),
        "fy" => Ok(OpDecl::new(prec, FY, name)),
        "xf" => Ok(OpDecl::new(prec, XF, name)),
        "yf" => Ok(OpDecl::new(prec, YF, name)),
        _ => Err(CompilationError::InconsistentEntry),
    }
}

fn setup_op_decl(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<OpDecl, CompilationError> {
    let name = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        Term::Constant(_, Constant::Char(c)) => clause_name!(c.to_string(), atom_tbl),
        _ => return Err(CompilationError::InconsistentEntry),
    };

    let spec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        Term::Constant(_, Constant::Char(c)) => clause_name!(c.to_string(), atom_tbl),
        _ => return Err(CompilationError::InconsistentEntry),
    };

    let prec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Fixnum(bi)) => match usize::try_from(bi) {
            Ok(n) if n <= 1200 => n,
            _ => return Err(CompilationError::InconsistentEntry),
        },
        _ => return Err(CompilationError::InconsistentEntry),
    };

    to_op_decl(prec, spec.as_str(), name)
}

fn setup_predicate_indicator(term: &mut Term) -> Result<PredicateKey, CompilationError> {
    match term {
        Term::Clause(_, ref slash, ref mut terms, Some(_))
            if (slash.as_str() == "/" || slash.as_str() == "//") && terms.len() == 2 =>
        {
            let arity = *terms.pop().unwrap();
            let name = *terms.pop().unwrap();

            let arity = arity
                .into_constant()
                .and_then(|c| match c {
                    Constant::Integer(n) => n.to_usize(),
                    Constant::Fixnum(n) => usize::try_from(n).ok(),
                    _ => None,
                })
                .ok_or(CompilationError::InvalidModuleExport)?;

            let name = name
                .into_constant()
                .and_then(|c| c.to_atom())
                .ok_or(CompilationError::InvalidModuleExport)?;

            if slash.as_str() == "/" {
                Ok((name, arity))
            } else {
                Ok((name, arity + 2))
            }
        }
        _ => Err(CompilationError::InvalidModuleExport),
    }
}

/*
fn setup_scoped_predicate_indicator(term: &mut Term) -> Result<ScopedPredicateKey, CompilationError>
{
    match term {
        Term::Clause(_, ref name, ref mut terms, Some(_))
            if name.as_str() == ":" && terms.len() == 2 =>
        {
            let mut predicate_indicator = *terms.pop().unwrap();
            let module_name = *terms.pop().unwrap();

            let module_name = module_name
                .to_constant()
                .and_then(|c| c.to_atom())
                .ok_or(CompilationError::InvalidModuleExport)?;

            let key = setup_predicate_indicator(&mut predicate_indicator)?;

            Ok((module_name, key))
        }
        _ => Err(CompilationError::InvalidModuleExport),
    }
}
*/

fn setup_module_export(
    mut term: Term,
    atom_tbl: TabledData<Atom>,
) -> Result<ModuleExport, CompilationError> {
    setup_predicate_indicator(&mut term)
        .map(ModuleExport::PredicateKey)
        .or_else(|_| {
            if let Term::Clause(_, name, terms, _) = term {
                if terms.len() == 3 && name.as_str() == "op" {
                    Ok(ModuleExport::OpDecl(setup_op_decl(terms, atom_tbl)?))
                } else {
                    Err(CompilationError::InvalidModuleDecl)
                }
            } else {
                Err(CompilationError::InvalidModuleDecl)
            }
        })
}

pub(super) fn setup_module_export_list(
    mut export_list: Term,
    atom_tbl: TabledData<Atom>,
) -> Result<Vec<ModuleExport>, CompilationError> {
    let mut exports = vec![];

    while let Term::Cons(_, t1, t2) = export_list {
        let module_export = setup_module_export(*t1, atom_tbl.clone())?;

        exports.push(module_export);
        export_list = *t2;
    }

    if let Term::Constant(_, Constant::EmptyList) = export_list {
        Ok(exports)
    } else {
        Err(CompilationError::InvalidModuleDecl)
    }
}

fn setup_module_decl(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<ModuleDecl, CompilationError> {
    let export_list = *terms.pop().unwrap();
    let name = terms
        .pop()
        .unwrap()
        .into_constant()
        .and_then(|c| c.to_atom())
        .ok_or(CompilationError::InvalidModuleDecl)?;

    let exports = setup_module_export_list(export_list, atom_tbl)?;
    Ok(ModuleDecl { name, exports })
}

fn setup_use_module_decl(mut terms: Vec<Box<Term>>) -> Result<ModuleSource, CompilationError> {
    match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 =>
        {
            terms
                .pop()
                .unwrap()
                .into_constant()
                .and_then(|c| c.to_atom())
                .map(|c| ModuleSource::Library(c))
                .ok_or(CompilationError::InvalidUseModuleDecl)
        }
        Term::Constant(_, Constant::Atom(ref name, _)) => Ok(ModuleSource::File(name.clone())),
        _ => Err(CompilationError::InvalidUseModuleDecl),
    }
}

/*
fn setup_double_quotes(mut terms: Vec<Box<Term>>) -> Result<DoubleQuotes, CompilationError> {
    let dbl_quotes = *terms.pop().unwrap();

    match terms[0].as_ref() {
        Term::Constant(_, Constant::Atom(ref name, _))
            if name.as_str() == "double_quotes" => {
                match dbl_quotes {
                    Term::Constant(_, Constant::Atom(name, _)) => {
                        match name.as_str() {
                            "atom"  => Ok(DoubleQuotes::Atom),
                            "chars" => Ok(DoubleQuotes::Chars),
                            "codes" => Ok(DoubleQuotes::Codes),
                            _ => Err(CompilationError::InvalidDoubleQuotesDecl),
                        }
                    }
                    _ => {
                        Err(CompilationError::InvalidDoubleQuotesDecl)
                    }
                }
            },
        _ => {
            Err(CompilationError::InvalidDoubleQuotesDecl)
        }
    }
}
 */

type UseModuleExport = (ModuleSource, IndexSet<ModuleExport>);

fn setup_qualified_import(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<UseModuleExport, CompilationError> {
    let mut export_list = *terms.pop().unwrap();
    let module_src = match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 =>
        {
            terms
                .pop()
                .unwrap()
                .into_constant()
                .and_then(|c| c.to_atom())
                .map(|c| ModuleSource::Library(c))
                .ok_or(CompilationError::InvalidUseModuleDecl)
        }
        Term::Constant(_, Constant::Atom(ref name, _)) => Ok(ModuleSource::File(name.clone())),
        _ => Err(CompilationError::InvalidUseModuleDecl),
    }?;

    let mut exports = IndexSet::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.insert(setup_module_export(*t1, atom_tbl.clone())?);
        export_list = *t2;
    }

    if let Term::Constant(_, Constant::EmptyList) = export_list {
        Ok((module_src, exports))
    } else {
        Err(CompilationError::InvalidModuleDecl)
    }
}

/*
 * setup_meta_predicate tries to extract meta-predicate information
 * from an appropriately formed declaration
 *
 * :- meta_predicate maplist(:, ?, ?).
 *
 * indicating that, for each QueryTerm call to maplist/3, the first
 * argument is to be expanded with the call resolution ((:)/2)
 * operator, the first argument of which is the name of the host
 * module, as an atom. For example,
 *
 * p(X) :- maplist(X, [a,b,c], Result).
 *
 * If p/2 is defined in a module named "mod", the call is expanded to
 *
 * maplist(mod:X, [a,b,c], Result).
 *
 * before the predicate is compiled to WAM instructions.
 *
 * If the term bound to X -- the predicate to be called -- is
 * qualified with (:)/2 already, the innermost qualifier is used for
 * call resolution.
 *
 * The three arguments returned by a successful call are the module name,
 * predicate name, and the list of meta-specs, one for each predicate argument.
 *
 * The module name might be used to specify intra-module meta-predicates whose
 * module is not yet defined. There are several examples of this
 * contained in src/lib/ops_and_meta_predicates.pl, which is loaded before
 * src/lib/builtins.pl.
 *
 * Meta-specs have three forms:
 *
 * (:)  (the argument should be expanded with (:)/2 as described above)
 * +    (mode declarations under the mode syntax, which currently have no effect)
 * -
 * ?
 */
fn setup_meta_predicate<'a>(
    mut terms: Vec<Box<Term>>,
    load_state: &LoadState<'a>,
) -> Result<(ClauseName, ClauseName, Vec<MetaSpec>), CompilationError> {
    fn get_name_and_meta_specs(
        name: ClauseName,
        terms: &mut [Box<Term>],
    ) -> Result<(ClauseName, Vec<MetaSpec>), CompilationError> {
        let mut meta_specs = vec![];

        for meta_spec in terms.into_iter() {
            match &**meta_spec {
                Term::Constant(_, Constant::Atom(meta_spec, _)) => {
                    let meta_spec = match meta_spec.as_str() {
                        "+" => MetaSpec::Plus,
                        "-" => MetaSpec::Minus,
                        "?" => MetaSpec::Either,
                        _ => return Err(CompilationError::InvalidMetaPredicateDecl),
                    };

                    meta_specs.push(meta_spec);
                }
                Term::Constant(_, Constant::Fixnum(n)) => match usize::try_from(*n) {
                    Ok(n) if n <= MAX_ARITY => {
                        meta_specs.push(MetaSpec::RequiresExpansionWithArgument(n));
                    }
                    _ => {
                        return Err(CompilationError::InvalidMetaPredicateDecl);
                    }
                },
                _ => {
                    return Err(CompilationError::InvalidMetaPredicateDecl);
                }
            }
        }

        Ok((name, meta_specs))
    }

    match *terms.pop().unwrap() {
        Term::Clause(_, name, mut terms, _) if name.as_str() == ":" && terms.len() == 2 => {
            let spec = *terms.pop().unwrap();
            let module_name = *terms.pop().unwrap();

            match module_name {
                Term::Constant(_, Constant::Atom(module_name, _)) => match spec {
                    Term::Clause(_, name, mut terms, _) => {
                        let (name, meta_specs) = get_name_and_meta_specs(name, &mut terms)?;

                        Ok((module_name, name, meta_specs))
                    }
                    _ => Err(CompilationError::InvalidMetaPredicateDecl),
                },
                _ => Err(CompilationError::InvalidMetaPredicateDecl),
            }
        }
        Term::Clause(_, name, mut terms, _) => {
            let (name, meta_specs) = get_name_and_meta_specs(name, &mut terms)?;
            Ok((
                load_state.compilation_target.module_name(),
                name,
                meta_specs,
            ))
        }
        _ => Err(CompilationError::InvalidMetaPredicateDecl),
    }
}

fn merge_clauses(tls: &mut VecDeque<TopLevel>) -> Result<TopLevel, CompilationError> {
    let mut clauses = vec![];

    while let Some(tl) = tls.pop_front() {
        match tl {
            TopLevel::Query(_) if clauses.is_empty() && tls.is_empty() => {
                return Ok(tl);
            }
            TopLevel::Query(_) => {
                return Err(CompilationError::InconsistentEntry);
            }
            TopLevel::Fact(fact) => {
                let clause = PredicateClause::Fact(fact);
                clauses.push(clause);
            }
            TopLevel::Rule(rule) => {
                let clause = PredicateClause::Rule(rule);
                clauses.push(clause);
            }
            TopLevel::Predicate(predicate) => clauses.extend(predicate.into_iter()),
        }
    }

    if clauses.is_empty() {
        Err(CompilationError::InconsistentEntry)
    } else {
        Ok(TopLevel::Predicate(clauses))
    }
}

fn mark_cut_variables_as(terms: &mut Vec<Term>, name: ClauseName) {
    for term in terms.iter_mut() {
        match term {
            &mut Term::Constant(_, Constant::Atom(ref mut var, _)) if var.as_str() == "!" => {
                *var = name.clone()
            }
            _ => {}
        }
    }
}

fn mark_cut_variable(term: &mut Term) -> bool {
    let cut_var_found = match term {
        &mut Term::Constant(_, Constant::Atom(ref var, _)) if var.as_str() == "!" => true,
        _ => false,
    };

    if cut_var_found {
        *term = Term::Var(Cell::default(), rc_atom!("!"));
        true
    } else {
        false
    }
}

fn mark_cut_variables(terms: &mut Vec<Term>) -> bool {
    let mut found_cut_var = false;

    for item in terms.iter_mut() {
        found_cut_var = mark_cut_variable(item) || found_cut_var;
    }

    found_cut_var
}

// terms is a list of goals composing one clause in a (;) functor. it
// checks that the first (and only) of these clauses is a ->. if so,
// it expands its terms using a blocked_!.
fn check_for_internal_if_then(terms: &mut Vec<Term>) {
    if terms.len() != 1 {
        return;
    }

    if let Some(Term::Clause(_, ref name, ref subterms, _)) = terms.last() {
        if name.as_str() != "->" || subterms.len() != 2 {
            return;
        }
    } else {
        return;
    }

    if let Some(Term::Clause(_, _, mut subterms, _)) = terms.pop() {
        let mut conq_terms = VecDeque::from(unfold_by_str(*subterms.pop().unwrap(), ","));
        let mut pre_cut_terms = VecDeque::from(unfold_by_str(*subterms.pop().unwrap(), ","));

        conq_terms.push_front(Term::Constant(
            Cell::default(),
            Constant::Atom(clause_name!("blocked_!"), None),
        ));

        while let Some(term) = pre_cut_terms.pop_back() {
            conq_terms.push_front(term);
        }

        let tail_term = conq_terms.pop_back().unwrap();

        terms.push(fold_by_str(
            conq_terms.into_iter(),
            tail_term,
            clause_name!(","),
        ));
    }
}

pub(super) fn setup_declaration<'a>(
    load_state: &LoadState<'a>,
    mut terms: Vec<Box<Term>>,
) -> Result<Declaration, CompilationError> {
    let term = *terms.pop().unwrap();
    let atom_tbl = load_state.wam.machine_st.atom_tbl.clone();

    match term {
        Term::Clause(_, name, mut terms, _) => match (name.as_str(), terms.len()) {
            ("dynamic", 1) => {
                let (name, arity) = setup_predicate_indicator(&mut *terms.pop().unwrap())?;
                Ok(Declaration::Dynamic(name, arity))
            }
            ("module", 2) => Ok(Declaration::Module(setup_module_decl(terms, atom_tbl)?)),
            ("op", 3) => Ok(Declaration::Op(setup_op_decl(terms, atom_tbl)?)),
            ("non_counted_backtracking", 1) => {
                let (name, arity) = setup_predicate_indicator(&mut *terms.pop().unwrap())?;
                Ok(Declaration::NonCountedBacktracking(name, arity))
            }
            ("use_module", 1) => Ok(Declaration::UseModule(setup_use_module_decl(terms)?)),
            ("use_module", 2) => {
                let (name, exports) = setup_qualified_import(terms, atom_tbl)?;
                Ok(Declaration::UseQualifiedModule(name, exports))
            }
            ("meta_predicate", 1) => {
                let (module_name, name, meta_specs) = setup_meta_predicate(terms, load_state)?;
                Ok(Declaration::MetaPredicate(module_name, name, meta_specs))
            }
            _ => Err(CompilationError::InconsistentEntry),
        },
        _ => Err(CompilationError::InconsistentEntry),
    }
}

#[inline]
fn clause_to_query_term<'a>(
    load_state: &mut LoadState<'a>,
    name: ClauseName,
    terms: Vec<Box<Term>>,
    fixity: Option<SharedOpDesc>,
) -> QueryTerm {
    let ct = load_state.get_clause_type(name, terms.len(), fixity);
    QueryTerm::Clause(Cell::default(), ct, terms, false)
}

#[inline]
fn qualified_clause_to_query_term<'a>(
    load_state: &mut LoadState<'a>,
    module_name: ClauseName,
    name: ClauseName,
    terms: Vec<Box<Term>>,
    fixity: Option<SharedOpDesc>,
) -> QueryTerm {
    let ct = load_state.get_qualified_clause_type(module_name, name, terms.len(), fixity);
    QueryTerm::Clause(Cell::default(), ct, terms, false)
}

#[derive(Debug)]
pub(crate) struct Preprocessor {
    queue: VecDeque<VecDeque<Term>>,
}

impl Preprocessor {
    pub(super) fn new() -> Self {
        Preprocessor {
            queue: VecDeque::new(),
        }
    }

    fn setup_fact(&mut self, term: Term) -> Result<Term, CompilationError> {
        match term {
            Term::Clause(..) | Term::Constant(_, Constant::Atom(..)) => Ok(term),
            _ => Err(CompilationError::InadmissibleFact),
        }
    }

    fn compute_head(&self, term: &Term) -> Vec<Term> {
        let mut vars = IndexSet::new();

        for term in post_order_iter(term) {
            if let TermRef::Var(_, _, v) = term {
                vars.insert(v.clone());
            }
        }

        vars.insert(rc_atom!("!"));
        vars.into_iter()
            .map(|v| Term::Var(Cell::default(), v))
            .collect()
    }

    fn fabricate_rule_body(&self, vars: &Vec<Term>, body_term: Term) -> Term {
        let vars_of_head = vars.iter().cloned().map(Box::new).collect();
        let head_term = Term::Clause(Cell::default(), clause_name!(""), vars_of_head, None);

        let rule = vec![Box::new(head_term), Box::new(body_term)];
        let turnstile = clause_name!(":-");

        Term::Clause(Cell::default(), turnstile, rule, None)
    }

    // the terms form the body of the rule. We create a head, by
    // gathering variables from the body of terms and recording them
    // in the head clause.
    fn fabricate_rule(&self, body_term: Term) -> (JumpStub, VecDeque<Term>) {
        // collect the vars of body_term into a head, return the num_vars
        // (the arity) as well.
        let vars = self.compute_head(&body_term);
        let rule = self.fabricate_rule_body(&vars, body_term);

        (vars, VecDeque::from(vec![rule]))
    }

    fn fabricate_disjunct(&self, body_term: Term) -> (JumpStub, VecDeque<Term>) {
        let vars = self.compute_head(&body_term);
        let results = unfold_by_str(body_term, ";")
            .into_iter()
            .map(|term| {
                let mut subterms = unfold_by_str(term, ",");
                mark_cut_variables(&mut subterms);

                check_for_internal_if_then(&mut subterms);

                let term = subterms.pop().unwrap();
                let clause = fold_by_str(subterms.into_iter(), term, clause_name!(","));

                self.fabricate_rule_body(&vars, clause)
            })
            .collect();

        (vars, results)
    }

    fn fabricate_if_then(&self, prec: Term, conq: Term) -> (JumpStub, VecDeque<Term>) {
        let mut prec_seq = unfold_by_str(prec, ",");
        let comma_sym = clause_name!(",");
        let cut_sym = atom!("!");

        prec_seq.push(Term::Constant(Cell::default(), cut_sym));

        mark_cut_variables_as(&mut prec_seq, clause_name!("blocked_!"));

        let mut conq_seq = unfold_by_str(conq, ",");

        mark_cut_variables(&mut conq_seq);
        prec_seq.extend(conq_seq.into_iter());

        let back_term = Box::new(prec_seq.pop().unwrap());
        let front_term = Box::new(prec_seq.pop().unwrap());

        let body_term = Term::Clause(
            Cell::default(),
            comma_sym.clone(),
            vec![front_term, back_term],
            None,
        );

        self.fabricate_rule(fold_by_str(prec_seq.into_iter(), body_term, comma_sym))
    }

    fn to_query_term<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        term: Term,
    ) -> Result<QueryTerm, CompilationError> {
        match term {
            Term::Constant(_, Constant::Atom(name, fixity)) => {
                if name.as_str() == "!" || name.as_str() == "blocked_!" {
                    Ok(QueryTerm::BlockedCut)
                } else {
                    Ok(clause_to_query_term(load_state, name, vec![], fixity))
                }
            }
            Term::Constant(_, Constant::Char('!')) => Ok(QueryTerm::BlockedCut),
            Term::Var(_, ref v) if v.as_str() == "!" => {
                Ok(QueryTerm::UnblockedCut(Cell::default()))
            }
            Term::Clause(r, name, mut terms, fixity) => match (name.as_str(), terms.len()) {
                (";", 2) => {
                    let term = Term::Clause(r, name.clone(), terms, fixity);

                    let (stub, clauses) = self.fabricate_disjunct(term);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                ("->", 2) => {
                    let conq = *terms.pop().unwrap();
                    let prec = *terms.pop().unwrap();

                    let (stub, clauses) = self.fabricate_if_then(prec, conq);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                ("\\+", 1) => {
                    terms.push(Box::new(Term::Constant(
                        Cell::default(),
                        Constant::Atom(clause_name!("$fail"), None),
                    )));

                    let conq =
                        Term::Constant(Cell::default(), Constant::Atom(clause_name!("true"), None));

                    let prec = Term::Clause(Cell::default(), clause_name!("->"), terms, None);
                    let terms = vec![Box::new(prec), Box::new(conq)];

                    let term = Term::Clause(Cell::default(), clause_name!(";"), terms, None);
                    let (stub, clauses) = self.fabricate_disjunct(term);

                    debug_assert!(clauses.len() > 0);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                ("$get_level", 1) => {
                    if let Term::Var(_, ref var) = *terms[0] {
                        Ok(QueryTerm::GetLevelAndUnify(Cell::default(), var.clone()))
                    } else {
                        Err(CompilationError::InadmissibleQueryTerm)
                    }
                }
                (":", 2) => {
                    let predicate_name = *terms.pop().unwrap();
                    let module_name = *terms.pop().unwrap();

                    match (module_name, predicate_name) {
                        (
                            Term::Constant(_, Constant::Atom(module_name, _)),
                            Term::Constant(_, Constant::Atom(predicate_name, fixity)),
                        ) => Ok(qualified_clause_to_query_term(
                            load_state,
                            module_name,
                            predicate_name,
                            vec![],
                            fixity,
                        )),
                        (
                            Term::Constant(_, Constant::Atom(module_name, _)),
                            Term::Clause(_, name, terms, fixity),
                        ) => Ok(qualified_clause_to_query_term(
                            load_state,
                            module_name,
                            name,
                            terms,
                            fixity,
                        )),
                        (module_name, predicate_name) => {
                            terms.push(Box::new(module_name));
                            terms.push(Box::new(predicate_name));

                            Ok(clause_to_query_term(load_state, name, terms, fixity))
                        }
                    }
                }
                _ => Ok(clause_to_query_term(load_state, name, terms, fixity)),
            },
            Term::Var(..) => Ok(QueryTerm::Clause(
                Cell::default(),
                ClauseType::CallN,
                vec![Box::new(term)],
                false,
            )),
            _ => Err(CompilationError::InadmissibleQueryTerm),
        }
    }

    fn pre_query_term<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        term: Term,
    ) -> Result<QueryTerm, CompilationError> {
        match term {
            Term::Clause(r, name, mut subterms, fixity) => {
                if subterms.len() == 1 && name.as_str() == "$call_with_default_policy" {
                    self.to_query_term(load_state, *subterms.pop().unwrap())
                        .map(|mut query_term| {
                            query_term.set_default_caller();
                            query_term
                        })
                } else {
                    let clause = Term::Clause(r, name, subterms, fixity);
                    self.to_query_term(load_state, clause)
                }
            }
            _ => self.to_query_term(load_state, term),
        }
    }

    fn setup_query<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        terms: Vec<Box<Term>>,
        cut_context: CutContext,
    ) -> Result<Vec<QueryTerm>, CompilationError> {
        let mut query_terms = vec![];
        let mut work_queue = VecDeque::from(terms);

        while let Some(term) = work_queue.pop_front() {
            let mut term = *term;

            if let Term::Clause(cell, name, terms, op_spec) = term {
                if name.as_str() == "," && terms.len() == 2 {
                    let term = Term::Clause(cell, name, terms, op_spec);
                    let mut subterms = unfold_by_str(term, ",");

                    while let Some(subterm) = subterms.pop() {
                        work_queue.push_front(Box::new(subterm));
                    }

                    continue;
                } else {
                    term = Term::Clause(cell, name, terms, op_spec);
                }
            }

            if let CutContext::HasCutVariable = cut_context {
                mark_cut_variable(&mut term);
            }

            query_terms.push(self.pre_query_term(load_state, term)?);
        }

        Ok(query_terms)
    }

    fn setup_rule<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        mut terms: Vec<Box<Term>>,
        cut_context: CutContext,
    ) -> Result<Rule, CompilationError> {
        let post_head_terms: Vec<_> = terms.drain(1..).collect();
        let mut query_terms = self.setup_query(load_state, post_head_terms, cut_context)?;

        let clauses = query_terms.drain(1..).collect();
        let qt = query_terms.pop().unwrap();

        match *terms.pop().unwrap() {
            Term::Clause(_, name, terms, _) => Ok(Rule {
                head: (name, terms, qt),
                clauses,
            }),
            Term::Constant(_, Constant::Atom(name, _)) => Ok(Rule {
                head: (name, vec![], qt),
                clauses,
            }),
            _ => Err(CompilationError::InvalidRuleHead),
        }
    }

    fn try_term_to_query<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        terms: Vec<Box<Term>>,
        cut_context: CutContext,
    ) -> Result<TopLevel, CompilationError> {
        Ok(TopLevel::Query(self.setup_query(
            load_state,
            terms,
            cut_context,
        )?))
    }

    pub(super) fn try_term_to_tl<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
        term: Term,
        cut_context: CutContext,
    ) -> Result<TopLevel, CompilationError> {
        match term {
            Term::Clause(r, name, terms, fixity) => {
                if name.as_str() == "?-" {
                    self.try_term_to_query(load_state, terms, cut_context)
                } else if name.as_str() == ":-" && terms.len() == 2 {
                    Ok(TopLevel::Rule(self.setup_rule(
                        load_state,
                        terms,
                        cut_context,
                    )?))
                } else {
                    let term = Term::Clause(r, name, terms, fixity);
                    Ok(TopLevel::Fact(self.setup_fact(term)?))
                }
            }
            term => Ok(TopLevel::Fact(self.setup_fact(term)?)),
        }
    }

    fn try_terms_to_tls<'a, I: IntoIterator<Item = Term>>(
        &mut self,
        load_state: &mut LoadState<'a>,
        terms: I,
        cut_context: CutContext,
    ) -> Result<VecDeque<TopLevel>, CompilationError> {
        let mut results = VecDeque::new();

        for term in terms.into_iter() {
            results.push_back(self.try_term_to_tl(load_state, term, cut_context)?);
        }

        Ok(results)
    }

    pub(super) fn parse_queue<'a>(
        &mut self,
        load_state: &mut LoadState<'a>,
    ) -> Result<VecDeque<TopLevel>, CompilationError> {
        let mut queue = VecDeque::new();

        while let Some(terms) = self.queue.pop_front() {
            let clauses = merge_clauses(&mut self.try_terms_to_tls(
                load_state,
                terms,
                CutContext::HasCutVariable,
            )?)?;

            queue.push_back(clauses);
        }

        Ok(queue)
    }
}
