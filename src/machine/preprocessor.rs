use crate::atom_table::*;
use crate::codegen::CodeGenSettings;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::parser::ast::*;

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

pub(crate) fn fold_by_str<I>(terms: I, mut term: Term, sym: Atom) -> Term
where
    I: DoubleEndedIterator<Item = Term>,
{
    for prec in terms.rev() {
        term = Term::Clause(Cell::default(), sym, vec![prec, term]);
    }

    term
}

pub(crate) fn to_op_decl(
    prec: u16,
    spec: Atom,
    name: Atom,
) -> Result<OpDecl, CompilationError> {
    match spec {
        atom!("xfx") => Ok(OpDecl::new(OpDesc::build_with(prec, XFX as u8), name)),
        atom!("xfy") => Ok(OpDecl::new(OpDesc::build_with(prec, XFY as u8), name)),
        atom!("yfx") => Ok(OpDecl::new(OpDesc::build_with(prec, YFX as u8), name)),
        atom!("fx") => Ok(OpDecl::new(OpDesc::build_with(prec, FX as u8), name)),
        atom!("fy") => Ok(OpDecl::new(OpDesc::build_with(prec, FY as u8), name)),
        atom!("xf") => Ok(OpDecl::new(OpDesc::build_with(prec, XF as u8), name)),
        atom!("yf") => Ok(OpDecl::new(OpDesc::build_with(prec, YF as u8), name)),
        _ => Err(CompilationError::InconsistentEntry),
    }
}

fn setup_op_decl(
    mut terms: Vec<Term>,
    atom_tbl: &mut AtomTable,
) -> Result<OpDecl, CompilationError> {
    let name = match terms.pop().unwrap() {
        Term::Literal(_, Literal::Atom(name)) => name,
        Term::Literal(_, Literal::Char(c)) => atom_tbl.build_with(&c.to_string()),
        _ => return Err(CompilationError::InconsistentEntry),
    };

    let spec = match terms.pop().unwrap() {
        Term::Literal(_, Literal::Atom(name)) => name,
        Term::Literal(_, Literal::Char(c)) => atom_tbl.build_with(&c.to_string()),
        _ => return Err(CompilationError::InconsistentEntry),
    };

    let prec = match terms.pop().unwrap() {
        Term::Literal(_, Literal::Fixnum(bi)) => match u16::try_from(bi.get_num()) {
            Ok(n) if n <= 1200 => n,
            _ => return Err(CompilationError::InconsistentEntry),
        },
        _ => return Err(CompilationError::InconsistentEntry),
    };

    to_op_decl(prec, spec, name)
}

fn setup_predicate_indicator(term: &mut Term) -> Result<PredicateKey, CompilationError> {
    match term {
        Term::Clause(_, slash, ref mut terms)
            if (*slash == atom!("/") || *slash == atom!("//")) && terms.len() == 2 =>
        {
            let arity = terms.pop().unwrap();
            let name = terms.pop().unwrap();

            let arity = match arity {
                Term::Literal(_, Literal::Integer(n)) => n.to_usize(),
                Term::Literal(_, Literal::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
                _ => None,
            }.ok_or(CompilationError::InvalidModuleExport)?;

            let name = match name {
                Term::Literal(_, Literal::Atom(name)) => Some(name),
                _ => None,
            }.ok_or(CompilationError::InvalidModuleExport)?;

            if *slash == atom!("/") {
                Ok((name, arity))
            } else {
                Ok((name, arity + 2))
            }
        }
        _ => Err(CompilationError::InvalidModuleExport),
    }
}

fn setup_module_export(
    mut term: Term,
    atom_tbl: &mut AtomTable,
) -> Result<ModuleExport, CompilationError> {
    setup_predicate_indicator(&mut term)
        .map(ModuleExport::PredicateKey)
        .or_else(|_| {
            if let Term::Clause(_, name, terms) = term {
                if terms.len() == 3 && name == atom!("op") {
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
    atom_tbl: &mut AtomTable,
) -> Result<Vec<ModuleExport>, CompilationError> {
    let mut exports = vec![];

    while let Term::Cons(_, t1, t2) = export_list {
        let module_export = setup_module_export(*t1, atom_tbl)?;

        exports.push(module_export);
        export_list = *t2;
    }

    if let Term::Literal(_, Literal::Atom(atom!("[]"))) = export_list {
        Ok(exports)
    } else {
        Err(CompilationError::InvalidModuleDecl)
    }
}

fn setup_module_decl(
    mut terms: Vec<Term>,
    atom_tbl: &mut AtomTable,
) -> Result<ModuleDecl, CompilationError> {
    let export_list = terms.pop().unwrap();
    let name = terms.pop().unwrap();

    let name = match name {
        Term::Literal(_, Literal::Atom(name)) => Some(name),
        _ => None,
    }.ok_or(CompilationError::InvalidModuleDecl)?;

    let exports = setup_module_export_list(export_list, atom_tbl)?;

    Ok(ModuleDecl { name, exports })
}

fn setup_use_module_decl(mut terms: Vec<Term>) -> Result<ModuleSource, CompilationError> {
    match terms.pop().unwrap() {
        Term::Clause(_, name, mut terms)
            if name == atom!("library") && terms.len() == 1 =>
        {
            match terms.pop().unwrap() {
                Term::Literal(_, Literal::Atom(name)) => Ok(ModuleSource::Library(name)),
                _ => Err(CompilationError::InvalidModuleDecl),
            }
        }
        Term::Literal(_, Literal::Atom(name)) => Ok(ModuleSource::File(name)),
        _ => Err(CompilationError::InvalidUseModuleDecl),
    }
}

type UseModuleExport = (ModuleSource, IndexSet<ModuleExport>);

fn setup_qualified_import(
    mut terms: Vec<Term>,
    atom_tbl: &mut AtomTable,
) -> Result<UseModuleExport, CompilationError> {
    let mut export_list = terms.pop().unwrap();
    let module_src = match terms.pop().unwrap() {
        Term::Clause(_, name, mut terms)
            if name == atom!("library") && terms.len() == 1 =>
        {
            match terms.pop().unwrap() {
                Term::Literal(_, Literal::Atom(name)) => Ok(ModuleSource::Library(name)),
                _ => Err(CompilationError::InvalidModuleDecl),
            }
        }
        Term::Literal(_, Literal::Atom(name)) => Ok(ModuleSource::File(name)),
        _ => Err(CompilationError::InvalidUseModuleDecl),
    }?;

    let mut exports = IndexSet::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.insert(setup_module_export(*t1, atom_tbl)?);
        export_list = *t2;
    }

    if let Term::Literal(_, Literal::Atom(atom!("[]"))) = export_list {
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

fn setup_meta_predicate<'a, LS: LoadState<'a>>(
    mut terms: Vec<Term>,
    loader: &mut Loader<'a, LS>,
) -> Result<(Atom, Atom, Vec<MetaSpec>), CompilationError> {
    fn get_name_and_meta_specs(
        name: Atom,
        terms: &mut [Term],
    ) -> Result<(Atom, Vec<MetaSpec>), CompilationError> {
        let mut meta_specs = vec![];

        for meta_spec in terms.into_iter() {
            match meta_spec {
                Term::Literal(_, Literal::Atom(meta_spec)) => {
                    let meta_spec = match meta_spec {
                        atom!("+") => MetaSpec::Plus,
                        atom!("-") => MetaSpec::Minus,
                        atom!("?") => MetaSpec::Either,
                        atom!(":") => MetaSpec::Colon,
                        _ => return Err(CompilationError::InvalidMetaPredicateDecl),
                    };

                    meta_specs.push(meta_spec);
                }
                Term::Literal(_, Literal::Fixnum(n)) => match usize::try_from(n.get_num()) {
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

    match terms.pop().unwrap() {
        Term::Clause(_, name, mut terms) if name == atom!(":") && terms.len() == 2 => {
            let spec = terms.pop().unwrap();
            let module_name = terms.pop().unwrap();

            match module_name {
                Term::Literal(_, Literal::Atom(module_name)) => match spec {
                    Term::Clause(_, name, mut terms) => {
                        let (name, meta_specs) = get_name_and_meta_specs(name, &mut terms)?;
                        Ok((module_name, name, meta_specs))
                    }
                    _ => Err(CompilationError::InvalidMetaPredicateDecl),
                },
                _ => Err(CompilationError::InvalidMetaPredicateDecl),
            }
        }
        Term::Clause(_, name, mut terms) => {
            let (name, meta_specs) = get_name_and_meta_specs(name, &mut terms)?;
            Ok((
                loader.payload.compilation_target.module_name(),
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

fn mark_cut_variables_as(terms: &mut Vec<Term>, name: Atom) {
    for term in terms.iter_mut() {
        match term {
            &mut Term::Literal(_, Literal::Atom(ref mut var)) if *var == atom!("!") => {
                *var = name;
            }
            _ => {}
        }
    }
}

fn mark_cut_variable(term: &mut Term) -> bool {
    let cut_var_found = match term {
        &mut Term::Literal(_, Literal::Atom(ref var)) if *var == atom!("!") => true,
        _ => false,
    };

    if cut_var_found {
        *term = Term::Var(Cell::default(), Rc::new(String::from("!")));
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

    if let Some(Term::Clause(_, name, ref subterms)) = terms.last() {
        if *name != atom!("->") || source_arity(subterms) != 2 {
            return;
        }
    } else {
        return;
    }

    if let Some(Term::Clause(_, _, mut subterms)) = terms.pop() {
        let mut conq_terms = VecDeque::from(unfold_by_str(subterms.pop().unwrap(), atom!(",")));
        let mut pre_cut_terms = VecDeque::from(unfold_by_str(subterms.pop().unwrap(), atom!(",")));

        conq_terms.push_front(Term::Literal(
            Cell::default(),
            Literal::Atom(atom!("blocked_!")),
        ));

        while let Some(term) = pre_cut_terms.pop_back() {
            conq_terms.push_front(term);
        }

        let tail_term = conq_terms.pop_back().unwrap();

        terms.push(fold_by_str(
            conq_terms.into_iter(),
            tail_term,
            atom!(","),
        ));
    }
}

pub(super) fn setup_declaration<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    mut terms: Vec<Term>,
) -> Result<Declaration, CompilationError> {
    let term = terms.pop().unwrap();

    match term {
        Term::Clause(_, name, mut terms) => match (name, terms.len()) {
            (atom!("dynamic"), 1) => {
                let (name, arity) = setup_predicate_indicator(&mut terms.pop().unwrap())?;
                Ok(Declaration::Dynamic(name, arity))
            }
            (atom!("module"), 2) => {
                let atom_tbl = &mut LS::machine_st(&mut loader.payload).atom_tbl;
                Ok(Declaration::Module(setup_module_decl(terms, atom_tbl)?))
            }
            (atom!("op"), 3) => {
                let atom_tbl = &mut LS::machine_st(&mut loader.payload).atom_tbl;
                Ok(Declaration::Op(setup_op_decl(terms, atom_tbl)?))
            }
            (atom!("non_counted_backtracking"), 1) => {
                let (name, arity) = setup_predicate_indicator(&mut terms.pop().unwrap())?;
                Ok(Declaration::NonCountedBacktracking(name, arity))
            }
            (atom!("use_module"), 1) => Ok(Declaration::UseModule(setup_use_module_decl(terms)?)),
            (atom!("use_module"), 2) => {
                let atom_tbl = &mut LS::machine_st(&mut loader.payload).atom_tbl;
                let (name, exports) = setup_qualified_import(terms, atom_tbl)?;

                Ok(Declaration::UseQualifiedModule(name, exports))
            }
            (atom!("meta_predicate"), 1) => {
                let (module_name, name, meta_specs) = setup_meta_predicate(terms, loader)?;
                Ok(Declaration::MetaPredicate(module_name, name, meta_specs))
            }
            _ => Err(CompilationError::InconsistentEntry),
        },
        _ => Err(CompilationError::InconsistentEntry),
    }
}

fn build_meta_predicate_clause<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    module_name: Atom,
    terms: Vec<Term>,
    meta_specs: Vec<MetaSpec>,
) -> Vec<Term> {
    let mut arg_terms = Vec::with_capacity(terms.len());

    for (term, meta_spec) in terms.into_iter().zip(meta_specs.iter()) {
        if let MetaSpec::RequiresExpansionWithArgument(supp_args) = meta_spec {
            if let Some(name) = term.name() {
                if name == atom!("$call") {
                    arg_terms.push(term);
                    continue;
                }

                let arity = term.arity();

                fn get_qualified_name(
                    module_term: &Term,
                    qualified_term: &Term,
                ) -> Option<(Atom, Atom)> {
                    if let Term::Literal(_, Literal::Atom(module_name)) = module_term {
                        if let Some(name) = qualified_term.name() {
                            return Some((*module_name, name));
                        }
                    }

                    None
                }

                fn identity_fn(_module_name: Atom, term: Term) -> Term {
                    term
                }

                fn tag_with_module_name(module_name: Atom, term: Term) -> Term {
                    Term::Clause(Cell::default(), atom!(":"), vec![
                        Term::Literal(Cell::default(), Literal::Atom(module_name)),
                        term
                    ])
                }

                let process_term: fn(Atom, Term) -> Term;

                let (module_name, key, term) = match term {
                    Term::Clause(cell, atom!(":"), mut terms) if terms.len() == 2 => {
                        if let Some((module_name, name)) = get_qualified_name(&terms[0], &terms[1]) {
                            process_term = tag_with_module_name;
                            (module_name, (name, terms[1].arity() + supp_args), terms.pop().unwrap())
                        } else {
                            arg_terms.push(Term::Clause(cell, atom!(":"), terms));
                            continue;
                        }
                    }
                    term => {
                        process_term = identity_fn;
                        (module_name, (name, arity + supp_args), term)
                    }
                };

                let term = match term {
                    Term::Clause(cell, name, mut terms) => {
                        if let Some(Term::Literal(_, Literal::CodeIndex(_))) = terms.last() {
                            arg_terms.push(process_term(
                                module_name,
                                Term::Clause(cell, name, terms),
                            ));

                            continue;
                        }

                        let idx = loader.get_or_insert_qualified_code_index(module_name, key);

                        terms.push(Term::Literal(Cell::default(), Literal::CodeIndex(idx)));
                        process_term(module_name, Term::Clause(cell, name, terms))
                    }
                    Term::Literal(cell, Literal::Atom(name)) => {
                        let idx = loader.get_or_insert_qualified_code_index(module_name, key);

                        process_term(module_name, Term::Clause(
                            cell,
                            name,
                            vec![Term::Literal(Cell::default(), Literal::CodeIndex(idx))],
                        ))
                    }
                    term => term,
                };

                arg_terms.push(term);
                continue;
            }
        }

        arg_terms.push(term);
    }

    arg_terms
}

#[inline]
fn clause_to_query_term<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    name: Atom,
    mut terms: Vec<Term>,
    call_policy: CallPolicy,
) -> QueryTerm {
    if let Some(Term::Literal(_, Literal::CodeIndex(_))) = terms.last() {
        // supplementary code vector indices are unnecessary for
        // root-level clauses.
        terms.pop();
    }

    let mut ct = loader.get_clause_type(name, terms.len());

    if let ClauseType::Named(arity, name, idx) = ct {
        if let Some(meta_specs) = loader.get_meta_specs(name, arity).cloned() {
            let module_name = loader.payload.compilation_target.module_name();
            let terms = build_meta_predicate_clause(
                loader,
                module_name,
                terms,
                meta_specs,
            );

            return QueryTerm::Clause(
                Cell::default(),
                ClauseType::Named(arity, name, idx),
                terms,
                call_policy,
            );
        }

        ct = ClauseType::Named(arity, name, idx);
    }

    QueryTerm::Clause(Cell::default(), ct, terms, call_policy)
}

#[inline]
fn qualified_clause_to_query_term<'a, LS: LoadState<'a>>(
    loader: &mut Loader<'a, LS>,
    module_name: Atom,
    name: Atom,
    mut terms: Vec<Term>,
    call_policy: CallPolicy,
) -> QueryTerm {
    if let Some(Term::Literal(_, Literal::CodeIndex(_))) = terms.last() {
        // supplementary code vector indices are unnecessary for
        // root-level clauses.
        terms.pop();
    }

    let mut ct = loader.get_qualified_clause_type(module_name, name, terms.len());

    if let ClauseType::Named(arity, name, idx) = ct {
        if let Some(meta_specs) = loader.get_meta_specs(name, arity).cloned() {
            let terms = build_meta_predicate_clause(
                loader,
                module_name,
                terms,
                meta_specs,
            );

            return QueryTerm::Clause(
                Cell::default(),
                ClauseType::Named(arity, name, idx),
                terms,
                call_policy,
            );
        }

        ct = ClauseType::Named(arity, name, idx);
    }

    QueryTerm::Clause(Cell::default(), ct, terms, call_policy)
}

fn compute_head(term: &Term) -> Vec<Term> {
    let mut vars = IndexSet::new();

    for term in post_order_iter(term) {
        if let TermRef::Var(_, _, v) = term {
            vars.insert(v.clone());
        }
    }

    vars.insert(Rc::new(String::from("!")));
    vars.into_iter()
        .map(|v| Term::Var(Cell::default(), v))
        .collect()
}

pub(crate) fn build_rule_body(vars: &[Term], body_term: Term) -> Term {
    let head_term = Term::Clause(Cell::default(), atom!(""), vars.iter().cloned().collect());
    let rule = vec![head_term, body_term];

    Term::Clause(Cell::default(), atom!(":-"), rule)
}

// the terms form the body of the rule. We create a head, by
// gathering variables from the body of terms and recording them
// in the head clause.
fn build_rule(body_term: Term) -> (JumpStub, VecDeque<Term>) {
    // collect the vars of body_term into a head, return the num_vars
    // (the arity) as well.
    let vars = compute_head(&body_term);
    let rule = build_rule_body(&vars, body_term);

    (vars, VecDeque::from(vec![rule]))
}

fn build_disjunct(body_term: Term) -> (JumpStub, VecDeque<Term>) {
    let vars = compute_head(&body_term);
    let results = unfold_by_str(body_term, atom!(";"))
        .into_iter()
        .map(|term| {
            let mut subterms = unfold_by_str(term, atom!(","));
            mark_cut_variables(&mut subterms);

            check_for_internal_if_then(&mut subterms);

            let term = subterms.pop().unwrap();
            let clause = fold_by_str(subterms.into_iter(), term, atom!(","));

            build_rule_body(&vars, clause)
        })
        .collect();

    (vars, results)
}

fn build_if_then(prec: Term, conq: Term) -> (JumpStub, VecDeque<Term>) {
    let mut prec_seq = unfold_by_str(prec, atom!(","));
    let comma_sym = atom!(",");
    let cut_sym = Literal::Atom(atom!("!"));

    prec_seq.push(Term::Literal(Cell::default(), cut_sym));

    mark_cut_variables_as(&mut prec_seq, atom!("blocked_!"));

    let mut conq_seq = unfold_by_str(conq, atom!(","));

    mark_cut_variables(&mut conq_seq);
    prec_seq.extend(conq_seq.into_iter());

    let back_term = prec_seq.pop().unwrap();
    let front_term = prec_seq.pop().unwrap();

    let body_term = Term::Clause(
        Cell::default(),
        comma_sym,
        vec![front_term, back_term],
    );

    build_rule(fold_by_str(prec_seq.into_iter(), body_term, comma_sym))
}

#[derive(Debug)]
pub(crate) struct Preprocessor {
    queue: VecDeque<VecDeque<Term>>,
    settings: CodeGenSettings,
}

impl Preprocessor {
    pub(super) fn new(settings: CodeGenSettings) -> Self {
        Preprocessor {
            queue: VecDeque::new(),
            settings,
        }
    }

    fn setup_fact(&mut self, term: Term) -> Result<Term, CompilationError> {
        match term {
            Term::Clause(..) | Term::Literal(_, Literal::Atom(..)) => Ok(term),
            _ => Err(CompilationError::InadmissibleFact),
        }
    }

    fn to_query_term<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: Term,
    ) -> Result<QueryTerm, CompilationError> {
        match term {
            Term::Literal(_, Literal::Atom(name)) => {
                if name == atom!("!") || name == atom!("blocked_!") {
                    Ok(QueryTerm::BlockedCut)
                } else {
                    Ok(clause_to_query_term(
                        loader,
                        name,
                        vec![],
                        self.settings.default_call_policy(),
                    ))
                }
            }
            Term::Literal(_, Literal::Char('!')) => Ok(QueryTerm::BlockedCut),
            Term::Var(_, ref v) if v.as_str() == "!" => {
                Ok(QueryTerm::UnblockedCut(Cell::default()))
            }
            Term::Clause(r, name, mut terms) => match (name, source_arity(&terms)) {
                (atom!(";"), 2) => {
                    let term = Term::Clause(r, name, terms);

                    let (stub, clauses) = build_disjunct(term);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                (atom!("->"), 2) => {
                    let conq = terms.pop().unwrap();
                    let prec = terms.pop().unwrap();

                    let (stub, clauses) = build_if_then(prec, conq);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                (atom!("\\+"), 1) => {
                    terms.push(Term::Literal(
                        Cell::default(),
                        Literal::Atom(atom!("$fail")),
                    ));

                    let conq = Term::Literal(Cell::default(), Literal::Atom(atom!("true")));

                    let prec = Term::Clause(Cell::default(), atom!("->"), terms);
                    let terms = vec![prec, conq];

                    let term = Term::Clause(Cell::default(), atom!(";"), terms);
                    let (stub, clauses) = build_disjunct(term);

                    debug_assert!(clauses.len() > 0);
                    self.queue.push_back(clauses);

                    Ok(QueryTerm::Jump(stub))
                }
                (atom!("$get_level"), 1) => {
                    if let Term::Var(_, ref var) = &terms[0] {
                        Ok(QueryTerm::GetLevelAndUnify(Cell::default(), var.clone()))
                    } else {
                        Err(CompilationError::InadmissibleQueryTerm)
                    }
                }
                (atom!(":"), 2) => {
                    let predicate_name = terms.pop().unwrap();
                    let module_name = terms.pop().unwrap();

                    match (module_name, predicate_name) {
                        (
                            Term::Literal(_, Literal::Atom(module_name)),
                            Term::Literal(_, Literal::Atom(predicate_name)),
                        ) => Ok(qualified_clause_to_query_term(
                            loader,
                            module_name,
                            predicate_name,
                            vec![],
                            self.settings.default_call_policy(),
                        )),
                        (
                            Term::Literal(_, Literal::Atom(module_name)),
                            Term::Clause(_, name, terms),
                        ) => Ok(qualified_clause_to_query_term(
                            loader,
                            module_name,
                            name,
                            terms,
                            self.settings.default_call_policy()
                        )),
                        (module_name, predicate_name) => {
                            terms.push(module_name);
                            terms.push(predicate_name);

                            Ok(clause_to_query_term(
                                loader,
                                atom!("call"),
                                vec![Term::Clause(r, name, terms)],
                                self.settings.default_call_policy(),
                            ))
                        }
                    }
                }
                _ => Ok(clause_to_query_term(loader, name, terms,
                                             self.settings.default_call_policy())),
            },
            Term::Var(..) => Ok(QueryTerm::Clause(
                Cell::default(),
                ClauseType::CallN(1),
                vec![term],
                self.settings.default_call_policy(),
            )),
            _ => Err(CompilationError::InadmissibleQueryTerm),
        }
    }

    fn pre_query_term<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: Term,
    ) -> Result<QueryTerm, CompilationError> {
        match term {
            Term::Clause(r, name, mut subterms) => {
                if subterms.len() == 1 && name == atom!("$call_with_inference_counting") {
                    self.to_query_term(loader, subterms.pop().unwrap())
                        .map(|mut query_term| {
                            query_term.set_call_policy(CallPolicy::Counted);
                            query_term
                        })
                } else {
                    let clause = Term::Clause(r, name, subterms);
                    self.to_query_term(loader, clause)
                }
            }
            _ => self.to_query_term(loader, term),
        }
    }

    fn setup_query<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        terms: Vec<Term>,
        cut_context: CutContext,
    ) -> Result<Vec<QueryTerm>, CompilationError> {
        let mut query_terms = vec![];
        let mut work_queue = VecDeque::from(terms);

        while let Some(term) = work_queue.pop_front() {
            let mut term = term;

            if let Term::Clause(cell, name, terms) = term {
                if name == atom!(",") && source_arity(&terms) == 2 {
                    let term = Term::Clause(cell, name, terms);
                    let mut subterms = unfold_by_str(term, atom!(","));

                    while let Some(subterm) = subterms.pop() {
                        work_queue.push_front(subterm);
                    }

                    continue;
                } else {
                    term = Term::Clause(cell, name, terms);
                }
            }

            if let CutContext::HasCutVariable = cut_context {
                mark_cut_variable(&mut term);
            }

            query_terms.push(self.pre_query_term(loader, term)?);
        }

        Ok(query_terms)
    }

    fn setup_rule<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        mut terms: Vec<Term>,
        cut_context: CutContext,
    ) -> Result<Rule, CompilationError> {
        let post_head_terms: Vec<_> = terms.drain(1..).collect();
        let mut query_terms = self.setup_query(loader, post_head_terms, cut_context)?;

        let clauses = query_terms.drain(1..).collect();
        let qt = query_terms.pop().unwrap();

        match terms.pop().unwrap() {
            Term::Clause(_, name, terms) => Ok(Rule {
                head: (name, terms, qt),
                clauses,
            }),
            Term::Literal(_, Literal::Atom(name)) => Ok(Rule {
                head: (name, vec![], qt),
                clauses,
            }),
            _ => Err(CompilationError::InvalidRuleHead),
        }
    }

    fn try_term_to_query<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        terms: Vec<Term>,
        cut_context: CutContext,
    ) -> Result<TopLevel, CompilationError> {
        Ok(TopLevel::Query(self.setup_query(
            loader,
            terms,
            cut_context,
        )?))
    }

    pub(super) fn try_term_to_tl<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: Term,
        cut_context: CutContext,
    ) -> Result<TopLevel, CompilationError> {
        match term {
            Term::Clause(r, name, terms) => {
                if name == atom!("?-") {
                    self.try_term_to_query(loader, terms, cut_context)
                } else if name == atom!(":-") && terms.len() == 2 {
                    Ok(TopLevel::Rule(self.setup_rule(
                        loader,
                        terms,
                        cut_context,
                    )?))
                } else {
                    let term = Term::Clause(r, name, terms);
                    Ok(TopLevel::Fact(self.setup_fact(term)?))
                }
            }
            term => Ok(TopLevel::Fact(self.setup_fact(term)?)),
        }
    }

    fn try_terms_to_tls<'a, I: IntoIterator<Item = Term>, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        terms: I,
        cut_context: CutContext,
    ) -> Result<VecDeque<TopLevel>, CompilationError> {
        let mut results = VecDeque::new();

        for term in terms.into_iter() {
            results.push_back(self.try_term_to_tl(loader, term, cut_context)?);
        }

        Ok(results)
    }

    pub(super) fn parse_queue<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
    ) -> Result<VecDeque<TopLevel>, CompilationError> {
        let mut queue = VecDeque::new();

        while let Some(terms) = self.queue.pop_front() {
            let clauses = merge_clauses(&mut self.try_terms_to_tls(
                loader,
                terms,
                CutContext::HasCutVariable,
            )?)?;

            queue.push_back(clauses);
        }

        Ok(queue)
    }
}
