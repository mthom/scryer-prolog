use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::forms::*;
use prolog::iterators::*;
use prolog::machine::*;
use prolog::machine::code_repo::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::MachineState;
use prolog::machine::term_expansion::*;
use prolog::num::*;

use std::borrow::BorrowMut;
use std::collections::{HashMap, HashSet, VecDeque};
use std::cell::Cell;
use std::io::Read;
use std::mem;
use std::rc::Rc;

struct CompositeIndices<'a, 'b> {
    local: &'a mut IndexStore,
    static_code_dir: Option<&'b CodeDir>
}

macro_rules! composite_indices {
    ($in_module: expr, $local: expr, $static_code_dir: expr) => (
        CompositeIndices { local: $local,
                           static_code_dir: if $in_module {
                               None
                           } else {
                               Some($static_code_dir)
                           }}
    );
    ($local: expr) => (
        CompositeIndices { local: $local, static_code_dir: None }
    )
}

impl<'a, 'b> CompositeIndices<'a, 'b>
{
    fn get_code_index(&mut self, name: ClauseName, arity: usize) -> CodeIndex {
        let idx_opt = self.local.code_dir.get(&(name.clone(), arity))
            .or_else(|| {
                match &self.static_code_dir {
                    &Some(ref code_dir) => code_dir.get(&(name.clone(), arity)),
                    _ => None
                }
            }).cloned();

        if let Some(idx) = idx_opt {
            self.local.code_dir.insert((name, arity), idx.clone());
            idx
        } else {
            let idx = CodeIndex::default();
            self.local.code_dir.insert((name, arity), idx.clone());
            idx
        }
    }

    fn get_clause_type(&mut self, name: ClauseName, arity: usize, spec: Option<(usize, Specifier)>) -> ClauseType
    {
        match ClauseType::from(name, arity, spec) {
            ClauseType::Named(name, arity, _) => {
                let idx = self.get_code_index(name.clone(), arity);
                ClauseType::Named(name, arity, idx.clone())
            },
            ClauseType::Op(op_decl, _) => {
                let idx = self.get_code_index(op_decl.2.clone(), arity);
                ClauseType::Op(op_decl, idx.clone())
            },
            ct => ct
        }
    }
}

fn as_compile_time_hook(name: &str, arity: usize, terms: &Vec<Box<Term>>) -> Option<CompileTimeHook>
{
    match (name, arity) {
        ("term_expansion", 2) => Some(CompileTimeHook::TermExpansion),
        ("goal_expansion", 2) => Some(CompileTimeHook::GoalExpansion),
        (":", 2) => {
            if let &Term::Constant(_, Constant::Atom(ref name, _)) = &terms[0].as_ref() {
                if name.as_str() == "user" {
                    if let &Term::Clause(_, ref name, ref terms, _) = &terms[1].as_ref() {
                        return match name.as_str() {
                            "term_expansion" if terms.len() == 2 =>
                                Some(CompileTimeHook::UserTermExpansion),
                            "goal_expansion" if terms.len() == 2 =>
                                Some(CompileTimeHook::UserGoalExpansion),
                            _ => None
                        }
                    }
                }
            }

            None
        },
        _ => None
    }
}

#[inline]
fn is_compile_time_hook(name: &ClauseName, terms: &Vec<Box<Term>>) -> Option<CompileTimeHook> {
    if name.as_str() == ":-" {
        if let Some(ref term) = terms.first() {
            if let &Term::Clause(_, ref name, ref terms, _) = term.as_ref() {
                return as_compile_time_hook(name.as_str(), terms.len(), terms);
            }
        }
    }

    as_compile_time_hook(name.as_str(), terms.len(), terms)
}

type CompileTimeHookCompileInfo = (CompileTimeHook, PredicateClause, VecDeque<TopLevel>);

fn setup_op_decl(mut terms: Vec<Box<Term>>) -> Result<OpDecl, ParserError>
{
    let name = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        _ => return Err(ParserError::InconsistentEntry)
    };

    let spec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        _ => return Err(ParserError::InconsistentEntry)
    };

    let prec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Number(Number::Integer(bi))) =>
            match bi.to_usize() {
                Some(n) if n <= 1200 => n,
                _ => return Err(ParserError::InconsistentEntry)
            },
        _ => return Err(ParserError::InconsistentEntry)
    };

    match spec.as_str() {
        "xfx" => Ok(OpDecl(prec, XFX, name)),
        "xfy" => Ok(OpDecl(prec, XFY, name)),
        "yfx" => Ok(OpDecl(prec, YFX, name)),
        "fx"  => Ok(OpDecl(prec, FX, name)),
        "fy"  => Ok(OpDecl(prec, FY, name)),
        "xf"  => Ok(OpDecl(prec, XF, name)),
        "yf"  => Ok(OpDecl(prec, YF, name)),
        _     => Err(ParserError::InconsistentEntry)
    }
}

fn setup_predicate_indicator(mut term: Term) -> Result<PredicateKey, ParserError>
{
    match term {
        Term::Clause(_, ref name, ref mut terms, Some(_))
            if name.as_str() == "/" && terms.len() == 2 => {
                let arity = *terms.pop().unwrap();
                let name  = *terms.pop().unwrap();

                let arity = arity.to_constant().and_then(|c| c.to_integer())
                    .and_then(|n| if !n.is_negative() { n.to_usize() } else { None })
                    .ok_or(ParserError::InvalidModuleExport)?;

                let name = name.to_constant().and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidModuleExport)?;

                Ok((name, arity))
            },
        _ => Err(ParserError::InvalidModuleExport)
    }
}

fn setup_module_decl(mut terms: Vec<Box<Term>>) -> Result<ModuleDecl, ParserError>
{
    let mut export_list = *terms.pop().unwrap();
    let name = terms.pop().unwrap().to_constant().and_then(|c| c.to_atom())
        .ok_or(ParserError::InvalidModuleDecl)?;

    let mut exports = Vec::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.push(setup_predicate_indicator(*t1)?);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok(ModuleDecl { name, exports })
    }
}

fn setup_use_module_decl(mut terms: Vec<Box<Term>>) -> Result<ClauseName, ParserError>
{
    match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 => {
                terms.pop().unwrap().to_constant()
                    .and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidUseModuleDecl)
            },
        _ => Err(ParserError::InvalidUseModuleDecl)
    }
}

type UseModuleExport = (ClauseName, Vec<PredicateKey>);

fn setup_qualified_import(mut terms: Vec<Box<Term>>) -> Result<UseModuleExport, ParserError>
{
    let mut export_list = *terms.pop().unwrap();
    let name = match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 => {
                terms.pop().unwrap().to_constant()
                    .and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidUseModuleDecl)
            },
        _ => Err(ParserError::InvalidUseModuleDecl)
    }?;

    let mut exports = Vec::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.push(setup_predicate_indicator(*t1)?);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok((name, exports))
    }
}

fn setup_declaration(mut terms: Vec<Box<Term>>) -> Result<Declaration, ParserError>
{
    let term = *terms.pop().unwrap();
    
    match term {
        Term::Clause(_, name, mut terms, _) =>
            if name.as_str() == "op" && terms.len() == 3 {
                Ok(Declaration::Op(setup_op_decl(terms)?))
            } else if name.as_str() == "module" && terms.len() == 2 {
                Ok(Declaration::Module(setup_module_decl(terms)?))
            } else if name.as_str() == "use_module" && terms.len() == 1 {
                Ok(Declaration::UseModule(setup_use_module_decl(terms)?))
            } else if name.as_str() == "use_module" && terms.len() == 2 {
                let (name, exports) = setup_qualified_import(terms)?;
                Ok(Declaration::UseQualifiedModule(name, exports))
            } else if name.as_str() == "non_counted_backtracking" && terms.len() == 1 {
                let (name, arity) = setup_predicate_indicator(*terms.pop().unwrap())?;
                Ok(Declaration::NonCountedBacktracking(name, arity))
            } else if name.as_str() == "dynamic" && terms.len() == 1 {
                let (name, arity) = setup_predicate_indicator(*terms.pop().unwrap())?;
                Ok(Declaration::Dynamic(name, arity))
            } else {
                Err(ParserError::InconsistentEntry)
            },
        _ => return Err(ParserError::InconsistentEntry)
    }
}

fn is_consistent(tl: &TopLevel, clauses: &Vec<PredicateClause>) -> bool
{
    match clauses.first() {
        Some(ref cl) => tl.name() == cl.name() && tl.arity() == cl.arity(),
        None => true
    }
}

fn deque_to_packet(head: TopLevel, deque: VecDeque<TopLevel>) -> TopLevelPacket
{
    match head {
        TopLevel::Query(query) => TopLevelPacket::Query(query, deque),
        tl => TopLevelPacket::Decl(tl, deque)
    }
}

fn merge_clauses(tls: &mut VecDeque<TopLevel>) -> Result<TopLevel, ParserError>
{
    let mut clauses: Vec<PredicateClause> = vec![];

    while let Some(tl) = tls.pop_front() {
        match tl {
            TopLevel::Query(_) if clauses.is_empty() && tls.is_empty() =>
                return Ok(tl),
            TopLevel::Declaration(_) if clauses.is_empty() =>
                return Ok(tl),
            TopLevel::Query(_) =>
                return Err(ParserError::InconsistentEntry),
            TopLevel::Fact(_) if is_consistent(&tl, &clauses) =>
                if let TopLevel::Fact(fact) = tl {
                    let clause = PredicateClause::Fact(fact);
                    clauses.push(clause);
                },
            TopLevel::Rule(_) if is_consistent(&tl, &clauses) =>
                if let TopLevel::Rule(rule) = tl {
                    let clause = PredicateClause::Rule(rule);
                    clauses.push(clause);
                },
            TopLevel::Predicate(_) if is_consistent(&tl, &clauses) =>
                if let TopLevel::Predicate(pred) = tl {
                    clauses.extend(pred.clauses().into_iter())
                },
            _ => {
                tls.push_front(tl);
                break;
            }
        }
    }

    if clauses.is_empty() {
        Err(ParserError::InconsistentEntry)
    } else {
        Ok(TopLevel::Predicate(Predicate(clauses)))
    }
}

fn append_preds(preds: &mut Vec<PredicateClause>) -> Predicate {
    Predicate(mem::replace(preds, vec![]))
}

fn mark_cut_variables_as(terms: &mut Vec<Term>, name: ClauseName) {
    for term in terms.iter_mut() {
        match term {
            &mut Term::Constant(_, Constant::Atom(ref mut var, _)) if var.as_str() == "!" =>
                *var = name.clone(),
            _ => {}
        }
    }
}

fn mark_cut_variable(term: &mut Term) -> bool {
    let cut_var_found = match term {
        &mut Term::Constant(_, Constant::Atom(ref var, _)) if var.as_str() == "!" => true,
        _ => false
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

fn flatten_hook(mut term: Term) -> Term {
    if let &mut Term::Clause(_, ref mut name, ref mut terms, _) = &mut term {
        match (name.as_str(), terms.len()) {
            (":-", 2) => {
                let inner_term = match terms.first_mut().map(|term| term.borrow_mut()) {
                    Some(&mut Term::Clause(_, ref name, ref mut inner_terms, _)) =>
                        if name.as_str() == ":" && inner_terms.len() == 2 {
                            Some(*inner_terms.pop().unwrap())
                        } else {
                            None
                        },
                    _ => None
                };

                if let Some(mut inner_term) = inner_term {
                    mem::swap(&mut terms[0], &mut Box::new(inner_term));
                }
            },
            (":", 2) => return *terms.pop().unwrap(),
            _ => {}
        }
    }

    term
}

pub enum TopLevelPacket {
    Query(Vec<QueryTerm>, VecDeque<TopLevel>),
    Decl(TopLevel, VecDeque<TopLevel>)
}

struct RelationWorker {
    dynamic_clauses: Vec<(Term, Term)>, // Head, Body.
    queue: VecDeque<VecDeque<Term>>,
}

impl RelationWorker {
    fn new() -> Self {
        RelationWorker { dynamic_clauses: vec![],
                         queue: VecDeque::new() }
    }

    fn setup_fact(&mut self, term: Term, assume_dyn: bool) -> Result<Term, ParserError>
    {
        match term {
            Term::Clause(..) | Term::Constant(_, Constant::Atom(..)) => {
                let tail = Term::Constant(Cell::default(),
                                          Constant::Atom(clause_name!("true"), None));

                if assume_dyn {
                    self.dynamic_clauses.push((term.clone(), tail));
                }
                
                Ok(term)
            },
            _ =>
                Err(ParserError::InadmissibleFact)
        }
    }

    fn compute_head(&self, term: &Term) -> Vec<Term>
    {
        let mut vars = HashSet::new();

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

    fn fabricate_rule_body(&self, vars: &Vec<Term>, body_term: Term) -> Term
    {
        let vars_of_head = vars.iter().cloned().map(Box::new).collect();
        let head_term = Term::Clause(Cell::default(), clause_name!(""), vars_of_head, None);

        let rule = vec![Box::new(head_term), Box::new(body_term)];
        let turnstile = clause_name!(":-");

        Term::Clause(Cell::default(), turnstile, rule, None)
    }

    // the terms form the body of the rule. We create a head, by
    // gathering variables from the body of terms and recording them
    // in the head clause.
    fn fabricate_rule(&self, body_term: Term) -> (JumpStub, VecDeque<Term>)
    {
        // collect the vars of body_term into a head, return the num_vars
        // (the arity) as well.
        let vars = self.compute_head(&body_term);
        let rule = self.fabricate_rule_body(&vars, body_term);

        (vars, VecDeque::from(vec![rule]))
    }

    fn fabricate_disjunct(&self, body_term: Term) -> (JumpStub, VecDeque<Term>)
    {
        let vars = self.compute_head(&body_term);
        let clauses: Vec<_> = unfold_by_str(body_term, ";").into_iter()
            .map(|term| {
                let mut subterms = unfold_by_str(term, ",");
                mark_cut_variables(&mut subterms);

                let term = subterms.pop().unwrap();
                fold_by_str(subterms.into_iter(), term, clause_name!(","))
            }).collect();

        let results = clauses.into_iter()
            .map(|clause| self.fabricate_rule_body(&vars, clause))
            .collect();

        (vars, results)
    }

    fn fabricate_if_then(&self, prec: Term, conq: Term) -> (JumpStub, VecDeque<Term>)
    {
        let mut prec_seq = unfold_by_str(prec, ",");
        let comma_sym    = clause_name!(",");
        let cut_sym      = atom!("!");

        prec_seq.push(Term::Constant(Cell::default(), cut_sym));

        mark_cut_variables_as(&mut prec_seq, clause_name!("blocked_!"));

        let mut conq_seq = unfold_by_str(conq, ",");

        mark_cut_variables(&mut conq_seq);
        prec_seq.extend(conq_seq.into_iter());

        let back_term  = Box::new(prec_seq.pop().unwrap());
        let front_term = Box::new(prec_seq.pop().unwrap());

        let body_term  = Term::Clause(Cell::default(), comma_sym.clone(),
                                      vec![front_term, back_term], None);

        self.fabricate_rule(fold_by_str(prec_seq.into_iter(), body_term, comma_sym))
    }

    fn to_query_term(&mut self, indices: &mut CompositeIndices, term: Term) -> Result<QueryTerm, ParserError>
    {
        match term {
            Term::Constant(_, Constant::Atom(name, fixity)) =>
                if name.as_str() == "!" || name.as_str() == "blocked_!" {
                    Ok(QueryTerm::BlockedCut)
                } else {
                    let ct = indices.get_clause_type(name, 0, fixity);
                    Ok(QueryTerm::Clause(Cell::default(), ct, vec![], false))
                },
            Term::Var(_, ref v) if v.as_str() == "!" =>
                Ok(QueryTerm::UnblockedCut(Cell::default())),
            Term::Clause(r, name, mut terms, fixity) =>
                match (name.as_str(), terms.len()) {
                    (";", 2) => {
                        let term = Term::Clause(r, name.clone(), terms, fixity);
                        let (stub, clauses) = self.fabricate_disjunct(term);

                        self.queue.push_back(clauses);
                        Ok(QueryTerm::Jump(stub))
                    },
                    ("->", 2) => {
                        let conq = *terms.pop().unwrap();
                        let prec = *terms.pop().unwrap();

                        let (stub, clauses) = self.fabricate_if_then(prec, conq);

                        self.queue.push_back(clauses);
                        Ok(QueryTerm::Jump(stub))
                    },
                    ("$get_level", 1) =>
                        if let Term::Var(_, ref var) = *terms[0] {
                            Ok(QueryTerm::GetLevelAndUnify(Cell::default(), var.clone()))
                        } else {
                            Err(ParserError::InadmissibleQueryTerm)
                        },
                    ("partial_string", 2) => {
                        if let Term::Constant(_, Constant::String(_)) = *terms[0].clone() {
                            if let Term::Var(..) = *terms[1].clone() {
                                let ct = ClauseType::BuiltIn(BuiltInClauseType::PartialString);
                                return Ok(QueryTerm::Clause(Cell::default(), ct, terms, false));
                            }
                        }

                        Err(ParserError::InadmissibleQueryTerm)
                    },
                    _ => {
                        let ct = indices.get_clause_type(name, terms.len(), fixity);
                        Ok(QueryTerm::Clause(Cell::default(), ct, terms, false))
                    }
                },
            Term::Var(..) =>
                Ok(QueryTerm::Clause(Cell::default(), ClauseType::CallN, vec![Box::new(term)], false)),
            _ => Err(ParserError::InadmissibleQueryTerm)
        }
    }

    // never blocks cuts in the consequent.
    fn prepend_if_then(&self, prec: Term, conq: Term, queue: &mut VecDeque<Box<Term>>,
                       blocks_cuts: bool)
    {
        let cut_symb = atom!("blocked_!");
        let mut terms_seq = unfold_by_str(prec, ",");

        terms_seq.push(Term::Constant(Cell::default(), cut_symb));

        let mut conq_seq = unfold_by_str(conq, ",");

        if !blocks_cuts {
            for item in conq_seq.iter_mut() {
                mark_cut_variable(item);
            }
        }

        terms_seq.append(&mut conq_seq);

        while let Some(term) = terms_seq.pop() {
            queue.push_front(Box::new(term));
        }
    }

    fn pre_query_term(&mut self, indices: &mut CompositeIndices, term: Term) -> Result<QueryTerm, ParserError>
    {
        match term {
            Term::Clause(r, name, mut subterms, fixity) =>
                if subterms.len() == 1 && name.as_str() == "$call_with_default_policy" {
                    self.to_query_term(indices, *subterms.pop().unwrap())
                        .map(|mut query_term| {
                            query_term.set_default_caller();
                            query_term
                        })
                } else {
                    self.to_query_term(indices, Term::Clause(r, name, subterms, fixity))
                },
            _ => self.to_query_term(indices, term)
        }
    }

    fn setup_query(&mut self, indices: &mut CompositeIndices, terms: Vec<Box<Term>>,
                   blocks_cuts: bool)
                   -> Result<Vec<QueryTerm>, ParserError>
    {
        let mut query_terms = vec![];
        let mut work_queue = VecDeque::from(terms);

        while let Some(term) = work_queue.pop_front() {
            let mut term = *term;

            // a (->) clause makes up the entire query. That's what the test confirms.
            if query_terms.is_empty() && work_queue.is_empty() {
                // check for ->, inline it if found.
                if let &mut Term::Clause(_, ref name, ref mut subterms, _) = &mut term {
                    if name.as_str() == "->" && subterms.len() == 2 {
                        let conq = *subterms.pop().unwrap();
                        let prec = *subterms.pop().unwrap();

                        self.prepend_if_then(prec, conq, &mut work_queue, blocks_cuts);
                        continue;
                    }
                }
            }

            for mut subterm in unfold_by_str(term, ",") {
                if !blocks_cuts {
                    mark_cut_variable(&mut subterm);
                }

                query_terms.push(self.pre_query_term(indices, subterm)?);
            }
        }

        Ok(query_terms)
    }

    fn setup_hook(&mut self, hook: CompileTimeHook, indices: &mut CompositeIndices, term: Term)
                  -> Result<CompileTimeHookCompileInfo, ParserError>
    {
        match flatten_hook(term) {
            Term::Clause(r, name, terms, _) =>
                if name == hook.name() && terms.len() == hook.arity() {
                    let term = self.setup_fact(Term::Clause(r, name, terms, None), false)?;
                    Ok((hook, PredicateClause::Fact(term), VecDeque::from(vec![])))
                } else if name.as_str() == ":-" && terms.len() == 2 {
                    let rule = self.setup_rule(indices, terms, true, false)?;
                    let results_queue = self.parse_queue(indices)?;

                    Ok((hook, PredicateClause::Rule(rule), results_queue))
                } else {
                    Err(ParserError::InvalidHook)
                },
            _ => Err(ParserError::InvalidHook)
        }
    }

    fn setup_rule(&mut self, indices: &mut CompositeIndices, mut terms: Vec<Box<Term>>,
                  blocks_cuts: bool, assume_dyn: bool)
                  -> Result<Rule, ParserError>
    {
        let head = *terms.first().cloned().unwrap();
        let post_head_terms: Vec<_> = terms.drain(1 .. ).collect();

        let tail = *post_head_terms.first().cloned().unwrap();

        if assume_dyn {
            self.dynamic_clauses.push((head, tail));
        }

        let mut query_terms = self.setup_query(indices, post_head_terms, blocks_cuts)?;
        let clauses = query_terms.drain(1 ..).collect();
        let qt = query_terms.pop().unwrap();

        match *terms.pop().unwrap() {
            Term::Clause(_, name, terms, _) =>
                Ok(Rule { head: (name, terms, qt), clauses }),
            Term::Constant(_, Constant::Atom(name, _)) =>
                Ok(Rule { head: (name, vec![], qt), clauses }),
            _ => Err(ParserError::InvalidRuleHead)
        }
    }

    fn try_term_to_tl(&mut self, indices: &mut CompositeIndices, term: Term, blocks_cuts: bool)
                      -> Result<TopLevel, ParserError>
    {
        match term {
            Term::Clause(r, name, terms, fixity) =>
                if let Some(hook) = is_compile_time_hook(&name, &terms) {
                    let term = Term::Clause(r, name, terms, fixity);
                    let (hook, clause, queue) = self.setup_hook(hook, indices, term)?;

                    Ok(TopLevel::Declaration(Declaration::Hook(hook, clause, queue)))
                } else if name.as_str() == "?-" {
                    match setup_declaration(terms.iter().cloned().collect()) {
                        Ok(decl) => return Ok(TopLevel::Declaration(decl)),
                        _ => {}
                    };
                    
                    Ok(TopLevel::Query(self.setup_query(indices, terms, blocks_cuts)?))
                } else if name.as_str() == ":-" && terms.len() == 2 {
                    Ok(TopLevel::Rule(self.setup_rule(indices, terms, blocks_cuts, true)?))
                } else if name.as_str() == ":-" && terms.len() == 1 {
                    Ok(TopLevel::Declaration(setup_declaration(terms)?))
                } else {
                    let term = Term::Clause(r, name, terms, fixity);
                    Ok(TopLevel::Fact(try!(self.setup_fact(term, true))))
                },
            term => Ok(TopLevel::Fact(try!(self.setup_fact(term, true))))
        }
    }

    fn try_terms_to_tls<I>(&mut self, indices: &mut CompositeIndices, terms: I, blocks_cuts: bool)
                           -> Result<VecDeque<TopLevel>, ParserError>
        where I: IntoIterator<Item=Term>
    {
        let mut results = VecDeque::new();

        for term in terms.into_iter() {
            results.push_back(self.try_term_to_tl(indices, term, blocks_cuts)?);
        }

        Ok(results)
    }

    fn parse_queue(&mut self, indices: &mut CompositeIndices) -> Result<VecDeque<TopLevel>, ParserError>
    {
        let mut queue = VecDeque::new();

        while let Some(terms) = self.queue.pop_front() {
            let clauses = merge_clauses(&mut self.try_terms_to_tls(indices, terms, false)?)?;
            queue.push_back(clauses);
        }

        Ok(queue)
    }

    fn absorb(&mut self, other: RelationWorker) {
        self.queue.extend(other.queue.into_iter());
        self.dynamic_clauses.extend(other.dynamic_clauses.into_iter());
    }

    fn expand_queue_contents<'a, R>(&mut self, term_stream: &mut TermStream<'a, R>, op_dir: &OpDir)
                                    -> Result<(), SessionError>
        where R: Read
    {
        let mut machine_st = MachineState::new();
        let mut new_queue  = VecDeque::new();

        while let Some(terms) = self.queue.pop_front() {
            let mut new_terms = VecDeque::new();

            for term in terms {
                new_terms.push_back(term_stream.run_goal_expanders(&mut machine_st, &op_dir, term)?);
            }

            new_queue.push_back(new_terms);
        }

        Ok(self.queue = new_queue)
    }
}

fn term_to_toplevel<'a, R>(term_stream: &mut TermStream<'a, R>, code_dir: &mut CodeDir, term: Term)
                           -> Result<(TopLevel, RelationWorker), ParserError>
    where R: Read
{
    let mut rel_worker = RelationWorker::new();
    let mut indices = composite_indices!(false, term_stream.indices, code_dir);

    let tl = rel_worker.try_term_to_tl(&mut indices, term, true)?;
    Ok((tl, rel_worker))
}

pub
fn string_to_toplevel<R: Read>(buffer: R, wam: &mut Machine) -> Result<TopLevelPacket, SessionError>
{
    let mut term_stream = TermStream::new(buffer, wam.indices.atom_tbl(),
                                          wam.machine_flags(), &mut wam.indices,
                                          &mut wam.policies, &mut wam.code_repo);

    let term = term_stream.read_term(&OpDir::new())?;
    let mut code_dir = CodeDir::new();

    let (tl, mut rel_worker) = term_to_toplevel(&mut term_stream, &mut code_dir, term)?;

    rel_worker.expand_queue_contents(&mut term_stream, &OpDir::new())?;

    let mut indices = composite_indices!(false, term_stream.indices, &mut code_dir);
    let queue = rel_worker.parse_queue(&mut indices)?;

    Ok(deque_to_packet(tl, queue))
}

pub type DynamicClauseMap = HashMap<(ClauseName, usize), Vec<(Term, Term)>>;

pub struct TopLevelBatchWorker<'a, R: Read> {
    pub(crate) term_stream: TermStream<'a, R>,
    rel_worker: RelationWorker,
    pub(crate) results: Vec<(Predicate, VecDeque<TopLevel>)>,
    pub(crate) dynamic_clause_map: DynamicClauseMap,
    pub(crate) in_module: bool
}

impl<'a, R: Read> TopLevelBatchWorker<'a, R> {
    pub fn new(inner: R, atom_tbl: TabledData<Atom>,
               flags: MachineFlags, indices: &'a mut IndexStore,
               policies: &'a mut MachinePolicies, code_repo: &'a mut CodeRepo)
               -> Self
    {
        let term_stream = TermStream::new(inner, atom_tbl, flags,
                                          indices, policies, code_repo);

        TopLevelBatchWorker { term_stream,
                              rel_worker: RelationWorker::new(),
                              results: vec![],
                              dynamic_clause_map: HashMap::new(),
                              in_module: false }
    }

    fn try_term_to_tl(&self, indices: &mut IndexStore, term: Term)
                      -> Result<(TopLevel, RelationWorker), SessionError>
    {
        let mut new_rel_worker = RelationWorker::new();
        let mut indices = composite_indices!(self.in_module, indices,
                                             &self.term_stream.indices.code_dir);

        Ok((new_rel_worker.try_term_to_tl(&mut indices, term, true)?, new_rel_worker))
    }

    fn process_result(&mut self, indices: &mut IndexStore, preds: &mut Vec<PredicateClause>)
                      -> Result<(), SessionError>
    {
        self.rel_worker.expand_queue_contents(&mut self.term_stream, &indices.op_dir)?;

        let mut indices = composite_indices!(self.in_module, indices,
                                             &mut self.term_stream.indices.code_dir);

        let queue  = self.rel_worker.parse_queue(&mut indices)?;
        let result = (append_preds(preds), queue);

        let in_situ_code_dir = &mut self.term_stream.indices.in_situ_code_dir;

        self.term_stream.code_repo.add_in_situ_result(&result, in_situ_code_dir,
                                                      self.term_stream.flags)?;

        Ok(self.results.push(result))
    }

    fn take_dynamic_clauses(&mut self) {
        let (name, arity) = match self.rel_worker.dynamic_clauses.first() {
            Some((head, _)) =>
                (head.name().unwrap(), head.arity()),
            None =>
                return
        };

        match self.dynamic_clause_map.get_mut(&(name.clone(), arity)) {
            Some(ref mut entry) => {
                entry.clear(); // don't treat dynamic predicates as if they're discontiguous.
                entry.extend(self.rel_worker.dynamic_clauses.drain(0 ..));
            },
            _ => {
                self.rel_worker.dynamic_clauses.clear();
            }
        }
    }

    pub fn consume(&mut self, indices: &mut IndexStore) -> Result<Option<Declaration>, SessionError>
    {
        let mut preds = vec![];

        while !self.term_stream.eof()? {
            let term = self.term_stream.read_term(&indices.op_dir)?;
            let (tl, new_rel_worker) = self.try_term_to_tl(indices, term)?;

            // if is_consistent is false, preds is non-empty.
            if !is_consistent(&tl, &preds) {
                self.process_result(indices, &mut preds)?;
                self.take_dynamic_clauses();
            }

            self.rel_worker.absorb(new_rel_worker);

            match tl {
                TopLevel::Fact(fact) => preds.push(PredicateClause::Fact(fact)),
                TopLevel::Rule(rule) => preds.push(PredicateClause::Rule(rule)),
                TopLevel::Predicate(pred) => preds.extend(pred.0),
                TopLevel::Declaration(decl) => return Ok(Some(decl)),
                TopLevel::Query(_) => return Err(SessionError::NamelessEntry)
            }
        }

        if !preds.is_empty() {
            self.process_result(indices, &mut preds)?;
            self.take_dynamic_clauses();
        }

        Ok(None)
    }
}
