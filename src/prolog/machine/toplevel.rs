use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use crate::prolog::forms::*;
use crate::prolog::iterators::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::term_expansion::*;
use crate::prolog::machine::*;

use indexmap::{IndexMap, IndexSet};

use std::borrow::BorrowMut;
use std::cell::Cell;
use std::collections::VecDeque;
use std::io::Read;
use std::mem;
use std::ops::DerefMut;
use std::rc::Rc;

enum IndexSource<'a, T> {
    TermStream,
    Local(&'a mut T)
}

fn op_dir<'a, 'b: 'a>(from: &'b IndexSource<'a, IndexStore>) -> RefOrOwned<'a, OpDir> {
    match from {
        IndexSource::TermStream => RefOrOwned::Owned(OpDir::new()),
        IndexSource::Local(ref indices) => RefOrOwned::Borrowed(&indices.op_dir)
    }
}

struct CompositeIndices<'a, 'b, 'c, R: Read> {
    term_stream: &'b mut TermStream<'a, R>,
    index_src: IndexSource<'c, IndexStore>,
    static_code_dir: Option<IndexSource<'c, CodeDir>>
}

impl<'a, 'b, 'c, R: Read> CompositeIndices<'a, 'b, 'c, R> {
    fn new(
        term_stream: &'b mut TermStream<'a, R>,
        index_src: IndexSource<'c, IndexStore>,
        static_code_dir: Option<IndexSource<'c, CodeDir>>,
    ) -> Self {
        CompositeIndices {
            term_stream,
            index_src,
            static_code_dir,
        }
    }

    fn atom_tbl(&self) -> TabledData<Atom> {
        match self.index_src {
            IndexSource::TermStream => self.term_stream.wam.indices.atom_tbl.clone(),
            IndexSource::Local(ref indices) => indices.atom_tbl.clone(),
        }
    }

    fn local_code_dir(&mut self) -> &mut CodeDir {
        match self.index_src {
            IndexSource::TermStream => &mut self.term_stream.wam.indices.code_dir,
            IndexSource::Local(ref mut indices) => &mut indices.code_dir,
        }
    }

    fn static_code_dir(&self) -> Option<&CodeDir> {
        match self.static_code_dir {
            Some(IndexSource::TermStream) => Some(&self.term_stream.wam.indices.code_dir),
            Some(IndexSource::Local(ref code_dir)) => Some(code_dir),
            None => None
        }
    }

    fn get_code_index(&mut self, name: ClauseName, arity: usize) -> CodeIndex {
        let idx_opt = self.local_code_dir().get(&(name.clone(), arity));
        let idx_opt = match idx_opt {
            Some(idx) => Some(idx.clone()),
            None => match self.static_code_dir() {
                Some(ref code_dir) => code_dir.get(&(name.clone(), arity)).cloned(),
                _ => None,
            }
        };

        if let Some(idx) = idx_opt {
            self.local_code_dir().insert((name.clone(), arity), idx.clone());
            idx
        } else {
            let idx = CodeIndex::default();
            self.local_code_dir().insert((name.clone(), arity), idx.clone());
            idx
        }
    }

    fn get_clause_type(
        &mut self,
        name: ClauseName,
        arity: usize,
        spec: Option<SharedOpDesc>,
    ) -> ClauseType {
        match ClauseType::from(name, arity, spec) {
            ClauseType::Named(name, arity, _) => {
                let idx = self.get_code_index(name.clone(), arity);
                ClauseType::Named(name, arity, idx.clone())
            }
            ClauseType::Op(name, spec, _) => {
                let idx = self.get_code_index(name.clone(), arity);
                ClauseType::Op(name, spec, idx.clone())
            }
            ct => ct,
        }
    }

    fn add_in_situ_module_info(&mut self, module_name: ClauseName, term: &mut Term)
    {
        let atom_tbl =
            match self.term_stream.wam.indices.in_situ_module_dir.get(&module_name) {
                Some(ref module_stub) => module_stub.atom_tbl.clone(),
                None => {
                    let atom_tbl = match self.term_stream.wam.indices.modules.get(&module_name) {
                        Some(ref module) => module.atom_tbl.clone(),
                        None => TabledData::new(module_name.to_rc()),
                    };

                    self.term_stream.wam.indices.in_situ_module_dir.insert(
                        module_name.clone(),
                        ModuleStub::new(atom_tbl.clone()),
                    );

                    atom_tbl
                }
            };

        if let Some(name) = term.name() {
            term.set_name(name.with_table(atom_tbl));
        }
    }
}

fn as_compile_time_hook(
    name: &str,
    arity: usize,
    terms: &Vec<Box<Term>>,
) -> Option<CompileTimeHook> {
    match (name, arity) {
        ("term_expansion", 2) => Some(CompileTimeHook::TermExpansion),
        ("goal_expansion", 2) => Some(CompileTimeHook::GoalExpansion),
        (":", 2) => {
            if let &Term::Constant(_, Constant::Atom(ref name, _)) = &terms[0].as_ref() {
                if name.as_str() == "user" {
                    if let &Term::Clause(_, ref name, ref terms, _) = &terms[1].as_ref() {
                        return match name.as_str() {
                            "term_expansion" if terms.len() == 2 => {
                                Some(CompileTimeHook::UserTermExpansion)
                            }
                            "goal_expansion" if terms.len() == 2 => {
                                Some(CompileTimeHook::UserGoalExpansion)
                            }
                            _ => None,
                        };
                    }
                }
            }

            None
        }
        _ => None,
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

pub fn to_op_decl(prec: usize, spec: &str, name: ClauseName) -> Result<OpDecl, ParserError> {
    match spec {
        "xfx" => Ok(OpDecl(prec, XFX, name)),
        "xfy" => Ok(OpDecl(prec, XFY, name)),
        "yfx" => Ok(OpDecl(prec, YFX, name)),
        "fx" => Ok(OpDecl(prec, FX, name)),
        "fy" => Ok(OpDecl(prec, FY, name)),
        "xf" => Ok(OpDecl(prec, XF, name)),
        "yf" => Ok(OpDecl(prec, YF, name)),
        _ => Err(ParserError::InconsistentEntry),
    }
}

fn setup_op_decl(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<OpDecl, ParserError> {
    let name = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        Term::Constant(_, Constant::Char(c)) => clause_name!(c.to_string(), atom_tbl.clone()),
        _ => return Err(ParserError::InconsistentEntry),
    };

    let spec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name, _)) => name,
        Term::Constant(_, Constant::Char(c)) => clause_name!(c.to_string(), atom_tbl.clone()),
        _ => return Err(ParserError::InconsistentEntry),
    };

    let prec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Integer(bi)) => match bi.to_usize() {
            Some(n) if n <= 1200 => n,
            _ => return Err(ParserError::InconsistentEntry),
        },
        _ => return Err(ParserError::InconsistentEntry),
    };

    to_op_decl(prec, spec.as_str(), name)
}

fn setup_predicate_indicator(term: &mut Term) -> Result<PredicateKey, ParserError>
{
    match term {
        Term::Clause(_, ref name, ref mut terms, Some(_))
            if name.as_str() == "/" && terms.len() == 2 =>
        {
            let arity = *terms.pop().unwrap();
            let name  = *terms.pop().unwrap();

            let arity = arity
                .to_constant()
                .and_then(|c| c.to_integer())
                .and_then(|n| n.to_usize())
                .ok_or(ParserError::InvalidModuleExport)?;

            let name  = name
                .to_constant()
                .and_then(|c| c.to_atom())
                .ok_or(ParserError::InvalidModuleExport)?;

            Ok((name, arity))
        }
        _ => Err(ParserError::InvalidModuleExport),
    }
}

fn setup_scoped_predicate_indicator(term: &mut Term) -> Result<ScopedPredicateKey, ParserError>
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
                .ok_or(ParserError::InvalidModuleExport)?;

            let key = setup_predicate_indicator(&mut predicate_indicator)?;

            Ok((module_name, key))
        }
        _ => Err(ParserError::InvalidModuleExport),
    }
}

fn setup_module_export(
    mut term: Term,
    atom_tbl: TabledData<Atom>,
) -> Result<ModuleExport, ParserError> {
    setup_predicate_indicator(&mut term)
        .map(ModuleExport::PredicateKey)
        .or_else(|_| {
            if let Term::Clause(_, name, terms, _) = term {
                if terms.len() == 3 && name.as_str() == "op" {
                    Ok(ModuleExport::OpDecl(setup_op_decl(
                        terms,
                        atom_tbl
                    )?))
                } else {
                    Err(ParserError::InvalidModuleDecl)
                }
            } else {
                Err(ParserError::InvalidModuleDecl)
            }
        })
}

fn setup_module_decl(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<ModuleDecl, ParserError> {
    let mut export_list = *terms.pop().unwrap();
    let name = terms
        .pop()
        .unwrap()
        .to_constant()
        .and_then(|c| c.to_atom())
        .ok_or(ParserError::InvalidModuleDecl)?;

    let mut exports = vec![];

    while let Term::Cons(_, t1, t2) = export_list {
        let module_export = setup_module_export(*t1, atom_tbl.clone())?;

        exports.push(module_export);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok(ModuleDecl { name, exports })
    }
}

fn setup_use_module_decl(mut terms: Vec<Box<Term>>) -> Result<ModuleSource, ParserError> {
    match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 =>
        {
            terms
                .pop()
                .unwrap()
                .to_constant()
                .and_then(|c| c.to_atom())
                .map(|c| ModuleSource::Library(c))
                .ok_or(ParserError::InvalidUseModuleDecl)
        }
        Term::Constant(_, Constant::Atom(ref name, _)) =>
            Ok(ModuleSource::File(name.clone())),
        _ => Err(ParserError::InvalidUseModuleDecl),
    }
}

fn setup_double_quotes(mut terms: Vec<Box<Term>>) -> Result<DoubleQuotes, ParserError> {
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
                            _ => Err(ParserError::InvalidDoubleQuotesDecl),
                        }
                    }
                    _ => {
                        Err(ParserError::InvalidDoubleQuotesDecl)
                    }
                }
            },
        _ => {
            Err(ParserError::InvalidDoubleQuotesDecl)
        }
    }
}

type UseModuleExport = (ModuleSource, Vec<ModuleExport>);

fn setup_qualified_import(
    mut terms: Vec<Box<Term>>,
    atom_tbl: TabledData<Atom>,
) -> Result<UseModuleExport, ParserError> {
    let mut export_list = *terms.pop().unwrap();
    let module_src = match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 =>
        {
            terms
                .pop()
                .unwrap()
                .to_constant()
                .and_then(|c| c.to_atom())
                .map(|c| ModuleSource::Library(c))
                .ok_or(ParserError::InvalidUseModuleDecl)
        }
        Term::Constant(_, Constant::Atom(ref name, _)) => Ok(ModuleSource::File(name.clone())),
        _ => Err(ParserError::InvalidUseModuleDecl),
    }?;

    let mut exports = vec![];

    while let Term::Cons(_, t1, t2) = export_list {
        exports.push(setup_module_export(*t1, atom_tbl.clone())?);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok((module_src, exports))
    }
}

fn merge_clauses(tls: &mut VecDeque<TopLevel>) -> Result<TopLevel, ParserError>
{
    let mut clauses: Vec<PredicateClause> = vec![];

    while let Some(tl) = tls.pop_front() {
        match tl {
            TopLevel::Query(_) if clauses.is_empty() && tls.is_empty() => return Ok(tl),
            TopLevel::Declaration(_) if clauses.is_empty() => return Ok(tl),
            TopLevel::Query(_) => return Err(ParserError::InconsistentEntry),
            TopLevel::Fact(..) => {
                if let TopLevel::Fact(fact, line_num, col_num) = tl {
                    let clause = PredicateClause::Fact(fact, line_num, col_num);
                    clauses.push(clause);
                }
            }
            TopLevel::Rule(..) => {
                if let TopLevel::Rule(rule, line_num, col_num) = tl {
                    let clause = PredicateClause::Rule(rule, line_num, col_num);
                    clauses.push(clause);
                }
            }
            TopLevel::Predicate(..) => {
                if let TopLevel::Predicate(predicate) = tl {
                    clauses.extend(predicate.clauses().into_iter())
                }
            }
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
            Constant::Atom(clause_name!("blocked_!"), None))
        );

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

fn flatten_hook(mut term: Term) -> Term {
    if let Term::Clause(_, ref mut name, ref mut terms, _) = &mut term {
        match (name.as_str(), terms.len()) {
            (":-", 2) => {
                let inner_term = match terms.first_mut().map(|term| term.borrow_mut()) {
                    Some(&mut Term::Clause(_, ref name, ref mut inner_terms, _)) => {
                        if name.as_str() == ":" && inner_terms.len() == 2 {
                            Some(*inner_terms.pop().unwrap())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                if let Some(inner_term) = inner_term {
                    mem::swap(&mut terms[0], &mut Box::new(inner_term));
                }
            }
            (":", 2) => return *terms.pop().unwrap(),
            _ => {}
        }
    }

    term
}

fn draw_from_term_dir_impl(
    term_dir: &TermDir,
    term_dirs: &mut TermDirQuantum,
    key: &PredicateKey,
    preds: &mut Vec<PredicateClause>,
    queue: &mut VecDeque<TopLevel>
) {
    if let Some(entry) = term_dirs.get_mut(key) {
        if entry.is_fresh {
            entry.is_fresh = false;

            (entry.new_terms.0).0.extend(preds.drain(0 ..));
            entry.new_terms.1.extend(queue.drain(0 ..));

            *preds = (entry.old_terms.0).0
                .iter()
                .cloned()
                .chain((entry.new_terms.0).0.iter().cloned())
                .collect();

            *queue = entry.old_terms.1
                .iter()
                .cloned()
                .chain(entry.new_terms.1.iter().cloned())
                .collect();
        } else {
            *entry = TermDirQuantumEntry::new();
        }
    } else if term_dir.contains_key(key) {
        let entry = TermDirQuantumEntry::from(&Predicate::new(), &VecDeque::new());
        term_dirs.insert(key.clone(), entry);
    }
}

fn draw_from_term_dir<R: Read>(
    indices: &CompositeIndices<R>,
    intra_module_term_dirs: &mut IndexMap<ClauseName, TermDirQuantum>,
    top_level_term_dirs: &mut TermDirQuantum,
    key: &PredicateKey,
    preds: &mut Vec<PredicateClause>,
    queue: &mut VecDeque<TopLevel>,
) {
    let module = key.0.owning_module();

    // aaarghhh..
    match indices.term_stream.wam.indices.in_situ_module_dir.get(&module) {
        // modify module_stub to do this right.
        Some(ref module_stub) if key.0.has_table(&module_stub.atom_tbl) => {
            if let Some(ref mut term_dirs) = intra_module_term_dirs.get_mut(&module) {
                if let Some(ref module) = indices.term_stream.wam.indices.modules.get(&module) {
                    return draw_from_term_dir_impl(
                        &module.term_dir,
                        term_dirs,
                        key,
                        preds,
                        queue,
                    );
                }
            }
        }
        _ => {}
    }

    draw_from_term_dir_impl(
        &indices.term_stream.wam.code_repo.term_dir,
        top_level_term_dirs,
        key,
        preds,
        queue,
    );
}

fn setup_declaration<'a, 'b, 'c, R: Read>(
    indices: &mut CompositeIndices<'a, 'b, 'c, R>,
    flags: MachineFlags,
    mut terms: Vec<Box<Term>>,
    line_num: usize,
    col_num: usize,
) -> Result<Declaration, ParserError> {
    let term = *terms.pop().unwrap();

    match term {
        Term::Clause(_, name, mut terms, _) =>
	    match (name.as_str(), terms.len()) {
		("dynamic", 1) => {
		    let (name, arity) = setup_predicate_indicator(&mut *terms.pop().unwrap())?;
		    Ok(Declaration::Dynamic(name, arity))
		}
		("initialization", 1) => {
		    let mut rel_worker = RelationWorker::new(flags, line_num, col_num);
		    let query_terms = rel_worker.setup_query(indices, terms, false)?;
		    let queue = rel_worker.parse_queue(indices)?;

		    Ok(Declaration::ModuleInitialization(query_terms, queue))
		}
		("module", 2) =>
		    Ok(Declaration::Module(setup_module_decl(terms, indices.atom_tbl())?)),
		("op", 3) =>
		    Ok(Declaration::Op(setup_op_decl(terms, indices.atom_tbl())?)),
		("non_counted_backtracking", 1) => {
		    let (name, arity) = setup_predicate_indicator(&mut *terms.pop().unwrap())?;
		    Ok(Declaration::NonCountedBacktracking(name, arity))
		}
                ("set_prolog_flag", 2) => {
                    Ok(Declaration::SetPrologFlag(setup_double_quotes(terms)?))
                }
                ("multifile", 1) => {
                    let mut term = *terms.pop().unwrap();

                    match setup_predicate_indicator(&mut term) {
                        Ok((name, arity)) =>
                            Ok(Declaration::MultiFile(MultiFileIndicator::LocalScoped(name, arity))),
                        _ =>
                            setup_scoped_predicate_indicator(&mut term)
                                .map(|key| {
                                    Declaration::MultiFile(MultiFileIndicator::ModuleScoped(key))
                                })
                    }
                }
		("use_module", 1) => {
		    Ok(Declaration::UseModule(setup_use_module_decl(terms)?))
                }
		("use_module", 2) => {
		    let (name, exports) = setup_qualified_import(terms, indices.atom_tbl())?;
		    Ok(Declaration::UseQualifiedModule(name, exports))
		}
		_ => {
		    Err(ParserError::InconsistentEntry)
                }
	    },
        _ => Err(ParserError::InconsistentEntry),
    }
}

struct RelationWorker {
    flags: MachineFlags,
    dynamic_clauses: Vec<(Term, Term)>, // Head, Body.
    queue: VecDeque<VecDeque<Term>>,
    line_num: usize,
    col_num: usize
}

impl RelationWorker {
    fn new(flags: MachineFlags, line_num: usize, col_num: usize) -> Self {
        RelationWorker {
            dynamic_clauses: vec![],
            flags,
            queue: VecDeque::new(),
            line_num,
            col_num
        }
    }

    fn setup_fact(&mut self, term: Term, assume_dyn: bool) -> Result<Term, ParserError> {
        match term {
            Term::Clause(..) | Term::Constant(_, Constant::Atom(..)) => {
                let tail =
                    Term::Constant(Cell::default(), Constant::Atom(clause_name!("true"), None));

                if assume_dyn {
                    self.dynamic_clauses.push((term.clone(), tail));
                }

                Ok(term)
            }
            _ => Err(ParserError::InadmissibleFact),
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

    fn to_query_term<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        term: Term,
    ) -> Result<QueryTerm, ParserError> {
        match term {
            Term::Constant(_, Constant::Atom(name, fixity)) => {
                if name.as_str() == "!" || name.as_str() == "blocked_!" {
                    Ok(QueryTerm::BlockedCut)
                } else {
                    let ct = indices.get_clause_type(name, 0, fixity);
                    Ok(QueryTerm::Clause(Cell::default(), ct, vec![], false))
                }
            }
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
                        Constant::Atom(clause_name!("$fail"), None)
                    )));

                    let conq = Term::Constant(
                        Cell::default(),
                        Constant::Atom(clause_name!("true"), None)
                    );

                    let prec = Term::Clause(Cell::default(), clause_name!("->"), terms, None);
                    let terms = vec![Box::new(prec), Box::new(conq)];

                    let term = Term::Clause(Cell::default(), clause_name!(";"), terms, None);
                    let (stub, clauses) = self.fabricate_disjunct(term);

                    self.queue.push_back(clauses);
                    Ok(QueryTerm::Jump(stub))
                }
                ("$get_level", 1) => {
                    if let Term::Var(_, ref var) = *terms[0] {
                        Ok(QueryTerm::GetLevelAndUnify(Cell::default(), var.clone()))
                    } else {
                        Err(ParserError::InadmissibleQueryTerm)
                    }
                }
                _ => {
                    let ct = indices.get_clause_type(name, terms.len(), fixity);
                    Ok(QueryTerm::Clause(Cell::default(), ct, terms, false))
                }
            }
            Term::Var(..) => Ok(QueryTerm::Clause(
                Cell::default(),
                ClauseType::CallN,
                vec![Box::new(term)],
                false,
            )),
            _ => Err(ParserError::InadmissibleQueryTerm),
        }
    }

    fn pre_query_term<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        term: Term,
    ) -> Result<QueryTerm, ParserError> {
        match term {
            Term::Clause(r, name, mut subterms, fixity) => {
                if subterms.len() == 1 && name.as_str() == "$call_with_default_policy" {
                    self.to_query_term(indices, *subterms.pop().unwrap())
                        .map(|mut query_term| {
                            query_term.set_default_caller();
                            query_term
                        })
                } else {
                    self.to_query_term(indices, Term::Clause(r, name, subterms, fixity))
                }
            }
            _ => self.to_query_term(indices, term),
        }
    }

    fn setup_query<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        terms: Vec<Box<Term>>,
        blocks_cuts: bool,
    ) -> Result<Vec<QueryTerm>, ParserError> {
        let mut query_terms = vec![];
        let mut work_queue = VecDeque::from(terms);
        let mut machine_st = MachineState::new();

        while let Some(term) = work_queue.pop_front() {
            let term = *term;
            let op_dir = op_dir(&indices.index_src);

            let mut expanded_terms = indices.term_stream.expand_goals(
                &mut machine_st,
                op_dir.as_ref(),
                VecDeque::from(vec![term])
            )?;

            while let Some(term) = expanded_terms.pop() {
                work_queue.push_front(Box::new(term));
            }

            if let Some(term) = work_queue.pop_front() {
                let mut term = *term;

                if let Term::Clause(cell, name, terms, op_spec) = term {
                    if name.as_str() == "," {
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

                if !blocks_cuts {
                    mark_cut_variable(&mut term);
                }

                query_terms.push(self.pre_query_term(indices, term)?);
            }
        }

        Ok(query_terms)
    }

    fn setup_hook<'a, 'b, 'c, R: Read>(
        &mut self,
        hook: CompileTimeHook,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        term: Term,
    ) -> Result<CompileTimeHookCompileInfo, ParserError> {
        match flatten_hook(term) {
            Term::Clause(r, name, terms, _) => {
                if name == hook.name() && terms.len() == hook.arity() {
                    let term = self.setup_fact(Term::Clause(r, name, terms, None), false)?;
                    Ok((hook, PredicateClause::Fact(term, 0, 0), VecDeque::from(vec![])))
                } else if name.as_str() == ":-" && terms.len() == 2 {
                    let rule = self.setup_rule(indices, terms, true, false)?;
                    let results_queue = self.parse_queue(indices)?;

                    Ok((hook, PredicateClause::Rule(rule, 0, 0), results_queue))
                } else {
                    Err(ParserError::InvalidHook)
                }
            }
            _ => Err(ParserError::InvalidHook),
        }
    }

    fn setup_rule<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        mut terms: Vec<Box<Term>>,
        blocks_cuts: bool,
        assume_dyn: bool,
    ) -> Result<Rule, ParserError> {
        let head = *terms.first().cloned().unwrap();
        let post_head_terms: Vec<_> = terms.drain(1..).collect();

        let tail = *post_head_terms.first().cloned().unwrap();

        if assume_dyn {
            self.dynamic_clauses.push((head, tail));
        }

        let mut query_terms = self.setup_query(indices, post_head_terms, blocks_cuts)?;
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
            _ => Err(ParserError::InvalidRuleHead),
        }
    }

    fn try_term_to_query<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        terms: Vec<Box<Term>>,
        blocks_cuts: bool,
    ) -> Result<TopLevel, ParserError> {
        Ok(TopLevel::Query(self.setup_query(
            indices,
            terms,
            blocks_cuts,
        )?))
    }

    fn compact_module_scoped_head<'a, 'b, 'c, R: Read>(
        &self,
        term: &mut Term,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
    ) {
        let inner_term = match term {
            Term::Clause(_, ref name, ref mut inner_terms, _)
                if name.as_str() == ":" && inner_terms.len() == 2 => {
                    let module_name = match inner_terms[0].as_ref() {
                        &Term::Constant(_, Constant::Atom(ref module, _)) => {
                            module.clone()
                        }
                        _ => {
                            return;
                        }
                    };

                    indices.add_in_situ_module_info(module_name, inner_terms[1].deref_mut());
                    *inner_terms.pop().unwrap()
                }
            _ => {
                return;
            }
        };

        *term = inner_term;
    }

    fn try_term_to_tl<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        term: Term,
        blocks_cuts: bool,
    ) -> Result<TopLevel, ParserError> {
        match term {
            Term::Clause(r, name, mut terms, fixity) => {
                if let Some(hook) = is_compile_time_hook(&name, &terms) {
                    let term = Term::Clause(r, name, terms, fixity);
                    let (hook, clause, queue) = self.setup_hook(hook, indices, term)?;

                    Ok(TopLevel::Declaration(Declaration::Hook(
                        hook, clause, queue,
                    )))
                } else if name.as_str() == "?-" {
                    self.try_term_to_query(indices, terms, blocks_cuts)
                } else if name.as_str() == ":-" && terms.len() == 2 {
                    self.compact_module_scoped_head(&mut terms[0], indices);

                    Ok(TopLevel::Rule(self.setup_rule(
                        indices,
                        terms,
                        blocks_cuts,
                        true,
                    )?, self.line_num, self.col_num))
                } else if name.as_str() == ":-" && terms.len() == 1 {
                    Ok(TopLevel::Declaration(setup_declaration(indices, self.flags, terms,
                                                               self.line_num, self.col_num)?))
                } else {
                    let mut term = Term::Clause(r, name, terms, fixity);
                    self.compact_module_scoped_head(&mut term, indices);

                    Ok(TopLevel::Fact(self.setup_fact(term, true)?, self.line_num, self.col_num))
                }
            }
            term =>
                Ok(TopLevel::Fact(self.setup_fact(term, true)?, self.line_num, self.col_num)),
        }
    }

    fn try_terms_to_tls<'a, 'b, 'c, I, R>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
        terms: I,
        blocks_cuts: bool,
    ) -> Result<VecDeque<TopLevel>, ParserError>
    where
        I: IntoIterator<Item = Term>, R: Read
    {
        let mut results = VecDeque::new();

        for term in terms.into_iter() {
            results.push_back(self.try_term_to_tl(indices, term, blocks_cuts)?);
        }

        Ok(results)
    }

    fn parse_queue<'a, 'b, 'c, R: Read>(
        &mut self,
        indices: &mut CompositeIndices<'a, 'b, 'c, R>,
    ) -> Result<VecDeque<TopLevel>, ParserError> {
        let mut queue = VecDeque::new();

        while let Some(terms) = self.queue.pop_front() {
            let clauses = merge_clauses(&mut self.try_terms_to_tls(indices, terms, false)?)?;
            queue.push_back(clauses);
        }

        Ok(queue)
    }

    fn absorb(&mut self, other: RelationWorker) {
        self.queue.extend(other.queue.into_iter());
        self.dynamic_clauses
            .extend(other.dynamic_clauses.into_iter());
    }
}

pub type DynamicClause = Vec<(Term, Term)>;

pub type DynamicClauseMap = IndexMap<(ClauseName, usize), DynamicClause>;

pub struct TopLevelBatchWorker<'a, R: Read> {
    pub(crate) term_stream: TermStream<'a, R>,
    rel_worker: RelationWorker,
    pub(crate) results: Vec<(Predicate, VecDeque<TopLevel>)>,
    pub(crate) dynamic_clause_map: DynamicClauseMap,
    pub(crate) in_module: bool,
    pub(crate) term_dirs: TermDirQuantum,
    pub(crate) intra_module_term_dirs: IndexMap<ClauseName, TermDirQuantum>,
    pub(crate) non_counted_bt_preds: IndexSet<PredicateKey>,
}

impl<'a, R: Read> TopLevelBatchWorker<'a, R> {
    pub fn new(
        inner: &'a mut ParsingStream<R>,
        atom_tbl: TabledData<Atom>,
        flags: MachineFlags,
        wam: &'a mut Machine,
    ) -> Self {
        let term_stream = TermStream::new(inner, atom_tbl, flags, wam);

        let line_num = term_stream.line_num();
        let col_num  = term_stream.col_num();

        TopLevelBatchWorker {
            term_stream,
            rel_worker: RelationWorker::new(flags, line_num, col_num),
            results: vec![],
            dynamic_clause_map: IndexMap::new(),
            in_module: false,
            term_dirs: TermDirQuantum::new(),
            intra_module_term_dirs: IndexMap::new(),
            non_counted_bt_preds: IndexSet::new(),
        }
    }

    fn try_term_to_tl(
        &mut self,
        indices: &mut IndexStore,
        term: Term,
    ) -> Result<(TopLevel, RelationWorker), SessionError> {
        let line_num = self.term_stream.line_num();
        let col_num  = self.term_stream.col_num();

        let mut new_rel_worker = RelationWorker::new(self.rel_worker.flags, line_num, col_num);
        let mut indices = CompositeIndices::new(
            &mut self.term_stream,
            IndexSource::Local(indices),
            if self.in_module { None } else { Some(IndexSource::TermStream) }
        );

        Ok((
            new_rel_worker.try_term_to_tl(&mut indices, term, true)?,
            new_rel_worker,
        ))
    }

    fn process_result(
        &mut self,
        indices: &mut IndexStore,
        preds: &mut Vec<PredicateClause>,
    ) -> Result<(), SessionError> {
        let mut indices = CompositeIndices::new(
            &mut self.term_stream,
            IndexSource::Local(indices),
            if self.in_module { None } else { Some(IndexSource::TermStream) },
        );

        let key = (preds[0].name().unwrap(), preds[0].arity());

        let mut preds = mem::replace(preds, vec![]);
        let mut queue = self.rel_worker.parse_queue(&mut indices)?;

        draw_from_term_dir(
            &indices,
            &mut self.intra_module_term_dirs,
            &mut self.term_dirs,
            &key,
            &mut preds,
            &mut queue,
        );

        let result = (Predicate(preds), queue);

        indices.term_stream.wam.code_repo.add_in_situ_result(
            &result,
            &mut indices.term_stream.wam.indices.in_situ_code_dir,
            &mut indices.term_stream.wam.indices.in_situ_module_dir,
            &self.non_counted_bt_preds,
        )?;

        Ok(self.results.push(result))
    }

    fn take_dynamic_clauses(&mut self) {
        let (name, arity) = match self.rel_worker.dynamic_clauses.first() {
            Some((head, _)) => (head.name().unwrap(), head.arity()),
            None => return,
        };

        match self.dynamic_clause_map.get_mut(&(name.clone(), arity)) {
            Some(ref mut entry) => {
                entry.clear(); // don't treat dynamic predicates as if they're discontiguous.
                entry.extend(self.rel_worker.dynamic_clauses.drain(0..));
            }
            _ => {
                self.rel_worker.dynamic_clauses.clear();
            }
        }
    }

    pub fn consume(
        &mut self,
        indices: &mut IndexStore,
    ) -> Result<Option<Declaration>, SessionError> {
        let mut preds = vec![];

        while !self.term_stream.eof()? {
            let term = self.term_stream.read_term(&indices.op_dir)?;
            
            // if is_consistent is false, preds is non-empty.
            let term = if !term.is_consistent(&preds) {
                self.process_result(indices, &mut preds)?;
                self.take_dynamic_clauses();

                // expand the term after the addition of the previous
                // predicate.
                self.term_stream.expand_term(term, &indices.op_dir)?
            } else {
                term
            };

            let (mut tl, new_rel_worker) = self.try_term_to_tl(indices, term)?;

            if tl.is_end_of_file_atom() {
                tl = TopLevel::Declaration(Declaration::EndOfFile);
            }

            self.rel_worker.absorb(new_rel_worker);

            match tl {
                TopLevel::Fact(fact, line_num, col_num) =>
                    preds.push(PredicateClause::Fact(fact, line_num, col_num)),
                TopLevel::Rule(rule, line_num, col_num) =>
                    preds.push(PredicateClause::Rule(rule, line_num, col_num)),
                TopLevel::Predicate(pred) =>
                    preds.extend(pred.0),
                TopLevel::Declaration(decl) =>
                    return Ok(Some(decl)),
                TopLevel::Query(_) =>
                    return Err(SessionError::NamelessEntry),
            }
        }

        if !preds.is_empty() {
            self.process_result(indices, &mut preds)?;
            self.take_dynamic_clauses();
        }

        Ok(None)
    }
}
