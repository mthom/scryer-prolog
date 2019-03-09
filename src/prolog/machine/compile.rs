use prolog_parser::ast::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::instructions::*;
use prolog::codegen::*;
use prolog::debray_allocator::*;
use prolog::forms::*;
use prolog::machine::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::term_expansion::{ExpansionAdditionResult};
use prolog::machine::toplevel::*;

use std::cell::Cell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Read;
use std::mem;

#[allow(dead_code)]
fn print_code(code: &Code) {
    for clause in code {
        match clause {
            &Line::Arithmetic(ref arith) =>
                println!("{}", arith),
            &Line::Fact(ref fact_instr) =>
                println!("{}", fact_instr),
            &Line::Cut(ref cut) =>
                println!("{}", cut),
            &Line::Choice(ref choice) =>
                println!("{}", choice),
            &Line::Control(ref control) =>
                println!("{}", control),
            &Line::IndexedChoice(ref choice) =>
                println!("{}", choice),
            &Line::Indexing(ref indexing) =>
                println!("{}", indexing),
            &Line::Query(ref query_instr) =>
                println!("{}", query_instr)
        }
    }
}

pub type PredicateCompileQueue = (Predicate, VecDeque<TopLevel>);

// throw errors if declaration or query found.
fn compile_relation(tl: &TopLevel, non_counted_bt: bool, flags: MachineFlags)
                    -> Result<Code, ParserError>
{
    let mut cg = CodeGenerator::<DebrayAllocator>::new(non_counted_bt, flags);

    match tl {
        &TopLevel::Declaration(_) | &TopLevel::Query(_) =>
            Err(ParserError::ExpectedRel),
        &TopLevel::Predicate(ref clauses) =>
            cg.compile_predicate(&clauses.0),
        &TopLevel::Fact(ref fact) =>
            Ok(cg.compile_fact(fact)),
        &TopLevel::Rule(ref rule) =>
            cg.compile_rule(rule)
    }
}

// set first jmp_by_call or jmp_by_index instruction to code.len() -
// idx, where idx is the place it occurs. It only does this to the
// *first* uninitialized jmp index it encounters, then returns.
fn set_first_index(code: &mut Code)
{
    let code_len = code.len();

    for (idx, line) in code.iter_mut().enumerate() {
        match line {
            &mut Line::Control(ControlInstruction::JmpBy(_, ref mut offset, ..)) if *offset == 0 => {
                *offset = code_len - idx;
                break;
            },
            _ => {}
        };
    }
}

pub fn compile_appendix(code: &mut Code, queue: &VecDeque<TopLevel>, non_counted_bt: bool,
                        flags: MachineFlags)
                        -> Result<(), ParserError>
{
    for tl in queue.iter() {
        set_first_index(code);
        code.append(&mut compile_relation(tl, non_counted_bt, flags)?);
    }

    Ok(())
}

impl CodeRepo {
    pub fn compile_hook(&mut self, hook: CompileTimeHook, flags: MachineFlags)
                        -> Result<(), ParserError>
    {
        let key = (hook.name(), hook.arity());
        match self.term_dir.get(&key) {
            Some(preds) => {
                let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
                let mut code = cg.compile_predicate(&(preds.0).0)?;

                compile_appendix(&mut code, &preds.1, false, flags)?;

                Ok(match hook {
                    CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion =>
                        self.term_expanders = code,
                    CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion =>
                        self.goal_expanders = code
                })
            },
            None => Ok(())
        }
    }
}

fn compile_query(terms: Vec<QueryTerm>, queue: VecDeque<TopLevel>, flags: MachineFlags)
                 -> Result<(Code, AllocVarDict), ParserError>
{
    // count backtracking inferences.
    let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
    let mut code = try!(cg.compile_query(&terms));

    compile_appendix(&mut code, &queue, false, flags)?;
    Ok((code, cg.take_vars()))
}

fn compile_decl(wam: &mut Machine, compiler: &mut ListingCompiler, decl: Declaration)
                -> Result<IndexStore, SessionError>
{
    let flags = wam.machine_flags();
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    let wam_indices = &mut wam.indices;

    compiler.process_decl(decl, &mut wam.code_repo, wam_indices, &mut indices, flags)?;

    Ok(indices)
}

pub fn compile_term(wam: &mut Machine, packet: TopLevelPacket) -> EvalSession
{
    match packet {
        TopLevelPacket::Query(terms, queue) =>
            match compile_query(terms, queue, wam.machine_flags()) {
                Ok((mut code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        TopLevelPacket::Decl(TopLevel::Declaration(decl), _) => {
            let mut compiler = ListingCompiler::new(&wam.code_repo);
            let indices = try_eval_session!(compile_decl(wam, &mut compiler, decl));

            try_eval_session!(wam.check_toplevel_code(&indices));
            add_toplevel_code(wam, vec![], indices);

            EvalSession::EntrySuccess
        },
        _ => EvalSession::from(SessionError::UserPrompt)
    }
}

fn update_module_indices(wam: &Machine, module_name: ClauseName, mut indices: IndexStore)
{
    match wam.indices.modules.get(&module_name) {
        Some(module) => {
            let code_dir = mem::replace(&mut indices.code_dir, CodeDir::new());

            // replace the "user" module src's in the indices with module_name.
            for (key, idx) in code_dir.iter() {
                let p = idx.0.borrow().0;

                match module.code_dir.get(&key) {
                    Some(idx) => set_code_index!(idx, p, module_name.clone()),
                    _ => {}
                }

                match wam.indices.code_dir.get(&key) {
                    Some(idx) => if idx.0.borrow().1 == module_name {
                        set_code_index!(idx, p, module_name.clone());
                    },
                    _ => {}
                }
            }
        },
        _ => unreachable!()
    };
}

fn add_hooks_to_mockup(code_repo: &mut CodeRepo, hook: CompileTimeHook,
                       expansions: (Predicate, VecDeque<TopLevel>))
{
    let key = (hook.name(), hook.arity());
    let preds = code_repo.term_dir.entry(key.clone())
        .or_insert((Predicate::new(), VecDeque::from(vec![])));

    (preds.0).0.extend((expansions.0).0.iter().cloned());
    preds.1.extend(expansions.1.iter().cloned());
}

fn setup_module_expansions(wam: &mut Machine, module_name: ClauseName)
{
    match wam.indices.modules.get(&module_name) {
        Some(module) => {
            let term_expansions = module.term_expansions.clone();
            let goal_expansions = module.goal_expansions.clone();

            add_hooks_to_mockup(&mut wam.code_repo, CompileTimeHook::TermExpansion,
                                term_expansions);
            add_hooks_to_mockup(&mut wam.code_repo, CompileTimeHook::GoalExpansion,
                                goal_expansions);
        },
        _ => unreachable!()
    }
}

pub(super)
fn compile_into_module<R: Read>(wam: &mut Machine, module_name: ClauseName, src: R, name: ClauseName)
                                -> EvalSession
{
    let mut indices = default_index_store!(wam.atom_tbl_of(&name));
    try_eval_session!(setup_indices(wam, module_name.clone(), &mut indices));

    let mut compiler = ListingCompiler::new(&wam.code_repo);

    match compile_into_module_impl(wam, &mut compiler, module_name, src, indices) {
        Ok(()) => EvalSession::EntrySuccess,
        Err(e) => {
            compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo);            
            EvalSession::from(e)
        }
    }
}
    
fn compile_into_module_impl<R: Read>(wam: &mut Machine, compiler: &mut ListingCompiler,
                                     module_name: ClauseName, src: R, mut indices: IndexStore)
                                     -> Result<(), SessionError>
{   
    setup_module_expansions(wam, module_name.clone());

    let flags = wam.machine_flags();
    
    wam.code_repo.compile_hook(CompileTimeHook::TermExpansion, flags)?;
    wam.code_repo.compile_hook(CompileTimeHook::GoalExpansion, flags)?;
    
    let results = compiler.gather_items(wam, src, &mut indices)?;
    let module_code = compiler.generate_code(results.worker_results, wam,
                                             &mut indices.code_dir, 0)?;

    let mut clause_code_generator = ClauseCodeGenerator::new(module_code.len());
    clause_code_generator.generate_clause_code(results.dynamic_clause_map, wam)?;

    update_module_indices(wam, module_name, indices);
    
    wam.code_repo.code.extend(module_code.into_iter());
    clause_code_generator.add_clause_code(wam);

    Ok(compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo))
}

pub struct GatherResult {
    dynamic_clause_map: DynamicClauseMap,
    pub(crate) worker_results: Vec<PredicateCompileQueue>,
    toplevel_results: Vec<PredicateCompileQueue>,
    toplevel_indices: IndexStore,
    addition_results: ExpansionAdditionResult
}

pub struct ClauseCodeGenerator {
    len_offset: usize,
    code: Code,
    pi_to_loc: HashMap<PredicateKey, usize>
}

impl ClauseCodeGenerator {
    #[inline]
    fn new(len_offset: usize) -> Self {
        ClauseCodeGenerator { len_offset, code: vec![], pi_to_loc: HashMap::new() }
    }

    fn generate_clause_code(&mut self, dynamic_clause_map: DynamicClauseMap, wam: &Machine)
                            -> Result<(), SessionError>
    {
        for ((name, arity), heads_and_tails) in dynamic_clause_map {
            if heads_and_tails.is_empty() {
                continue;
            }

            let predicate = Predicate(heads_and_tails.into_iter().map(|(head, tail)| {
                let clause = Term::Clause(Cell::default(), clause_name!("clause"),
                                          vec![Box::new(head), Box::new(tail)],
                                          None);
                PredicateClause::Fact(clause)
            }).collect());

            let p = self.code.len() + wam.code_repo.code.len() + self.len_offset;
            let mut decl_code = compile_relation(&TopLevel::Predicate(predicate), false,
                                                 wam.machine_flags())?;

            compile_appendix(&mut decl_code, &VecDeque::new(), false, wam.machine_flags())?;

            self.pi_to_loc.insert((name, arity), p);
            self.code.extend(decl_code.into_iter());
        }

        Ok(())
    }

    fn add_clause_code(self, wam: &mut Machine) {
        wam.code_repo.code.extend(self.code.into_iter());

        for ((name, arity), p) in self.pi_to_loc {
            let entry = wam.indices.dynamic_code_dir.entry((name.owning_module(), name, arity))
                           .or_insert(DynamicPredicateInfo::default());

            entry.clauses_subsection_p = p;
        }
    }
}

pub struct ListingCompiler {
    non_counted_bt_preds: HashSet<PredicateKey>,
    module: Option<Module>,
    user_term_dir: TermDir,
    orig_term_expansion_lens: (usize, usize),
    orig_goal_expansion_lens: (usize, usize)
}

fn add_toplevel_code(wam: &mut Machine, code: Code, mut indices: IndexStore)
{
    let code_dir = mem::replace(&mut indices.code_dir, CodeDir::new());
    let op_dir   = mem::replace(&mut indices.op_dir, OpDir::new());

    wam.add_batched_code(code, code_dir);
    wam.add_batched_ops(op_dir);
}

#[inline]
fn add_module_code(wam: &mut Machine, mut module: Module, code: Code, mut indices: IndexStore)
{
    let code_dir = mem::replace(&mut indices.code_dir, CodeDir::new());
    let op_dir   = mem::replace(&mut indices.op_dir, OpDir::new());

    module.code_dir.extend(code_dir);
    module.op_dir.extend(op_dir.into_iter());

    wam.add_module(module, code);
}

fn add_non_module_code(wam: &mut Machine, dynamic_clause_map: DynamicClauseMap, code: Code,
                       indices: IndexStore)
                       -> Result<(), SessionError>
{
    wam.check_toplevel_code(&indices)?;

    let mut clause_code_generator = ClauseCodeGenerator::new(code.len());
    clause_code_generator.generate_clause_code(dynamic_clause_map, wam)?;

    add_toplevel_code(wam, code, indices);
    clause_code_generator.add_clause_code(wam);

    Ok(())
}

impl ListingCompiler {
    #[inline]
    pub fn new(code_repo: &CodeRepo) -> Self {
        ListingCompiler {
            non_counted_bt_preds: HashSet::new(),
            module: None,
            user_term_dir: TermDir::new(),
            orig_term_expansion_lens: code_repo.term_dir_entry_len((clause_name!("term_expansion"), 2)),
            orig_goal_expansion_lens: code_repo.term_dir_entry_len((clause_name!("goal_expansion"), 2)),
        }
    }

    /*
    Replace calls to self with a localized index cell, not available to the global CodeIndex.
    This is done to implement logical update semantics for dynamic database updates.
     */
    fn localize_self_calls(&mut self, name: ClauseName, arity: usize, code: &mut Code, p: usize)
    {
        let self_idx = CodeIndex::default();
        set_code_index!(self_idx, IndexPtr::Index(p), self.get_module_name());

        for instr in code.iter_mut() {
            if let &mut Line::Control(ControlInstruction::CallClause(ref mut ct, ..)) = instr {
                match ct {
                    &mut ClauseType::Named(ref ct_name, ct_arity, ref mut idx)
                        if ct_name == &name && arity == ct_arity => {
                            *idx = self_idx.clone();
                        },
                    &mut ClauseType::Op(ref op_decl, ref mut idx)
                        if op_decl.name() == name && op_decl.arity() == arity => {
                            *idx = self_idx.clone();
                        },
                    _ => {}
                }
            }
        }
    }

    fn use_module(&mut self, submodule: ClauseName, code_repo: &mut CodeRepo,
                  flags: MachineFlags, wam_indices: &mut IndexStore,
                  indices: &mut IndexStore)
                  -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        if let Some(mut submodule) = wam_indices.take_module(submodule) {
            unwind_protect!(indices.use_module(code_repo, flags, &submodule),
                            wam_indices.insert_module(submodule));

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                unwind_protect!(module.use_module(code_repo, flags, &submodule),
                                wam_indices.insert_module(submodule));
            } else {
                submodule.inserted_expansions = true;
                wam_indices.remove_module(clause_name!("user"), &submodule);
            }

            Ok(wam_indices.insert_module(submodule))
        } else {
            Err(SessionError::ModuleNotFound)
        }
    }

    fn use_qualified_module(&mut self, submodule: ClauseName, code_repo: &mut CodeRepo,
                            flags: MachineFlags, exports: &Vec<PredicateKey>,
                            wam_indices: &mut IndexStore, indices: &mut IndexStore)
                            -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        if let Some(mut submodule) = wam_indices.take_module(submodule) {
            unwind_protect!(indices.use_qualified_module(code_repo, flags, &submodule, exports),
                            wam_indices.insert_module(submodule));

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                unwind_protect!(module.use_qualified_module(code_repo, flags, &submodule, exports),
                                wam_indices.insert_module(submodule));
            } else {
                submodule.inserted_expansions = true;
                wam_indices.remove_module(clause_name!("user"), &submodule);
            }

            Ok(wam_indices.insert_module(submodule))
        } else {
            Err(SessionError::ModuleNotFound)
        }
    }

    #[inline]
    fn get_module_name(&self) -> ClauseName {
        self.module.as_ref()
            .map(|module| module.module_decl.name.clone())
            .unwrap_or(ClauseName::BuiltIn("user"))
    }

    pub(crate)
    fn generate_code(&mut self, decls: Vec<PredicateCompileQueue>, wam: &Machine,
                     code_dir: &mut CodeDir, code_offset: usize)
                     -> Result<Code, SessionError>
    {
        let mut code = vec![];

        for (decl, queue) in decls {
            let (name, arity) = decl.predicate_indicator().ok_or(SessionError::NamelessEntry)?;
            let non_counted_bt = self.non_counted_bt_preds.contains(&(name.clone(), arity));

            let p = code.len() + wam.code_repo.code.len() + code_offset;
            let mut decl_code = compile_relation(&TopLevel::Predicate(decl), non_counted_bt,
                                                 wam.machine_flags())?;

            compile_appendix(&mut decl_code, &queue, non_counted_bt, wam.machine_flags())?;

            let idx = code_dir.entry((name.clone(), arity)).or_insert(CodeIndex::default());
            set_code_index!(idx, IndexPtr::Index(p), self.get_module_name());

            self.localize_self_calls(name, arity, &mut decl_code, p);
            code.extend(decl_code.into_iter());
        }

        Ok(code)
    }

    fn add_non_counted_bt_flag(&mut self, name: ClauseName, arity: usize) {
        self.non_counted_bt_preds.insert((name, arity));
    }

    fn add_term_dir_terms(&mut self, hook: CompileTimeHook, code_repo: &mut CodeRepo,
                          key: PredicateKey, clause: PredicateClause, queue: VecDeque<TopLevel>)
                          -> (usize, usize)
    {
        let preds = code_repo.term_dir.entry(key.clone())
            .or_insert((Predicate::new(), VecDeque::from(vec![])));

        let (mut len, mut queue_len) = ((preds.0).0.len(), preds.1.len());

        if self.module.is_some() && hook.has_module_scope() {
            let module_preds = self.user_term_dir.entry(key.clone())
                .or_insert((Predicate::new(), VecDeque::from(vec![])));

            if let Some(ref mut module) = &mut self.module {
                module.add_module_expansion_record(hook, clause.clone(), queue.clone());
            }
            
            (module_preds.0).0.push(clause);
            module_preds.1.extend(queue.into_iter());

            (preds.0).0.extend((module_preds.0).0.iter().cloned());
            preds.1.extend(module_preds.1.iter().cloned());
        } else {
            let module_preds = self.user_term_dir.entry(key.clone())
                .or_insert((Predicate::new(), VecDeque::from(vec![])));

            len += 1;
            queue_len += queue_len;

            (preds.0).0.push(clause);
            preds.1.extend(queue.into_iter());

            (preds.0).0.extend((module_preds.0).0.iter().cloned());
            preds.1.extend(module_preds.1.iter().cloned());
        }

        (len, queue_len)
    }

    fn process_decl(&mut self, decl: Declaration, code_repo: &mut CodeRepo,
                    wam_indices: &mut IndexStore, indices: &mut IndexStore,
                    flags: MachineFlags)
                    -> Result<(), SessionError>
    {
        match decl {
            Declaration::Hook(hook, clause, queue) => {
                let key = (hook.name(), hook.arity());
                let (len, queue_len) = self.add_term_dir_terms(hook, code_repo, key.clone(),
                                                               clause, queue);

                let result = code_repo.compile_hook(hook, flags).map_err(SessionError::from);
                code_repo.truncate_terms(key, len, queue_len);

                result
            },
            Declaration::NonCountedBacktracking(name, arity) =>
                Ok(self.add_non_counted_bt_flag(name, arity)),
            Declaration::Op(op_decl) =>
                op_decl.submit(self.get_module_name(), &mut indices.op_dir),
            Declaration::UseModule(name) =>
                self.use_module(name, code_repo, flags, wam_indices, indices),
            Declaration::UseQualifiedModule(name, exports) =>
                self.use_qualified_module(name, code_repo, flags, &exports, wam_indices, indices),
            Declaration::Module(module_decl) =>
                if self.module.is_none() {
                    let module_name = module_decl.name.clone();
                    let atom_tbl = TabledData::new(module_name.to_rc());

                    Ok(self.module = Some(Module::new(module_decl, atom_tbl)))
                } else {
                    Err(SessionError::from(ParserError::InvalidModuleDecl))
                },
            Declaration::Dynamic(..) => Ok(())
        }
    }

    fn process_and_commit_decl<'a, R: Read>(&mut self, decl: Declaration,
                                            worker: &mut TopLevelBatchWorker<'a, R>,
                                            indices: &mut IndexStore, flags: MachineFlags)
                                            -> Result<(), SessionError>
    {
        match &decl {
            &Declaration::Dynamic(ref name, arity) => {
                worker.dynamic_clause_map.entry((name.clone(), arity)).or_insert(vec![]);
            },
            &Declaration::Hook(hook, _, ref queue) if self.module.is_none() =>
                worker.term_stream.incr_expansion_lens(hook.user_scope(), 1, queue.len()),
            &Declaration::Hook(hook, _, ref queue) if !hook.has_module_scope() =>
                worker.term_stream.incr_expansion_lens(hook, 1, queue.len()),
            _ => {}
        };

        self.process_decl(decl, &mut worker.term_stream.code_repo,
                          &mut worker.term_stream.indices, indices, flags)
    }

    pub(crate)
    fn gather_items<R: Read>(&mut self, wam: &mut Machine, src: R, indices: &mut IndexStore)
                             -> Result<GatherResult, SessionError>
    {
        let flags      = wam.machine_flags();
        let atom_tbl   = indices.atom_tbl.clone();
        let mut worker = TopLevelBatchWorker::new(src, atom_tbl.clone(), flags,
                                                  &mut wam.indices, &mut wam.policies,
                                                  &mut wam.code_repo);

        let mut toplevel_results = vec![];
        let mut toplevel_indices = default_index_store!(atom_tbl.clone());

        while let Some(decl) = worker.consume(indices)? {
            if decl.is_module_decl() {
                toplevel_indices.copy_and_swap(indices);
                mem::swap(&mut worker.results, &mut toplevel_results);
                worker.in_module = true;

                self.process_and_commit_decl(decl, &mut worker, indices, flags)?;

                if let &Some(ref module) = &self.module {
                    worker.term_stream.set_atom_tbl(module.atom_tbl.clone());
                }
            } else {
                self.process_and_commit_decl(decl, &mut worker, indices, flags)?;
            }
        }

        let addition_results = worker.term_stream.rollback_expansion_code()?;

        Ok(GatherResult {
            worker_results: worker.results,
            dynamic_clause_map: worker.dynamic_clause_map,
            toplevel_results,
            toplevel_indices,
            addition_results
        })
    }

    fn drop_expansions(&self, flags: MachineFlags, code_repo: &mut CodeRepo)
    {
        let (te_len, te_queue_len) = self.orig_term_expansion_lens;
        let (ge_len, ge_queue_len) = self.orig_goal_expansion_lens;

        code_repo.truncate_terms((clause_name!("term_expansion"), 2), te_len, te_queue_len);
        code_repo.truncate_terms((clause_name!("goal_expansion"), 2), ge_len, ge_queue_len);

        discard_result!(code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags));
        discard_result!(code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags));
    }
}

fn compile_work<R: Read>(compiler: &mut ListingCompiler, wam: &mut Machine, src: R,
                         mut indices: IndexStore)
                         -> EvalSession
{
    let mut results = try_eval_session!(compiler.gather_items(wam, src, &mut indices));

    let module_code = try_eval_session!(compiler.generate_code(results.worker_results, wam,
                                                               &mut indices.code_dir, 0));
    let toplvl_code = try_eval_session!(compiler.generate_code(results.toplevel_results, wam,
                                                               &mut results.toplevel_indices.code_dir,
                                                               module_code.len()));

    if let Some(ref mut module) = &mut compiler.module {
        module.user_term_expansions = results.addition_results.take_term_expansions();
        module.user_goal_expansions = results.addition_results.take_goal_expansions();
    }

    let flags = wam.machine_flags();

    try_eval_session!(wam.code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags));
    try_eval_session!(wam.code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags));

    if let Some(module) = compiler.module.take() {
        let mut clause_code_generator = ClauseCodeGenerator::new(module_code.len() + toplvl_code.len());

        try_eval_session!(wam.check_toplevel_code(&results.toplevel_indices));
        try_eval_session!(clause_code_generator.generate_clause_code(results.dynamic_clause_map,
                                                                     wam));

        add_module_code(wam, module, module_code, indices);
        add_toplevel_code(wam, toplvl_code, results.toplevel_indices);

        clause_code_generator.add_clause_code(wam);
    } else {
        try_eval_session!(add_non_module_code(wam, results.dynamic_clause_map, module_code,
                                              indices));
    }

    EvalSession::EntrySuccess
}

/* This is a truncated version of compile_user_module, used for
   compiling code composing special forms, ie. the code that calls
   M:verify_attributes on attributed variables. */
pub fn compile_special_form<R: Read>(wam: &mut Machine, src: R) -> Result<Code, SessionError>
{
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    setup_indices(wam, clause_name!("builtins"), &mut indices)?;

    let mut compiler = ListingCompiler::new(&wam.code_repo);
    let results = compiler.gather_items(wam, src, &mut indices)?;

    compiler.generate_code(results.worker_results, wam, &mut indices.code_dir, 0)
}

#[inline]
pub fn compile_listing<R: Read>(wam: &mut Machine, src: R, indices: IndexStore) -> EvalSession
{
    let mut compiler = ListingCompiler::new(&wam.code_repo);

    match compile_work(&mut compiler, wam, src, indices) {
        EvalSession::Error(e) => {
            compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo);
            EvalSession::Error(e)
        },
        result => result
    }
}

pub(super)
fn setup_indices(wam: &mut Machine, module: ClauseName, indices: &mut IndexStore)
                 -> Result<(), SessionError>
{
    if let Some(module) = wam.indices.take_module(module) {
        let flags  = wam.machine_flags();
        let result = indices.use_module(&mut wam.code_repo, flags, &module);

        wam.indices.insert_module(module);
        result
    } else {
        Err(SessionError::ModuleNotFound)
    }
}

pub fn compile_user_module<R: Read>(wam: &mut Machine, src: R) -> EvalSession {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    try_eval_session!(setup_indices(wam, clause_name!("builtins"), &mut indices));
    compile_listing(wam, src, indices)
}
