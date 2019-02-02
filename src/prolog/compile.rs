use prolog_parser::ast::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::instructions::*;
use prolog::debray_allocator::*;
use prolog::codegen::*;
use prolog::machine::*;
use prolog::machine::term_expansion::{ExpansionAdditionResult, TermStream};
use prolog::toplevel::*;

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Read;
use std::mem;

#[allow(dead_code)]
fn print_code(code: &Code) {
    for clause in code {
        match clause {
            &Line::Arithmetic(ref arith) =>
                println!("{}", arith),
            &Line::Fact(ref fact) =>
                for fact_instr in fact {
                    println!("{}", fact_instr);
                },
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
            &Line::Query(ref query) =>
                for query_instr in query {
                    println!("{}", query_instr);
                }
        }
    }
}

type PredicateCompileQueue = (Predicate, VecDeque<TopLevel>);

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
            try_eval_session!(compiler.add_code(wam, vec![], indices));

            EvalSession::EntrySuccess
        },
        _ => EvalSession::from(SessionError::UserPrompt)
    }
}

struct GatherResult {
    worker_results: Vec<PredicateCompileQueue>,
    toplevel_results: Vec<PredicateCompileQueue>,
    toplevel_indices: IndexStore,
    addition_results: ExpansionAdditionResult
}

pub struct ListingCompiler {
    non_counted_bt_preds: HashSet<PredicateKey>,
    module: Option<Module>,
    user_term_dir: TermDir,
    orig_term_expansion_lens: (usize, usize),
    orig_goal_expansion_lens: (usize, usize)
}

impl ListingCompiler {
    #[inline]
    pub fn new(code_repo: &CodeRepo) -> Self {
        ListingCompiler {
            module: None, non_counted_bt_preds: HashSet::new(),
            user_term_dir: TermDir::new(),
            orig_term_expansion_lens: code_repo.term_dir_entry_len((clause_name!("term_expansion"), 2)),
            orig_goal_expansion_lens: code_repo.term_dir_entry_len((clause_name!("goal_expansion"), 2)),
        }
    }

    fn use_module(&mut self, submodule: ClauseName, code_repo: &mut CodeRepo,
                  flags: MachineFlags, wam_indices: &mut IndexStore,
                  indices: &mut IndexStore)
                  -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        if let Some(mut submodule) = wam_indices.take_module(submodule) {
            indices.use_module(code_repo, flags, &submodule)?;

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                module.use_module(code_repo, flags, &submodule)?;
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
            indices.use_qualified_module(code_repo, flags, &submodule, exports)?;

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                module.use_qualified_module(code_repo, flags, &submodule, exports)?;
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

    fn generate_code(&mut self, decls: Vec<PredicateCompileQueue>,
                     wam: &Machine, code_dir: &mut CodeDir)
                     -> Result<Code, SessionError>
    {
        let mut code = vec![];

        for (decl, queue) in decls {
            let (name, arity) = decl.0.first().and_then(|cl| {
                let arity = cl.arity();
                cl.name().map(|name| (name, arity))
            }).ok_or(SessionError::NamelessEntry)?;
            
            let non_counted_bt = self.non_counted_bt_preds.contains(&(name.clone(), arity));

            let p = code.len() + wam.code_size();                                    
            let mut decl_code = compile_relation(&TopLevel::Predicate(decl), non_counted_bt,
                                                 wam.machine_flags())?;

            compile_appendix(&mut decl_code, &queue, non_counted_bt, wam.machine_flags())?;

            let idx = code_dir.entry((name, arity)).or_insert(CodeIndex::default());
            set_code_index!(idx, IndexPtr::Index(p), self.get_module_name());

            code.extend(decl_code.into_iter());
        }

        Ok(code)
    }

    fn add_code(&mut self, wam: &mut Machine, code: Code, mut indices: IndexStore)
                -> Result<(), SessionError>
    {
        let code_dir = mem::replace(&mut indices.code_dir, CodeDir::new());
        let op_dir   = mem::replace(&mut indices.op_dir, OpDir::new());

        if let Some(mut module) = self.module.take() {
            module.code_dir.extend(as_module_code_dir(code_dir));
            module.op_dir.extend(op_dir.into_iter());

            wam.add_module(module, code);
        } else {
            wam.add_batched_code(code, code_dir)?;
            wam.add_batched_ops(op_dir);
        }

        Ok(())
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
                }
        }
    }

    fn process_and_commit_decl<'a, R: Read>(&mut self, decl: Declaration,
                                            term_stream: &mut TermStream<'a, R>,
                                            indices: &mut IndexStore, flags: MachineFlags)
                                            -> Result<(), SessionError>
    {
        match &decl {
            &Declaration::Hook(hook, _, ref queue) if self.module.is_none() =>
                term_stream.incr_expansion_lens(hook.user_scope(), 1, queue.len()),
            &Declaration::Hook(hook, _, ref queue) if !hook.has_module_scope() =>
                term_stream.incr_expansion_lens(hook, 1, queue.len()),
            _ => {}
        };

        self.process_decl(decl, term_stream.code_repo, term_stream.indices, indices, flags)
    }

    fn gather_items<R: Read>(&mut self, wam: &mut Machine, src: R, indices: &mut IndexStore)
                             -> Result<GatherResult, SessionError>
    {
        let flags = wam.machine_flags();
        let wam_indices = &mut wam.indices;

        let atom_tbl   = wam_indices.atom_tbl.clone();
        let mut worker = TopLevelBatchWorker::new(src, atom_tbl.clone(), flags,
                                                  wam_indices, &mut wam.policies,
                                                  &mut wam.code_repo);

        let mut toplevel_results = vec![];
        let mut toplevel_indices = default_index_store!(atom_tbl.clone());

        while let Some(decl) = worker.consume(indices)? {
            if decl.is_module_decl() {
                toplevel_indices.copy_and_swap(indices);
                mem::swap(&mut worker.results, &mut toplevel_results);
                worker.in_module = true;

                self.process_and_commit_decl(decl, &mut worker.term_stream,
                                             indices, flags)?;

                if let &Some(ref module) = &self.module {
                    worker.term_stream.set_atom_tbl(module.atom_tbl.clone());
                }
            } else {
                self.process_and_commit_decl(decl, &mut worker.term_stream,
                                             indices, flags)?;
            }
        }

        let addition_results = worker.term_stream.rollback_expansion_code()?;

        Ok(GatherResult {
            worker_results: worker.results,
            toplevel_results,
            toplevel_indices,
            addition_results
        })
    }

    fn drop_expansions(&self, wam: &mut Machine, err: SessionError) -> SessionError {
        let (te_len, te_queue_len) = self.orig_term_expansion_lens;
        let (ge_len, ge_queue_len) = self.orig_goal_expansion_lens;

        let flags = wam.machine_flags();

        wam.code_repo.truncate_terms((clause_name!("term_expansion"), 2), te_len, te_queue_len);
        wam.code_repo.truncate_terms((clause_name!("goal_expansion"), 2), ge_len, ge_queue_len);

        discard_result!(wam.code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags));
        discard_result!(wam.code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags));

        err
    }
}

fn compile_work<R: Read>(compiler: &mut ListingCompiler, wam: &mut Machine, src: R,
                         mut indices: IndexStore)
                         -> EvalSession
{
    let mut results  = try_eval_session!(compiler.gather_items(wam, src, &mut indices));

    let module_code = try_eval_session!(compiler.generate_code(results.worker_results, wam,
                                                               &mut indices.code_dir));
    let toplvl_code = try_eval_session!(compiler.generate_code(results.toplevel_results, wam,
                                                               &mut results.toplevel_indices.code_dir));

    if let Some(ref mut module) = &mut compiler.module {
        module.term_expansions = results.addition_results.take_term_expansions();
        module.goal_expansions = results.addition_results.take_goal_expansions();
    }

    try_eval_session!(compiler.add_code(wam, module_code, indices));
    try_eval_session!(compiler.add_code(wam, toplvl_code, results.toplevel_indices));

    let flags = wam.machine_flags();

    try_eval_session!(wam.code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags));
    try_eval_session!(wam.code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags));

    EvalSession::EntrySuccess
}

#[inline]
pub fn compile_listing<R: Read>(wam: &mut Machine, src: R, indices: IndexStore) -> EvalSession
{
    let mut compiler = ListingCompiler::new(&wam.code_repo);

    match compile_work(&mut compiler, wam, src, indices) {
        EvalSession::Error(e) => EvalSession::Error(compiler.drop_expansions(wam, e)),
        result => result
    }
}

fn setup_indices(wam: &mut Machine, indices: &mut IndexStore) -> Result<(), SessionError> {
    if let Some(builtins) = wam.indices.take_module(clause_name!("builtins")) {
        let flags  = wam.machine_flags();
        let result = indices.use_module(&mut wam.code_repo, flags, &builtins);

        wam.indices.insert_module(builtins);
        result
    } else {
        Err(SessionError::ModuleNotFound)
    }
}

pub fn compile_user_module<R: Read>(wam: &mut Machine, src: R) -> EvalSession {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    try_eval_session!(setup_indices(wam, &mut indices));    
    compile_listing(wam, src, indices)
}
