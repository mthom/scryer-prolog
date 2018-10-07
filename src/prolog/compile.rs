use prolog_parser::ast::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::instructions::*;
use prolog::debray_allocator::*;
use prolog::codegen::*;
use prolog::machine::*;
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

// throw errors if declaration or query found.
fn compile_relation(tl: &TopLevel, non_counted_bt: bool, flags: MachineFlags) -> Result<Code, ParserError>
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

fn compile_appendix(code: &mut Code, queue: Vec<TopLevel>, non_counted_bt: bool, flags: MachineFlags)
                    -> Result<(), ParserError>
{
    for tl in queue.iter() {
        set_first_index(code);
        code.append(&mut compile_relation(tl, non_counted_bt, flags)?);
    }

    Ok(())
}

fn compile_query(terms: Vec<QueryTerm>, queue: Vec<TopLevel>, flags: MachineFlags)
                 -> Result<(Code, AllocVarDict), ParserError>
{
    // count backtracking inferences.
    let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
    let mut code = try!(cg.compile_query(&terms));

    compile_appendix(&mut code, queue, false, flags)?;

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

pub fn compile_term(wam: &mut Machine, term: Term) -> EvalSession
{
    let packet = try_eval_session!(consume_term(term, &mut wam.indices));

    match packet {
        TopLevelPacket::Query(terms, queue) =>
            match compile_query(terms, queue, wam.machine_flags()) {
                Ok((mut code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        TopLevelPacket::Decl(TopLevel::Declaration(decl), _) => {
            let mut compiler = ListingCompiler::new();

            let indices = try_eval_session!(compile_decl(wam, &mut compiler, decl));
            try_eval_session!(compiler.add_code(wam, vec![], indices));

            EvalSession::EntrySuccess
        },
        _ => EvalSession::from(SessionError::UserPrompt)
    }
}

struct GatherResult {
    worker_results: Vec<(Predicate, VecDeque<TopLevel>)>,
    toplevel_results: Vec<(Predicate, VecDeque<TopLevel>)>,
    toplevel_indices: IndexStore
}

pub struct ListingCompiler {
    non_counted_bt_preds: HashSet<PredicateKey>,
    module: Option<Module>,
}

impl ListingCompiler {
    #[inline]
    pub fn new() -> Self {
        ListingCompiler {
            module: None, non_counted_bt_preds: HashSet::new()
        }
    }

    fn use_module(&mut self, submodule: ClauseName, wam_indices: &mut IndexStore, indices: &mut IndexStore)
                  -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        if let Some(submodule) = wam_indices.take_module(submodule) {
            indices.use_module(&submodule)?;

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                module.use_module(&submodule)?;
            } else {
                wam_indices.remove_module(clause_name!("user"), &submodule);
            }

            Ok(wam_indices.insert_module(submodule))
        } else {
            Err(SessionError::ModuleNotFound)
        }
    }

    fn use_qualified_module(&mut self, submodule: ClauseName, exports: &Vec<PredicateKey>,
                            wam_indices: &mut IndexStore, indices: &mut IndexStore)
                            -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        if let Some(submodule) = wam_indices.take_module(submodule) {
            indices.use_qualified_module(&submodule, exports)?;

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(mod_name, &submodule);
                module.use_qualified_module(&submodule, exports)?;
            } else {
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

    fn generate_code(&mut self, decls: Vec<(Predicate, VecDeque<TopLevel>)>,
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

            compile_appendix(&mut decl_code, Vec::from(queue), non_counted_bt, wam.machine_flags())?;

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

    fn process_decl(&mut self, decl: Declaration, code_repo: &mut CodeRepo,
                    wam_indices: &mut IndexStore, indices: &mut IndexStore,
                    flags: MachineFlags)
                    -> Result<(), SessionError>
    {
        match decl {
            Declaration::Hook(CompileTimeHook::TermExpansion, clause, queue) => {
                let key = (clause_name!("term_expansion"), 2);
                let preds = code_repo.term_dir.entry(key).or_insert(Predicate(vec![]));

                preds.0.push(clause);

                let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
                let mut code = cg.compile_predicate(&preds.0)?;

                compile_appendix(&mut code, Vec::from(queue), false, flags)?;

                Ok(code_repo.term_expanders = code)
            },
            Declaration::NonCountedBacktracking(name, arity) =>
                Ok(self.add_non_counted_bt_flag(name, arity)),
            Declaration::Op(op_decl) =>
                op_decl.submit(self.get_module_name(), &mut indices.op_dir),
            Declaration::UseModule(name) =>
                self.use_module(name, wam_indices, indices),
            Declaration::UseQualifiedModule(name, exports) =>
                self.use_qualified_module(name, &exports, wam_indices, indices),
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

    fn gather_items<R: Read>(&mut self, wam: &mut Machine, src: R, indices: &mut IndexStore)
                             -> Result<GatherResult, SessionError>
    {
        let flags = wam.machine_flags();
        let machine_st  = &mut wam.machine_st;
        let wam_indices = &mut wam.indices;

        let atom_tbl   = wam_indices.atom_tbl.clone();

        let mut worker = TopLevelBatchWorker::new(src, atom_tbl.clone(), flags,
                                                  wam_indices, &mut wam.policies,
                                                  &mut wam.code_repo);

        let mut toplevel_results = vec![];
        let mut toplevel_indices = default_index_store!(atom_tbl.clone());

        while let Some(decl) = worker.consume(machine_st, indices)? {
            if decl.is_module_decl() {
                toplevel_indices.copy_and_swap(indices);
                mem::swap(&mut worker.results, &mut toplevel_results);
                worker.in_module = true;

                self.process_decl(decl, worker.term_stream.code_repo,
                                  worker.term_stream.indices,
                                  indices, flags)?;

                if let &Some(ref module) = &self.module {
                    worker.term_stream.set_atom_tbl(module.atom_tbl.clone());
                }
            } else {
                self.process_decl(decl, worker.term_stream.code_repo,
                                  worker.term_stream.indices,
                                  indices, flags)?;
            }
        }

        Ok(GatherResult {
            worker_results: worker.results,
            toplevel_results,
            toplevel_indices
        })
    }
}

pub
fn compile_listing<R: Read>(wam: &mut Machine, src: R, mut indices: IndexStore) -> EvalSession
{
    let mut compiler = ListingCompiler::new();
    let mut results = try_eval_session!(compiler.gather_items(wam, src, &mut indices));

    let module_code = try_eval_session!(compiler.generate_code(results.worker_results, wam,
                                                               &mut indices.code_dir));
    let toplvl_code = try_eval_session!(compiler.generate_code(results.toplevel_results, wam,
                                                               &mut results.toplevel_indices.code_dir));

    try_eval_session!(compiler.add_code(wam, module_code, indices));
    try_eval_session!(compiler.add_code(wam, toplvl_code, results.toplevel_indices));

    EvalSession::EntrySuccess
}

fn setup_indices(wam: &Machine, indices: &mut IndexStore) -> Result<(), SessionError> {
    if let Some(ref builtins) = wam.indices.modules.get(&clause_name!("builtins")) {
        indices.use_module(builtins)
    } else {
        Err(SessionError::ModuleNotFound)
    }
}

pub fn compile_user_module<R: Read>(wam: &mut Machine, src: R) -> EvalSession {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    try_eval_session!(setup_indices(&wam, &mut indices));
    compile_listing(wam, src, indices)
}
