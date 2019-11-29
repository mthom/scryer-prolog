use prolog_parser::ast::*;
use prolog_parser::parser::get_desc;
use prolog_parser::tabled_rc::TabledData;

use crate::prolog::codegen::*;
use crate::prolog::debray_allocator::*;
use crate::prolog::forms::*;
use crate::prolog::instructions::*;
use crate::prolog::iterators::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::term_expansion::ExpansionAdditionResult;
use crate::prolog::machine::toplevel::*;
use crate::prolog::machine::*;

use indexmap::{IndexMap, IndexSet};

use ref_thread_local::RefThreadLocal;

use std::cell::Cell;
use std::collections::VecDeque;
use std::fs::File;
use std::io::Read;
use std::mem;
use std::path::PathBuf;

#[allow(dead_code)]
pub fn print_code(code: &Code) {
    for clause in code {
        match clause {
            &Line::Arithmetic(ref arith) => println!("{}", arith),
            &Line::Fact(ref fact_instr) => println!("{}", fact_instr),
            &Line::Cut(ref cut) => println!("{}", cut),
            &Line::Choice(ref choice) => println!("{}", choice),
            &Line::Control(ref control) => println!("{}", control),
            &Line::IndexedChoice(ref choice) => println!("{}", choice),
            &Line::Indexing(ref indexing) => println!("{}", indexing),
            &Line::Query(ref query_instr) => println!("{}", query_instr),
        }
    }
}

fn fix_filename(atom_tbl: TabledData<Atom>, filename: &str) -> Result<PathBuf, SessionError> {
    let mut path = PathBuf::from(filename);

    if !path.is_file() {
        if path.extension().is_none() {
            path.set_extension("pl");
        }

        if !path.is_file() {
            let filename = clause_name!(path.to_string_lossy().to_string(), atom_tbl);
            return Err(SessionError::InvalidFileName(filename));
        }
    }

    Ok(path)
}

fn load_module<R: Read>(
    wam: &mut Machine,
    stream: ParsingStream<R>,
    suppress_warnings: bool,
    listing_src: ClauseName,
) -> Result<ClauseName, SessionError> {
    // follow the operation of compile_user_module, but before
    // compiling, check that a module is declared in the file. if not,
    // throw an exception.
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    setup_indices(wam, clause_name!("builtins"), &mut indices)?;

    let mut compiler = ListingCompiler::new(
        &wam.code_repo,
        suppress_warnings,
        listing_src.clone(),
    );

    let results = compiler.gather_items(wam, stream, &mut indices);

    let module_name = if let Some(ref module) = &compiler.module {
        module.module_decl.name.clone()
    } else {
        // this impromptu definition (namely, its exports) will be filled out later.
        let module_decl = ModuleDecl { name: listing_src, exports: vec![] };

        let mut module = Module::new(module_decl, wam.indices.atom_tbl.clone());
        let module_name = module.module_decl.name.clone();

        module.is_impromptu_module = true;

        compiler.module = Some(module);
        module_name
    };

    results.and_then(|results| compile_work_impl(&mut compiler, wam, indices, results))
           .or_else(|e| {
               compiler.print_error(&e);
               Err(e)
           })?;

    Ok(module_name)
}

pub(super)
fn load_module_from_file(
    wam: &mut Machine,
    filename: &str,
    suppress_warnings: bool,
) -> Result<ClauseName, SessionError> {
    let path = fix_filename(wam.indices.atom_tbl.clone(), filename)?;
    let filename = clause_name!(path.to_string_lossy().to_string(), wam.indices.atom_tbl);

    let file_handle = File::open(&path).or_else(|_| {
        Err(SessionError::InvalidFileName(filename.clone()))
    })?;

    load_module(wam, parsing_stream(file_handle), suppress_warnings, filename)
}

pub type PredicateCompileQueue = (Predicate, VecDeque<TopLevel>);

// throw errors if declaration or query found.
fn compile_relation(
    cg: &mut CodeGenerator<DebrayAllocator>,
    tl: &TopLevel
) -> Result<Code, ParserError> {
    match tl {
        &TopLevel::Declaration(_) | &TopLevel::Query(_) => Err(ParserError::ExpectedRel),
        &TopLevel::Predicate(ref clauses) => cg.compile_predicate(&clauses.0),
        &TopLevel::Fact(ref fact, ..) => Ok(cg.compile_fact(fact)),
        &TopLevel::Rule(ref rule, ..) => cg.compile_rule(rule),
    }
}

fn issue_singleton_warnings(
    src_name: ClauseName,
    terms_and_locs: Vec<(Term, usize, usize)>,
) {
    for (term, line_num, _col_num) in terms_and_locs {
        let mut singletons = vec![];
        let mut var_count = IndexMap::new();

        for subterm in breadth_first_iter(&term, true) {
            if let TermRef::Var(_, _, var) = subterm {
                let entry = var_count.entry(var).or_insert(0);
                *entry += 1;
            }
        }

        for (var, count) in var_count {
            if count == 1 && !var.starts_with("_") && var.as_str() != "!" {
                singletons.push(var);
            }
        }

        if let Some(last_var) = singletons.pop() {
            print!("Warning: {}:{}: Singleton variables: [",
                   src_name, line_num);

            for var in singletons {
                print!("{}, ", var);
            }

            println!("{}]", last_var);
        }
    }
}

// set first jmp_by_call or jmp_by_index instruction to code.len() -
// idx, where idx is the place it occurs. It only does this to the
// *first* uninitialized jmp index it encounters, then returns.
fn set_first_index(code: &mut Code) {
    let code_len = code.len();

    for (idx, line) in code.iter_mut().enumerate() {
        match line {
            &mut Line::Control(ControlInstruction::JmpBy(_, ref mut offset, ..))
                if *offset == 0 =>
            {
                *offset = code_len - idx;
                break;
            }
            _ => {}
        };
    }
}

pub fn compile_appendix(
    code: &mut Code,
    queue: &VecDeque<TopLevel>,
    non_counted_bt: bool,
    flags: MachineFlags,
) -> Result<(), ParserError> {
    for tl in queue.iter() {
        set_first_index(code);
        let mut cg = CodeGenerator::<DebrayAllocator>::new(non_counted_bt, flags);
        let decl_code = compile_relation(&mut cg, tl)?;
        code.extend(decl_code.into_iter());
    }

    Ok(())
}

impl CodeRepo {
    pub fn compile_hook(
        &mut self,
        hook: CompileTimeHook,
        flags: MachineFlags,
    ) -> Result<(), ParserError> {
        let key = (hook.name(), hook.arity());

        match self.term_dir.get(&key) {
            Some(preds) => {
                let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
                let mut code = cg.compile_predicate(&(preds.0).0)?;

                compile_appendix(&mut code, &preds.1, false, flags)?;

                Ok(match hook {
                    CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                        self.term_expanders = code
                    }
                    CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                        self.goal_expanders = code
                    }
                })
            }
            None => Ok(()),
        }
    }
}

fn compile_query(
    terms: Vec<QueryTerm>,
    queue: VecDeque<TopLevel>,
    flags: MachineFlags,
) -> Result<(Code, AllocVarDict), ParserError> {
    // count backtracking inferences.
    let mut cg = CodeGenerator::<DebrayAllocator>::new(false, flags);
    let mut code = cg.compile_query(&terms)?;

    compile_appendix(&mut code, &queue, false, flags)?;
    Ok((code, cg.take_vars()))
}

fn add_hooks_to_mockup(
    code_repo: &mut CodeRepo,
    hook: CompileTimeHook,
    expansions: (Predicate, VecDeque<TopLevel>),
) {
    let key = (hook.name(), hook.arity());
    let preds = code_repo
        .term_dir
        .entry(key.clone())
        .or_insert((Predicate::new(), VecDeque::from(vec![])));

    (preds.0).0.extend((expansions.0).0.into_iter());
    preds.1.extend(expansions.1.into_iter());
}

fn setup_module_expansions(wam: &mut Machine, module: &Module) {
    let term_expansions = module.term_expansions.clone();
    let goal_expansions = module.goal_expansions.clone();

    add_hooks_to_mockup(
        &mut wam.code_repo,
        CompileTimeHook::TermExpansion,
        term_expansions,
    );

    add_hooks_to_mockup(
        &mut wam.code_repo,
        CompileTimeHook::GoalExpansion,
        goal_expansions,
    );
}

pub(super) fn compile_into_module<R: Read>(
    wam: &mut Machine,
    module_name: ClauseName,
    src: ParsingStream<R>,
    name: ClauseName,
) -> EvalSession {
    let mut indices = default_index_store!(wam.atom_tbl_of(&name));
    let module = wam.indices.take_module(module_name.clone()).unwrap();

    indices.code_dir = module.code_dir.clone();
    indices.op_dir   = module.op_dir.clone();
    indices.atom_tbl = module.atom_tbl.clone();

    let mut compiler = ListingCompiler::new(&wam.code_repo, true, module_name.clone());

    match compile_into_module_impl(wam, &mut compiler, module, src, indices) {
        Ok(()) => EvalSession::EntrySuccess,
        Err(e) => {
            if let Some(module) = compiler.module.take() {
                wam.indices.insert_module(module);
            }

            compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo);
            EvalSession::from(e)
        }
    }
}

fn compile_into_module_impl<R: Read>(
    wam: &mut Machine,
    compiler: &mut ListingCompiler,
    module: Module,
    src: ParsingStream<R>,
    mut indices: IndexStore,
) -> Result<(), SessionError> {
    setup_module_expansions(wam, &module);

    let module_name = module.module_decl.name.clone();
    compiler.module = Some(module);

    let flags = wam.machine_flags();

    wam.code_repo.compile_hook(CompileTimeHook::TermExpansion, flags)?;
    wam.code_repo.compile_hook(CompileTimeHook::GoalExpansion, flags)?;

    let results = compiler.gather_items(wam, src, &mut indices)?;
    let module_code =
        compiler.generate_code(results.worker_results, wam, &mut indices.code_dir, 0)?;

    let mut clause_code_generator = ClauseCodeGenerator::new(module_code.len(), module_name.clone());

    clause_code_generator.generate_clause_code(&results.dynamic_clause_map, wam)?;
    add_module_code(wam, compiler.module.take().unwrap(), module_code, indices);
    clause_code_generator.add_clause_code(wam, results.dynamic_clause_map);

    Ok(compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo))
}

pub struct GatherResult {
    dynamic_clause_map: DynamicClauseMap,
    pub(crate) worker_results: Vec<PredicateCompileQueue>,
    toplevel_results: Vec<PredicateCompileQueue>,
    toplevel_indices: IndexStore,
    addition_results: ExpansionAdditionResult,
    top_level_terms: Vec<(Term, usize, usize)>
}

pub struct ClauseCodeGenerator {
    len_offset: usize,
    code: Code,
    module_name: ClauseName,
    pi_to_loc: IndexMap<PredicateKey, usize>,
}

impl ClauseCodeGenerator {
    #[inline]
    fn new(len_offset: usize, module_name: ClauseName) -> Self {
        ClauseCodeGenerator {
            len_offset,
            code: vec![],
            module_name,
            pi_to_loc: IndexMap::new(),
        }
    }

    // compiles the latest version of clause/2.
    fn generate_clause_code(
        &mut self,
        dynamic_clause_map: &DynamicClauseMap,
        wam: &Machine,
    ) -> Result<(), SessionError> {
        for ((name, arity), heads_and_tails) in dynamic_clause_map {
            if heads_and_tails.is_empty() {
                continue;
            }

            let predicate = Predicate(
                heads_and_tails
                    .iter()
                    .map(|(head, tail)| {
                        let clause = Term::Clause(
                            Cell::default(),
                            clause_name!("clause"),
                            vec![Box::new(head.clone()), Box::new(tail.clone())],
                            None,
                        );
                        PredicateClause::Fact(clause, 0, 0)
                    })
                    .collect(),
            );

            let p = self.code.len() + wam.code_repo.code.len() + self.len_offset;
            let mut cg = CodeGenerator::<DebrayAllocator>::new(false, wam.machine_flags());

            let mut decl_code = compile_relation(
                &mut cg,
                &TopLevel::Predicate(predicate),
            )?;

            compile_appendix(&mut decl_code, &VecDeque::new(), false, wam.machine_flags())?;

            self.pi_to_loc.insert((name.clone(), *arity), p);
            self.code.extend(decl_code.into_iter());
        }

        Ok(())
    }

    fn add_clause_code(self, wam: &mut Machine, dynamic_code_dir: DynamicClauseMap)
    {
        wam.code_repo.code.extend(self.code.into_iter());

        if self.module_name.as_str() == "user" {
            for ((name, arity), _) in &dynamic_code_dir {
                wam.indices.code_dir.entry((name.clone(), *arity))
                   .or_insert(CodeIndex::dynamic_undefined(clause_name!("user")));
            }
        }

        for ((name, arity), _) in dynamic_code_dir {
            wam.indices.dynamic_code_dir.insert((name.owning_module(), name, arity),
                                                DynamicPredicateInfo::default());
        }

        for ((name, arity), p) in self.pi_to_loc {
            let entry = wam
                .indices
                .dynamic_code_dir
                .entry((name.owning_module(), name, arity))
                .or_insert(DynamicPredicateInfo::default());

            entry.clauses_subsection_p = p;
        }
    }
}

pub struct ListingCompiler {
    non_counted_bt_preds: IndexSet<PredicateKey>,
    module: Option<Module>,
    user_term_dir: TermDir,
    orig_term_expansion_lens: (usize, usize),
    orig_goal_expansion_lens: (usize, usize),
    initialization_goals: (Vec<QueryTerm>, VecDeque<TopLevel>),
    suppress_warnings: bool,
    listing_src: ClauseName // a file? a module?
}

fn add_toplevel_code(wam: &mut Machine, code: Code, indices: IndexStore) {
    wam.add_batched_code(code, indices.code_dir);
    wam.add_batched_ops(indices.op_dir);
}

#[inline]
fn add_module_code(wam: &mut Machine, mut module: Module, code: Code, indices: IndexStore)
{
    module.code_dir.extend(indices.code_dir);
    module.op_dir.extend(indices.op_dir.into_iter());

    wam.add_module(module, code);
}

fn add_non_module_code(
    wam: &mut Machine,
    dynamic_clause_map: DynamicClauseMap,
    code: Code,
    indices: IndexStore,
) -> Result<(), SessionError> {
    wam.check_toplevel_code(&indices)?;

    let mut clause_code_generator = ClauseCodeGenerator::new(code.len(), clause_name!("user"));
    clause_code_generator.generate_clause_code(&dynamic_clause_map, wam)?;

    add_toplevel_code(wam, code, indices);
    clause_code_generator.add_clause_code(wam, dynamic_clause_map);

    Ok(())
}

pub(super)
fn load_library(
    wam: &mut Machine,
    name: ClauseName,
    suppress_warnings: bool,
) -> Result<ClauseName, SessionError> {
    match LIBRARIES.borrow().get(name.as_str()) {
        Some(code) => {
            load_module(wam, parsing_stream(code.as_bytes()),
                        suppress_warnings, name.clone())
        }
        None => Err(SessionError::ModuleNotFound)
    }
}

impl ListingCompiler {
    #[inline]
    pub fn new(
        code_repo: &CodeRepo,
        suppress_warnings: bool,
        listing_src: ClauseName,
    ) -> Self {
        ListingCompiler {
            non_counted_bt_preds: IndexSet::new(),
            module: None,
            user_term_dir: TermDir::new(),
            orig_term_expansion_lens: code_repo
                .term_dir_entry_len((clause_name!("term_expansion"), 2)),
            orig_goal_expansion_lens: code_repo
                .term_dir_entry_len((clause_name!("goal_expansion"), 2)),
	    initialization_goals: (vec![], VecDeque::from(vec![])),
            suppress_warnings,
            listing_src
        }
    }

    /*
    Replace calls to self with a localized index cell, not available to the global CodeIndex.
    This is done to implement logical update semantics for dynamic database updates.
     */
    fn localize_self_calls(&mut self, name: ClauseName, arity: usize, code: &mut Code, p: usize) {
        let self_idx = CodeIndex::default();
        set_code_index!(self_idx, IndexPtr::Index(p), self.get_module_name());

        for instr in code.iter_mut() {
            if let &mut Line::Control(ControlInstruction::CallClause(ref mut ct, ..)) = instr {
                match ct {
                    &mut ClauseType::Named(ref ct_name, ct_arity, ref mut idx)
                        if ct_name == &name && arity == ct_arity =>
                    {
                        *idx = self_idx.clone();
                    }
                    &mut ClauseType::Op(ref op_name, ref shared_op_desc, ref mut idx)
                        if op_name == &name && shared_op_desc.arity() == arity =>
                    {
                        *idx = self_idx.clone();
                    }
                    _ => {}
                }
            }
        }
    }

    fn use_module(
        &mut self,
        submodule: ClauseName,
        code_repo: &mut CodeRepo,
        flags: MachineFlags,
        wam_indices: &mut IndexStore,
        indices: &mut IndexStore,
    ) -> Result<(), SessionError> {
        let module_name = self.get_module_name();

        if let Some(mut submodule) = wam_indices.take_module(submodule) {
            unwind_protect!(
                indices.use_module(code_repo, flags, &submodule),
                wam_indices.insert_module(submodule)
            );

            if let Some(ref mut module) = &mut self.module {
                module.remove_module(module_name, &submodule);
                unwind_protect!(
                    module.use_module(code_repo, flags, &submodule),
                    wam_indices.insert_module(submodule)
                );
            } else {
                submodule.inserted_expansions = true;
                wam_indices.remove_module(clause_name!("user"), &submodule);
            }

            Ok(wam_indices.insert_module(submodule))
        } else {
            Err(SessionError::ModuleNotFound)
        }
    }

    fn use_qualified_module(
        &mut self,
        submodule: ClauseName,
        code_repo: &mut CodeRepo,
        flags: MachineFlags,
        exports: &Vec<ModuleExport>,
        wam_indices: &mut IndexStore,
        indices: &mut IndexStore,
    ) -> Result<(), SessionError> {
        let module_name = self.get_module_name();

        if let Some(mut submodule) = wam_indices.take_module(submodule) {
            unwind_protect!(
                indices.use_qualified_module(code_repo, flags, &submodule, exports),
                wam_indices.insert_module(submodule)
            );

            if let &mut Some(ref mut module) = &mut self.module {
                module.remove_module(module_name, &submodule);
                unwind_protect!(
                    module.use_qualified_module(code_repo, flags, &submodule, exports),
                    wam_indices.insert_module(submodule)
                );
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
        self.module
            .as_ref()
            .map(|module| module.module_decl.name.clone())
            .unwrap_or(ClauseName::BuiltIn("user"))
    }

    fn generate_init_goal_code(
	&mut self,
	flags: MachineFlags
    ) -> Result<Code, SessionError> {
	let query_terms = mem::replace(&mut self.initialization_goals.0, vec![]);
	let queue = mem::replace(&mut self.initialization_goals.1, VecDeque::new());

	compile_query(query_terms, queue, flags)
	    .map(|(code, _)| code)
	    .map_err(SessionError::from)
    }

    pub(crate) fn generate_code(
        &mut self,
        decls: Vec<PredicateCompileQueue>,
        wam: &Machine,
        code_dir: &mut CodeDir,
        code_offset: usize,
    ) -> Result<Code, SessionError> {
        let mut code = vec![];

        for (decl, queue) in decls {
            let (name, arity) = decl
                .predicate_indicator()
                .ok_or(SessionError::NamelessEntry)?;
            let non_counted_bt = self.non_counted_bt_preds.contains(&(name.clone(), arity));

            let p = code.len() + wam.code_repo.code.len() + code_offset;
            let mut cg = CodeGenerator::<DebrayAllocator>::new(non_counted_bt, wam.machine_flags());

            let decl = TopLevel::Predicate(decl);
            let mut decl_code = compile_relation(&mut cg, &decl)?;

            compile_appendix(&mut decl_code, &queue, non_counted_bt, wam.machine_flags())?;

            let idx = code_dir
                .entry((name.clone(), arity))
                .or_insert(CodeIndex::default());
            set_code_index!(idx, IndexPtr::Index(p), self.get_module_name());

            self.localize_self_calls(name, arity, &mut decl_code, p);
            code.extend(decl_code.into_iter());
        }

        Ok(code)
    }

    fn add_non_counted_bt_flag(&mut self, name: ClauseName, arity: usize) {
        self.non_counted_bt_preds.insert((name, arity));
    }

    fn add_term_dir_terms(
        &mut self,
        hook: CompileTimeHook,
        code_repo: &mut CodeRepo,
        key: PredicateKey,
        clause: PredicateClause,
        queue: VecDeque<TopLevel>,
    ) -> (usize, usize) {
        let preds = code_repo
            .term_dir
            .entry(key.clone())
            .or_insert((Predicate::new(), VecDeque::from(vec![])));

        let (mut len, mut queue_len) = ((preds.0).0.len(), preds.1.len());

        if self.module.is_some() && hook.has_module_scope() {
            let module_preds = self
                .user_term_dir
                .entry(key.clone())
                .or_insert((Predicate::new(), VecDeque::from(vec![])));

            if let Some(ref mut module) = &mut self.module {
                module.add_expansion_record(hook, clause.clone(), queue.clone());
                module.add_local_expansion(hook, clause.clone(), queue.clone());
            }

            (module_preds.0).0.push(clause);
            module_preds.1.extend(queue.into_iter());

            (preds.0).0.extend((module_preds.0).0.iter().cloned());
            preds.1.extend(module_preds.1.iter().cloned());
        } else {
            let module_preds = self
                .user_term_dir
                .entry(key.clone())
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

    fn submit_op(
        &mut self,
        wam: &Machine,
        indices: &mut IndexStore,
        op_decl: &OpDecl,
    ) -> Result<(), SessionError> {
        let spec = get_desc(
            op_decl.name(),
            composite_op!(
                self.module.is_some(),
                &wam.indices.op_dir,
                &mut indices.op_dir
            ),
        );

        op_decl.submit(self.get_module_name(), spec, &mut indices.op_dir)        
    }

    fn process_decl(
        &mut self,
        decl: Declaration,
        wam: &mut Machine,
        indices: &mut IndexStore,
        flags: MachineFlags,
    ) -> Result<(), SessionError> {
        match decl {
            Declaration::EndOfFile => Ok(()),
            Declaration::Hook(hook, clause, queue) => {
                let key = (hook.name(), hook.arity());
                let (len, queue_len) =
                    self.add_term_dir_terms(hook, &mut wam.code_repo, key.clone(), clause, queue);

                let result = wam
                    .code_repo
                    .compile_hook(hook, flags)
                    .map_err(SessionError::from);
                
                wam.code_repo.truncate_terms(key, len, queue_len);

                result
            }
            Declaration::NonCountedBacktracking(name, arity) => {
                Ok(self.add_non_counted_bt_flag(name, arity))
            }
            Declaration::Op(op_decl) => {
                self.submit_op(wam, indices, &op_decl)
            }
            Declaration::UseModule(ModuleSource::Library(name)) => {
                let name = if !wam.indices.modules.contains_key(&name) {
                    load_library(wam, name, true)?
                } else {
                    name
                };

                self.use_module(name, &mut wam.code_repo, flags, &mut wam.indices, indices)
            }
            Declaration::UseQualifiedModule(ModuleSource::Library(name), exports) => {
                let name = if !wam.indices.modules.contains_key(&name) {
                    load_library(wam, name, true)?
                } else {
                    name
                };

                self.use_qualified_module(
                    name,
                    &mut wam.code_repo,
                    flags,
                    &exports,
                    &mut wam.indices,
                    indices
                )
            },
            Declaration::Module(module_decl) => {
                if self.module.is_none() {
                    let module_name = module_decl.name.clone();
                    let atom_tbl = TabledData::new(module_name.to_rc());

                    for export in module_decl.exports.iter() {
                        if let ModuleExport::OpDecl(ref op_decl) = export {
                            self.submit_op(wam, indices, op_decl)?;
                        }
                    }

                    Ok(self.module = Some(Module::new(module_decl, atom_tbl)))
                } else {
                    Err(SessionError::from(ParserError::InvalidModuleDecl))
                }
            }
            Declaration::UseModule(ModuleSource::File(filename)) => {
                let name = load_module_from_file(wam, filename.as_str(), true)?;
                self.use_module(name, &mut wam.code_repo, flags, &mut wam.indices, indices)
            }
            Declaration::UseQualifiedModule(ModuleSource::File(filename), exports) => {
                let name = load_module_from_file(wam, filename.as_str(), true)?;

                self.use_qualified_module(
                    name,
                    &mut wam.code_repo,
                    flags,
                    &exports,
                    &mut wam.indices,
                    indices,
                )
            }
	    Declaration::ModuleInitialization(query_terms, queue) => {
		self.initialization_goals.0.extend(query_terms.into_iter());
		self.initialization_goals.1.extend(queue.into_iter());

		Ok(())
	    }
            Declaration::Dynamic(..) => Ok(()),
        }
    }

    fn process_and_commit_decl<R: Read>(
        &mut self,
        decl: Declaration,
        worker: &mut TopLevelBatchWorker<R>,
        indices: &mut IndexStore,
        flags: MachineFlags,
    ) -> Result<(), SessionError> {
        let mut update_expansion_lengths = false;

        match &decl {
            &Declaration::Dynamic(ref name, arity) => {
                worker
                    .dynamic_clause_map
                    .entry((name.clone(), arity))
                    .or_insert(vec![]);

		indices.code_dir
		       .entry((name.clone(), arity))
		       .or_insert(CodeIndex::dynamic_undefined(self.get_module_name()));
            }
            &Declaration::Hook(hook, _, ref queue) if self.module.is_none() => worker
                .term_stream
                .incr_expansion_lens(hook.user_scope(), 1, queue.len()),
            &Declaration::Hook(hook, _, ref queue) if !hook.has_module_scope() => {
                worker.term_stream.incr_expansion_lens(hook, 1, queue.len())
            }
            &Declaration::UseModule(_) | &Declaration::UseQualifiedModule(..) => {
                update_expansion_lengths = true
            }
            _ => {}
        };

        let result = self.process_decl(decl, &mut worker.term_stream.wam, indices, flags);

        if update_expansion_lengths {
            worker.term_stream.update_expansion_lens();
        }

        result
    }

    pub(crate) fn gather_items<R: Read>(
        &mut self,
        wam: &mut Machine,
        mut src: ParsingStream<R>,
        indices: &mut IndexStore,
    ) -> Result<GatherResult, SessionError> {
        let flags = wam.machine_flags();
        let atom_tbl = indices.atom_tbl.clone();
        let mut worker = TopLevelBatchWorker::new(&mut src, atom_tbl.clone(), flags, wam);

        let mut toplevel_results = vec![];
        let mut toplevel_indices = default_index_store!(atom_tbl.clone());

        while let Some(decl) = worker.consume(indices)? {
            if decl.is_module_decl() {
                toplevel_indices.copy_and_swap(indices);
                mem::swap(&mut worker.results, &mut toplevel_results);
                worker.in_module = true;

                self.process_and_commit_decl(decl, &mut worker, indices, flags)?;

                if let Some(ref module) = &self.module {
                    worker.term_stream.set_atom_tbl(module.atom_tbl.clone());
                }
            } else if decl.is_end_of_file() {
                break;
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
            addition_results,
            top_level_terms: worker.term_stream.top_level_terms(),
        })
    }

    fn drop_expansions(&self, flags: MachineFlags, code_repo: &mut CodeRepo) {
        let (te_len, te_queue_len) = self.orig_term_expansion_lens;
        let (ge_len, ge_queue_len) = self.orig_goal_expansion_lens;

        code_repo.truncate_terms((clause_name!("term_expansion"), 2), te_len, te_queue_len);
        code_repo.truncate_terms((clause_name!("goal_expansion"), 2), ge_len, ge_queue_len);

        discard_result!(code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags));
        discard_result!(code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags));
    }

    fn print_error(&self, e: &SessionError) {
        if let &SessionError::ParserError(ref e) = e {
            if let Some((line_num, _col_num)) = e.line_and_col_num() {
                println!("{}:{}: {}", self.listing_src, line_num, e.as_str());
            }
        }
    }
}

fn compile_work_impl(
    compiler: &mut ListingCompiler,
    wam: &mut Machine,
    mut indices: IndexStore,
    mut results: GatherResult,
) -> Result<(), SessionError> {
    if let Some(ref mut module) = &mut compiler.module {
        // compile the module-level goal and term expansions and store
        // their locations to the module's code_dir.
        let decls = module.take_local_expansions();
            
        if !decls.is_empty() {
            results.worker_results.extend(decls.into_iter());
        }
    }
    
    let module_code = compiler.generate_code(
        results.worker_results,
        wam,
        &mut indices.code_dir,
        0
    )?;

    let toplvl_code = compiler.generate_code(
        results.toplevel_results,
        wam,
        &mut results.toplevel_indices.code_dir,
        module_code.len()
    )?;

    if let Some(ref mut module) = &mut compiler.module {
        if !module.is_impromptu_module {
            module.user_term_expansions = results.addition_results.take_term_expansions();
            module.user_goal_expansions = results.addition_results.take_goal_expansions();
        }
    }

    let flags = wam.machine_flags();

    wam.code_repo.compile_hook(CompileTimeHook::UserTermExpansion, flags)?;
    wam.code_repo.compile_hook(CompileTimeHook::UserGoalExpansion, flags)?;

    if let Some(mut module) = compiler.module.take() {
        if module.is_impromptu_module {
            module.module_decl.exports = indices.code_dir.keys().cloned()
                .filter(|(name, _)| name.owning_module().as_str() != "builtins")
                .map(ModuleExport::PredicateKey)
                .collect();
        }

        let mut clause_code_generator =
            ClauseCodeGenerator::new(module_code.len() + toplvl_code.len(),
                                     module.module_decl.name.clone());

        wam.check_toplevel_code(&results.toplevel_indices)?;
        clause_code_generator.generate_clause_code(&results.dynamic_clause_map, wam)?;

        if let Some(ref module) = wam.indices.modules.swap_remove(&module.module_decl.name) {
            wam.indices.remove_module(clause_name!("user"), module);
        }

        if module.is_impromptu_module {
            add_module_code(wam, module, module_code, indices);

            let module = wam.indices.take_module(compiler.listing_src.clone()).unwrap();

            wam.indices.use_module(&mut wam.code_repo, wam.machine_st.flags, &module)?;
            wam.indices.insert_module(module);
        } else {                  
            add_module_code(wam, module, module_code, indices);
        }

        add_toplevel_code(wam, toplvl_code, results.toplevel_indices);
        clause_code_generator.add_clause_code(wam, results.dynamic_clause_map);
    } else {
        add_non_module_code(
            wam,
            results.dynamic_clause_map,
            module_code,
            indices
        )?;
    }

    let init_goal_code = compiler.generate_init_goal_code(
	wam.machine_flags()
    )?;

    if init_goal_code.len() > 0 {
	if !wam.run_init_code(init_goal_code) {
            println!("Warning: initialization goal for {} failed",
                     compiler.listing_src);
        }
    }

    if !compiler.suppress_warnings {
        issue_singleton_warnings(
            compiler.listing_src.clone(),
            results.top_level_terms,
        );
    }

    Ok(())
}

fn compile_work<R: Read>(
    compiler: &mut ListingCompiler,
    wam: &mut Machine,
    src: ParsingStream<R>,
    mut indices: IndexStore,
) -> EvalSession {
    let results = try_eval_session!(compiler.gather_items(wam, src, &mut indices));
    try_eval_session!(compile_work_impl(compiler, wam, indices, results));
    EvalSession::EntrySuccess
}

/* This is a truncated version of compile_user_module, used for
compiling code composing special forms, ie. the code that calls
M:verify_attributes on attributed variables. */
pub fn compile_special_form<R: Read>(
    wam: &mut Machine,
    src: ParsingStream<R>,
    listing_src: ClauseName,
) -> Result<usize, SessionError> {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    setup_indices(wam, clause_name!("builtins"), &mut indices)?;

    let mut compiler = ListingCompiler::new(&wam.code_repo, true, listing_src);
    let results = compiler.gather_items(wam, src, &mut indices)?;

    let code = compiler.generate_code(results.worker_results, wam, &mut indices.code_dir, 0)?;
    let p = wam.code_repo.code.len();

    add_toplevel_code(wam, code, indices);

    Ok(p)
}

#[inline]
pub fn compile_listing<R: Read>(
    wam: &mut Machine,
    src: ParsingStream<R>,
    indices: IndexStore,
    suppress_warnings: bool,
    listing_src: ClauseName,
) -> EvalSession {
    let mut compiler = ListingCompiler::new(&wam.code_repo, suppress_warnings, listing_src);

    match compile_work(&mut compiler, wam, src, indices) {
        EvalSession::Error(e) => {
            compiler.drop_expansions(wam.machine_flags(), &mut wam.code_repo);
            compiler.print_error(&e);

            EvalSession::Error(e)
        }
        result => result,
    }
}

pub(super) fn setup_indices(
    wam: &mut Machine,
    module: ClauseName,
    indices: &mut IndexStore,
) -> Result<(), SessionError> {
    if let Some(module) = wam.indices.take_module(module) {
        let flags = wam.machine_flags();
        let result = indices.use_module(&mut wam.code_repo, flags, &module);

        wam.indices.insert_module(module);
        result
    } else {
        Err(SessionError::ModuleNotFound)
    }
}

pub fn compile_user_module<R: Read>(
    wam: &mut Machine,
    src: ParsingStream<R>,
    suppress_warnings: bool,
    listing_src: ClauseName,
) -> EvalSession {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    try_eval_session!(setup_indices(wam, clause_name!("builtins"), &mut indices));
    compile_listing(wam, src, indices, suppress_warnings, listing_src)
}
