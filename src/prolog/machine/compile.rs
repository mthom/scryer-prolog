use prolog_parser::ast::*;
use prolog_parser::parser::get_desc;
use prolog_parser::tabled_rc::TabledData;

use crate::prolog::codegen::*;
use crate::prolog::debray_allocator::*;
use crate::prolog::forms::*;
use crate::prolog::instructions::*;
use crate::prolog::iterators::*;
use crate::prolog::machine::code_walker::*;
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

fn fix_filename(
    atom_tbl: TabledData<Atom>,
    mut path: PathBuf,
) -> Result<PathBuf, SessionError>
{
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

fn load_module(
    wam: &mut Machine,
    stream: Stream,
    suppress_warnings: bool,
    listing_src: &ListingSource,
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

    let mut stream = parsing_stream(stream)?;

    let results = compiler.gather_items(
        wam,
        &mut stream,
        &mut indices,
    );

    let module_name = if let Some(ref module) = &compiler.module {
        module.module_decl.name.clone()
    } else {
        // this impromptu definition (namely, its exports) will be filled out later.
        let module_decl = ModuleDecl { name: listing_src.name(), exports: vec![] };

        let mut module  = Module::new(module_decl, wam.indices.atom_tbl.clone(), listing_src.clone());
        let module_name = module.module_decl.name.clone();

        module.is_impromptu_module = true;

        compiler.module = Some(module);
        module_name
    };

    results.and_then(|results| compile_work_impl(&mut compiler, wam, indices, results))
           .or_else(|e| {
               wam.indices.take_module(module_name.clone());
               compiler.print_error(&e);
               Err(e)
           })?;

    Ok(module_name)
}

pub(super)
fn load_module_from_file(
    wam: &mut Machine,
    path_buf: PathBuf,
    suppress_warnings: bool,
) -> Result<ClauseName, SessionError> {
    let mut path_buf = fix_filename(wam.indices.atom_tbl.clone(), path_buf)?;
    let filename = clause_name!(path_buf.to_string_lossy().to_string(), wam.indices.atom_tbl);

    let file_handle = Stream::from(File::open(&path_buf).or_else(|_| {
        Err(SessionError::InvalidFileName(filename.clone()))
    })?);

    path_buf.pop();

    let listing_src = ListingSource::from_file_and_path(filename, path_buf);
    load_module(wam, file_handle, suppress_warnings, &listing_src)
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
                debug_assert!(*offset > 0);

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
) -> Result<(), ParserError> {
    for tl in queue.iter() {
        set_first_index(code);
        let mut cg = CodeGenerator::<DebrayAllocator>::new(non_counted_bt);
        let decl_code = compile_relation(&mut cg, tl)?;
        code.extend(decl_code.into_iter());
    }

    Ok(())
}

fn append_trivial_goal(name: &ClauseName, pred: &mut Predicate)
{
    let var = Box::new(Term::Var(Cell::default(), Rc::new(String::from("X"))));
    let body = QueryTerm::Clause(
        Cell::default(),
        ClauseType::from(clause_name!("$at_end_of_expansion"), 0, None),
        vec![],
        false
    );

    let rule = Rule {
        head: (name.clone(), vec![var.clone(), var], body),
        clauses: vec![]
    };

    pred.0.push(PredicateClause::Rule(rule, 0, 0));
}

impl CodeRepo {
    pub fn compile_hook(
        &mut self,
        hook: CompileTimeHook,
    ) -> Result<(), ParserError> {
        let key = (hook.name(), hook.arity());

        match self.term_dir.get_mut(&key) {
            Some(ref mut preds) => {
                append_trivial_goal(&key.0, &mut preds.0);

                let mut cg = CodeGenerator::<DebrayAllocator>::new(false);
                let mut code = cg.compile_predicate(&(preds.0).0)?;

                compile_appendix(&mut code, &preds.1, false)?;

                (preds.0).0.pop();

                Ok(match hook {
                    CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                        self.term_expanders = code
                    }
                    CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                        self.goal_expanders = code
                    }
                })
            }
            None => Ok(match hook {
                CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                    if self.term_expanders.is_empty() {
                        let mut preds = Predicate::new();
                        append_trivial_goal(&key.0, &mut preds);

                        let mut cg = CodeGenerator::<DebrayAllocator>::new(false);
                        self.term_expanders = cg.compile_predicate(&preds.0)?;
                    }
                }
                CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                    if self.goal_expanders.is_empty() {
                        let mut preds = Predicate::new();
                        append_trivial_goal(&key.0, &mut preds);

                        let mut cg = CodeGenerator::<DebrayAllocator>::new(false);
                        self.goal_expanders = cg.compile_predicate(&preds.0)?;
                    }
                }
            })
        }
    }
}

fn compile_query(
    terms: Vec<QueryTerm>,
    queue: VecDeque<TopLevel>,
) -> Result<(Code, AllocVarDict), ParserError> {
    // count backtracking inferences.
    let mut cg = CodeGenerator::<DebrayAllocator>::new(false);
    let mut code = cg.compile_query(&terms)?;

    compile_appendix(&mut code, &queue, false)?;
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

pub(super)
fn compile_into_module(
    wam: &mut Machine,
    module_name: ClauseName,
    src: Stream,
    name: ClauseName,
) -> EvalSession {
    let mut indices = default_index_store!(wam.atom_tbl_of(&name));
    let module = wam.indices.take_module(module_name.clone()).unwrap();

    indices.code_dir = module.code_dir.clone();
    indices.op_dir   = module.op_dir.clone();
    indices.atom_tbl = module.atom_tbl.clone();

    let mut compiler = ListingCompiler::new(
        &wam.code_repo,
        true,
        module.listing_src.clone(),
    );

    match compile_into_module_impl(wam, &mut compiler, module, src, indices) {
        Ok(()) => EvalSession::EntrySuccess,
        Err(e) => {
            if let Some(module) = compiler.module.take() {
                wam.indices.insert_module(module);
            }

            compiler.drop_expansions(&mut wam.code_repo);
            EvalSession::from(e)
        }
    }
}

fn compile_into_module_impl(
    wam: &mut Machine,
    compiler: &mut ListingCompiler,
    module: Module,
    src: Stream,
    mut indices: IndexStore,
) -> Result<(), SessionError> {
    setup_module_expansions(wam, &module);

    let module_name = module.module_decl.name.clone();
    compiler.module = Some(module);

    wam.code_repo.compile_hook(CompileTimeHook::TermExpansion)?;
    wam.code_repo.compile_hook(CompileTimeHook::GoalExpansion)?;

    let mut stream = parsing_stream(src)?;

    let mut results = compiler.gather_items(
        wam,
        &mut stream,
        &mut indices,
    )?;

    compiler.adapt_in_situ_code(
        results.worker_results,
        wam,
        &mut indices.code_dir,
        &mut indices.module_dir,
        &mut results.in_situ_code,
        &results.in_situ_code_dir,
        &results.in_situ_module_dir,
    )?;

    let mut clause_code_generator = ClauseCodeGenerator::new(
        results.in_situ_code.len(),
        module_name.clone()
    );

    clause_code_generator.generate_clause_code(&results.dynamic_clause_map, wam)?;

    let top_level_term_dir = results.top_level_term_dirs.consolidate();

    add_module(
        wam,
        compiler.module.take().unwrap(),
        indices,
        top_level_term_dir,
    );

    wam.code_repo.code.extend(results.in_situ_code.into_iter());
    clause_code_generator.add_clause_code(wam, results.dynamic_clause_map);

    Ok(compiler.drop_expansions(&mut wam.code_repo))
}

#[derive(Debug)]
pub struct GatherResult {
    dynamic_clause_map: DynamicClauseMap,
    pub(crate) worker_results: Vec<PredicateCompileQueue>,
    toplevel_results: Vec<PredicateCompileQueue>,
    toplevel_indices: IndexStore,
    addition_results: ExpansionAdditionResult,
    top_level_terms: Vec<(Term, usize, usize)>,
    top_level_term_dirs: TermDirQuantum,
    module_term_dirs: TermDirQuantum,
    in_situ_code_dir: InSituCodeDir,
    in_situ_code: Code,
    in_situ_module_dir: ModuleStubDir,
}

#[derive(Debug)]
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
            let mut cg = CodeGenerator::<DebrayAllocator>::new(false);

            let mut decl_code = compile_relation(
                &mut cg,
                &TopLevel::Predicate(predicate),
            )?;

            compile_appendix(&mut decl_code, &VecDeque::new(), false)?;

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

fn insert_or_refresh_term_dir_quantum(
    term_dir: &TermDir,
    key: PredicateKey,
    term_dirs: &mut TermDirQuantum
) {
    match term_dir.get(&key) {
        Some((ref preds, ref queue)) => {
            let entry = TermDirQuantumEntry::from(preds, queue);
            term_dirs.insert_or_refresh(key, entry);
        }
        None => {
            let entry = TermDirQuantumEntry::from(&Predicate::new(), &VecDeque::new());
            term_dirs.insert_or_refresh(key, entry);
        }
    }
}

#[derive(Debug)]
pub struct ListingCompiler {
    module: Option<Module>,
    user_term_dir: TermDir,
    orig_term_expansion_lens: (usize, usize),
    orig_goal_expansion_lens: (usize, usize),
    initialization_goals: (Vec<QueryTerm>, VecDeque<TopLevel>),
    suppress_warnings: bool,
    listing_src: ListingSource, // a file? a module?
}

fn add_toplevel(
    wam: &mut Machine,
    indices: IndexStore,
    term_dir: TermDir,
) {
    wam.add_batched_code_dir(indices.code_dir);
    wam.add_batched_ops(indices.op_dir);
    wam.add_in_situ_module_dir(indices.module_dir);

    wam.code_repo.term_dir.extend(term_dir.into_iter());
}

#[inline]
fn add_module(
    wam: &mut Machine,
    mut module: Module,
    indices: IndexStore,
    term_dir: TermDir,
) {
    module.code_dir.extend(indices.code_dir);
    module.op_dir.extend(indices.op_dir);
    module.term_dir.extend(term_dir);

    wam.add_in_situ_module_dir(indices.module_dir);
    wam.add_module(module);
}

fn add_non_module_code(
    wam: &mut Machine,
    dynamic_clause_map: DynamicClauseMap,
    code: Code,
    indices: IndexStore,
    term_dir: TermDir,
) -> Result<(), SessionError> {
    wam.check_toplevel_code(&indices)?;

    let mut clause_code_generator = ClauseCodeGenerator::new(code.len(), clause_name!("user"));
    clause_code_generator.generate_clause_code(&dynamic_clause_map, wam)?;

    add_toplevel(wam, indices, term_dir);
    wam.code_repo.code.extend(code);
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
            let mut lib_path = current_dir();

            lib_path.pop();
            lib_path.push("lib");

            let listing_src = ListingSource::from_file_and_path(name, lib_path);

            load_module(
                wam,
                Stream::from(*code),
                suppress_warnings,
                &listing_src,
            )
        }
        None => {
            let err = ExistenceError::ModuleSource(ModuleSource::Library(
                name.clone()
            ));

            Err(SessionError::ExistenceError(err))
        }
    }
}

impl ListingCompiler {
    #[inline]
    pub fn new(
        code_repo: &CodeRepo,
        suppress_warnings: bool,
        listing_src: ListingSource,
    ) -> Self {
        ListingCompiler {
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

    /* Replace calls to self with a localized index cell, not
     * available to the global CodeIndex.  This is done to implement
     * logical update semantics for dynamic database updates.
     */
    fn localize_self_calls(&mut self, key: PredicateKey, code: &mut Code, p: usize, target_p: usize)
    {
        let (name, arity) = key;

        let self_idx = CodeIndex::default();
        set_code_index!(self_idx, IndexPtr::Index(target_p), self.get_module_name());

        walk_code_mut(code, p, |instr|
            match instr {
                Line::Control(ControlInstruction::CallClause(ref mut ct, ..)) => {
                    match ct {
                        ClauseType::Named(ref ct_name, ct_arity, ref mut idx)
                            if ct_name == &name && arity == *ct_arity =>
                        {
                            *idx = self_idx.clone();
                        }
                        ClauseType::Op(ref op_name, ref shared_op_desc, ref mut idx)
                            if op_name == &name && shared_op_desc.arity() == arity =>
                        {
                            *idx = self_idx.clone();
                        }
                        _ => {}
                    }
                }
                _ => {}
            },
        );
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
            let err = ExistenceError::ModuleSource(ModuleSource::File(
                module_name,
            ));

            Err(SessionError::ExistenceError(err))
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
            let err = ExistenceError::ModuleSource(ModuleSource::File(
                module_name
            ));

            Err(SessionError::ExistenceError(err))
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
    ) -> Result<Code, SessionError> {
	let query_terms = mem::replace(&mut self.initialization_goals.0, vec![]);
	let queue = mem::replace(&mut self.initialization_goals.1, VecDeque::new());

	compile_query(query_terms, queue)
	    .map(|(code, _)| code)
	    .map_err(SessionError::from)
    }

    fn set_code_index(
        &mut self,
        wam: &Machine,
        key: PredicateKey,
        in_situ_code: &mut Code,
        code_dir: &mut CodeDir,
        in_situ_code_dir: &InSituCodeDir,
        decl: PredicateCompileQueue,
    ) -> Result<(), SessionError> {
        let p = wam.code_repo.code.len();

        let idx = code_dir
            .entry(key.clone())
            .or_insert(CodeIndex::default());

        Ok(match in_situ_code_dir.get(&key) {
            Some(in_situ_p) => {
                set_code_index!(idx, IndexPtr::Index(p + *in_situ_p), self.get_module_name());
                self.localize_self_calls(key, in_situ_code, *in_situ_p, p + *in_situ_p);
            }
            None => {
                let (decl, queue) = decl;

                let mut cg = CodeGenerator::<DebrayAllocator>::new(false);
                let mut decl_code = cg.compile_predicate(&decl.0)?;

                compile_appendix(&mut decl_code, &queue, false)?;

                let in_situ_p = in_situ_code.len();

                in_situ_code.extend(decl_code.into_iter());

                set_code_index!(idx, IndexPtr::Index(p + in_situ_p), self.get_module_name());
                self.localize_self_calls(key, in_situ_code, in_situ_p, p + in_situ_p);
            }
        })
    }

    fn adapt_in_situ_code(
        &mut self,
        decls: Vec<PredicateCompileQueue>,
        wam: &Machine,
        code_dir: &mut CodeDir,
        module_dir: &mut ModuleDir,
        in_situ_code: &mut Code,
        in_situ_code_dir: &InSituCodeDir,
        in_situ_module_dir: &ModuleStubDir,
    ) -> Result<(), SessionError> {
        for decl in decls {
            let key = decl.0
                .predicate_indicator()
                .ok_or(SessionError::NamelessEntry)?;

            let (name, _arity) = key.clone();
            let module_name = name.owning_module();

            match in_situ_module_dir.get(&module_name) {
                Some(ref module_stub) if name.has_table(&module_stub.atom_tbl) => {
                    let module =
                        module_dir.entry(module_name.clone())
                                  .or_insert_with(|| {
                                      let module_decl = ModuleDecl {
                                          name: module_name.clone(),
                                          exports: vec![]
                                      };

                                      Module::new(
                                          module_decl,
                                          module_stub.atom_tbl.clone(),
                                          self.listing_src.clone(),
                                      )
                                  });

                    self.set_code_index(
                        wam,
                        key,
                        in_situ_code,
                        &mut module.code_dir,
                        &module_stub.in_situ_code_dir,
                        decl,
                    )?;
                }
                _ => {
                    self.set_code_index(
                        wam,
                        key,
                        in_situ_code,
                        code_dir,
                        in_situ_code_dir,
                        decl,
                    )?;
                }
            }
        }

        Ok(())
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
            queue_len += queue.len();

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
        non_counted_bt_preds: &mut IndexSet<PredicateKey>,
    ) -> Result<(), SessionError> {
        match decl {
            Declaration::Dynamic(..) => {
                Ok(())
            }
            Declaration::EndOfFile => {
                Ok(())
            }
            Declaration::Hook(hook, clause, queue) => {
                let key = (hook.name(), hook.arity());
                let (len, queue_len) =
                    self.add_term_dir_terms(hook, &mut wam.code_repo, key.clone(), clause, queue);

                let result = wam
                    .code_repo
                    .compile_hook(hook)
                    .map_err(SessionError::from);

                wam.code_repo.truncate_terms(key, len, queue_len);

                result
            }
            Declaration::Module(module_decl) => {
                if self.module.is_none() {
                    let module_name = module_decl.name.clone();
                    let atom_tbl = TabledData::new(module_name.to_rc());

                    for export in module_decl.exports.iter() {
                        if let ModuleExport::OpDecl(ref op_decl) = export {
                            self.submit_op(wam, indices, op_decl)?;
                        }
                    }

                    let listing_src = self.listing_src.clone();

                    Ok(self.module = Some(Module::new(module_decl, atom_tbl, listing_src)))
                } else {
                    Err(SessionError::from(ParserError::InvalidModuleDecl))
                }
            }
	        Declaration::ModuleInitialization(query_terms, queue) => {
		        self.initialization_goals.0.extend(query_terms.into_iter());
		        self.initialization_goals.1.extend(queue.into_iter());

		        Ok(())
	        }
            Declaration::MultiFile(..) => {
                Ok(())
            }
            Declaration::NonCountedBacktracking(name, arity) => {
                non_counted_bt_preds.insert((name, arity));
                Ok(())
            }
            Declaration::Op(op_decl) => {
                self.submit_op(wam, indices, &op_decl)
            }
            Declaration::SetPrologFlag(dbl_quotes) => {
                wam.machine_st.flags.double_quotes = dbl_quotes;
                Ok(())
            }
            Declaration::UseModule(ModuleSource::Library(name)) => {
                let name = if !wam.indices.modules.contains_key(&name) {
                    load_library(wam, name, true)?
                } else {
                    name
                };

                self.use_module(name, &mut wam.code_repo, flags, &mut wam.indices, indices)
            }
            Declaration::UseModule(ModuleSource::File(filename)) => {
                let mut path_buf = self.listing_src.path();
                path_buf.push(filename.as_str());

                let name = load_module_from_file(wam, path_buf, true)?;
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
            }
            Declaration::UseQualifiedModule(ModuleSource::File(filename), exports) => {
                let mut path_buf = self.listing_src.path();
                path_buf.push(filename.as_str());

                let name = load_module_from_file(wam, path_buf, true)?;

                self.use_qualified_module(
                    name,
                    &mut wam.code_repo,
                    flags,
                    &exports,
                    &mut wam.indices,
                    indices,
                )
            }
        }
    }

    fn setup_multifile_decl(
        &self,
        indicator: MultiFileIndicator,
        worker: &mut TopLevelBatchWorker,
    ) -> Result<(), SessionError> {
        match indicator {
            MultiFileIndicator::LocalScoped(name, arity) => {
                let term_dir  = &worker.term_stream.wam.code_repo.term_dir;
                let key       = (name, arity);
                let term_dirs = &mut worker.term_dirs;

                insert_or_refresh_term_dir_quantum(term_dir, key, term_dirs);
            }
            MultiFileIndicator::ModuleScoped((module_name, key)) => {
                match worker.term_stream.wam.indices.modules.get(&module_name) {
                    Some(ref module) => {
                        let term_dir  = &module.term_dir;
                        let term_dirs = worker.intra_module_term_dirs
                            .entry(module_name)
                            .or_insert(TermDirQuantum::new());

                        insert_or_refresh_term_dir_quantum(term_dir, key, term_dirs);
                    }
                    None => {
                        let err = ExistenceError::ModuleSource(ModuleSource::File(
                            module_name,
                        ));

                        return Err(SessionError::ExistenceError(err));
                    }
                }
            }
        };

        Ok(())
    }

    fn process_and_commit_decl(
        &mut self,
        decl: Declaration,
        worker: &mut TopLevelBatchWorker,
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
            &Declaration::MultiFile(ref indicator) => {
                self.setup_multifile_decl(indicator.clone(), worker)?;
            }
            &Declaration::UseModule(_) | &Declaration::UseQualifiedModule(..) => {
                update_expansion_lengths = true
            }
            _ => {}
        };

        let result = self.process_decl(
            decl,
            &mut worker.term_stream.wam,
            indices,
            flags,
            &mut worker.non_counted_bt_preds,
        );

        if update_expansion_lengths {
            worker.term_stream.update_expansion_lens();
        }

        result
    }

    pub(crate) fn gather_items(
        &mut self,
        wam: &mut Machine,
        src: &mut ParsingStream<Stream>,
        indices: &mut IndexStore,
    ) -> Result<GatherResult, SessionError> {
        let flags = wam.machine_flags();
        let atom_tbl = indices.atom_tbl.clone();
        let mut worker = TopLevelBatchWorker::new(src, atom_tbl.clone(), flags, wam);

        let mut toplevel_results = vec![];
        let mut toplevel_indices = default_index_store!(atom_tbl.clone());

        let mut top_level_term_dirs = TermDirQuantum::new();

        while let Some(decl) = worker.consume(indices)? {
            if decl.is_module_decl() {
                toplevel_indices.copy_and_swap(indices);
                mem::swap(&mut worker.results, &mut toplevel_results);
                worker.in_module = true;

                self.process_and_commit_decl(decl, &mut worker, indices, flags)?;

                if let Some(ref module) = &self.module {
                    worker.term_stream.set_atom_tbl(module.atom_tbl.clone());

                    top_level_term_dirs = mem::replace(
                        &mut worker.term_dirs,
                        TermDirQuantum::new(),
                    );
                }
            } else if decl.is_end_of_file() {
                break;
            } else {
                self.process_and_commit_decl(decl, &mut worker, indices, flags)?;
            }
        }

        let addition_results = worker.term_stream.rollback_expansion_code()?;

        let module_term_dirs = if self.module.is_some() {
            worker.term_dirs
        } else {
            top_level_term_dirs = worker.term_dirs;
            TermDirQuantum::new()
        };

        Ok(GatherResult {
            worker_results: worker.results,
            dynamic_clause_map: worker.dynamic_clause_map,
            toplevel_results,
            toplevel_indices,
            addition_results,
            top_level_terms: worker.term_stream.top_level_terms(),
            top_level_term_dirs,
            module_term_dirs,
            in_situ_code_dir: worker.term_stream.wam.indices.take_in_situ_code_dir(),
            in_situ_code: worker.term_stream.wam.code_repo.take_in_situ_code(),
            in_situ_module_dir: worker.term_stream.wam.indices.take_in_situ_module_dir(),
        })
    }

    fn drop_expansions(&self, code_repo: &mut CodeRepo) {
        let (te_len, te_queue_len) = self.orig_term_expansion_lens;
        let (ge_len, ge_queue_len) = self.orig_goal_expansion_lens;

        code_repo.truncate_terms((clause_name!("term_expansion"), 2), te_len, te_queue_len);
        code_repo.truncate_terms((clause_name!("goal_expansion"), 2), ge_len, ge_queue_len);

        discard_result!(code_repo.compile_hook(CompileTimeHook::UserGoalExpansion));
        discard_result!(code_repo.compile_hook(CompileTimeHook::UserTermExpansion));
    }

    fn print_error(&self, e: &SessionError) {
        if let &SessionError::ParserError(ref e) = e {
            if let Some((line_num, _col_num)) = e.line_and_col_num() {
                println!("{}:{}: {}", self.listing_src.name(), line_num, e.as_str());
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
        let mut decls = module.take_local_expansions();

        if !decls.is_empty() {
            append_trivial_goal(&clause_name!("term_expansion"), &mut decls[0].0);
            append_trivial_goal(&clause_name!("goal_expansion"), &mut decls[1].0);

            results.worker_results.extend(decls.into_iter());
        }
    }

    let top_level_term_dir = results.top_level_term_dirs.consolidate();
    let module_term_dir = results.module_term_dirs.consolidate();

    let mut code = results.in_situ_code;

    let in_situ_code_dir = results.in_situ_code_dir;
    let in_situ_module_dir = results.in_situ_module_dir;

    compiler.adapt_in_situ_code(
        results.worker_results,
        wam,
        &mut indices.code_dir,
        &mut indices.module_dir,
        &mut code,
        &in_situ_code_dir,
        &in_situ_module_dir,
    )?;

    compiler.adapt_in_situ_code(
        results.toplevel_results,
        wam,
        &mut results.toplevel_indices.code_dir,
        &mut indices.module_dir,
        &mut code,
        &in_situ_code_dir,
        &in_situ_module_dir,
    )?;

    if let Some(ref mut module) = &mut compiler.module {
        if !module.is_impromptu_module {
            module.user_term_expansions = results.addition_results.take_term_expansions();
            module.user_goal_expansions = results.addition_results.take_goal_expansions();
        }
    }

    wam.code_repo.compile_hook(CompileTimeHook::UserTermExpansion)?;
    wam.code_repo.compile_hook(CompileTimeHook::UserGoalExpansion)?;

    if let Some(mut module) = compiler.module.take() {
        if module.is_impromptu_module {
            module.module_decl.exports = indices.code_dir.keys().cloned()
                .filter(|(name, _)| name.owning_module().as_str() != "builtins")
                .map(ModuleExport::PredicateKey)
                .collect();

            module.module_decl.exports.extend(
                indices.op_dir.iter()
                    .map(|((name, _), OpDirValue (shared_op_desc, _))|
                        ModuleExport::OpDecl(OpDecl(
                            shared_op_desc.prec(),
                            shared_op_desc.assoc(),
                            name.clone(),
                        ))
                    )
            );
        }

        let mut clause_code_generator =
            ClauseCodeGenerator::new(code.len(), module.module_decl.name.clone());

        wam.check_toplevel_code(&results.toplevel_indices)?;
        clause_code_generator.generate_clause_code(&results.dynamic_clause_map, wam)?;

        if let Some(ref module) = wam.indices.modules.swap_remove(&module.module_decl.name) {
            wam.indices.remove_module(clause_name!("user"), module);
        }

        if module.is_impromptu_module {
            add_module(wam, module, indices, module_term_dir);

            let module = wam.indices.take_module(compiler.listing_src.name()).unwrap();

            wam.indices.use_module(&mut wam.code_repo, wam.machine_st.flags, &module)?;
            wam.indices.insert_module(module);
        } else {
            add_module(wam, module, indices, module_term_dir);
        }

        add_toplevel(wam, results.toplevel_indices, top_level_term_dir);
        wam.code_repo.code.extend(code.into_iter());

        clause_code_generator.add_clause_code(wam, results.dynamic_clause_map);
    } else {
        add_non_module_code(
            wam,
            results.dynamic_clause_map,
            code,
            indices,
            top_level_term_dir,
        )?;
    }

    let init_goal_code = compiler.generate_init_goal_code()?;

    if init_goal_code.len() > 0 {
	if !wam.run_init_code(init_goal_code) {
            println!("Warning: initialization goal for {} failed",
                     compiler.listing_src.name());
        }
    }

    if !compiler.suppress_warnings {
        issue_singleton_warnings(
            compiler.listing_src.name(),
            results.top_level_terms,
        );
    }

    Ok(())
}

fn compile_work(
    compiler: &mut ListingCompiler,
    wam: &mut Machine,
    src: Stream,
    mut indices: IndexStore,
) -> EvalSession {
    let mut stream = try_eval_session!(parsing_stream(src));
    let src = &mut stream;
    let results = try_eval_session!(compiler.gather_items(wam, src, &mut indices));

    try_eval_session!(compile_work_impl(compiler, wam, indices, results));

    EvalSession::EntrySuccess
}

/* This is a truncated version of compile_user_module, used for
compiling code composing special forms, ie. the code that calls
M:verify_attributes on attributed variables. */
pub fn compile_special_form(
    wam: &mut Machine,
    src: Stream,
    listing_src: ListingSource,
) -> Result<usize, SessionError> {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    setup_indices(wam, clause_name!("builtins"), &mut indices)?;

    let mut src = parsing_stream(src)?;
    let mut compiler = ListingCompiler::new(&wam.code_repo, true, listing_src);
    let mut results = compiler.gather_items(wam, &mut src, &mut indices)?;

    compiler.adapt_in_situ_code(
        results.worker_results,
        wam,
        &mut indices.code_dir,
        &mut indices.module_dir,
        &mut results.in_situ_code,
        &results.in_situ_code_dir,
        &results.in_situ_module_dir,
    )?;

    let p = wam.code_repo.code.len();
    let top_level_term_dir = results.top_level_term_dirs.consolidate();

    add_toplevel(wam, indices, top_level_term_dir);

    wam.code_repo.code.extend(results.in_situ_code.into_iter());

    Ok(p)
}

#[inline]
pub fn compile_listing(
    wam: &mut Machine,
    src: Stream,
    indices: IndexStore,
    suppress_warnings: bool,
    listing_src: ListingSource,
) -> EvalSession {
    let mut compiler = ListingCompiler::new(&wam.code_repo, suppress_warnings, listing_src);

    match compile_work(&mut compiler, wam, src, indices) {
        EvalSession::Error(e) => {
            compiler.drop_expansions(&mut wam.code_repo);
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
    if let Some(module) = wam.indices.take_module(module.clone()) {
        let flags = wam.machine_flags();
        let result = indices.use_module(&mut wam.code_repo, flags, &module);

        wam.indices.insert_module(module);
        result
    } else {
        let err = ExistenceError::ModuleSource(ModuleSource::Library(
            module
        ));

        Err(SessionError::ExistenceError(err))
    }
}

pub fn compile_user_module(
    wam: &mut Machine,
    src: Stream,
    suppress_warnings: bool,
    listing_src: ListingSource,
) -> EvalSession {
    let mut indices = default_index_store!(wam.indices.atom_tbl.clone());
    try_eval_session!(setup_indices(wam, clause_name!("builtins"), &mut indices));
    compile_listing(wam, src, indices, suppress_warnings, listing_src)
}
