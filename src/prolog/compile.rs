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

fn package_term(wam: &mut Machine, term: Term) -> Result<TopLevelPacket, ParserError> {
    let mut code_dir = wam.take_code_dir();
    let packet = consume_term(&mut code_dir, term, &mut wam.indices)?;    
    wam.swap_code_dir(&mut code_dir); 
    Ok(packet)
}

pub fn compile_term(wam: &mut Machine, term: Term) -> EvalSession
{
    let packet = try_eval_session!(package_term(wam, term));

    match packet {
        TopLevelPacket::Query(terms, queue) =>
            match compile_query(terms, queue, wam.machine_flags()) {
                Ok((mut code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        TopLevelPacket::Decl(TopLevel::Declaration(decl), _) => {
            let mut compiler = ListingCompiler::new();
            let mut indices = default_index_store!(wam.indices.atom_tbl.clone());

            try_eval_session!(compiler.process_decl(decl, wam, &mut indices));
            try_eval_session!(compiler.add_code(wam, vec![], indices));

            EvalSession::EntrySuccess
        },
        _ => EvalSession::from(SessionError::UserPrompt)
    }
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

    fn use_module(&mut self, submodule: Module, wam: &mut Machine, indices: &mut IndexStore)
                  -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        indices.use_module(&submodule)?;

        if let &mut Some(ref mut module) = &mut self.module {
            module.remove_module(mod_name, &submodule);
            module.use_module(&submodule)?;
        } else {
            wam.remove_module(&submodule);
        }

        Ok(wam.insert_module(submodule))
    }

    fn use_qualified_module(&mut self, submodule: Module, wam: &mut Machine,
                            exports: &Vec<PredicateKey>, indices: &mut IndexStore)
                            -> Result<(), SessionError>
    {
        let mod_name = self.get_module_name();

        indices.use_qualified_module(&submodule, exports)?;

        if let &mut Some(ref mut module) = &mut self.module {
            module.remove_module(mod_name, &submodule);
            module.use_qualified_module(&submodule, exports)?;
        } else {
            wam.remove_module(&submodule);
        }

        Ok(wam.insert_module(submodule))
    }

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

    fn process_decl(&mut self, decl: Declaration, wam: &mut Machine, indices: &mut IndexStore)
                    -> Result<(), SessionError>
    {
        match decl {
            Declaration::Hook(CompileTimeHook::TermExpansion, clause) =>
                Ok(wam.add_term_expansion_clause(clause)?),
            Declaration::NonCountedBacktracking(name, arity) =>
                Ok(self.add_non_counted_bt_flag(name, arity)),
            Declaration::Op(op_decl) =>
                op_decl.submit(self.get_module_name(), &mut indices.op_dir),
            Declaration::UseModule(name) =>
                if let Some(submodule) = wam.take_module(name) {
                    self.use_module(submodule, wam, indices)
                } else {
                    Err(SessionError::ModuleNotFound)
                },
            Declaration::UseQualifiedModule(name, exports) =>
                if let Some(submodule) = wam.take_module(name) {
                    self.use_qualified_module(submodule, wam, &exports, indices)
                } else {
                    Err(SessionError::ModuleNotFound)
                },
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
}

pub
fn compile_listing<R: Read>(wam: &mut Machine, src: R, mut indices: IndexStore,
                            mut toplevel_indices: IndexStore)
                            -> EvalSession
{
    let code_dir = wam.take_code_dir();
    let mut worker = TopLevelBatchWorker::new(src, wam.indices.atom_tbl.clone(),
                                              wam.machine_flags(),
                                              code_dir);
    
    let mut compiler = ListingCompiler::new();
    let mut toplevel_results = vec![];

    while let Some(decl) = try_eval_session!(worker.consume(wam, &mut indices)) {
        if decl.is_module_decl() {
            toplevel_indices.copy_and_swap(&mut indices);
            mem::swap(&mut worker.results, &mut toplevel_results);
            worker.in_module = true;

            try_eval_session!(compiler.process_decl(decl, wam, &mut indices));

            if let &Some(ref module) = &compiler.module {
                worker.term_stream.set_atom_tbl(module.atom_tbl.clone());
            }
        } else {
            try_eval_session!(compiler.process_decl(decl, wam, &mut indices));
        }
    }

    wam.swap_code_dir(&mut worker.static_code_dir);
    
    let module_code = try_eval_session!(compiler.generate_code(worker.results, wam,
                                                               &mut indices.code_dir));
    let toplvl_code = try_eval_session!(compiler.generate_code(toplevel_results, wam,
                                                               &mut toplevel_indices.code_dir));

    try_eval_session!(compiler.add_code(wam, module_code, indices));
    try_eval_session!(compiler.add_code(wam, toplvl_code, toplevel_indices));

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
    let atom_tbl = wam.indices.atom_tbl.clone();    
    let mut indices = default_index_store!(atom_tbl.clone());
    
    try_eval_session!(setup_indices(&wam, &mut indices));
    
    compile_listing(wam, src, indices, default_index_store!(atom_tbl))
}
