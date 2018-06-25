use prolog::ast::*;
use prolog::debray_allocator::*;
use prolog::codegen::*;
use prolog::machine::*;
use prolog::toplevel::*;

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

pub fn parse_code(wam: &mut Machine, buffer: &str) -> Result<TopLevelPacket, ParserError>
{
    let atom_tbl = wam.atom_tbl();
    let index = MachineCodeIndex {
        code_dir: &mut wam.code_dir,
        op_dir: &mut wam.op_dir,
        modules: &wam.modules
    };

    let mut worker = TopLevelWorker::new(buffer.as_bytes(), atom_tbl, index);
    worker.parse_code(clause_name!("user"))
}

// throw errors if declaration or query found.
fn compile_relation(tl: &TopLevel) -> Result<Code, ParserError>
{
    let mut cg = CodeGenerator::<DebrayAllocator>::new();

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

fn compile_appendix(code: &mut Code, queue: Vec<TopLevel>) -> Result<(), ParserError>
{
    for tl in queue.iter() {
        set_first_index(code);
        code.append(&mut compile_relation(tl)?);
    }

    Ok(())
}

fn compile_query(terms: Vec<QueryTerm>, queue: Vec<TopLevel>) -> Result<(Code, AllocVarDict), ParserError>
{
    let mut cg = CodeGenerator::<DebrayAllocator>::new();
    let mut code = try!(cg.compile_query(&terms));

    compile_appendix(&mut code, queue)?;

    Ok((code, cg.take_vars()))
}

fn compile_decl(wam: &mut Machine, tl: TopLevel, queue: Vec<TopLevel>) -> EvalSession
{
    match tl {
        TopLevel::Declaration(Declaration::Op(op_decl)) => {
            try_eval_session!(op_decl.submit(clause_name!("user"), &mut wam.op_dir));
            EvalSession::EntrySuccess
        },
        TopLevel::Declaration(Declaration::UseModule(name)) =>
            wam.use_module_in_toplevel(name),
        TopLevel::Declaration(Declaration::UseQualifiedModule(name, exports)) =>
            wam.use_qualified_module_in_toplevel(name, exports),
        TopLevel::Declaration(_) =>
            EvalSession::from(ParserError::InvalidModuleDecl),
        _ => {
            let name = try_eval_session!(if let Some(name) = tl.name() {
                Ok(name)
            } else {
                Err(SessionError::NamelessEntry)
            });

            let mut code = try_eval_session!(compile_relation(&tl));
            try_eval_session!(compile_appendix(&mut code, queue));

            if !code.is_empty() {
                wam.add_user_code(name, tl.arity(), code, tl.as_predicate().ok().unwrap())
            } else {
                EvalSession::from(SessionError::ImpermissibleEntry(String::from("no code generated.")))
            }
        }
    }
}

pub fn compile_packet(wam: &mut Machine, tl: TopLevelPacket) -> EvalSession
{
    match tl {
        TopLevelPacket::Query(terms, queue) =>
            match compile_query(terms, queue) { //, &mut wam.code_dir) { //wam.code_size(), &mut wam.code_dir) {
                Ok((mut code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        TopLevelPacket::Decl(tl, queue) =>
            compile_decl(wam, tl, queue)
    }
}

pub fn compile_listing(wam: &mut Machine, src_str: &str) -> EvalSession
{
    fn get_module_name(module: &Option<Module>) -> ClauseName {
        match module {
            &Some(ref module) => module.module_decl.name.clone(),
            _ => ClauseName::BuiltIn("user")
        }
    }

    let mut module: Option<Module> = None;

    let mut code_dir = CodeDir::new();
    let mut op_dir   = default_op_dir();

    let mut code = Vec::new();

    let tls = {
        let indices = machine_code_index!(&mut code_dir, &mut op_dir, &wam.modules);
        let mut worker = TopLevelWorker::new(src_str.as_bytes(), wam.atom_tbl(), indices);

        try_eval_session!(worker.parse_batch(clause_name!("user")))
    };

    for tl in tls {
        match tl {
            TopLevelPacket::Query(..) =>
                return EvalSession::from(ParserError::ExpectedRel),
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::Module(module_decl)), _) =>
                if module.is_none() {
                    module = Some(Module::new(module_decl));
                } else {
                    return EvalSession::from(ParserError::InvalidModuleDecl);
                },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::UseModule(name)), _) => {
                if let Some(ref submodule) = wam.get_module(name.clone()) {
                    if let Some(ref mut module) = module {
                        let mut code_index = machine_code_index!(&mut code_dir, &mut op_dir, &wam.modules);

                        module.use_module(submodule);
                        code_index.use_module(submodule);

                        continue;
                    }
                } else {
                    return EvalSession::from(SessionError::ModuleNotFound);
                }

                wam.use_module_in_toplevel(name);
            },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::UseQualifiedModule(name, exports)), _)
                =>
            {
                if let Some(ref submodule) = wam.get_module(name.clone()) {
                    if let Some(ref mut module) = module {
                        let mut code_index = machine_code_index!(&mut code_dir, &mut op_dir, &wam.modules);

                        module.use_qualified_module(submodule, &exports);
                        code_index.use_qualified_module(submodule, &exports);

                        continue;
                    }
                } else {
                    return EvalSession::from(SessionError::ModuleNotFound);
                }

                wam.use_qualified_module_in_toplevel(name, exports);
            },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::Op(..)), _) => {},
            TopLevelPacket::Decl(decl, queue) => {
                let p = code.len() + wam.code_size();
                let mut decl_code = try_eval_session!(compile_relation(&decl));

                try_eval_session!(compile_appendix(&mut decl_code, queue));

                let name = try_eval_session!(if let Some(name) = decl.name() {
                    Ok(name)
                } else {
                    Err(SessionError::NamelessEntry)
                });

                if let Some(ref mut idx) = code_dir.get_mut(&(name, decl.arity())) {
                    set_code_index!(idx, IndexPtr::Index(p), get_module_name(&module));
                }

                code.extend(decl_code.into_iter());
            }
        }
    }

    if let Some(mut module) = module {
        module.code_dir.extend(as_module_code_dir(code_dir));
        module.op_dir.extend(op_dir.into_iter());

        wam.add_module(module, code);
    } else {
        wam.add_batched_code(code, code_dir);
        wam.add_batched_ops(op_dir);
    }

    EvalSession::EntrySuccess
}
