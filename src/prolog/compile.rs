use prolog::ast::*;
use prolog::debray_allocator::*;
use prolog::codegen::*;
use prolog::machine::*;
use prolog::toplevel::*;

use std::collections::{HashMap, VecDeque};
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

pub fn parse_code(wam: &mut Machine, buffer: &str) -> Result<TopLevelPacket, ParserError>
{
    let atom_tbl = wam.atom_tbl();
    let index = MachineCodeIndices {
        code_dir: &mut wam.code_dir,
        op_dir: &mut wam.op_dir,
    };

    let mut worker = TopLevelWorker::new(buffer.as_bytes(), atom_tbl, index);
    worker.parse_code()
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
            match compile_query(terms, queue) {
                Ok((mut code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        TopLevelPacket::Decl(tl, queue) =>
            compile_decl(wam, tl, queue)
    }
}

pub struct ListingCompiler<'a> {
    wam: &'a mut Machine,
    module: Option<Module>
}

impl<'a> ListingCompiler<'a> {
    pub fn new(wam: &'a mut Machine) -> Self {
        ListingCompiler { wam, module: None }
    }

    fn get_module_name(&self) -> ClauseName {
        self.module.as_ref()
            .map(|module| module.module_decl.name.clone())
            .unwrap_or(ClauseName::BuiltIn("user"))
    }

    fn gen_code(&mut self, decls: Vec<(Predicate, VecDeque<TopLevel>)>, code_dir: &mut CodeDir)
                -> Result<Code, SessionError>
    {
        let mut code = vec![];

        for (decl, queue) in decls {
            let (name, arity) = decl.0.first().and_then(|cl| {
                let arity = cl.arity();
                cl.name().map(|name| (name, arity))
            }).ok_or(SessionError::NamelessEntry)?;

            let p = code.len() + self.wam.code_size();
            let mut decl_code = compile_relation(&TopLevel::Predicate(decl))?;

            compile_appendix(&mut decl_code, Vec::from(queue))?;

            let idx = code_dir.entry((name, arity)).or_insert(CodeIndex::default());
            set_code_index!(idx, IndexPtr::Index(p), self.get_module_name());

            code.extend(decl_code.into_iter());
        }

        Ok(code)
    }

    fn add_code(self, code: Code, indices: MachineCodeIndices) {
        let code_dir = mem::replace(indices.code_dir, HashMap::new());
        let op_dir   = mem::replace(indices.op_dir, HashMap::new());

        if let Some(mut module) = self.module {
            module.code_dir.extend(as_module_code_dir(code_dir));
            module.op_dir.extend(op_dir.into_iter());

            self.wam.add_module(module, code);
        } else {
            self.wam.add_batched_code(code, code_dir);
            self.wam.add_batched_ops(op_dir);
        }
    }

}

fn use_module(module: &mut Option<Module>, submodule: &Module, indices: &mut MachineCodeIndices)
{
    indices.use_module(submodule);

    if let &mut Some(ref mut module) = module {
        module.use_module(submodule);
    }
}

fn use_qualified_module(module: &mut Option<Module>, submodule: &Module, exports: &Vec<PredicateKey>,
                        indices: &mut MachineCodeIndices)
{
    indices.use_qualified_module(submodule, exports);

    if let &mut Some(ref mut module) = module {
        module.use_qualified_module(submodule, exports);
    }
}

pub
fn compile_listing(wam: &mut Machine, src_str: &str, mut indices: MachineCodeIndices) -> EvalSession
{
    let mut worker   = TopLevelBatchWorker::new(src_str.as_bytes(), wam.atom_tbl());
    let mut compiler = ListingCompiler::new(wam);

    while let Some(decl) = try_eval_session!(worker.consume(&mut indices)) {
        match decl {
            Declaration::Op(op_decl) =>
                try_eval_session!(op_decl.submit(compiler.get_module_name(), &mut indices.op_dir)),
            Declaration::UseModule(name) =>
                if let Some(ref submodule) = compiler.wam.get_module(name.clone()) {
                    use_module(&mut compiler.module, submodule, &mut indices);
                } else {
                    return EvalSession::from(SessionError::ModuleNotFound);
                },
            Declaration::UseQualifiedModule(name, exports) =>
                if let Some(ref submodule) = compiler.wam.get_module(name.clone()) {
                    use_qualified_module(&mut compiler.module, submodule, &exports, &mut indices);
                } else {
                    return EvalSession::from(SessionError::ModuleNotFound);
                },
            Declaration::Module(module_decl) =>
                if compiler.module.is_none() {
                    worker.source_mod = module_decl.name.clone();
                    compiler.module = Some(Module::new(module_decl));
                } else {
                    return EvalSession::from(ParserError::InvalidModuleDecl);
                }
        }
    }

    let code = try_eval_session!(compiler.gen_code(worker.results, &mut indices.code_dir));
    compiler.add_code(code, indices);

    EvalSession::EntrySuccess
}

pub fn compile_user_module(wam: &mut Machine, src_str: &str) -> EvalSession {
    let mut indices = machine_code_indices!(&mut CodeDir::new(), &mut default_op_dir());

    if let Some(ref builtins) = wam.modules.get(&clause_name!("builtins")) {
        indices.use_module(builtins);
    } else {
        return EvalSession::from(SessionError::ModuleNotFound);
    }

    compile_listing(wam, src_str, indices)
}
