use prolog::ast::*;
use prolog::builtins::*;
use prolog::codegen::*;
use prolog::debray_allocator::*;
use prolog::heap_print::*;
use prolog::machine::*;
use prolog::parser::toplevel::*;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;

impl fmt::Display for ClauseName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl fmt::Display for FactInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FactInstruction::GetConstant(lvl, ref constant, ref r) =>
                write!(f, "get_constant {}, {}{}", constant, lvl, r.reg_num()),
            &FactInstruction::GetList(lvl, ref r) =>
                write!(f, "get_list {}{}", lvl, r.reg_num()),
            &FactInstruction::GetStructure(ref ct, ref arity, ref r) =>
                write!(f, "get_structure {}/{}, {}", ct.name(), arity, r),
            &FactInstruction::GetValue(ref x, ref a) =>
                write!(f, "get_value {}, A{}", x, a),
            &FactInstruction::GetVariable(ref x, ref a) =>
                write!(f, "fact:get_variable {}, A{}", x, a),
            &FactInstruction::UnifyConstant(ref constant) =>
                write!(f, "unify_constant {}", constant),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable {}", r),
            &FactInstruction::UnifyLocalValue(ref r) =>
                write!(f, "unify_local_value {}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value {}", r),
            &FactInstruction::UnifyVoid(n) =>
                write!(f, "unify_void {}", n)
        }
    }
}

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &QueryInstruction::GetVariable(ref x, ref a) =>
                write!(f, "query:get_variable {}, A{}", x, a),
            &QueryInstruction::PutConstant(lvl, ref constant, ref r) =>
                write!(f, "put_constant {}, {}{}", constant, lvl, r.reg_num()),
            &QueryInstruction::PutList(lvl, ref r) =>
                write!(f, "put_list {}{}", lvl, r.reg_num()),
            &QueryInstruction::PutStructure(ref ct, ref arity, ref r) =>
                write!(f, "put_structure {}/{}, {}", ct.name(), arity, r),
            &QueryInstruction::PutUnsafeValue(y, a) =>
                write!(f, "put_unsafe_value Y{}, A{}", y, a),
            &QueryInstruction::PutValue(ref x, ref a) =>
                write!(f, "put_value {}, A{}", x, a),
            &QueryInstruction::PutVariable(ref x, ref a) =>
                write!(f, "put_variable {}, A{}", x, a),
            &QueryInstruction::SetConstant(ref constant) =>
                write!(f, "set_constant {}", constant),
            &QueryInstruction::SetLocalValue(ref r) =>
                write!(f, "set_local_value {}", r),
            &QueryInstruction::SetVariable(ref r) =>
                write!(f, "set_variable {}", r),
            &QueryInstruction::SetValue(ref r) =>
                write!(f, "set_value {}", r),
            &QueryInstruction::SetVoid(n) =>
                write!(f, "set_void {}", n)
        }
    }
}

impl fmt::Display for CompareNumberQT {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CompareNumberQT::GreaterThan => write!(f, ">"),
            &CompareNumberQT::GreaterThanOrEqual => write!(f, ">="),
            &CompareNumberQT::LessThan => write!(f, "<"),
            &CompareNumberQT::LessThanOrEqual => write!(f, "<="),
            &CompareNumberQT::NotEqual => write!(f, "=\\="),
            &CompareNumberQT::Equal => write!(f, "=:="),
        }
    }
}

impl fmt::Display for CompareTermQT {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CompareTermQT::GreaterThan => write!(f, "@>"),
            &CompareTermQT::GreaterThanOrEqual => write!(f, "@>="),
            &CompareTermQT::LessThan => write!(f, "@<"),
            &CompareTermQT::LessThanOrEqual => write!(f, "@<="),
            &CompareTermQT::NotEqual => write!(f, "\\=@="),
            &CompareTermQT::Equal => write!(f, "=@="),
        }
    }
}


impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::CallClause(ref ct, arity, pvs, true) =>
                write!(f, "execute {}/{}, {}", ct.name(), arity, pvs),
            &ControlInstruction::CallClause(ref ct, arity, pvs, false) =>
                write!(f, "call {}/{}, {}", ct.name(), arity, pvs),
            &ControlInstruction::CheckCpExecute =>
                write!(f, "check_cp_execute"),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
            &ControlInstruction::GetCleanerCall =>
                write!(f, "get_cleaner_call"),
            &ControlInstruction::Goto(p, arity, false) =>
                write!(f, "goto_call {}/{}", p, arity),
            &ControlInstruction::Goto(p, arity, true) =>
                write!(f, "goto_execute {}/{}", p, arity),
            &ControlInstruction::IsClause(false, r, ref at) =>
                write!(f, "is_call {}, {}", r, at),
            &ControlInstruction::IsClause(true, r, ref at) =>
                write!(f, "is_execute {}, {}", r, at),
            &ControlInstruction::DynamicIs =>
                write!(f, "call_is"),
            &ControlInstruction::JmpBy(arity, offset, pvs, false) =>
                write!(f, "jmp_by_call {}/{}, {}", offset, arity, pvs),
            &ControlInstruction::JmpBy(arity, offset, pvs, true) =>
                write!(f, "jmp_by_execute {}/{}, {}", offset, arity, pvs),
            &ControlInstruction::Proceed =>
                write!(f, "proceed"),
        }
    }
}

impl fmt::Display for IndexedChoiceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexedChoiceInstruction::Try(offset) =>
                write!(f, "try {}", offset),
            &IndexedChoiceInstruction::Retry(offset) =>
                write!(f, "retry {}", offset),
            &IndexedChoiceInstruction::Trust(offset) =>
                write!(f, "trust {}", offset)
        }
    }
}

impl fmt::Display for BuiltInInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &BuiltInInstruction::CleanUpBlock =>
                write!(f, "clean_up_block"),
            &BuiltInInstruction::DefaultSetCutPoint(r) =>
                write!(f, "default_set_cp {}", r),
            &BuiltInInstruction::DefaultRetryMeElse(o) =>
                write!(f, "default_retry_me_else {}", o),
            &BuiltInInstruction::DefaultTrustMe =>
                write!(f, "default_trust_me"),
            &BuiltInInstruction::InstallInferenceCounter(r1, r2, r3) =>
                write!(f, "install_inference_counter {}, {}, {}", r1, r2, r3),
            &BuiltInInstruction::EraseBall =>
                write!(f, "erase_ball"),
            &BuiltInInstruction::Fail =>
                write!(f, "false"),
            &BuiltInInstruction::GetArgCall =>
                write!(f, "get_arg_call X1, X2, X3"),
            &BuiltInInstruction::GetArgExecute =>
                write!(f, "get_arg_execute X1, X2, X3"),
            &BuiltInInstruction::GetBall =>
                write!(f, "get_ball X1"),
            &BuiltInInstruction::GetCurrentBlock =>
                write!(f, "get_current_block X1"),
            &BuiltInInstruction::GetCutPoint(r) =>
                write!(f, "get_cp {}", r),
            &BuiltInInstruction::InferenceLevel(r1, r2) =>
                write!(f, "inference_level {}, {}", r1, r2),
            &BuiltInInstruction::InstallCleaner =>
                write!(f, "install_cleaner"),
            &BuiltInInstruction::InstallNewBlock =>
                write!(f, "install_new_block"),
            &BuiltInInstruction::InternalCallN =>
                write!(f, "internal_call_N"),
            &BuiltInInstruction::ResetBlock =>
                write!(f, "reset_block"),
            &BuiltInInstruction::RestoreCutPolicy =>
                write!(f, "restore_cut_point"),
            &BuiltInInstruction::SetBall =>
                write!(f, "set_ball"),
            &BuiltInInstruction::SetCutPoint(r) =>
                write!(f, "set_cp {}", r),
            &BuiltInInstruction::Succeed =>
                write!(f, "true"),
            &BuiltInInstruction::UnwindStack =>
                write!(f, "unwind_stack"),
            &BuiltInInstruction::Unify =>
                write!(f, "unify"),
            &BuiltInInstruction::IsAtom(r) =>
                write!(f, "is_atom {}", r),
            &BuiltInInstruction::IsAtomic(r) =>
                write!(f, "is_atomic {}", r),
            &BuiltInInstruction::IsCompound(r) =>
                write!(f, "is_compound {}", r),
            &BuiltInInstruction::IsFloat(r) =>
                write!(f, "is_float {}", r),
            &BuiltInInstruction::IsRational(r) =>
                write!(f, "is_rational {}", r),
            &BuiltInInstruction::IsNonVar(r) =>
                write!(f, "is_non_var {}", r),
            &BuiltInInstruction::IsString(r) =>
                write!(f, "is_string {}", r),
            &BuiltInInstruction::IsInteger(r) =>
                write!(f, "is_integer {}", r),
            &BuiltInInstruction::IsVar(r) =>
                write!(f, "is_var {}", r),
            &BuiltInInstruction::CompareNumber(cmp, ref at_1, ref at_2) =>
                write!(f, "number_test {}, {}, {} ", cmp, at_1, at_2),
            &BuiltInInstruction::DynamicCompareNumber(cmp) =>
                write!(f, "dynamic_number_test {}", cmp),
            &BuiltInInstruction::RemoveCallPolicyCheck =>
                write!(f, "remove_call_policy_check"),
            &BuiltInInstruction::RemoveInferenceCounter(r1, r2) =>
                write!(f, "remove_inference_counter {}, {}", r1, r2)
        }
    }
}

impl fmt::Display for ChoiceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ChoiceInstruction::TryMeElse(offset) =>
                write!(f, "try_me_else {}", offset),
            &ChoiceInstruction::RetryMeElse(offset) =>
                write!(f, "retry_me_else {}", offset),
            &ChoiceInstruction::TrustMe =>
                write!(f, "trust_me")
        }
    }
}

impl fmt::Display for IndexingInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexingInstruction::SwitchOnTerm(v, c, l, s) =>
                write!(f, "switch_on_term {}, {}, {}, {}", v, c, l, s),
            &IndexingInstruction::SwitchOnConstant(num_cs, _) =>
                write!(f, "switch_on_constant {}", num_cs),
            &IndexingInstruction::SwitchOnStructure(num_ss, _) =>
                write!(f, "switch_on_structure {}", num_ss)
        }
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &EvalError::ModuleNotFound => write!(f, "module not found."),
            &EvalError::ModuleDoesNotContainExport => write!(f, "module does not contain claimed export."),
            &EvalError::QueryFailure => write!(f, "false."),
            &EvalError::QueryFailureWithException(ref e) => write!(f, "{}", error_string(e)),
            &EvalError::ImpermissibleEntry(ref msg) => write!(f, "cannot overwrite builtin {}.", msg),
            &EvalError::OpIsInfixAndPostFix =>
                write!(f, "cannot define an op to be both postfix and infix."),
            &EvalError::NamelessEntry => write!(f, "the predicate head is not an atom or clause."),
            &EvalError::ParserError(ref e) => write!(f, "{:?}", e)
        }
    }
}

impl fmt::Display for ArithmeticTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ArithmeticTerm::Reg(r) => write!(f, "{}", r),
            &ArithmeticTerm::Interm(i) => write!(f, "@{}", i),
            &ArithmeticTerm::Number(ref n) => write!(f, "{}", n),
        }
    }
}

impl fmt::Display for ArithmeticInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ArithmeticInstruction::Add(ref a1, ref a2, ref t) =>
                write!(f, "add {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Sub(ref a1, ref a2, ref t) =>
                write!(f, "sub {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Mul(ref a1, ref a2, ref t) =>
                write!(f, "mul {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Div(ref a1, ref a2, ref t) =>
                write!(f, "div {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::IDiv(ref a1, ref a2, ref t) =>
                write!(f, "idiv {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::FIDiv(ref a1, ref a2, ref t) =>
                write!(f, "floored_idiv {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::RDiv(ref a1, ref a2, ref t) =>
                write!(f, "rdiv {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Shl(ref a1, ref a2, ref t) =>
                write!(f, "shl {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Shr(ref a1, ref a2, ref t) =>
                write!(f, "shr {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Xor(ref a1, ref a2, ref t) =>
                write!(f, "xor {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::And(ref a1, ref a2, ref t) =>
                write!(f, "and {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Or(ref a1, ref a2, ref t) =>
                write!(f, "or {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Mod(ref a1, ref a2, ref t) =>
                write!(f, "mod {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Rem(ref a1, ref a2, ref t) =>
                write!(f, "rem {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Neg(ref a, ref t) =>
                write!(f, "neg {}, @{}", a, t)
        }
    }
}

impl fmt::Display for CutInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CutInstruction::Cut(r) =>
                write!(f, "cut {}", r),
            &CutInstruction::NeckCut =>
                write!(f, "neck_cut"),
            &CutInstruction::GetLevel(r) =>
                write!(f, "get_level {}", r)
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Level::Root | &Level::Shallow => write!(f, "A"),
            &Level::Deep => write!(f, "X")
        }
    }
}

impl fmt::Display for VarReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VarReg::Norm(RegType::Perm(reg)) => write!(f, "Y{}", reg),
            &VarReg::Norm(RegType::Temp(reg)) => write!(f, "X{}", reg),
            &VarReg::ArgAndNorm(RegType::Perm(reg), arg) =>
                write!(f, "Y{} A{}", reg, arg),
            &VarReg::ArgAndNorm(RegType::Temp(reg), arg) =>
                write!(f, "X{} A{}", reg, arg)
        }
    }
}

impl fmt::Display for RegType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RegType::Perm(val) => write!(f, "Y{}", val),
            &RegType::Temp(val) => write!(f, "X{}", val)
        }
    }
}

#[allow(dead_code)]
pub fn print_code(code: &Code) {
    for clause in code {
        match clause {
            &Line::Arithmetic(ref arith) =>
                println!("{}", arith),
            &Line::Fact(ref fact) =>
                for fact_instr in fact {
                    println!("{}", fact_instr);
                },
            &Line::BuiltIn(ref instr) =>
                println!("{}", instr),
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

pub fn parse_code(wam: &Machine, buffer: &str) -> Result<TopLevelPacket, ParserError>
{
    let mut worker = TopLevelWorker::new(buffer.as_bytes(), wam.atom_tbl());
    worker.parse_code(&wam.op_dir)
}

pub enum Input {
    Quit,
    Clear,
    Line(String),
    Batch(String)
}

fn read_lines(buffer: &mut String, end_delim: &str) -> String {
    let mut result = String::new();
    let stdin = stdin();

    buffer.clear();
    stdin.read_line(buffer).unwrap();

    while &*buffer.trim() != end_delim {
        result += buffer.as_str();
        buffer.clear();
        stdin.read_line(buffer).unwrap();
    }

    result
}

pub fn read() -> Input {
    let _ = stdout().flush();
    let mut buffer = String::new();

    let stdin = stdin();
    stdin.read_line(&mut buffer).unwrap();

    match &*buffer.trim() {
        ":{"    => Input::Line(read_lines(&mut buffer, "}:")),
        ":{{"   => Input::Batch(read_lines(&mut buffer, "}}:")),
        "quit"  => Input::Quit,
        "clear" => Input::Clear,
        _       => Input::Line(buffer)
    }
}

// throw errors if declaration or query found.
fn compile_relation(tl: &TopLevel) -> Result<Code, ParserError>
{
    let mut cg = CodeGenerator::<DebrayAllocator>::new();

    match tl {
        &TopLevel::Declaration(_) | &TopLevel::Query(_) =>
            Err(ParserError::ExpectedRel),
        &TopLevel::Predicate(ref clauses) =>
            cg.compile_predicate(clauses),
        &TopLevel::Fact(ref fact) =>
            Ok(cg.compile_fact(fact)),
        &TopLevel::Rule(ref rule) =>
            cg.compile_rule(rule)
    }
}

// set first jmp_by_call or jmp_by_index instruction to code.len() - idx,
// where idx is the place it occurs. It only does this to the *first* uninitialized
// jmp index it encounters, then returns.
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

fn compile_query(terms: Vec<QueryTerm>, queue: Vec<TopLevel>)
                 -> Result<(Code, AllocVarDict), ParserError>
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
            let mut code = try_eval_session!(compile_relation(&tl));
            try_eval_session!(compile_appendix(&mut code, queue));

            if !code.is_empty() {
                if let Some(name) = tl.name() {
                    wam.add_user_code(name, tl.arity(), code)
                } else {
                    EvalSession::from(EvalError::NamelessEntry)
                }
            } else {
                EvalSession::from(EvalError::ImpermissibleEntry(String::from("no code generated.")))
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

pub fn compile_listing(wam: &mut Machine, src_str: &str) -> EvalSession
{
    fn get_module_name(module: &Option<Module>) -> ClauseName {
        match module {
            &Some(ref module) => module.module_decl.name.clone(),
            _ => ClauseName::BuiltIn("builtin")
        }
    }

    let mut module: Option<Module> = None;
    let (mut code_dir, mut op_dir) = build_code_and_op_dirs();

    let mut code = Vec::new();

    let mut worker = TopLevelWorker::new(src_str.as_bytes(), wam.atom_tbl());
    let tls = try_eval_session!(worker.parse_batch(&mut op_dir));

    for tl in tls {
        match tl {
            TopLevelPacket::Query(..) =>
                return EvalSession::from(ParserError::ExpectedRel),
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::Module(module_decl)), _) =>
                if module.is_none() {
                    let (builtin_code_dir, builtin_op_dir) = build_code_and_op_dirs();

                    code_dir.extend(builtin_code_dir.into_iter());
                    op_dir.extend(builtin_op_dir.into_iter());

                    module = Some(Module::new(module_decl));
                } else {
                    return EvalSession::from(ParserError::InvalidModuleDecl);
                },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::UseModule(name)), _) => {
                if let Some(ref submodule) = wam.get_module(name.clone()) {
                    if let Some(ref mut module) = module {
                        module.use_module(submodule);
                        continue;
                    }
                } else {
                    return EvalSession::from(EvalError::ModuleNotFound);
                }

                wam.use_module_in_toplevel(name);
            },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::UseQualifiedModule(name, exports)), _) => {
                if let Some(ref submodule) = wam.get_module(name.clone()) {
                    if let Some(ref mut module) = module {
                        module.use_qualified_module(submodule, exports);
                        continue;
                    }
                } else {
                    return EvalSession::from(EvalError::ModuleNotFound);
                }

                wam.use_qualified_module_in_toplevel(name, exports);
            },
            TopLevelPacket::Decl(TopLevel::Declaration(Declaration::Op(..)), _) => {},
            TopLevelPacket::Decl(decl, queue) => {
                let p = code.len() + wam.code_size();
                let mut decl_code = try_eval_session!(compile_relation(&decl));

                try_eval_session!(compile_appendix(&mut decl_code, queue));

                code.extend(decl_code.into_iter());
                code_dir.insert((decl.name().unwrap(), decl.arity()), (p, get_module_name(&module)));
            }
        }
    }

    if let Some(mut module) = module {
        module.code_dir.extend(code_dir.into_iter());
        module.op_dir.extend(op_dir.into_iter());

        wam.add_module(module, code);
    } else {
        wam.add_batched_code(code, code_dir);
        wam.add_batched_ops(op_dir);
    }

    EvalSession::EntrySuccess
}

fn error_string(e: &String) -> String {
    format!("error: exception thrown: {}", e)
}

pub fn print(wam: &mut Machine, result: EvalSession) {
    match result {
        EvalSession::InitialQuerySuccess(alloc_locs, mut heap_locs) => {
            print!("true");

            if !wam.or_stack_is_empty() {
                print!(" ");
            }

            println!(".");

            if heap_locs.is_empty() {
                return;
            }

            loop {
                let mut result = EvalSession::from(EvalError::QueryFailure);
                let mut output = PrinterOutputter::new();

                let bindings = wam.heap_view(&heap_locs, output).result();

                let stdin = stdin();
                let mut stdout = stdout().into_raw_mode().unwrap();

                write!(stdout, "{}", bindings).unwrap();
                stdout.flush().unwrap();

                if !wam.or_stack_is_empty() {
                    stdout.flush().unwrap();

                    for c in stdin.keys() {
                        match c.unwrap() {
                            Key::Char(' ') | Key::Char(';') => {
                                write!(stdout, " ;\n\r").unwrap();
                                result = wam.continue_query(&alloc_locs, &mut heap_locs);
                                break;
                            },
                            Key::Char('.') => {
                                write!(stdout, " .\n\r").unwrap();
                                return;
                            },
                            _ => {}
                        }
                    }

                    if let &EvalSession::Error(EvalError::QueryFailure) = &result
                    {
                        write!(stdout, "false.\n\r").unwrap();
                        stdout.flush().unwrap();
                        return;
                    }

                    if let &EvalSession::Error(EvalError::QueryFailureWithException(ref e)) = &result
                    {
                        write!(stdout, "{}\n\r", error_string(e)).unwrap();
                        stdout.flush().unwrap();
                        return;
                    }
                } else {
                    break;
                }
            }

            write!(stdout(), ".\n").unwrap();
        },
        EvalSession::Error(e) => println!("{}", e),
        _ => {}
    };
}
