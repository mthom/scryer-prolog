use prolog::ast::*;
use prolog::codegen::*;
use prolog::debray_allocator::*;
use prolog::fixtures::*;
use prolog::heap_print::*;
use prolog::machine::*;
use prolog::parser::toplevel::*;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;

impl fmt::Display for FactInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FactInstruction::GetConstant(Level::Shallow, ref constant, ref r) =>
                write!(f, "get_constant {}, A{}", constant, r.reg_num()),
            &FactInstruction::GetConstant(Level::Deep, ref constant, ref r) =>
                write!(f, "get_constant {}, {}", constant, r),
            &FactInstruction::GetList(Level::Shallow, ref r) =>
                write!(f, "get_list A{}", r.reg_num()),
            &FactInstruction::GetList(Level::Deep, ref r) =>
                write!(f, "get_list {}", r),
            &FactInstruction::GetStructure(Level::Deep, ref name, ref arity, ref r, _) =>
                write!(f, "get_structure {}/{}, {}", name, arity, r),
            &FactInstruction::GetStructure(Level::Shallow, ref name, ref arity, ref r, _) =>
                write!(f, "get_structure {}/{}, A{}", name, arity, r.reg_num()),
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
            &QueryInstruction::PutConstant(Level::Shallow, ref constant, ref r) =>
                write!(f, "put_constant {}, A{}", constant, r.reg_num()),
            &QueryInstruction::PutConstant(Level::Deep, ref constant, ref r) =>
                write!(f, "put_constant {}, {}", constant, r),
            &QueryInstruction::PutList(Level::Shallow, ref r) =>
                write!(f, "put_list A{}", r.reg_num()),
            &QueryInstruction::PutList(Level::Deep, ref r) =>
                write!(f, "put_list {}", r),
            &QueryInstruction::PutStructure(Level::Deep, ref name, ref arity, ref r, _) =>
                write!(f, "put_structure {}/{}, {}", name, arity, r),
            &QueryInstruction::PutStructure(Level::Shallow, ref name, ref arity, ref r, _) =>
                write!(f, "put_structure {}/{}, A{}", name, arity, r.reg_num()),
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

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::ArgCall =>
                write!(f, "arg_call"),
            &ControlInstruction::ArgExecute =>
                write!(f, "arg_execute"),
            &ControlInstruction::Call(ref name, arity, pvs) =>
                write!(f, "call {}/{}, {}", name, arity, pvs),
            &ControlInstruction::CallN(arity) =>
                write!(f, "call_N {}", arity),
            &ControlInstruction::CatchCall =>
                write!(f, "catch_call"),
            &ControlInstruction::CatchExecute =>
                write!(f, "catch_execute"),
            &ControlInstruction::CheckCpExecute =>
                write!(f, "check_cp_execute"),
            &ControlInstruction::DisplayCall =>
                write!(f, "display_call"),
            &ControlInstruction::DisplayExecute =>
                write!(f, "display_execute"),
            &ControlInstruction::DuplicateTermCall =>
                write!(f, "call_duplicate_term"),
            &ControlInstruction::DuplicateTermExecute =>
                write!(f, "execute_duplicate_term"),
            &ControlInstruction::ExecuteN(arity) =>
                write!(f, "execute_N {}", arity),
            &ControlInstruction::FunctorCall =>
                write!(f, "functor_call"),
            &ControlInstruction::FunctorExecute =>
                write!(f, "functor_execute"),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
            &ControlInstruction::Execute(ref name, arity) =>
                write!(f, "execute {}/{}", name, arity),
            &ControlInstruction::GetCleanerCall =>
                write!(f, "get_cleaner_call"),
            &ControlInstruction::GotoCall(p, arity) =>
                write!(f, "goto_call {}/{}", p, arity),
            &ControlInstruction::GotoExecute(p, arity) =>
                write!(f, "goto_execute {}/{}", p, arity),
            &ControlInstruction::IsCall(r, ref at) =>
                write!(f, "is_call {}, {}", r, at),
            &ControlInstruction::IsExecute(r, ref at) =>
                write!(f, "is_execute {}, {}", r, at),
            &ControlInstruction::JmpByCall(arity, offset) =>
                write!(f, "jmp_by_call {}/{}", offset, arity),
            &ControlInstruction::JmpByExecute(arity, offset) =>
                write!(f, "jmp_by_execute {}/{}", offset, arity),
            &ControlInstruction::Proceed =>
                write!(f, "proceed"),
            &ControlInstruction::ThrowCall =>
                write!(f, "call_throw"),
            &ControlInstruction::ThrowExecute =>
                write!(f, "execute_throw"),
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
            &BuiltInInstruction::CompareNumber(cmp, ref at_1, ref at_2) =>
                write!(f, "number_test {}, {}, {} ", cmp, at_1, at_2),
            &BuiltInInstruction::DynamicCompareNumber(cmp) =>
                write!(f, "dynamic_number_test {}", cmp),
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
            &BuiltInInstruction::InstallCleaner =>
                write!(f, "install_cleaner"),
            &BuiltInInstruction::InstallNewBlock =>
                write!(f, "install_new_block"),
            &BuiltInInstruction::InternalCallN =>
                write!(f, "internal_call_N"),
            &BuiltInInstruction::IsAtomic(r) =>
                write!(f, "is_atomic {}", r),
            &BuiltInInstruction::IsInteger(r) =>
                write!(f, "is_integer {}", r),
            &BuiltInInstruction::DynamicIs =>
                write!(f, "call_is"),
            &BuiltInInstruction::IsVar(r) =>
                write!(f, "is_var {}", r),
            &BuiltInInstruction::ResetBlock =>
                write!(f, "reset_block"),
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
            &EvalError::QueryFailure => write!(f, "false."),
            &EvalError::QueryFailureWithException(ref e) => write!(f, "{}", error_string(e)),
            &EvalError::ImpermissibleEntry(ref msg) => write!(f, "cannot overwrite builtin {}", msg),
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
            &Level::Shallow => write!(f, "A"),
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

pub fn parse_code(wam: &mut Machine, buffer: &str) -> Result<TopLevelPacket, ParserError>
{
    let mut worker = TopLevelWorker::new(wam.atom_tbl(), wam.op_dir());
    worker.parse_code(buffer)
}

pub fn parse_batch(wam: &mut Machine, buffer: &str) -> Result<Vec<TopLevelPacket>, ParserError>
{
    let mut worker = TopLevelWorker::new(wam.atom_tbl(), wam.op_dir());
    worker.parse_batch(buffer)
}

pub fn read() -> String {
    let _ = stdout().flush();

    let mut buffer = String::new();
    let mut result = String::new();

    let stdin = stdin();
    stdin.read_line(&mut buffer).unwrap();

    if &*buffer.trim() == ":{" {
        buffer.clear();

        stdin.read_line(&mut buffer).unwrap();

        while &*buffer.trim() != "}:" {
            result += buffer.as_str();
            buffer.clear();
            stdin.read_line(&mut buffer).unwrap();
        }
    } else {
        result = buffer;
    }

    result
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
            &mut Line::Control(ControlInstruction::JmpByExecute(_, ref mut offset))
          | &mut Line::Control(ControlInstruction::JmpByCall(_, ref mut offset)) if *offset == 0 => {
              *offset = code_len - idx;
              break;
            },
            _ => {}
        };
    }
}

fn compile_appendix(code: &mut Code, queue: &Vec<TopLevel>) -> Result<(), ParserError>
{
    for tl in queue.iter() {
        set_first_index(code);
        code.append(&mut compile_relation(tl)?);
    }

    Ok(())
}

fn compile_query<'a>(terms: &'a Vec<QueryTerm>, queue: &'a Vec<TopLevel>)
                     -> Result<(Code, AllocVarDict<'a>), ParserError>
{
    let mut cg = CodeGenerator::<DebrayAllocator>::new();
    let mut code = try!(cg.compile_query(terms));

    compile_appendix(&mut code, queue)?;

    Ok((code, cg.take_vars()))
}

fn compile_decl<'a, 'b: 'a>(wam: &'a mut Machine, tl: &'b TopLevel, queue: &'b Vec<TopLevel>)
                            -> EvalSession<'b>
{
    match tl {
        &TopLevel::Declaration(ref decl) => wam.submit_decl(decl),
        _ => {
            let mut code = match compile_relation(tl) {
                Ok(code) => code,
                Err(e) => return EvalSession::from(EvalError::ParserError(e))
            };

            if let Err(e) = compile_appendix(&mut code, queue) {
                return EvalSession::from(e);
            };

            print_code(&code);
            
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

pub fn compile<'a, 'b: 'a>(wam: &'a mut Machine, tl: &'b TopLevelPacket) -> EvalSession<'b>
{
    match tl {
        &TopLevelPacket::Query(ref terms, ref queue) =>
            match compile_query(terms, queue) {
                Ok((code, vars)) => wam.submit_query(code, vars),
                Err(e) => EvalSession::from(e)
            },
        &TopLevelPacket::Decl(ref tl, ref queue) =>
            compile_decl(wam, tl, queue)
    }
}

pub fn compile_batch<'a, 'b: 'a>(wam: &'a mut Machine, tls: &'b Vec<TopLevelPacket>)
                                 -> EvalSession<'b>
{
    for tl in tls {
        match tl {
            &TopLevelPacket::Query(..) =>
                return EvalSession::from(ParserError::ExpectedRel),
            &TopLevelPacket::Decl(ref tl, ref queue) => {
                let result = compile_decl(wam, tl, queue);

                if let &EvalSession::Error(_) = &result {
                    return result;
                }
            }
        }
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
                            Key::Char(' ') => {
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
