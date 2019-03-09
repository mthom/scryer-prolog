use prolog::clause_types::*;
use prolog::forms::*;
use prolog::heap_print::*;
use prolog::instructions::*;
use prolog::machine::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;

use termion::raw::{IntoRawMode, RawTerminal};
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;

fn error_string<StringT: AsRef<str>>(e: &StringT) -> String {
    format!("error: exception thrown: {}", e.as_ref())
}

impl fmt::Display for LocalCodePtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LocalCodePtr::DirEntry(p) =>
                write!(f, "LocalCodePtr::DirEntry({})", p),
            LocalCodePtr::InSituDirEntry(p) =>
                write!(f, "LocalCodePtr::InSituDirEntry({})", p),
            LocalCodePtr::TopLevel(cn, p) =>
                write!(f, "LocalCodePtr::TopLevel({}, {})", cn, p),
            LocalCodePtr::UserGoalExpansion(p) =>
                write!(f, "LocalCodePtr::UserGoalExpansion({})", p),
            LocalCodePtr::UserTermExpansion(p) =>
                write!(f, "LocalCodePtr::UserTermExpansion({})", p),
        }
    }
}

impl fmt::Display for IndexPtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexPtr::Undefined =>
                write!(f, "undefined"),
            &IndexPtr::Index(i)  =>
                write!(f, "{}", i)
        }
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

impl fmt::Display for ClauseType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ClauseType::System(SystemClauseType::SetCutPoint(r)) =>
                write!(f, "$set_cp({})", r),
            &ClauseType::Named(ref name, _, ref idx)
          | &ClauseType::Op(OpDecl(.., ref name), ref idx) =>
            {
                let idx = idx.0.borrow();
                write!(f, "{}:{}/{}", idx.1, name, idx.0)
            },
            ref ct => write!(f, "{}", ct.name())
        }
    }
}

impl fmt::Display for HeapCellValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &HeapCellValue::Addr(ref addr) =>
                write!(f, "{}", addr),
            &HeapCellValue::NamedStr(arity, ref name, Some((priority, spec))) =>
                write!(f, "{}/{} (op, priority: {}, spec: {})", name.as_str(), arity,
                       priority, spec),
            &HeapCellValue::NamedStr(arity, ref name, None) =>
                write!(f, "{}/{}", name.as_str(), arity)
        }
    }
}

impl fmt::Display for Addr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Addr::Con(ref c) => write!(f, "Addr::Con({})", c),
            &Addr::Lis(l) => write!(f, "Addr::Lis({})", l),
            &Addr::AttrVar(h) => write!(f, "Addr::AttrVar({})", h),
            &Addr::HeapCell(h) => write!(f, "Addr::HeapCell({})", h),
            &Addr::StackCell(fr, sc)=> write!(f, "Addr::StackCell({}, {})", fr, sc),
            &Addr::Str(s) => write!(f, "Addr::Str({})", s)
        }
    }
}

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::CallClause(ref ct, arity, pvs, true, true) =>
                write!(f, "call_with_default_policy {}/{}, {}", ct, arity, pvs),
            &ControlInstruction::CallClause(ref ct, arity, pvs, false, true) =>
                write!(f, "execute_with_default_policy {}/{}, {}", ct, arity, pvs),
            &ControlInstruction::CallClause(ref ct, arity, pvs, true, false) =>
                write!(f, "execute {}/{}, {}", ct, arity, pvs),
            &ControlInstruction::CallClause(ref ct, arity, pvs, false, false) =>
                write!(f, "call {}/{}, {}", ct, arity, pvs),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
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

impl fmt::Display for ChoiceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ChoiceInstruction::TryMeElse(offset) =>
                write!(f, "try_me_else {}", offset),
            &ChoiceInstruction::DefaultRetryMeElse(offset) =>
                write!(f, "retry_me_else_by_default {}", offset),
            &ChoiceInstruction::RetryMeElse(offset) =>
                write!(f, "retry_me_else {}", offset),
            &ChoiceInstruction::DefaultTrustMe =>
                write!(f, "trust_me_by_default"),
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

impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &SessionError::CannotOverwriteBuiltIn(ref msg) =>
                write!(f, "cannot overwrite {}", msg),
            &SessionError::CannotOverwriteImport(ref msg) =>
                write!(f, "cannot overwrite import {}", msg),
            &SessionError::ModuleNotFound => write!(f, "module not found."),
            &SessionError::ModuleDoesNotContainExport =>
                write!(f, "module does not contain claimed export."),
            &SessionError::QueryFailure =>
                write!(f, "false."),
            &SessionError::QueryFailureWithException(ref e) =>
                write!(f, "{}", error_string(e)),
            &SessionError::OpIsInfixAndPostFix =>
                write!(f, "cannot define an op to be both postfix and infix."),
            &SessionError::NamelessEntry =>
                write!(f, "the predicate head is not an atom or clause."),
            &SessionError::ParserError(ref e) =>
                write!(f, "syntax_error({})", e.as_str()),
            &SessionError::UserPrompt =>
                write!(f, "enter predicate at [user] prompt")
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
            &ArithmeticInstruction::Abs(ref a1, ref t) =>
                write!(f, "abs {}, @{}", a1, t),
            &ArithmeticInstruction::Add(ref a1, ref a2, ref t) =>
                write!(f, "add {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Sub(ref a1, ref a2, ref t) =>
                write!(f, "sub {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Mul(ref a1, ref a2, ref t) =>
                write!(f, "mul {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Pow(ref a1, ref a2, ref t) =>
                write!(f, "pow {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Div(ref a1, ref a2, ref t) =>
                write!(f, "div {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::IDiv(ref a1, ref a2, ref t) =>
                write!(f, "idiv {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Max(ref a1, ref a2, ref t) =>
                write!(f, "max {}, {}, @{}", a1, a2, t),
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
                write!(f, "get_level {}", r),
            &CutInstruction::GetLevelAndUnify(r) =>
                write!(f, "get_level_and_unify {}", r)
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

enum ContinueResult {
    ContinueQuery,
    Conclude
}

fn next_step(mut stdout: RawTerminal<std::io::Stdout>) -> ContinueResult
{
    let stdin = stdin();

    for c in stdin.keys() {
        match c.unwrap() {
            Key::Char(' ') | Key::Char(';') => {
                write!(stdout, " ;\r\n").unwrap();
                return ContinueResult::ContinueQuery;
            },
            Key::Char('.') => {
                write!(stdout, " .\r\n").unwrap();
                return ContinueResult::Conclude;
            },
            _ => {}
        }
    }

    ContinueResult::Conclude
}

pub fn print(wam: &mut Machine, result: EvalSession) {
    match result {
        EvalSession::InitialQuerySuccess(alloc_locs, mut heap_locs) => {
            if wam.or_stack_is_empty() {
                println!("true.");

                if heap_locs.is_empty() {
                    return;
                }
            }

            if !wam.or_stack_is_empty() {
                print!("true .");

                if !heap_locs.is_empty() {
                    println!("\r");
                }
            }

            loop {
                let mut output = PrinterOutputter::new();

                let bindings = wam.heap_view(&heap_locs, output).result();
                let mut raw_stdout = stdout().into_raw_mode().unwrap();

                if !heap_locs.is_empty() {
                    write!(raw_stdout, "{}", bindings).unwrap();
                    raw_stdout.flush().unwrap();
                    
                    let attr_goals = wam.attribute_goals(&heap_locs);
                    
                    if !attr_goals.is_empty() {
                        write!(raw_stdout, "\r\n{}\r\n", attr_goals).unwrap();
                    }
                }

                if !wam.or_stack_is_empty() {
                    raw_stdout.flush().unwrap();

                    let result = match next_step(raw_stdout) {
                        ContinueResult::ContinueQuery =>
                            wam.continue_query(&alloc_locs, &mut heap_locs),
                        ContinueResult::Conclude =>
                            return
                    };

                    let mut raw_stdout = stdout().into_raw_mode().unwrap();

                    if let &EvalSession::Error(SessionError::QueryFailure) = &result
                    {
                        write!(raw_stdout, "false.\r\n").unwrap();
                        raw_stdout.flush().unwrap();
                        return;
                    }

                    if let &EvalSession::Error(SessionError::QueryFailureWithException(ref e)) = &result
                    {
                        write!(raw_stdout, "{}\r\n", error_string(e)).unwrap();
                        raw_stdout.flush().unwrap();
                        return;
                    }
                } else {
                    if heap_locs.is_empty() {
                        write!(raw_stdout, "true.\r\n").unwrap();
                    } else {
                        write!(raw_stdout, ".\r\n").unwrap();
                    }
                    
                    break;
                }
            }
        },
        EvalSession::Error(e) => println!("{}", e),
        _ => {}
    };
}
