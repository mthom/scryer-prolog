use prolog::ast::*;
use prolog::heap_print::*;
use prolog::machine::*;
use prolog::ordered_float::OrderedFloat;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

use std::io::{Write, stdin, stdout};
use std::fmt;

impl fmt::Display for IndexPtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &IndexPtr::Module =>
                write!(f, ""),
            &IndexPtr::Undefined =>
                write!(f, "undefined"),
            &IndexPtr::Index(i)  =>
                write!(f, "{}", i)
        }
    }
}

impl fmt::Display for ClauseName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Constant::Atom(ref atom) =>
                if atom.as_str().chars().any(|c| "`.$'\" ".contains(c)) {
                    write!(f, "'{}'", atom.as_str())
                } else {
                    write!(f, "{}", atom.as_str())
                },
            &Constant::Char(c) =>
                write!(f, "'{}'", c as u8),
            &Constant::EmptyList =>
                write!(f, "[]"),
            &Constant::Number(ref n) =>
                write!(f, "{}", n),
            &Constant::String(ref s) =>
                write!(f, "\"{}\"", s),
            &Constant::Usize(integer) =>
                write!(f, "u{}", integer)
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
            &ClauseType::Named(ref name, ref idx) | &ClauseType::Op(ref name, _, ref idx) => {
                let idx = idx.0.borrow();
                write!(f, "{}:{}/{}", idx.1, name, idx.0)
            },
            ref ct => write!(f, "{}", ct.name())
        }
    }
}

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::CallClause(ref ct, arity, pvs, true) =>
                write!(f, "execute {}/{}, {}", ct, arity, pvs),
            &ControlInstruction::CallClause(ref ct, arity, pvs, false) =>
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

impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &SessionError::ModuleNotFound => write!(f, "module not found."),
            &SessionError::ModuleDoesNotContainExport => write!(f, "module does not contain claimed export."),
            &SessionError::QueryFailure => write!(f, "false."),
            &SessionError::QueryFailureWithException(ref e) => write!(f, "{}", error_string(e)),
            &SessionError::ImpermissibleEntry(ref msg) => write!(f, "cannot overwrite {}.", msg),
            &SessionError::OpIsInfixAndPostFix =>
                write!(f, "cannot define an op to be both postfix and infix."),
            &SessionError::NamelessEntry => write!(f, "the predicate head is not an atom or clause."),
            &SessionError::ParserError(ref e) => write!(f, "{:?}", e)
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
                let mut result = EvalSession::from(SessionError::QueryFailure);
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

                    if let &EvalSession::Error(SessionError::QueryFailure) = &result
                    {
                        write!(stdout, "false.\n\r").unwrap();
                        stdout.flush().unwrap();
                        return;
                    }

                    if let &EvalSession::Error(SessionError::QueryFailureWithException(ref e)) = &result
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
