use prolog::clause_types::*;
use prolog::forms::*;
use prolog::instructions::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;

use termion::input::TermRead;
use termion::event::Key;

use std::io::stdin;
use std::fmt;

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

impl fmt::Display for REPLCodePtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            REPLCodePtr::CompileBatch =>
                write!(f, "REPLCodePtr::CompileBatch"),
            REPLCodePtr::SubmitQueryAndPrintResults =>
                write!(f, "REPLCodePtr::SubmitQueryAndPrintResults")
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
        }
    }
}

impl fmt::Display for ClauseType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ClauseType::System(SystemClauseType::SetCutPoint(r)) =>
                write!(f, "$set_cp({})", r),
            &ClauseType::Named(ref name, _, ref idx)
          | &ClauseType::Op(ref name, _, ref idx) =>
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
            &HeapCellValue::NamedStr(arity, ref name, Some(ref cell)) =>
                write!(f, "{}/{} (op, priority: {}, spec: {})", name.as_str(), arity,
                       cell.prec(), cell.assoc()),
            &HeapCellValue::NamedStr(arity, ref name, None) =>
                write!(f, "{}/{}", name.as_str(), arity)
        }
    }
}

impl fmt::Display for DBRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DBRef::BuiltInPred(ref name, arity, _) =>  write!(f, "db_ref:builtin:{}/{}", name, arity),
            &DBRef::NamedPred(ref name, arity, _) =>    write!(f, "db_ref:named:{}/{}", name, arity),
            &DBRef::Op(priority, spec, ref name, ..) => write!(f, "db_ref:op({}, {}, {})", priority,
                                                               spec, name)
        }
    }
}

impl fmt::Display for Addr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Addr::Con(ref c) => write!(f, "Addr::Con({})", c),
            &Addr::DBRef(ref db_ref) => write!(f, "Addr::DBRef({})", db_ref),
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
            &SessionError::InvalidFileName(ref filename) =>
                write!(f, "filename {} is invalid", filename),            
            &SessionError::ModuleNotFound => write!(f, "module not found."),
            &SessionError::ModuleDoesNotContainExport =>
                write!(f, "module does not contain claimed export."),
            &SessionError::NoModuleDeclaration(ref name) =>
                write!(f, "file {}.pl lacks an expected module declaration.", name),
            &SessionError::OpIsInfixAndPostFix(_) =>
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

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Number::Float(fl) => write!(f, "{}", fl),
            &Number::Integer(ref bi) => write!(f, "{}", bi),
            &Number::Rational(ref r) => write!(f, "{}", r)
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
                write!(f, "** {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::IntPow(ref a1, ref a2, ref t) =>
                write!(f, "^ {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Div(ref a1, ref a2, ref t) =>
                write!(f, "div {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::IDiv(ref a1, ref a2, ref t) =>
                write!(f, "idiv {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Max(ref a1, ref a2, ref t) =>
                write!(f, "max {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Min(ref a1, ref a2, ref t) =>
                write!(f, "min {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::IntFloorDiv(ref a1, ref a2, ref t) =>
                write!(f, "int_floor_div {}, {}, @{}", a1, a2, t),
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
            &ArithmeticInstruction::ATan2(ref a1, ref a2, ref t) =>
                write!(f, "atan2 {}, {}, @{}", a1, a2, t),
            &ArithmeticInstruction::Plus(ref a, ref t) =>
                write!(f, "plus {}, @{}", a, t),
            &ArithmeticInstruction::Neg(ref a, ref t) =>
                write!(f, "neg {}, @{}", a, t),
            &ArithmeticInstruction::Cos(ref a, ref t) =>
                write!(f, "cos {}, @{}", a, t),
            &ArithmeticInstruction::Sin(ref a, ref t) =>
                write!(f, "sin {}, @{}", a, t),
            &ArithmeticInstruction::Tan(ref a, ref t) =>
                write!(f, "tan {}, @{}", a, t),
            &ArithmeticInstruction::ATan(ref a, ref t) =>
                write!(f, "atan {}, @{}", a, t),
            &ArithmeticInstruction::ASin(ref a, ref t) =>
                write!(f, "asin {}, @{}", a, t),
            &ArithmeticInstruction::ACos(ref a, ref t) =>
                write!(f, "acos {}, @{}", a, t),
            &ArithmeticInstruction::Log(ref a, ref t) =>
                write!(f, "log {}, @{}", a, t),
            &ArithmeticInstruction::Exp(ref a, ref t) =>
                write!(f, "exp {}, @{}", a, t),
            &ArithmeticInstruction::Sqrt(ref a, ref t) =>
                write!(f, "sqrt {}, @{}", a, t),
            &ArithmeticInstruction::BitwiseComplement(ref a, ref t) =>
                write!(f, "bitwise_complement {}, @{}", a, t),
            &ArithmeticInstruction::Truncate(ref a, ref t) =>
                write!(f, "truncate {}, @{}", a, t),
            &ArithmeticInstruction::Round(ref a, ref t) =>
                write!(f, "round {}, @{}", a, t),
            &ArithmeticInstruction::Ceiling(ref a, ref t) =>
                write!(f, "ceiling {}, @{}", a, t),
            &ArithmeticInstruction::Floor(ref a, ref t) =>
                write!(f, "floor {}, @{}", a, t),
            &ArithmeticInstruction::Float(ref a, ref t) =>
                write!(f, "float {}, @{}", a, t),
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

pub enum ContinueResult {
    ContinueQuery,
    Conclude
}

pub
fn next_keypress() -> ContinueResult
{
    let stdin = stdin();

    for c in stdin.keys() {
        match c.unwrap() {
            Key::Char(' ') | Key::Char(';') =>
                return ContinueResult::ContinueQuery,
            Key::Char('.') =>
                return ContinueResult::Conclude,
            _ => {}
        }
    }

    ContinueResult::Conclude
}
