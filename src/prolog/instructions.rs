use prolog_parser::ast::*;

use prolog::clause_types::*;
use prolog::forms::*;
use prolog::machine::machine_errors::MachineStub;
use prolog::machine::machine_indices::*;

use prolog::rug::Integer;

use std::collections::{HashMap, VecDeque};

fn reg_type_into_functor(r: RegType) -> MachineStub {
    match r {
        RegType::Temp(r) =>
            functor!("x", 1, [heap_integer!(Integer::from(r))]),
        RegType::Perm(r) =>
            functor!("y", 1, [heap_integer!(Integer::from(r))])
    }
}

impl Level {
    fn into_functor(self) -> MachineStub {
        match self {
            Level::Root =>
                functor!("level", 1, [heap_atom!("root")]),
            Level::Shallow =>
                functor!("level", 1, [heap_atom!("shallow")]),
            Level::Deep =>
                functor!("level", 1, [heap_atom!("deep")]),
        }
    }
}

impl ArithmeticTerm {
    fn into_functor(&self) -> MachineStub {
        match self {
            &ArithmeticTerm::Reg(r) =>
                reg_type_into_functor(r),
            &ArithmeticTerm::Interm(i) =>
                functor!("intermediate", 1, [heap_integer!(Integer::from(i))]),
            &ArithmeticTerm::Number(ref n) =>
                vec![heap_con!(n.clone().to_constant())]
        }
    }
}

pub enum ChoiceInstruction {
    DefaultRetryMeElse(usize),
    DefaultTrustMe,
    RetryMeElse(usize),
    TrustMe,
    TryMeElse(usize)
}

impl ChoiceInstruction {
    pub fn to_functor(&self) -> MachineStub {
        match self {
            &ChoiceInstruction::TryMeElse(offset) =>
                functor!("try_me_else", 1, [heap_integer!(Integer::from(offset))]),
            &ChoiceInstruction::RetryMeElse(offset) =>
                functor!("retry_me_else", 1, [heap_integer!(Integer::from(offset))]),
            &ChoiceInstruction::TrustMe =>
                vec![heap_atom!("trust_me")],
            &ChoiceInstruction::DefaultRetryMeElse(offset) =>
                functor!("default_retry_me_else", 1, [heap_integer!(Integer::from(offset))]),
            &ChoiceInstruction::DefaultTrustMe =>
                vec![heap_atom!("default_trust_me")],
        }
    }
}

pub enum CutInstruction {
    Cut(RegType),
    GetLevel(RegType),
    GetLevelAndUnify(RegType),
    NeckCut
}

impl CutInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &CutInstruction::Cut(r) => {
                let mut stub = functor!("cut", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &CutInstruction::GetLevel(r) => {
                let mut stub = functor!("get_level", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &CutInstruction::GetLevelAndUnify(r) => {
                let mut stub = functor!("get_level_and_unify", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &CutInstruction::NeckCut =>
                vec![heap_atom!("neck_cut")]
        }
    }
}

pub enum IndexedChoiceInstruction {
    Retry(usize),
    Trust(usize),
    Try(usize)
}

impl From<IndexedChoiceInstruction> for Line {
    fn from(i: IndexedChoiceInstruction) -> Self {
        Line::IndexedChoice(i)
    }
}

impl IndexedChoiceInstruction {
    pub fn offset(&self) -> usize {
        match self {
            &IndexedChoiceInstruction::Retry(offset) => offset,
            &IndexedChoiceInstruction::Trust(offset) => offset,
            &IndexedChoiceInstruction::Try(offset)   => offset
        }
    }

    pub fn to_functor(&self) -> MachineStub {
        match self {
            &IndexedChoiceInstruction::Try(offset) =>
                functor!("try", 1, [heap_integer!(Integer::from(offset))]),
            &IndexedChoiceInstruction::Trust(offset) =>
                functor!("trust", 1, [heap_integer!(Integer::from(offset))]),
            &IndexedChoiceInstruction::Retry(offset) =>
                functor!("retry", 1, [heap_integer!(Integer::from(offset))])
        }
    }
}

pub enum Line {
    Arithmetic(ArithmeticInstruction),
    Choice(ChoiceInstruction),
    Control(ControlInstruction),
    Cut(CutInstruction),
    Fact(FactInstruction),
    Indexing(IndexingInstruction),
    IndexedChoice(IndexedChoiceInstruction),
    Query(QueryInstruction)
}

impl Line {
    pub fn is_head_instr(&self) -> bool {
        match self {
            &Line::Cut(_) => true,
            &Line::Fact(_) => true,
            &Line::Query(_) => true,
            _ => false
        }
    }

    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &Line::Arithmetic(ref arith_instr) => arith_instr.to_functor(h),
            &Line::Choice(ref choice_instr) => choice_instr.to_functor(),
            &Line::Control(ref control_instr) => control_instr.to_functor(),
            &Line::Cut(ref cut_instr) => cut_instr.to_functor(h),
            &Line::Fact(ref fact_instr) => fact_instr.to_functor(h),
            &Line::Indexing(ref indexing_instr) => indexing_instr.to_functor(),
            &Line::IndexedChoice(ref indexed_choice_instr) => indexed_choice_instr.to_functor(),
            &Line::Query(ref query_instr) => query_instr.to_functor(h)
        }
    }
}

#[derive(Clone)]
pub enum ArithmeticInstruction {
    Add(ArithmeticTerm, ArithmeticTerm, usize),
    Sub(ArithmeticTerm, ArithmeticTerm, usize),
    Mul(ArithmeticTerm, ArithmeticTerm, usize),
    Pow(ArithmeticTerm, ArithmeticTerm, usize),
    IntPow(ArithmeticTerm, ArithmeticTerm, usize),
    IDiv(ArithmeticTerm, ArithmeticTerm, usize),
    Max(ArithmeticTerm, ArithmeticTerm, usize),
    Min(ArithmeticTerm, ArithmeticTerm, usize),
    IntFloorDiv(ArithmeticTerm, ArithmeticTerm, usize),
    RDiv(ArithmeticTerm, ArithmeticTerm, usize),
    Div(ArithmeticTerm, ArithmeticTerm, usize),
    Shl(ArithmeticTerm, ArithmeticTerm, usize),
    Shr(ArithmeticTerm, ArithmeticTerm, usize),
    Xor(ArithmeticTerm, ArithmeticTerm, usize),
    And(ArithmeticTerm, ArithmeticTerm, usize),
    Or(ArithmeticTerm, ArithmeticTerm, usize),
    Mod(ArithmeticTerm, ArithmeticTerm, usize),
    Rem(ArithmeticTerm, ArithmeticTerm, usize),
    Cos(ArithmeticTerm, usize),
    Sin(ArithmeticTerm, usize),
    Tan(ArithmeticTerm, usize),
    Log(ArithmeticTerm, usize),
    Exp(ArithmeticTerm, usize),
    ACos(ArithmeticTerm, usize),
    ASin(ArithmeticTerm, usize),
    ATan(ArithmeticTerm, usize),
    ATan2(ArithmeticTerm, ArithmeticTerm, usize),
    Sqrt(ArithmeticTerm, usize),
    Abs(ArithmeticTerm, usize),
    Float(ArithmeticTerm, usize),
    Truncate(ArithmeticTerm, usize),
    Round(ArithmeticTerm, usize),
    Ceiling(ArithmeticTerm, usize),
    Floor(ArithmeticTerm, usize),
    Neg(ArithmeticTerm, usize),
    Plus(ArithmeticTerm, usize),
    BitwiseComplement(ArithmeticTerm, usize)
}

fn arith_instr_unary_functor(h: usize, name: &'static str, at: &ArithmeticTerm, t: usize)
                             -> MachineStub
{
    let at_stub = at.into_functor();

    let mut stub = functor!(name, 2,
                            [heap_cell!(h + 4),
                             heap_integer!(Integer::from(t))]);

    stub.extend(at_stub.into_iter());
    stub
}

fn arith_instr_bin_functor(h: usize, name: &'static str, at_1: &ArithmeticTerm,
                           at_2: &ArithmeticTerm, t: usize)
                           -> MachineStub
{
    let at_1_stub = at_1.into_functor();
    let at_2_stub = at_2.into_functor();

    let mut stub = functor!(name, 3,
                            [heap_cell!(h + 4),
                             heap_cell!(h + 4 + at_1_stub.len()),
                             heap_integer!(Integer::from(t))]);

    stub.extend(at_1_stub.into_iter());
    stub.extend(at_2_stub.into_iter());

    stub
}

impl ArithmeticInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &ArithmeticInstruction::Add(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "add", at_1, at_2, t),
            &ArithmeticInstruction::Sub(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "sub", at_1, at_2, t),
            &ArithmeticInstruction::Mul(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "mul", at_1, at_2, t),
            &ArithmeticInstruction::IntPow(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "int_pow", at_1, at_2, t),
            &ArithmeticInstruction::Pow(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "pow", at_1, at_2, t),
            &ArithmeticInstruction::IDiv(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "idiv", at_1, at_2, t),
            &ArithmeticInstruction::Max(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "max", at_1, at_2, t),
            &ArithmeticInstruction::Min(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "min", at_1, at_2, t),
            &ArithmeticInstruction::IntFloorDiv(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "int_floor_div", at_1, at_2, t),
            &ArithmeticInstruction::RDiv(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "rdiv", at_1, at_2, t),
            &ArithmeticInstruction::Div(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "div", at_1, at_2, t),
            &ArithmeticInstruction::Shl(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "shl", at_1, at_2, t),
            &ArithmeticInstruction::Shr(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "shr", at_1, at_2, t),
            &ArithmeticInstruction::Xor(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "xor", at_1, at_2, t),
            &ArithmeticInstruction::And(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "and", at_1, at_2, t),
            &ArithmeticInstruction::Or(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "or", at_1, at_2, t),
            &ArithmeticInstruction::Mod(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "mod", at_1, at_2, t),
            &ArithmeticInstruction::Rem(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "rem", at_1, at_2, t),
            &ArithmeticInstruction::ATan2(ref at_1, ref at_2, t) =>
                arith_instr_bin_functor(h, "rem", at_1, at_2, t),
            &ArithmeticInstruction::Cos(ref at, t) =>
                arith_instr_unary_functor(h, "cos", at, t),
            &ArithmeticInstruction::Sin(ref at, t) =>
                arith_instr_unary_functor(h, "sin", at, t),
            &ArithmeticInstruction::Tan(ref at, t) =>
                arith_instr_unary_functor(h, "tan", at, t),
            &ArithmeticInstruction::Log(ref at, t) =>
                arith_instr_unary_functor(h, "log", at, t),
            &ArithmeticInstruction::Exp(ref at, t) =>
                arith_instr_unary_functor(h, "exp", at, t),
            &ArithmeticInstruction::ACos(ref at, t) =>
                arith_instr_unary_functor(h, "acos", at, t),
            &ArithmeticInstruction::ASin(ref at, t) =>
                arith_instr_unary_functor(h, "asin", at, t),
            &ArithmeticInstruction::ATan(ref at, t) =>
                arith_instr_unary_functor(h, "atan", at, t),
            &ArithmeticInstruction::Sqrt(ref at, t) =>
                arith_instr_unary_functor(h, "sqrt", at, t),
            &ArithmeticInstruction::Abs(ref at, t) =>
                arith_instr_unary_functor(h, "abs", at, t),
            &ArithmeticInstruction::Float(ref at, t) =>
                arith_instr_unary_functor(h, "float", at, t),
            &ArithmeticInstruction::Truncate(ref at, t) =>
                arith_instr_unary_functor(h, "truncate", at, t),
            &ArithmeticInstruction::Round(ref at, t) =>
                arith_instr_unary_functor(h, "round", at, t),
            &ArithmeticInstruction::Ceiling(ref at, t) =>
                arith_instr_unary_functor(h, "ceiling", at, t),
            &ArithmeticInstruction::Floor(ref at, t) =>
                arith_instr_unary_functor(h, "floor", at, t),
            &ArithmeticInstruction::Neg(ref at, t) =>
                arith_instr_unary_functor(h, "-", at, t),
            &ArithmeticInstruction::Plus(ref at, t) =>
                arith_instr_unary_functor(h, "+", at, t),
            &ArithmeticInstruction::BitwiseComplement(ref at, t) =>
                arith_instr_unary_functor(h, "\\", at, t),
        }
    }
}

pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    // name, arity, perm_vars after threshold, last call, use default call policy.
    CallClause(ClauseType, usize, usize, bool, bool),
    Deallocate,
    JmpBy(usize, usize, usize, bool), // arity, global_offset, perm_vars after threshold, last call.
    Proceed
}

impl ControlInstruction {
    pub fn is_jump_instr(&self) -> bool {
        match self {
            &ControlInstruction::CallClause(..)  => true,
            &ControlInstruction::JmpBy(..) => true,
            _ => false
        }
    }

    pub fn to_functor(&self) -> MachineStub {
        match self {
            &ControlInstruction::Allocate(num_frames) =>
                functor!("allocate", 1, [heap_integer!(Integer::from(num_frames))]),
            &ControlInstruction::CallClause(ref ct, arity, _, false, _) =>
                functor!("call", 2, [heap_con!(Constant::Atom(ct.name(), None)),
                                     heap_integer!(Integer::from(arity))]),
            &ControlInstruction::CallClause(ref ct, arity, _, true, _) =>
                functor!("execute", 2, [heap_con!(Constant::Atom(ct.name(), None)),
                                        heap_integer!(Integer::from(arity))]),
            &ControlInstruction::Deallocate =>
                vec![heap_atom!("deallocate")],
            &ControlInstruction::JmpBy(_, offset, ..) =>
                functor!("jmp_by", 1, [heap_integer!(Integer::from(offset))]),
            &ControlInstruction::Proceed =>
                vec![heap_atom!("proceed")]
        }
    }
}

pub enum IndexingInstruction {
    SwitchOnTerm(usize, usize, usize, usize),
    SwitchOnConstant(usize, HashMap<Constant, usize>),
    SwitchOnStructure(usize, HashMap<(ClauseName, usize), usize>)
}

impl From<IndexingInstruction> for Line {
    fn from(i: IndexingInstruction) -> Self {
        Line::Indexing(i)
    }
}

impl IndexingInstruction {
    pub fn to_functor(&self) -> MachineStub {
        match self {
            &IndexingInstruction::SwitchOnTerm(vars, constants, lists, structures) =>
                functor!("switch_on_term", 4,
                         [heap_integer!(Integer::from(vars)),
                          heap_integer!(Integer::from(constants)),
                          heap_integer!(Integer::from(lists)),
                          heap_integer!(Integer::from(structures))]),
            &IndexingInstruction::SwitchOnConstant(constants, _) =>
                functor!("switch_on_constant", 1,
                         [heap_integer!(Integer::from(constants))]),
            &IndexingInstruction::SwitchOnStructure(structures, _) =>
                functor!("switch_on_structure", 1,
                         [heap_integer!(Integer::from(structures))])
        }
    }
}

#[derive(Clone)]
pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetStructure(ClauseType, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),
    UnifyConstant(Constant),
    UnifyLocalValue(RegType),
    UnifyVariable(RegType),
    UnifyValue(RegType),
    UnifyVoid(usize)
}

impl FactInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &FactInstruction::GetConstant(lvl, ref constant, r) => {
                let mut stub = functor!("get_constant", 3,
                                        [heap_str!(h + 4),
                                         heap_con!(constant.clone()),
                                         heap_str!(h + 6)]);

                stub.append(&mut lvl.into_functor());
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::GetList(lvl, r) => {
                let mut stub = functor!("get_list", 2,
                                        [heap_str!(h + 3),
                                         heap_str!(h + 5)]);
                stub.append(&mut lvl.into_functor());
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::GetStructure(ref ct, arity, r) => {
                let mut stub = functor!("get_structure", 3,
                                        [heap_con!(Constant::Atom(ct.name(), None)),
                                         heap_integer!(Integer::from(arity)),
                                         heap_str!(h + 4)]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::GetValue(r, arg) => {
                let mut stub = functor!("get_value", 2,
                                        [heap_str!(h + 3),
                                         heap_integer!(Integer::from(arg))]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::GetVariable(r, arg) => {
                let mut stub = functor!("get_variable", 2,
                                        [heap_str!(h + 3),
                                         heap_integer!(Integer::from(arg))]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::UnifyConstant(ref constant) =>
                functor!("unify_constant", 1, [heap_con!(constant.clone())]),
            &FactInstruction::UnifyLocalValue(r) => {
                let mut stub = functor!("unify_local_value", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::UnifyVariable(r) => {
                let mut stub = functor!("unify_variable", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::UnifyValue(r) => {
                let mut stub = functor!("unify_value", 1, [heap_str!(h + 2)]);
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &FactInstruction::UnifyVoid(vars) =>
                functor!("unify_void", 1, [heap_integer!(Integer::from(vars))])
        }
    }
}

#[derive(Clone)]
pub enum QueryInstruction {
    GetVariable(RegType, usize),
    PutConstant(Level, Constant, RegType),
    PutList(Level, RegType),
    PutStructure(ClauseType, usize, RegType),
    PutUnsafeValue(usize, usize),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetConstant(Constant),
    SetLocalValue(RegType),
    SetVariable(RegType),
    SetValue(RegType),
    SetVoid(usize)
}

impl QueryInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &QueryInstruction::PutUnsafeValue(norm, arg) =>
                functor!("put_unsafe_value", 2,
                         [heap_integer!(Integer::from(norm)),
                          heap_integer!(Integer::from(arg))]),
            &QueryInstruction::PutConstant(lvl, ref constant, r) => {
                let mut stub = functor!("put_constant", 3,
                                        [heap_str!(h + 4),
                                         heap_con!(constant.clone()),
                                         heap_str!(h + 6)]);

                stub.append(&mut lvl.into_functor());
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &QueryInstruction::PutList(lvl, r) => {
                let mut stub = functor!("put_list", 2,
                                        [heap_str!(h + 3),
                                         heap_str!(h + 5)]);

                stub.append(&mut lvl.into_functor());
                stub.append(&mut reg_type_into_functor(r));

                stub
            },
            &QueryInstruction::PutStructure(ref ct, arity, r) => {
                let mut stub = functor!("put_structure", 3,
                                        [heap_con!(Constant::Atom(ct.name(), None)),
                                         heap_integer!(Integer::from(arity)),
                                         heap_str!(h + 4)]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::PutValue(r, arg) => {
                let mut stub = functor!("put_value", 2,
                                        [heap_str!(h + 3),
                                         heap_integer!(Integer::from(arg))]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::GetVariable(r, arg) => {
                let mut stub = functor!("get_variable", 2,
                                        [heap_str!(h + 3),
                                         heap_integer!(Integer::from(arg))]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::PutVariable(r, arg) => {
                let mut stub = functor!("put_variable", 2,
                                        [heap_str!(h + 3),
                                         heap_integer!(Integer::from(arg))]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::SetConstant(ref constant) =>
                functor!("set_constant", 1, [heap_con!(constant.clone())]),
            &QueryInstruction::SetLocalValue(r) => {
                let mut stub = functor!("set_local_value", 1, [heap_str!(h + 2)]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::SetVariable(r) => {
                let mut stub = functor!("set_variable", 1, [heap_str!(h + 2)]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::SetValue(r) => {
                let mut stub = functor!("set_value", 1, [heap_str!(h + 2)]);

                stub.append(&mut reg_type_into_functor(r));
                stub
            },
            &QueryInstruction::SetVoid(vars) =>
                functor!("set_void", 1, [heap_integer!(Integer::from(vars))])
        }
    }
}

pub type CompiledFact = Vec<FactInstruction>;

pub type ThirdLevelIndex = Vec<IndexedChoiceInstruction>;

pub type Code = Vec<Line>;

pub type CodeDeque = VecDeque<Line>;
