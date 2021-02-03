use crate::prolog_parser_rebis::ast::*;

use crate::clause_types::*;
use crate::forms::*;
use crate::indexing::IndexingCodePtr;
use crate::machine::heap::*;
use crate::machine::machine_errors::MachineStub;
use crate::machine::machine_indices::*;
use crate::rug::Integer;

use crate::indexmap::IndexMap;

use slice_deque::SliceDeque;

use std::rc::Rc;

fn reg_type_into_functor(r: RegType) -> MachineStub {
    match r {
        RegType::Temp(r) => functor!("x", [integer(r)]),
        RegType::Perm(r) => functor!("y", [integer(r)]),
    }
}

impl Level {
    fn into_functor(self) -> MachineStub {
        match self {
            Level::Root => functor!("level", [atom("root")]),
            Level::Shallow => functor!("level", [atom("shallow")]),
            Level::Deep => functor!("level", [atom("deep")]),
        }
    }
}

impl ArithmeticTerm {
    fn into_functor(&self) -> MachineStub {
        match self {
            &ArithmeticTerm::Reg(r) => {
                reg_type_into_functor(r)
            }
            &ArithmeticTerm::Interm(i) => {
                functor!("intermediate", [integer(i)])
            }
            &ArithmeticTerm::Number(ref n) => {
                vec![n.clone().into()]
            }
        }
    }
}

#[derive(Debug)]
pub enum ChoiceInstruction {
    DefaultRetryMeElse(usize),
    DefaultTrustMe(usize),
    RetryMeElse(usize),
    TrustMe(usize),
    TryMeElse(usize),
}

impl ChoiceInstruction {
    pub fn to_functor(&self) -> MachineStub {
        match self {
            &ChoiceInstruction::TryMeElse(offset) => {
                functor!("try_me_else", [integer(offset)])
            }
            &ChoiceInstruction::RetryMeElse(offset) => {
                functor!("retry_me_else", [integer(offset)])
            }
            &ChoiceInstruction::TrustMe(offset) => {
                functor!("trust_me", [integer(offset)])
            }
            &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                functor!("default_retry_me_else", [integer(offset)])
            }
            &ChoiceInstruction::DefaultTrustMe(offset) => {
                functor!("default_trust_me", [integer(offset)])
            }
        }
    }
}

#[derive(Debug)]
pub enum CutInstruction {
    Cut(RegType),
    GetLevel(RegType),
    GetLevelAndUnify(RegType),
    NeckCut,
}

impl CutInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &CutInstruction::Cut(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!("cut", [aux(h, 0)], [rt_stub])
            }
            &CutInstruction::GetLevel(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!("get_level", [aux(h, 0)], [rt_stub])
            }
            &CutInstruction::GetLevelAndUnify(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!("get_level_and_unify", [aux(h, 0)], [rt_stub])
            }
            &CutInstruction::NeckCut => {
                functor!("neck_cut")
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum IndexedChoiceInstruction {
    Retry(usize),
    Trust(usize),
    Try(usize),
}

impl IndexedChoiceInstruction {
    pub fn offset(&self) -> usize {
        match self {
            &IndexedChoiceInstruction::Retry(offset) => offset,
            &IndexedChoiceInstruction::Trust(offset) => offset,
            &IndexedChoiceInstruction::Try(offset) => offset,
        }
    }

    pub fn to_functor(&self) -> MachineStub {
        match self {
            &IndexedChoiceInstruction::Try(offset) => {
                functor!("try", [integer(offset)])
            }
            &IndexedChoiceInstruction::Trust(offset) => {
                functor!("trust", [integer(offset)])
            }
            &IndexedChoiceInstruction::Retry(offset) => {
                functor!("retry", [integer(offset)])
            }
        }
    }
}

/// A `Line` is an instruction (cf. page 98 of wambook).
#[derive(Debug)]
pub enum IndexingLine {
    Indexing(IndexingInstruction),
    IndexedChoice(SliceDeque<IndexedChoiceInstruction>),
}

impl From<IndexingInstruction> for IndexingLine {
    #[inline]
    fn from(instr: IndexingInstruction) -> Self {
        IndexingLine::Indexing(instr)
    }
}

impl From<SliceDeque<IndexedChoiceInstruction>> for IndexingLine {
    #[inline]
    fn from(instrs: SliceDeque<IndexedChoiceInstruction>) -> Self {
        IndexingLine::IndexedChoice(instrs)
    }
}

#[derive(Debug)]
pub enum Line {
    Arithmetic(ArithmeticInstruction),
    Choice(ChoiceInstruction),
    Control(ControlInstruction),
    Cut(CutInstruction),
    Fact(FactInstruction),
    IndexingCode(Vec<IndexingLine>),
    IndexedChoice(IndexedChoiceInstruction),
    Query(QueryInstruction),
}

impl Line {
    #[inline]
    pub fn is_head_instr(&self) -> bool {
        match self {
            &Line::Cut(_) => true,
            &Line::Fact(_) => true,
            &Line::Query(_) => true,
            _ => false,
        }
    }

    pub fn enqueue_functors(&self, mut h: usize, functors: &mut Vec<MachineStub>) {
        match self {
            &Line::Arithmetic(ref arith_instr) =>
                functors.push(arith_instr.to_functor(h)),
            &Line::Choice(ref choice_instr) =>
                functors.push(choice_instr.to_functor()),
            &Line::Control(ref control_instr) =>
                functors.push(control_instr.to_functor()),
            &Line::Cut(ref cut_instr) =>
                functors.push(cut_instr.to_functor(h)),
            &Line::Fact(ref fact_instr) =>
                functors.push(fact_instr.to_functor(h)),
            &Line::IndexingCode(ref indexing_instrs) => {
                for indexing_instr in indexing_instrs {
                    match indexing_instr {
                        IndexingLine::Indexing(indexing_instr) => {
                            let section = indexing_instr.to_functor(h);
                            h += section.len();
                            functors.push(section);
                        }
                        IndexingLine::IndexedChoice(indexed_choice_instrs) => {
                            for indexed_choice_instr in indexed_choice_instrs {
                                let section = indexed_choice_instr.to_functor();
                                h += section.len();
                                functors.push(section);
                            }
                        }
                    }
                }
            }
            &Line::IndexedChoice(ref indexed_choice_instr) =>
                functors.push(indexed_choice_instr.to_functor()),
            &Line::Query(ref query_instr) =>
                functors.push(query_instr.to_functor(h)),
        }
    }
}

#[inline]
pub fn to_indexing_line_mut(line: &mut Line) -> Option<&mut Vec<IndexingLine>> {
    match line {
        Line::IndexingCode(ref mut indexing_code) => {
            Some(indexing_code)
        }
        _ => {
            None
        }
    }
}

#[inline]
pub fn to_indexing_line(line: &Line) -> Option<&Vec<IndexingLine>> {
    match line {
        Line::IndexingCode(ref indexing_code) => {
            Some(indexing_code)
        }
        _ => {
            None
        }
    }
}

#[derive(Debug, Clone)]
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
    Gcd(ArithmeticTerm, ArithmeticTerm, usize),
    Sign(ArithmeticTerm, usize),
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
    BitwiseComplement(ArithmeticTerm, usize),
}

fn arith_instr_unary_functor(
    h: usize,
    name: &'static str,
    at: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_stub = at.into_functor();

    functor!(
        name,
        [aux(h, 0), integer(t)],
        [at_stub]
    )
}

fn arith_instr_bin_functor(
    h: usize,
    name: &'static str,
    at_1: &ArithmeticTerm,
    at_2: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_1_stub = at_1.into_functor();
    let at_2_stub = at_2.into_functor();

    functor!(
        name,
        [aux(h, 0), aux(h, 1), integer(t)],
        [at_1_stub, at_2_stub]
    )
}

impl ArithmeticInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &ArithmeticInstruction::Add(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "add", at_1, at_2, t)
            }
            &ArithmeticInstruction::Sub(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "sub", at_1, at_2, t)
            }
            &ArithmeticInstruction::Mul(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "mul", at_1, at_2, t)
            }
            &ArithmeticInstruction::IntPow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "int_pow", at_1, at_2, t)
            }
            &ArithmeticInstruction::Pow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "pow", at_1, at_2, t)
            }
            &ArithmeticInstruction::IDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "idiv", at_1, at_2, t)
            }
            &ArithmeticInstruction::Max(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "max", at_1, at_2, t)
            }
            &ArithmeticInstruction::Min(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "min", at_1, at_2, t)
            }
            &ArithmeticInstruction::IntFloorDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "int_floor_div", at_1, at_2, t)
            }
            &ArithmeticInstruction::RDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "rdiv", at_1, at_2, t)
            }
            &ArithmeticInstruction::Div(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "div", at_1, at_2, t)
            }
            &ArithmeticInstruction::Shl(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "shl", at_1, at_2, t)
            }
            &ArithmeticInstruction::Shr(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "shr", at_1, at_2, t)
            }
            &ArithmeticInstruction::Xor(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "xor", at_1, at_2, t)
            }
            &ArithmeticInstruction::And(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "and", at_1, at_2, t)
            }
            &ArithmeticInstruction::Or(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "or", at_1, at_2, t)
            }
            &ArithmeticInstruction::Mod(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "mod", at_1, at_2, t)
            }
            &ArithmeticInstruction::Rem(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "rem", at_1, at_2, t)
            }
            &ArithmeticInstruction::ATan2(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "rem", at_1, at_2, t)
            }
            &ArithmeticInstruction::Gcd(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, "gcd", at_1, at_2, t)
            }
            &ArithmeticInstruction::Sign(ref at, t) => {
                arith_instr_unary_functor(h, "sign", at, t)
            }
            &ArithmeticInstruction::Cos(ref at, t)  => {
                arith_instr_unary_functor(h, "cos", at, t)
            }
            &ArithmeticInstruction::Sin(ref at, t)  => {
                arith_instr_unary_functor(h, "sin", at, t)
            }
            &ArithmeticInstruction::Tan(ref at, t)  => {
                arith_instr_unary_functor(h, "tan", at, t)
            }
            &ArithmeticInstruction::Log(ref at, t)  => {
                arith_instr_unary_functor(h, "log", at, t)
            }
            &ArithmeticInstruction::Exp(ref at, t)  => {
                arith_instr_unary_functor(h, "exp", at, t)
            }
            &ArithmeticInstruction::ACos(ref at, t) => {
                arith_instr_unary_functor(h, "acos", at, t)
            }
            &ArithmeticInstruction::ASin(ref at, t) => {
                arith_instr_unary_functor(h, "asin", at, t)
            }
            &ArithmeticInstruction::ATan(ref at, t) => {
                arith_instr_unary_functor(h, "atan", at, t)
            }
            &ArithmeticInstruction::Sqrt(ref at, t) => {
                arith_instr_unary_functor(h, "sqrt", at, t)
            }
            &ArithmeticInstruction::Abs(ref at, t) => {
                arith_instr_unary_functor(h, "abs", at, t)
            }
            &ArithmeticInstruction::Float(ref at, t) => {
                arith_instr_unary_functor(h, "float", at, t)
            }
            &ArithmeticInstruction::Truncate(ref at, t) => {
                arith_instr_unary_functor(h, "truncate", at, t)
            }
            &ArithmeticInstruction::Round(ref at, t) => {
                arith_instr_unary_functor(h, "round", at, t)
            }
            &ArithmeticInstruction::Ceiling(ref at, t) => {
                arith_instr_unary_functor(h, "ceiling", at, t)
            }
            &ArithmeticInstruction::Floor(ref at, t) => {
                arith_instr_unary_functor(h, "floor", at, t)
            }
            &ArithmeticInstruction::Neg(ref at, t) => {
                arith_instr_unary_functor(h, "-", at, t)
            }
            &ArithmeticInstruction::Plus(ref at, t) => {
                arith_instr_unary_functor(h, "+", at, t)
            }
            &ArithmeticInstruction::BitwiseComplement(ref at, t) => {
                arith_instr_unary_functor(h, "\\", at, t)
            }
        }
    }
}

#[derive(Debug)]
pub enum ControlInstruction {
    Allocate(usize), // num_frames.
    // name, arity, perm_vars after threshold, last call, use default call policy.
    CallClause(ClauseType, usize, usize, bool, bool),
    Deallocate,
    JmpBy(usize, usize, usize, bool), // arity, global_offset, perm_vars after threshold, last call.
    RevJmpBy(usize), // notice the lack of context change as in
                     // JmpBy. RevJmpBy is used only to patch extensible
                     // predicates together.
    Proceed,
}

impl ControlInstruction {
    pub fn perm_vars(&self) -> Option<usize> {
        match self {
            ControlInstruction::CallClause(_, _, num_cells, ..) =>
                Some(*num_cells),
            ControlInstruction::JmpBy(_, _, num_cells, ..) =>
                Some(*num_cells),
            _ =>
                None
        }
    }

    pub fn to_functor(&self) -> MachineStub {
        match self {
            &ControlInstruction::Allocate(num_frames) => {
                functor!("allocate", [integer(num_frames)])
            }
            &ControlInstruction::CallClause(ref ct, arity, _, false, _) => {
                functor!("call", [clause_name(ct.name()), integer(arity)])
            }
            &ControlInstruction::CallClause(ref ct, arity, _, true, _) => {
                functor!("execute", [clause_name(ct.name()), integer(arity)])
            }
            &ControlInstruction::Deallocate => {
                functor!("deallocate")
            }
            &ControlInstruction::JmpBy(_, offset, ..) => {
                functor!("jmp_by", [integer(offset)])
            }
            &ControlInstruction::RevJmpBy(offset) => {
                functor!("rev_jmp_by", [integer(offset)])
            }
            &ControlInstruction::Proceed => {
                functor!("proceed")
            }
        }
    }
}

/// `IndexingInstruction` cf. page 110 of wambook.
#[derive(Debug)]
pub enum IndexingInstruction {
    // The first index is the optimal argument being indexed.
    SwitchOnTerm(usize, usize, IndexingCodePtr, IndexingCodePtr, IndexingCodePtr),
    SwitchOnConstant(IndexMap<Constant, IndexingCodePtr>),
    SwitchOnStructure(IndexMap<(ClauseName, usize), IndexingCodePtr>),
}

impl IndexingInstruction {
    pub fn to_functor(&self, mut h: usize) -> MachineStub {
        match self {
            &IndexingInstruction::SwitchOnTerm(arg, vars, constants, lists, structures) => {
                functor!(
                    "switch_on_term",
                    [integer(arg),
                     integer(vars),
                     indexing_code_ptr(h, constants),
                     indexing_code_ptr(h, lists),
                     indexing_code_ptr(h, structures)]
                )
            }
            &IndexingInstruction::SwitchOnConstant(ref constants) => {
                let mut key_value_list_stub = vec![];
                let orig_h = h;

                h += 2; // skip the 2-cell "switch_on_constant" functor.

                for (c, ptr) in constants.iter() {
                    let key_value_pair = functor!(
                        ":",
                        SharedOpDesc::new(600, XFY),
                        [constant(c),
                         indexing_code_ptr(h + 3, *ptr)]
                    );

                    key_value_list_stub.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
                    key_value_list_stub.push(HeapCellValue::Addr(Addr::Str(h + 3)));
                    key_value_list_stub.push(HeapCellValue::Addr(
                        Addr::HeapCell(h + 3 + key_value_pair.len())
                    ));

                    h += key_value_pair.len() + 3;
                    key_value_list_stub.extend(key_value_pair.into_iter());
                }

                key_value_list_stub.push(HeapCellValue::Addr(Addr::EmptyList));

                functor!(
                    "switch_on_constant",
                    [aux(orig_h, 0)],
                    [key_value_list_stub]
                )
            }
            &IndexingInstruction::SwitchOnStructure(ref structures) => {
                let mut key_value_list_stub = vec![];
                let orig_h = h;

                h += 2; // skip the 2-cell "switch_on_constant" functor.

                for ((name, arity), ptr) in structures.iter() {
                    let predicate_indicator_stub = functor!(
                        "/",
                        SharedOpDesc::new(400, YFX),
                        [clause_name(name.clone()),
                         integer(*arity)]
                    );

                    let key_value_pair = functor!(
                        ":",
                        SharedOpDesc::new(600, XFY),
                        [aux(h + 3, 0),
                         indexing_code_ptr(h + 3, *ptr)],
                        [predicate_indicator_stub]
                    );

                    key_value_list_stub.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
                    key_value_list_stub.push(HeapCellValue::Addr(Addr::Str(h + 3)));
                    key_value_list_stub.push(HeapCellValue::Addr(
                        Addr::HeapCell(h + 3 + key_value_pair.len())
                    ));

                    h += key_value_pair.len() + 3;
                    key_value_list_stub.extend(key_value_pair.into_iter());
                }

                key_value_list_stub.push(HeapCellValue::Addr(Addr::EmptyList));

                functor!(
                    "switch_on_structure",
                    [aux(orig_h, 0)],
                    [key_value_list_stub]
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum FactInstruction {
    GetConstant(Level, Constant, RegType),
    GetList(Level, RegType),
    GetPartialString(Level, String, RegType, bool),
    GetStructure(ClauseType, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),
    UnifyConstant(Constant),
    UnifyLocalValue(RegType),
    UnifyVariable(RegType),
    UnifyValue(RegType),
    UnifyVoid(usize),
}

impl FactInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &FactInstruction::GetConstant(lvl, ref c, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "get_constant",
                    [aux(h, 0), constant(h, c), aux(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "get_list",
                    [aux(h, 0), aux(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetPartialString(lvl, ref s, r, has_tail) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "get_partial_string",
                    [aux(h, 0), string(h, s), aux(h, 1), boolean(has_tail)],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetStructure(ref ct, arity, r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "get_structure",
                    [clause_name(ct.name()), integer(arity), aux(h, 0)],
                    [rt_stub]
                )
            }
            &FactInstruction::GetValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "get_value",
                    [aux(h, 0), integer(arg)],
                    [rt_stub]
                )
            }
            &FactInstruction::GetVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "get_variable",
                    [aux(h, 0), integer(arg)],
                    [rt_stub]
                )
            }
            &FactInstruction::UnifyConstant(ref c) => {
                functor!("unify_constant", [constant(h, c)], [])
            }
            &FactInstruction::UnifyLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "unify_local_value",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &FactInstruction::UnifyVariable(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "unify_variable",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &FactInstruction::UnifyValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "unify_value",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &FactInstruction::UnifyVoid(vars) => {
                functor!("unify_void", [integer(vars)])
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum QueryInstruction {
    GetVariable(RegType, usize),
    PutConstant(Level, Constant, RegType),
    PutList(Level, RegType),
    PutPartialString(Level, String, RegType, bool),
    PutStructure(ClauseType, usize, RegType),
    PutUnsafeValue(usize, usize),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetConstant(Constant),
    SetLocalValue(RegType),
    SetVariable(RegType),
    SetValue(RegType),
    SetVoid(usize),
}

impl QueryInstruction {
    pub fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &QueryInstruction::PutUnsafeValue(norm, arg) => functor!(
                "put_unsafe_value",
                [integer(norm), integer(arg)]
            ),
            &QueryInstruction::PutConstant(lvl, ref c, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "put_constant",
                    [aux(h, 0), constant(h, c), aux(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "put_list",
                    [aux(h, 0), aux(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutPartialString(lvl, ref s, r, has_tail) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub  = reg_type_into_functor(r);

                functor!(
                    "put_partial_string",
                    [aux(h, 0), string(h, s), aux(h, 1), boolean(has_tail)],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutStructure(ref ct, arity, r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "put_structure",
                    [clause_name(ct.name()), integer(arity), aux(h, 0)],
                    [rt_stub]
                )
            }
            &QueryInstruction::PutValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "put_value",
                    [aux(h, 0), integer(arg)],
                    [rt_stub]
                )
            }
            &QueryInstruction::GetVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "get_variable",
                    [aux(h, 0), integer(arg)],
                    [rt_stub]
                )
            }
            &QueryInstruction::PutVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "put_variable",
                    [aux(h, 0), integer(arg)],
                    [rt_stub]
                )
            }
            &QueryInstruction::SetConstant(ref c) => {
                functor!("set_constant", [constant(h, c)], [])
            }
            &QueryInstruction::SetLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "set_local_value",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &QueryInstruction::SetVariable(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "set_variable",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &QueryInstruction::SetValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    "set_value",
                    [aux(h, 0)],
                    [rt_stub]
                )
            }
            &QueryInstruction::SetVoid(vars) => {
                functor!("set_void", [integer(vars)])
            }
        }
    }
}

pub type CompiledFact = Vec<FactInstruction>;

pub type Code = Vec<Line>;
