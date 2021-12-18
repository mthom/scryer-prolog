use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;

use crate::clause_types::*;
use crate::forms::*;
use crate::types::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::MachineStub;

use indexmap::IndexMap;
use slice_deque::SliceDeque;

fn reg_type_into_functor(r: RegType) -> MachineStub {
    match r {
        RegType::Temp(r) => functor!(atom!("x"), [fixnum(r)]),
        RegType::Perm(r) => functor!(atom!("y"), [fixnum(r)]),
    }
}

impl Level {
    fn into_functor(self) -> MachineStub {
        match self {
            Level::Root => functor!(atom!("level"), [atom(atom!("root"))]),
            Level::Shallow => functor!(atom!("level"), [atom(atom!("shallow"))]),
            Level::Deep => functor!(atom!("level"), [atom(atom!("deep"))]),
        }
    }
}

impl ArithmeticTerm {
    fn into_functor(&self, arena: &mut Arena) -> MachineStub {
        match self {
            &ArithmeticTerm::Reg(r) => reg_type_into_functor(r),
            &ArithmeticTerm::Interm(i) => {
                functor!(atom!("intermediate"), [fixnum(i)])
            }
            &ArithmeticTerm::Number(n) => {
                vec![HeapCellValue::from((n, arena))]
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum NextOrFail {
    Next(usize),
    Fail(usize),
}

impl NextOrFail {
    #[inline]
    pub fn is_next(&self) -> bool {
        if let NextOrFail::Next(_) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Death {
    Finite(usize),
    Infinity,
}

#[derive(Debug)]
pub(crate) enum ChoiceInstruction {
    DynamicElse(usize, Death, NextOrFail),
    DynamicInternalElse(usize, Death, NextOrFail),
    DefaultRetryMeElse(usize),
    DefaultTrustMe(usize),
    RetryMeElse(usize),
    TrustMe(usize),
    TryMeElse(usize),
}

impl ChoiceInstruction {
    pub(crate) fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &ChoiceInstruction::DynamicElse(birth, death, next_or_fail) => {
                match (death, next_or_fail) {
                    (Death::Infinity, NextOrFail::Next(i)) => {
                        functor!(
                            atom!("dynamic_else"),
                            [fixnum(birth), atom(atom!("inf")), fixnum(i)]
                        )
                    }
                    (Death::Infinity, NextOrFail::Fail(i)) => {
                        let next_functor = functor!(atom!("fail"), [fixnum(i)]);

                        functor!(
                            atom!("dynamic_else"),
                            [fixnum(birth), atom(atom!("inf")), str(h, 0)],
                            [next_functor]
                        )
                    }
                    (Death::Finite(d), NextOrFail::Fail(i)) => {
                        let next_functor = functor!(atom!("fail"), [fixnum(i)]);

                        functor!(
                            atom!("dynamic_else"),
                            [fixnum(birth), fixnum(d), str(h, 0)],
                            [next_functor]
                        )
                    }
                    (Death::Finite(d), NextOrFail::Next(i)) => {
                        functor!(atom!("dynamic_else"), [fixnum(birth), fixnum(d), fixnum(i)])
                    }
                }
            }
            &ChoiceInstruction::DynamicInternalElse(birth, death, next_or_fail) => {
                match (death, next_or_fail) {
                    (Death::Infinity, NextOrFail::Next(i)) => {
                        functor!(
                            atom!("dynamic_internal_else"),
                            [fixnum(birth), atom(atom!("inf")), fixnum(i)]
                        )
                    }
                    (Death::Infinity, NextOrFail::Fail(i)) => {
                        let next_functor = functor!(atom!("fail"), [fixnum(i)]);

                        functor!(
                            atom!("dynamic_internal_else"),
                            [fixnum(birth), atom(atom!("inf")), str(h, 0)],
                            [next_functor]
                        )
                    }
                    (Death::Finite(d), NextOrFail::Fail(i)) => {
                        let next_functor = functor!(atom!("fail"), [fixnum(i)]);

                        functor!(
                            atom!("dynamic_internal_else"),
                            [fixnum(birth), fixnum(d), str(h, 0)],
                            [next_functor]
                        )
                    }
                    (Death::Finite(d), NextOrFail::Next(i)) => {
                        functor!(
                            atom!("dynamic_internal_else"),
                            [fixnum(birth), fixnum(d), fixnum(i)]
                        )
                    }
                }
            }
            &ChoiceInstruction::TryMeElse(offset) => {
                functor!(atom!("try_me_else"), [fixnum(offset)])
            }
            &ChoiceInstruction::RetryMeElse(offset) => {
                functor!(atom!("retry_me_else"), [fixnum(offset)])
            }
            &ChoiceInstruction::TrustMe(offset) => {
                functor!(atom!("trust_me"), [fixnum(offset)])
            }
            &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                functor!(atom!("default_retry_me_else"), [fixnum(offset)])
            }
            &ChoiceInstruction::DefaultTrustMe(offset) => {
                functor!(atom!("default_trust_me"), [fixnum(offset)])
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum CutInstruction {
    Cut(RegType),
    GetLevel(RegType),
    GetLevelAndUnify(RegType),
    NeckCut,
}

impl CutInstruction {
    pub(crate) fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &CutInstruction::Cut(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("cut"), [str(h, 0)], [rt_stub])
            }
            &CutInstruction::GetLevel(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_level"), [str(h, 0)], [rt_stub])
            }
            &CutInstruction::GetLevelAndUnify(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_level_and_unify"), [str(h, 0)], [rt_stub])
            }
            &CutInstruction::NeckCut => {
                functor!(atom!("neck_cut"))
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum IndexedChoiceInstruction {
    Retry(usize),
    Trust(usize),
    Try(usize),
}

impl IndexedChoiceInstruction {
    pub(crate) fn offset(&self) -> usize {
        match self {
            &IndexedChoiceInstruction::Retry(offset) => offset,
            &IndexedChoiceInstruction::Trust(offset) => offset,
            &IndexedChoiceInstruction::Try(offset) => offset,
        }
    }

    pub(crate) fn to_functor(&self) -> MachineStub {
        match self {
            &IndexedChoiceInstruction::Try(offset) => {
                functor!(atom!("try"), [fixnum(offset)])
            }
            &IndexedChoiceInstruction::Trust(offset) => {
                functor!(atom!("trust"), [fixnum(offset)])
            }
            &IndexedChoiceInstruction::Retry(offset) => {
                functor!(atom!("retry"), [fixnum(offset)])
            }
        }
    }
}

/// A `Line` is an instruction (cf. page 98 of wambook).
#[derive(Debug)]
pub(crate) enum IndexingLine {
    Indexing(IndexingInstruction),
    IndexedChoice(SliceDeque<IndexedChoiceInstruction>),
    DynamicIndexedChoice(SliceDeque<usize>),
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
pub(crate) enum Line {
    Arithmetic(ArithmeticInstruction),
    Choice(ChoiceInstruction),
    Control(ControlInstruction),
    Cut(CutInstruction),
    Fact(FactInstruction),
    IndexingCode(Vec<IndexingLine>),
    IndexedChoice(IndexedChoiceInstruction),
    DynamicIndexedChoice(usize),
    Query(QueryInstruction),
}

impl Line {
    #[inline]
    pub(crate) fn is_head_instr(&self) -> bool {
        match self {
            &Line::Fact(_) => true,
            &Line::Query(_) => true,
            _ => false,
        }
    }

    pub(crate) fn enqueue_functors(
        &self,
        mut h: usize,
        arena: &mut Arena,
        functors: &mut Vec<MachineStub>,
    ) {
        match self {
            &Line::Arithmetic(ref arith_instr) => {
                functors.push(arith_instr.to_functor(h, arena))
            }
            &Line::Choice(ref choice_instr) => functors.push(choice_instr.to_functor(h)),
            &Line::Control(ref control_instr) => functors.push(control_instr.to_functor()),
            &Line::Cut(ref cut_instr) => functors.push(cut_instr.to_functor(h)),
            &Line::Fact(ref fact_instr) => functors.push(fact_instr.to_functor(h)),
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
                        IndexingLine::DynamicIndexedChoice(indexed_choice_instrs) => {
                            for indexed_choice_instr in indexed_choice_instrs {
                                let section = functor!(
                                    atom!("dynamic"),
                                    [fixnum(*indexed_choice_instr)]
                                );

                                h += section.len();
                                functors.push(section);
                            }
                        }
                    }
                }
            }
            &Line::IndexedChoice(ref indexed_choice_instr) => {
                functors.push(indexed_choice_instr.to_functor())
            }
            &Line::DynamicIndexedChoice(ref indexed_choice_instr) => {
                functors.push(functor!(atom!("dynamic"), [fixnum(*indexed_choice_instr)]));
            }
            &Line::Query(ref query_instr) => functors.push(query_instr.to_functor(h)),
        }
    }
}

#[inline]
pub(crate) fn to_indexing_line_mut(line: &mut Line) -> Option<&mut Vec<IndexingLine>> {
    match line {
        Line::IndexingCode(ref mut indexing_code) => Some(indexing_code),
        _ => None,
    }
}

#[inline]
pub(crate) fn to_indexing_line(line: &Line) -> Option<&Vec<IndexingLine>> {
    match line {
        Line::IndexingCode(ref indexing_code) => Some(indexing_code),
        _ => None,
    }
}

#[derive(Debug, Copy, Clone)]
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
    name: Atom,
    arena: &mut Arena,
    at: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_stub = at.into_functor(arena);
    functor!(name, [str(h, 0), fixnum(t)], [at_stub])
}

fn arith_instr_bin_functor(
    h: usize,
    name: Atom,
    arena: &mut Arena,
    at_1: &ArithmeticTerm,
    at_2: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_1_stub = at_1.into_functor(arena);
    let at_2_stub = at_2.into_functor(arena);

    functor!(
        name,
        [str(h, 0), str(h, 1), fixnum(t)],
        [at_1_stub, at_2_stub]
    )
}

impl ArithmeticInstruction {
    pub(crate) fn to_functor(
        &self,
        h: usize,
        arena: &mut Arena,
    ) -> MachineStub {
        match self {
            &ArithmeticInstruction::Add(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("add"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Sub(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("sub"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Mul(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("mul"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::IntPow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("int_pow"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Pow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("pow"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::IDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("idiv"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Max(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("max"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Min(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("min"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::IntFloorDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("int_floor_div"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::RDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("rdiv"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Div(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("div"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Shl(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("shl"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Shr(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("shr"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Xor(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("xor"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::And(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("and"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Or(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("or"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Mod(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("mod"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Rem(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("rem"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::ATan2(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("rem"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Gcd(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(h, atom!("gcd"), arena, at_1, at_2, t)
            }
            &ArithmeticInstruction::Sign(ref at, t) => {
                arith_instr_unary_functor(h, atom!("sign"), arena, at, t)
            }
            &ArithmeticInstruction::Cos(ref at, t) => {
                arith_instr_unary_functor(h, atom!("cos"), arena, at, t)
            }
            &ArithmeticInstruction::Sin(ref at, t) => {
                arith_instr_unary_functor(h, atom!("sin"), arena, at, t)
            }
            &ArithmeticInstruction::Tan(ref at, t) => {
                arith_instr_unary_functor(h, atom!("tan"), arena, at, t)
            }
            &ArithmeticInstruction::Log(ref at, t) => {
                arith_instr_unary_functor(h, atom!("log"), arena, at, t)
            }
            &ArithmeticInstruction::Exp(ref at, t) => {
                arith_instr_unary_functor(h, atom!("exp"), arena, at, t)
            }
            &ArithmeticInstruction::ACos(ref at, t) => {
                arith_instr_unary_functor(h, atom!("acos"), arena, at, t)
            }
            &ArithmeticInstruction::ASin(ref at, t) => {
                arith_instr_unary_functor(h, atom!("asin"), arena, at, t)
            }
            &ArithmeticInstruction::ATan(ref at, t) => {
                arith_instr_unary_functor(h, atom!("atan"), arena, at, t)
            }
            &ArithmeticInstruction::Sqrt(ref at, t) => {
                arith_instr_unary_functor(h, atom!("sqrt"), arena, at, t)
            }
            &ArithmeticInstruction::Abs(ref at, t) => {
                arith_instr_unary_functor(h, atom!("abs"), arena, at, t)
            }
            &ArithmeticInstruction::Float(ref at, t) => {
                arith_instr_unary_functor(h, atom!("float"), arena, at, t)
            }
            &ArithmeticInstruction::Truncate(ref at, t) => {
                arith_instr_unary_functor(h, atom!("truncate"), arena, at, t)
            }
            &ArithmeticInstruction::Round(ref at, t) => {
                arith_instr_unary_functor(h, atom!("round"), arena, at, t)
            }
            &ArithmeticInstruction::Ceiling(ref at, t) => {
                arith_instr_unary_functor(h, atom!("ceiling"), arena, at, t)
            }
            &ArithmeticInstruction::Floor(ref at, t) => {
                arith_instr_unary_functor(h, atom!("floor"), arena, at, t)
            }
            &ArithmeticInstruction::Neg(ref at, t) => arith_instr_unary_functor(
                h,
                atom!("-"),
                arena,
                at,
                t,
            ),
            &ArithmeticInstruction::Plus(ref at, t) => arith_instr_unary_functor(
                h,
                atom!("+"),
                arena,
                at,
                t,
            ),
            &ArithmeticInstruction::BitwiseComplement(ref at, t) => arith_instr_unary_functor(
                h,
                atom!("\\"),
                arena,
                at,
                t,
            ),
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
    RevJmpBy(usize),                  // notice the lack of context change as in
    // JmpBy. RevJmpBy is used only to patch extensible
    // predicates together.
    Proceed,
}

impl ControlInstruction {
    pub(crate) fn perm_vars(&self) -> Option<usize> {
        match self {
            ControlInstruction::CallClause(_, _, num_cells, ..) => Some(*num_cells),
            ControlInstruction::JmpBy(_, _, num_cells, ..) => Some(*num_cells),
            _ => None,
        }
    }

    pub(crate) fn to_functor(&self) -> MachineStub {
        match self {
            &ControlInstruction::Allocate(num_frames) => {
                functor!(atom!("allocate"), [fixnum(num_frames)])
            }
            &ControlInstruction::CallClause(ref ct, arity, _, false, _) => {
                functor!(atom!("call"), [atom(ct.name()), fixnum(arity)])
            }
            &ControlInstruction::CallClause(ref ct, arity, _, true, _) => {
                functor!(atom!("execute"), [atom(ct.name()), fixnum(arity)])
            }
            &ControlInstruction::Deallocate => {
                functor!(atom!("deallocate"))
            }
            &ControlInstruction::JmpBy(_, offset, ..) => {
                functor!(atom!("jmp_by"), [fixnum(offset)])
            }
            &ControlInstruction::RevJmpBy(offset) => {
                functor!(atom!("rev_jmp_by"), [fixnum(offset)])
            }
            &ControlInstruction::Proceed => {
                functor!(atom!("proceed"))
            }
        }
    }
}

/// `IndexingInstruction` cf. page 110 of wambook.
#[derive(Debug)]
pub(crate) enum IndexingInstruction {
    // The first index is the optimal argument being indexed.
    SwitchOnTerm(
        usize,
        IndexingCodePtr,
        IndexingCodePtr,
        IndexingCodePtr,
        IndexingCodePtr,
    ),
    SwitchOnConstant(IndexMap<Literal, IndexingCodePtr>),
    SwitchOnStructure(IndexMap<(Atom, usize), IndexingCodePtr>),
}

impl IndexingCodePtr {
    #[allow(dead_code)]
    pub(crate) fn to_functor(self) -> MachineStub {
        match self {
            IndexingCodePtr::DynamicExternal(o) => functor!(atom!("dynamic_external"), [fixnum(o)]),
            IndexingCodePtr::External(o) => functor!(atom!("external"), [fixnum(o)]),
            IndexingCodePtr::Internal(o) => functor!(atom!("internal"), [fixnum(o)]),
            IndexingCodePtr::Fail => {
                vec![atom_as_cell!(atom!("fail"))]
            },
        }
    }
}

impl IndexingInstruction {
    pub(crate) fn to_functor(&self, mut h: usize) -> MachineStub {
        match self {
            &IndexingInstruction::SwitchOnTerm(arg, vars, constants, lists, structures) => {
                functor!(
                    atom!("switch_on_term"),
                    [
                        fixnum(arg),
                        indexing_code_ptr(h, vars),
                        indexing_code_ptr(h, constants),
                        indexing_code_ptr(h, lists),
                        indexing_code_ptr(h, structures)
                    ]
                )
            }
            &IndexingInstruction::SwitchOnConstant(ref constants) => {
                let mut key_value_list_stub = vec![];
                let orig_h = h;

                h += 2; // skip the 2-cell "switch_on_constant" functor.

                for (c, ptr) in constants.iter() {
                    let key_value_pair = functor!(
                        atom!(":"),
                        [literal(*c), indexing_code_ptr(h + 3, *ptr)]
                    );

                    key_value_list_stub.push(list_loc_as_cell!(h + 1));
                    key_value_list_stub.push(str_loc_as_cell!(h + 3));
                    key_value_list_stub.push(heap_loc_as_cell!(h + 3 + key_value_pair.len()));

                    h += key_value_pair.len() + 3;
                    key_value_list_stub.extend(key_value_pair.into_iter());
                }

                key_value_list_stub.push(empty_list_as_cell!());

                functor!(
                    atom!("switch_on_constant"),
                    [str(orig_h, 0)],
                    [key_value_list_stub]
                )
            }
            &IndexingInstruction::SwitchOnStructure(ref structures) => {
                let mut key_value_list_stub = vec![];
                let orig_h = h;

                h += 2; // skip the 2-cell "switch_on_constant" functor.

                for ((name, arity), ptr) in structures.iter() {
                    let predicate_indicator_stub = functor!(
                        atom!("/"),
                        [atom(name), fixnum(*arity)]
                    );

                    let key_value_pair = functor!(
                        atom!(":"),
                        [str(h + 3, 0), indexing_code_ptr(h + 3, *ptr)],
                        [predicate_indicator_stub]
                    );

                    key_value_list_stub.push(list_loc_as_cell!(h + 1));
                    key_value_list_stub.push(str_loc_as_cell!(h + 3));
                    key_value_list_stub.push(heap_loc_as_cell!(h + 3 + key_value_pair.len()));

                    h += key_value_pair.len() + 3;
                    key_value_list_stub.extend(key_value_pair.into_iter());
                }

                key_value_list_stub.push(empty_list_as_cell!());

                functor!(
                    atom!("switch_on_structure"),
                    [str(orig_h, 0)],
                    [key_value_list_stub]
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum FactInstruction {
    GetConstant(Level, HeapCellValue, RegType),
    GetList(Level, RegType),
    GetPartialString(Level, Atom, RegType, bool),
    GetStructure(ClauseType, usize, RegType),
    GetValue(RegType, usize),
    GetVariable(RegType, usize),
    UnifyConstant(HeapCellValue),
    UnifyLocalValue(RegType),
    UnifyVariable(RegType),
    UnifyValue(RegType),
    UnifyVoid(usize),
}

impl FactInstruction {
    pub(crate) fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &FactInstruction::GetConstant(lvl, c, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_constant"),
                    [str(h, 0), cell(c), str(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_list"),
                    [str(h, 0), str(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetPartialString(lvl, s, r, has_tail) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_partial_string"),
                    [
                        str(h, 0),
                        string(h, s),
                        str(h, 1),
                        boolean(has_tail)
                    ],
                    [lvl_stub, rt_stub]
                )
            }
            &FactInstruction::GetStructure(ref ct, arity, r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_structure"),
                    [atom(ct.name()), fixnum(arity), str(h, 0)],
                    [rt_stub]
                )
            }
            &FactInstruction::GetValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("get_value"), [str(h, 0), fixnum(arg)], [rt_stub])
            }
            &FactInstruction::GetVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("get_variable"), [str(h, 0), fixnum(arg)], [rt_stub])
            }
            &FactInstruction::UnifyConstant(c) => {
                functor!(atom!("unify_constant"), [cell(c)])
            }
            &FactInstruction::UnifyLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("unify_local_value"), [str(h, 0)], [rt_stub])
            }
            &FactInstruction::UnifyVariable(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("unify_variable"), [str(h, 0)], [rt_stub])
            }
            &FactInstruction::UnifyValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("unify_value"), [str(h, 0)], [rt_stub])
            }
            &FactInstruction::UnifyVoid(vars) => {
                functor!(atom!("unify_void"), [fixnum(vars)])
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum QueryInstruction {
    GetVariable(RegType, usize),
    PutConstant(Level, HeapCellValue, RegType),
    PutList(Level, RegType),
    PutPartialString(Level, Atom, RegType, bool),
    PutStructure(ClauseType, usize, RegType),
    PutUnsafeValue(usize, usize),
    PutValue(RegType, usize),
    PutVariable(RegType, usize),
    SetConstant(HeapCellValue),
    SetLocalValue(RegType),
    SetVariable(RegType),
    SetValue(RegType),
    SetVoid(usize),
}

impl QueryInstruction {
    pub(crate) fn to_functor(&self, h: usize) -> MachineStub {
        match self {
            &QueryInstruction::PutUnsafeValue(norm, arg) => {
                functor!(atom!("put_unsafe_value"), [fixnum(norm), fixnum(arg)])
            }
            &QueryInstruction::PutConstant(lvl, c, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_constant"),
                    [str(h, 0), cell(c), str(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_list"),
                    [str(h, 0), str(h, 1)],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutPartialString(lvl, s, r, has_tail) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_partial_string"),
                    [
                        str(h, 0),
                        string(h, s),
                        str(h, 1),
                        boolean(has_tail)
                    ],
                    [lvl_stub, rt_stub]
                )
            }
            &QueryInstruction::PutStructure(ref ct, arity, r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_structure"),
                    [atom(ct.name()), fixnum(arity), str(h, 0)],
                    [rt_stub]
                )
            }
            &QueryInstruction::PutValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("put_value"), [str(h, 0), fixnum(arg)], [rt_stub])
            }
            &QueryInstruction::GetVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("get_variable"), [str(h, 0), fixnum(arg)], [rt_stub])
            }
            &QueryInstruction::PutVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("put_variable"), [str(h, 0), fixnum(arg)], [rt_stub])
            }
            &QueryInstruction::SetConstant(c) => {
                functor!(atom!("set_constant"), [cell(c)], [])
            }
            &QueryInstruction::SetLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("set_local_value"), [str(h, 0)], [rt_stub])
            }
            &QueryInstruction::SetVariable(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("set_variable"), [str(h, 0)], [rt_stub])
            }
            &QueryInstruction::SetValue(r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("set_value"), [str(h, 0)], [rt_stub])
            }
            &QueryInstruction::SetVoid(vars) => {
                functor!(atom!("set_void"), [fixnum(vars)])
            }
        }
    }
}

pub(crate) type CompiledFact = Vec<FactInstruction>;

pub(crate) type Code = Vec<Line>;
