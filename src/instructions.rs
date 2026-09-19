use crate::arena::*;
use crate::arithmetic::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::functor_macro::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::MachineStub;
use crate::machine::machine_indices::{CodeIndex, IndexingSpecs};
use crate::parser::ast::*;
use crate::types::*;

use fxhash::FxBuildHasher;
use hashbrown::hash_table::*;
use indexmap::IndexSet;
use modular_bitfield::specifiers::B63;
use modular_bitfield::{Specifier, bitfield};

use std::collections::VecDeque;
use std::fmt::Debug;
use std::rc::Rc;

include!(concat!(env!("OUT_DIR"), "/instructions.rs"));

fn reg_type_into_functor(r: RegType) -> MachineStub {
    match r {
        RegType::Temp(r) => functor!(atom!("x"), [fixnum(r)]),
        RegType::Perm(r) => functor!(atom!("y"), [fixnum(r)]),
    }
}

impl Level {
    fn into_functor(self) -> MachineStub {
        match self {
            Level::Root => functor!(atom!("level"), [atom_as_cell((atom!("root")))]),
            Level::Shallow => functor!(atom!("level"), [atom_as_cell((atom!("shallow")))]),
            Level::Deep => functor!(atom!("level"), [atom_as_cell((atom!("deep")))]),
        }
    }
}

impl ArithmeticTerm {
    fn into_functor(self, arena: &mut Arena) -> MachineStub {
        match self {
            ArithmeticTerm::Reg(r) => reg_type_into_functor(r),
            ArithmeticTerm::IntermReg(i) => {
                functor!(atom!("x"), [fixnum(i)])
            }
            ArithmeticTerm::Number(n) => {
                functor!(atom!("number"), [number(n, arena)])
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NextOrFail {
    Next(usize),
    Fail(usize),
}

impl Default for NextOrFail {
    fn default() -> Self {
        NextOrFail::Fail(0)
    }
}

impl NextOrFail {
    #[inline]
    pub fn is_next(&self) -> bool {
        matches!(self, NextOrFail::Next(_))
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Death {
    Finite(usize),
    #[default]
    Infinity,
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone)]
pub enum IndexedChoiceInstructionTable {
    SwitchOnTerm {
        arg_num: usize,
        constants: TermIndexingCodePtr<HeapCellValue>,
        lists: Option<IndexingCodePtr>,
        structures: TermIndexingCodePtr<(Atom, usize)>,
    },
    OnDemandTerm {
        arg_num: usize,
    },
    DeadIndices {
        arg_num: usize,
        indices: IndexSet<usize, FxBuildHasher>,
    },
}

impl IndexedChoiceInstructionTable {
    #[inline]
    pub(crate) fn arg_num(&self) -> usize {
        match *self {
            IndexedChoiceInstructionTable::SwitchOnTerm { arg_num, .. } => arg_num,
            IndexedChoiceInstructionTable::OnDemandTerm { arg_num } => arg_num,
            IndexedChoiceInstructionTable::DeadIndices { arg_num, .. } => arg_num,
        }
    }

    pub(crate) fn to_functor(&self) -> MachineStub {
        match *self {
            IndexedChoiceInstructionTable::SwitchOnTerm {
                arg_num,
                ref constants,
                ref lists,
                ref structures,
            } => {
                functor!(
                    atom!("switch_on_term"),
                    [
                        fixnum(arg_num),
                        term_indexing_code_ptr(constants),
                        indexing_code_ptr_opt(lists),
                        term_indexing_code_ptr(structures)
                    ]
                )
            }
            IndexedChoiceInstructionTable::OnDemandTerm { arg_num, .. } => {
                let rt_stub = reg_type_into_functor(temp_v!(arg_num));
                functor!(atom!("dindex_on_term"), [functor(rt_stub)])
            }
            IndexedChoiceInstructionTable::DeadIndices {
                arg_num,
                ref indices,
            } => {
                let offsets_list = variadic_functor(
                    atom!("offsets"),
                    1,
                    indices
                        .iter()
                        .cloned()
                        .map(|o| functor!(atom!("external"), [fixnum(o)])),
                );

                functor!(
                    atom!("dead_indices"),
                    [fixnum(arg_num), functor(offsets_list)]
                )
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum StaticIndexedChoiceInstructionOffset {
    Try(usize),
    Retry(usize),
    DefaultRetry(usize),
    Trust(usize),
    DefaultTrust(usize),
}

impl StaticIndexedChoiceInstructionOffset {
    pub(crate) fn to_functor(&self) -> MachineStub {
        let offset = self.offset() as i64;

        match self {
            StaticIndexedChoiceInstructionOffset::Try(_offset) => {
                functor!(atom!("try"), [fixnum(offset)])
            }
            StaticIndexedChoiceInstructionOffset::Trust(_offset) => {
                functor!(atom!("trust"), [fixnum(offset)])
            }
            StaticIndexedChoiceInstructionOffset::Retry(_offset) => {
                functor!(atom!("retry"), [fixnum(offset)])
            }
            StaticIndexedChoiceInstructionOffset::DefaultTrust(_offset) => {
                functor!(atom!("default_trust"), [fixnum(offset)])
            }
            StaticIndexedChoiceInstructionOffset::DefaultRetry(_offset) => {
                functor!(atom!("default_retry"), [fixnum(offset)])
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Appended {
    A(usize),
    Z(usize),
}

impl PartialOrd for Appended {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Appended {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Appended::A(x), Appended::A(y)) => y.cmp(x),
            (Appended::A(_x), Appended::Z(_y)) => std::cmp::Ordering::Less,
            (Appended::Z(_x), Appended::A(_y)) => std::cmp::Ordering::Greater,
            (Appended::Z(x), Appended::Z(y)) => x.cmp(y),
        }
    }
}

pub trait HasOffset {
    fn offset(&self) -> usize;
}

impl HasOffset for Appended {
    fn offset(&self) -> usize {
        match self {
            &Appended::A(offset) | &Appended::Z(offset) => offset,
        }
    }
}

impl HasOffset for StaticIndexedChoiceInstructionOffset {
    fn offset(&self) -> usize {
        match self {
            &StaticIndexedChoiceInstructionOffset::Try(offset)
            | &StaticIndexedChoiceInstructionOffset::Retry(offset)
            | &StaticIndexedChoiceInstructionOffset::Trust(offset)
            | &StaticIndexedChoiceInstructionOffset::DefaultRetry(offset)
            | &StaticIndexedChoiceInstructionOffset::DefaultTrust(offset) => offset,
        }
    }
}

pub trait SecondLevelIndexType {
    type ThirdLevelIndex: Copy + Debug + HasOffset;

    fn to_indexing_line(tbl: SecondLevelTable<Self>) -> IndexingLine;
    fn to_functor(offset: &Self::ThirdLevelIndex) -> MachineStub;
}

#[derive(Debug, Clone)]
pub struct StaticIndexedChoiceInstruction;
#[derive(Debug, Clone)]
pub struct DynamicIndexedChoiceInstruction;

#[derive(Debug, Clone)]
pub struct SecondLevelTable<I: ?Sized + SecondLevelIndexType> {
    pub tables: VecDeque<IndexedChoiceInstructionTable>,
    pub offsets: VecDeque<I::ThirdLevelIndex>,
}

impl<I: ?Sized + SecondLevelIndexType> SecondLevelTable<I> {
    pub fn new() -> Self {
        Self {
            tables: VecDeque::new(),
            offsets: VecDeque::new(),
        }
    }

    fn to_functors(&self) -> Vec<MachineStub> {
        let mut functors = Vec::with_capacity(self.tables.len() + self.offsets.len());

        for table in &self.tables {
            functors.push(table.to_functor());
        }

        for offset in &self.offsets {
            functors.push(I::to_functor(offset));
        }

        functors
    }
}

impl SecondLevelIndexType for StaticIndexedChoiceInstruction {
    type ThirdLevelIndex = StaticIndexedChoiceInstructionOffset;

    #[inline]
    fn to_indexing_line(tbl: SecondLevelTable<Self>) -> IndexingLine {
        IndexingLine::StaticIndexedChoice(tbl)
    }

    #[inline]
    fn to_functor(offset: &StaticIndexedChoiceInstructionOffset) -> MachineStub {
        offset.to_functor()
    }
}

impl SecondLevelIndexType for DynamicIndexedChoiceInstruction {
    type ThirdLevelIndex = Appended;

    #[inline]
    fn to_indexing_line(tbl: SecondLevelTable<Self>) -> IndexingLine {
        IndexingLine::DynamicIndexedChoice(tbl)
    }

    #[inline]
    fn to_functor(offset: &Appended) -> MachineStub {
        let offset = offset.offset() as i64;
        functor!(atom!("dynamic_else"), [fixnum(offset)])
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ExternalIndexingCodePtr {
    Static(usize),
    Dynamic(usize),
}

impl ExternalIndexingCodePtr {
    #[inline]
    pub fn offset(self) -> usize {
        match self {
            ExternalIndexingCodePtr::Static(offset) | ExternalIndexingCodePtr::Dynamic(offset) => {
                offset
            }
        }
    }

    pub(crate) fn set_offset(&mut self, old_v: usize) {
        match self {
            ExternalIndexingCodePtr::Static(offset) | ExternalIndexingCodePtr::Dynamic(offset) => {
                *offset = old_v;
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum TermIndexingCodePtr<KeyType: Debug + Clone> {
    External(KeyType, usize), // the index points past the indexing instruction prelude.
    Fail,
    Internal(KeyType, usize),
    SwitchOnType(Box<HashTable<(KeyType, IndexingCodePtr)>>),
}

impl TermIndexingCodePtr<HeapCellValue> {
    fn to_functor(&self) -> MachineStub {
        match self {
            &TermIndexingCodePtr::External(key, o) => {
                functor!(atom!("external"), [cell(key), fixnum(o)])
            }
            &TermIndexingCodePtr::Internal(key, o) => {
                functor!(atom!("internal"), [cell(key), fixnum(o)])
            }
            TermIndexingCodePtr::Fail => functor!(atom!("fail")),
            TermIndexingCodePtr::SwitchOnType(constants) => variadic_functor(
                atom!("switch_on_constants"),
                1,
                constants
                    .iter()
                    .map(|(c, ptr)| functor!(atom!(":"), [cell((*c)), indexing_code_ptr((*ptr))])),
            ),
        }
    }
}

impl<IndexKey: Debug + Clone> From<(IndexKey, IndexingCodePtr)> for TermIndexingCodePtr<IndexKey> {
    fn from((key, value): (IndexKey, IndexingCodePtr)) -> Self {
        let o = value.offset() as usize;

        match value.tag() {
            IndexingCodePtrTag::External => TermIndexingCodePtr::External(key, o),
            IndexingCodePtrTag::Internal => TermIndexingCodePtr::Internal(key, o),
        }
    }
}

impl TermIndexingCodePtr<(Atom, usize)> {
    fn to_functor(&self) -> MachineStub {
        match self {
            &TermIndexingCodePtr::External((name, arity), o) => {
                let pi_functor = functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)]);
                functor!(atom!("external"), [functor(pi_functor), fixnum(o)])
            }
            &TermIndexingCodePtr::Internal((name, arity), o) => {
                let pi_functor = functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)]);
                functor!(atom!("internal"), [functor(pi_functor), fixnum(o)])
            }
            TermIndexingCodePtr::Fail => functor!(atom!("fail")),
            TermIndexingCodePtr::SwitchOnType(structures) => variadic_functor(
                atom!("switch_on_structure"),
                1,
                structures.iter().map(|((name, arity), ptr)| {
                    functor!(
                        atom!(":"),
                        [
                            functor((atom!("/")), [atom_as_cell(name), fixnum((*arity))]),
                            indexing_code_ptr((*ptr))
                        ]
                    )
                }),
            ),
        }
    }
}

#[derive(Specifier, Debug, Clone, Copy, PartialEq, Eq)]
#[bits = 1]
pub enum IndexingCodePtrTag {
    External,
    Internal,
}

#[repr(u64)]
#[bitfield]
#[derive(Debug, Clone, Copy)]
pub struct IndexingCodePtr {
    pub tag: IndexingCodePtrTag,
    pub offset: B63,
}

impl IndexingCodePtr {
    pub fn external(o: usize) -> Self {
        IndexingCodePtr::new()
            .with_tag(IndexingCodePtrTag::External)
            .with_offset(o as u64)
    }

    pub fn internal(o: usize) -> Self {
        IndexingCodePtr::new()
            .with_tag(IndexingCodePtrTag::Internal)
            .with_offset(o as u64)
    }

    pub fn to_functor(self) -> MachineStub {
        let o = self.offset();

        match self.tag() {
            IndexingCodePtrTag::External => functor!(atom!("external"), [fixnum(o)]),
            IndexingCodePtrTag::Internal => functor!(atom!("internal"), [fixnum(o)]),
        }
    }
}

/// A `Line` is an instruction (cf. page 98 of wambook).
#[derive(Debug, Clone)]
pub enum IndexingLine {
    StaticIndexedChoice(SecondLevelTable<StaticIndexedChoiceInstruction>),
    DynamicIndexedChoice(SecondLevelTable<DynamicIndexedChoiceInstruction>),
}

impl IndexingLine {
    #[inline]
    pub fn tables_mut(&mut self) -> &mut VecDeque<IndexedChoiceInstructionTable> {
        match self {
            IndexingLine::StaticIndexedChoice(SecondLevelTable { tables, .. })
            | IndexingLine::DynamicIndexedChoice(SecondLevelTable { tables, .. }) => tables,
        }
    }

    pub fn tables(&self) -> &VecDeque<IndexedChoiceInstructionTable> {
        match self {
            IndexingLine::StaticIndexedChoice(SecondLevelTable { tables, .. })
            | IndexingLine::DynamicIndexedChoice(SecondLevelTable { tables, .. }) => tables,
        }
    }
}

fn arith_instr_unary_functor(
    name: Atom,
    arena: &mut Arena,
    at: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_stub = at.into_functor(arena);
    functor!(name, [functor(at_stub), fixnum(t)])
}

fn arith_instr_bin_functor(
    name: Atom,
    arena: &mut Arena,
    at_1: &ArithmeticTerm,
    at_2: &ArithmeticTerm,
    t: usize,
) -> MachineStub {
    let at_1_stub = at_1.into_functor(arena);
    let at_2_stub = at_2.into_functor(arena);

    functor!(name, [functor(at_1_stub), functor(at_2_stub), fixnum(t)])
}

pub type Code = Vec<Instruction>;
pub type CodeDeque = VecDeque<Instruction>;

impl Instruction {
    pub fn enqueue_functors(&self, arena: &mut Arena, functors: &mut Vec<MachineStub>) {
        match self {
            Instruction::IndexingCode { code, .. } => {
                for indexing_instr in code {
                    match indexing_instr {
                        IndexingLine::StaticIndexedChoice(indexing_instr) => {
                            functors.extend(indexing_instr.to_functors());
                        }
                        IndexingLine::DynamicIndexedChoice(indexed_choice_instrs) => {
                            functors.extend(indexed_choice_instrs.to_functors());
                        }
                    }
                }
            }
            instr => functors.push(instr.to_functor(arena)),
        }
    }

    fn to_functor(&self, arena: &mut Arena) -> MachineStub {
        match self {
            &Instruction::RunVerifyAttr => {
                functor!(atom!("run_verify_attr"))
            }
            &Instruction::DynamicElse(birth, death, next_or_fail) => match (death, next_or_fail) {
                (Death::Infinity, NextOrFail::Next(i)) => {
                    functor!(
                        atom!("dynamic_else"),
                        [fixnum(birth), atom_as_cell((atom!("inf"))), fixnum(i)]
                    )
                }
                (Death::Infinity, NextOrFail::Fail(i)) => {
                    functor!(
                        atom!("dynamic_else"),
                        [
                            fixnum(birth),
                            atom_as_cell((atom!("inf"))),
                            functor((atom!("fail")), [fixnum(i)])
                        ]
                    )
                }
                (Death::Finite(d), NextOrFail::Fail(i)) => {
                    functor!(
                        atom!("dynamic_else"),
                        [
                            fixnum(birth),
                            fixnum(d),
                            functor((atom!("fail")), [fixnum(i)])
                        ]
                    )
                }
                (Death::Finite(d), NextOrFail::Next(i)) => {
                    functor!(atom!("dynamic_else"), [fixnum(birth), fixnum(d), fixnum(i)])
                }
            },
            &Instruction::DynamicInternalElse(birth, death, next_or_fail) => {
                match (death, next_or_fail) {
                    (Death::Infinity, NextOrFail::Next(i)) => {
                        functor!(
                            atom!("dynamic_internal_else"),
                            [fixnum(birth), atom_as_cell((atom!("inf"))), fixnum(i)]
                        )
                    }
                    (Death::Infinity, NextOrFail::Fail(i)) => {
                        functor!(
                            atom!("dynamic_internal_else"),
                            [
                                fixnum(birth),
                                atom_as_cell((atom!("inf"))),
                                functor((atom!("fail")), [fixnum(i)])
                            ]
                        )
                    }
                    (Death::Finite(d), NextOrFail::Fail(i)) => {
                        functor!(
                            atom!("dynamic_internal_else"),
                            [
                                fixnum(birth),
                                fixnum(d),
                                functor((atom!("fail")), [fixnum(i)])
                            ]
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
            &Instruction::TryMeElse(offset) => {
                functor!(atom!("try_me_else"), [fixnum(offset)])
            }
            &Instruction::RetryMeElse(offset) => {
                functor!(atom!("retry_me_else"), [fixnum(offset)])
            }
            &Instruction::TrustMe(offset) => {
                functor!(atom!("trust_me"), [fixnum(offset)])
            }
            &Instruction::DefaultRetryMeElse(offset) => {
                functor!(atom!("default_retry_me_else"), [fixnum(offset)])
            }
            &Instruction::DefaultTrustMe(offset) => {
                functor!(atom!("default_trust_me"), [fixnum(offset)])
            }
            &Instruction::Cut(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("cut"), [functor(rt_stub)])
            }
            &Instruction::CutPrev(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("cut_prev"), [functor(rt_stub)])
            }
            &Instruction::GetLevel(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_level"), [functor(rt_stub)])
            }
            &Instruction::GetPrevLevel(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_prev_level"), [functor(rt_stub)])
            }
            &Instruction::GetCutPoint(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_cut_point"), [functor(rt_stub)])
            }
            &Instruction::NeckCut => {
                functor!(atom!("neck_cut"))
            }
            &Instruction::Add(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("add"), arena, at_1, at_2, t)
            }
            &Instruction::Sub(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("sub"), arena, at_1, at_2, t)
            }
            &Instruction::Mul(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("mul"), arena, at_1, at_2, t)
            }
            &Instruction::IntPow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("int_pow"), arena, at_1, at_2, t)
            }
            &Instruction::Pow(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("pow"), arena, at_1, at_2, t)
            }
            &Instruction::IDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("idiv"), arena, at_1, at_2, t)
            }
            &Instruction::Max(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("max"), arena, at_1, at_2, t)
            }
            &Instruction::Min(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("min"), arena, at_1, at_2, t)
            }
            &Instruction::IntFloorDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("int_floor_div"), arena, at_1, at_2, t)
            }
            &Instruction::RDiv(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("rdiv"), arena, at_1, at_2, t)
            }
            &Instruction::Div(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("div"), arena, at_1, at_2, t)
            }
            &Instruction::Shl(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("shl"), arena, at_1, at_2, t)
            }
            &Instruction::Shr(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("shr"), arena, at_1, at_2, t)
            }
            &Instruction::Xor(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("xor"), arena, at_1, at_2, t)
            }
            &Instruction::And(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("and"), arena, at_1, at_2, t)
            }
            &Instruction::Or(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("or"), arena, at_1, at_2, t)
            }
            &Instruction::Mod(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("mod"), arena, at_1, at_2, t)
            }
            &Instruction::Rem(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("rem"), arena, at_1, at_2, t)
            }
            &Instruction::ATan2(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("rem"), arena, at_1, at_2, t)
            }
            &Instruction::Gcd(ref at_1, ref at_2, t) => {
                arith_instr_bin_functor(atom!("gcd"), arena, at_1, at_2, t)
            }
            &Instruction::Sign(ref at, t) => arith_instr_unary_functor(atom!("sign"), arena, at, t),
            &Instruction::Cos(ref at, t) => arith_instr_unary_functor(atom!("cos"), arena, at, t),
            &Instruction::Sin(ref at, t) => arith_instr_unary_functor(atom!("sin"), arena, at, t),
            &Instruction::Tan(ref at, t) => arith_instr_unary_functor(atom!("tan"), arena, at, t),
            &Instruction::Log(ref at, t) => arith_instr_unary_functor(atom!("log"), arena, at, t),
            &Instruction::Exp(ref at, t) => arith_instr_unary_functor(atom!("exp"), arena, at, t),
            &Instruction::ACos(ref at, t) => arith_instr_unary_functor(atom!("acos"), arena, at, t),
            &Instruction::ASin(ref at, t) => arith_instr_unary_functor(atom!("asin"), arena, at, t),
            &Instruction::ATan(ref at, t) => arith_instr_unary_functor(atom!("atan"), arena, at, t),
            &Instruction::Sqrt(ref at, t) => arith_instr_unary_functor(atom!("sqrt"), arena, at, t),
            &Instruction::Abs(ref at, t) => arith_instr_unary_functor(atom!("abs"), arena, at, t),
            &Instruction::Float(ref at, t) => {
                arith_instr_unary_functor(atom!("float"), arena, at, t)
            }
            &Instruction::Truncate(ref at, t) => {
                arith_instr_unary_functor(atom!("truncate"), arena, at, t)
            }
            &Instruction::Round(ref at, t) => {
                arith_instr_unary_functor(atom!("round"), arena, at, t)
            }
            &Instruction::Ceiling(ref at, t) => {
                arith_instr_unary_functor(atom!("ceiling"), arena, at, t)
            }
            &Instruction::Floor(ref at, t) => {
                arith_instr_unary_functor(atom!("floor"), arena, at, t)
            }
            &Instruction::FloatFractionalPart(ref at, t) => {
                arith_instr_unary_functor(atom!("float_fractional_part"), arena, at, t)
            }
            &Instruction::FloatIntegerPart(ref at, t) => {
                arith_instr_unary_functor(atom!("float_integer_part"), arena, at, t)
            }
            &Instruction::Neg(ref at, t) => arith_instr_unary_functor(atom!("-"), arena, at, t),
            &Instruction::Plus(ref at, t) => arith_instr_unary_functor(atom!("+"), arena, at, t),
            &Instruction::BitwiseComplement(ref at, t) => {
                arith_instr_unary_functor(atom!("\\"), arena, at, t)
            }
            &Instruction::IndexingCode { .. } => {
                // this case is covered in enqueue_functors, which
                // should be called instead (to_functor is a private
                // function for this reason).
                vec![]
            }
            &Instruction::Allocate(num_frames) => {
                functor!(atom!("allocate"), [fixnum(num_frames)])
            }
            &Instruction::CallNamed(arity, name, ..) => {
                functor!(atom!("call"), [atom_as_cell(name), fixnum(arity)])
            }
            &Instruction::ExecuteNamed(arity, name, ..) => {
                functor!(atom!("execute"), [atom_as_cell(name), fixnum(arity)])
            }
            &Instruction::DefaultCallNamed(arity, name, ..) => {
                functor!(atom!("call_default"), [atom_as_cell(name), fixnum(arity)])
            }
            &Instruction::DefaultExecuteNamed(arity, name, ..) => {
                functor!(
                    atom!("execute_default"),
                    [atom_as_cell(name), fixnum(arity)]
                )
            }
            &Instruction::CallN(arity) => {
                functor!(atom!("call_n"), [fixnum(arity)])
            }
            &Instruction::ExecuteN(arity) => {
                functor!(atom!("execute_n"), [fixnum(arity)])
            }
            &Instruction::DefaultCallN(arity) => {
                functor!(atom!("call_default_n"), [fixnum(arity)])
            }
            &Instruction::DefaultExecuteN(arity) => {
                functor!(atom!("execute_default_n"), [fixnum(arity)])
            }
            &Instruction::CallFastCallN(arity) => {
                functor!(atom!("call_fast_call_n"), [fixnum(arity)])
            }
            &Instruction::ExecuteFastCallN(arity) => {
                functor!(atom!("execute_fast_call_n"), [fixnum(arity)])
            }
            &Instruction::CallTermGreaterThan
            | &Instruction::CallTermLessThan
            | &Instruction::CallTermGreaterThanOrEqual
            | &Instruction::CallTermLessThanOrEqual
            | &Instruction::CallTermEqual
            | &Instruction::CallTermNotEqual
            | &Instruction::CallNumberGreaterThan(..)
            | &Instruction::CallNumberLessThan(..)
            | &Instruction::CallNumberGreaterThanOrEqual(..)
            | &Instruction::CallNumberLessThanOrEqual(..)
            | &Instruction::CallNumberEqual(..)
            | &Instruction::CallNumberNotEqual(..)
            | &Instruction::CallIs(..)
            | &Instruction::CallAcyclicTerm
            | &Instruction::CallArg
            | &Instruction::CallCompare
            | &Instruction::CallCopyTerm
            | &Instruction::CallFunctor
            | &Instruction::CallGround
            | &Instruction::CallKeySort
            | &Instruction::CallSort
            | &Instruction::CallGetNumber(_) => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("call"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            &Instruction::ExecuteTermGreaterThan
            | &Instruction::ExecuteTermLessThan
            | &Instruction::ExecuteTermGreaterThanOrEqual
            | &Instruction::ExecuteTermLessThanOrEqual
            | &Instruction::ExecuteTermEqual
            | &Instruction::ExecuteTermNotEqual
            | &Instruction::ExecuteNumberGreaterThan(..)
            | &Instruction::ExecuteNumberLessThan(..)
            | &Instruction::ExecuteNumberGreaterThanOrEqual(..)
            | &Instruction::ExecuteNumberLessThanOrEqual(..)
            | &Instruction::ExecuteNumberEqual(..)
            | &Instruction::ExecuteNumberNotEqual(..)
            | &Instruction::ExecuteAcyclicTerm
            | &Instruction::ExecuteArg
            | &Instruction::ExecuteCompare
            | &Instruction::ExecuteCopyTerm
            | &Instruction::ExecuteFunctor
            | &Instruction::ExecuteGround
            | &Instruction::ExecuteIs(..)
            | &Instruction::ExecuteKeySort
            | &Instruction::ExecuteSort
            | &Instruction::ExecuteGetNumber(_) => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("execute"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            &Instruction::DefaultCallTermGreaterThan
            | &Instruction::DefaultCallTermLessThan
            | &Instruction::DefaultCallTermGreaterThanOrEqual
            | &Instruction::DefaultCallTermLessThanOrEqual
            | &Instruction::DefaultCallTermEqual
            | &Instruction::DefaultCallTermNotEqual
            | &Instruction::DefaultCallNumberGreaterThan(..)
            | &Instruction::DefaultCallNumberLessThan(..)
            | &Instruction::DefaultCallNumberGreaterThanOrEqual(..)
            | &Instruction::DefaultCallNumberLessThanOrEqual(..)
            | &Instruction::DefaultCallNumberEqual(..)
            | &Instruction::DefaultCallNumberNotEqual(..)
            | &Instruction::DefaultCallAcyclicTerm
            | &Instruction::DefaultCallArg
            | &Instruction::DefaultCallCompare
            | &Instruction::DefaultCallCopyTerm
            | &Instruction::DefaultCallFunctor
            | &Instruction::DefaultCallGround
            | &Instruction::DefaultCallIs(..)
            | &Instruction::DefaultCallKeySort
            | &Instruction::DefaultCallSort
            | &Instruction::DefaultCallGetNumber(_) => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("call_default"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            &Instruction::DefaultExecuteTermGreaterThan
            | &Instruction::DefaultExecuteTermLessThan
            | &Instruction::DefaultExecuteTermGreaterThanOrEqual
            | &Instruction::DefaultExecuteTermLessThanOrEqual
            | &Instruction::DefaultExecuteTermEqual
            | &Instruction::DefaultExecuteTermNotEqual
            | &Instruction::DefaultExecuteNumberGreaterThan(..)
            | &Instruction::DefaultExecuteNumberLessThan(..)
            | &Instruction::DefaultExecuteNumberGreaterThanOrEqual(..)
            | &Instruction::DefaultExecuteNumberLessThanOrEqual(..)
            | &Instruction::DefaultExecuteNumberEqual(..)
            | &Instruction::DefaultExecuteNumberNotEqual(..)
            | &Instruction::DefaultExecuteAcyclicTerm
            | &Instruction::DefaultExecuteArg
            | &Instruction::DefaultExecuteCompare
            | &Instruction::DefaultExecuteCopyTerm
            | &Instruction::DefaultExecuteFunctor
            | &Instruction::DefaultExecuteGround
            | &Instruction::DefaultExecuteIs(..)
            | &Instruction::DefaultExecuteKeySort
            | &Instruction::DefaultExecuteSort
            | &Instruction::DefaultExecuteGetNumber(_) => {
                let (name, arity) = self.to_name_and_arity();
                functor!(
                    atom!("execute_default"),
                    [atom_as_cell(name), fixnum(arity)]
                )
            }
            &Instruction::CallIsAtom(r)
            | &Instruction::CallIsAtomic(r)
            | &Instruction::CallIsCompound(r)
            | &Instruction::CallIsInteger(r)
            | &Instruction::CallIsNumber(r)
            | &Instruction::CallIsRational(r)
            | &Instruction::CallIsFloat(r)
            | &Instruction::CallIsNonVar(r)
            | &Instruction::CallIsVar(r) => {
                let (name, arity) = self.to_name_and_arity();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("call"),
                    [atom_as_cell(name), fixnum(arity), functor(rt_stub)]
                )
            }
            &Instruction::ExecuteIsAtom(r)
            | &Instruction::ExecuteIsAtomic(r)
            | &Instruction::ExecuteIsCompound(r)
            | &Instruction::ExecuteIsInteger(r)
            | &Instruction::ExecuteIsNumber(r)
            | &Instruction::ExecuteIsRational(r)
            | &Instruction::ExecuteIsFloat(r)
            | &Instruction::ExecuteIsNonVar(r)
            | &Instruction::ExecuteIsVar(r) => {
                let (name, arity) = self.to_name_and_arity();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("execute"),
                    [atom_as_cell(name), fixnum(arity), functor(rt_stub)]
                )
            }
            //
            &Instruction::CallAtomChars
            | &Instruction::CallAtomCodes
            | &Instruction::CallAtomLength
            | &Instruction::CallBindFromRegister
            | &Instruction::CallContinuation
            | &Instruction::CallCharCode
            | &Instruction::CallCharType
            | &Instruction::CallCharsToNumber
            | &Instruction::CallCodesToNumber
            | &Instruction::CallCopyTermWithoutAttrVars
            | &Instruction::CallCheckCutPoint
            | &Instruction::CallClose
            | &Instruction::CallCopyToLiftedHeap
            | &Instruction::CallCreatePartialString
            | &Instruction::CallCurrentHostname
            | &Instruction::CallCurrentInput
            | &Instruction::CallCurrentOutput
            | &Instruction::CallDirectoryFiles
            | &Instruction::CallFileSize
            | &Instruction::CallFileExists
            | &Instruction::CallDirectoryExists
            | &Instruction::CallDirectorySeparator
            | &Instruction::CallMakeDirectory
            | &Instruction::CallMakeDirectoryPath
            | &Instruction::CallDeleteFile
            | &Instruction::CallRenameFile
            | &Instruction::CallFileCopy
            | &Instruction::CallWorkingDirectory
            | &Instruction::CallDeleteDirectory
            | &Instruction::CallPathCanonical
            | &Instruction::CallFileTime
            | &Instruction::CallDynamicModuleResolution(..)
            | &Instruction::CallPrepareCallClause(..)
            | &Instruction::CallCompileInlineOrExpandedGoal
            | &Instruction::CallIsExpandedOrInlined
            | &Instruction::CallGetFromAttributedVarList
            | &Instruction::CallPutToAttributedVarList
            | &Instruction::CallDeleteFromAttributedVarList
            | &Instruction::CallDeleteAllAttributesFromVar
            | &Instruction::CallUnattributedVar
            | &Instruction::CallGetDBRefs
            | &Instruction::CallInferenceLimitExceeded
            | &Instruction::CallFetchGlobalVar
            | &Instruction::CallFirstStream
            | &Instruction::CallFlushOutput
            | &Instruction::CallGetByte
            | &Instruction::CallGetChar
            | &Instruction::CallGetNChars
            | &Instruction::CallGetCode
            | &Instruction::CallGetSingleChar
            | &Instruction::CallTruncateIfNoLiftedHeapGrowthDiff
            | &Instruction::CallTruncateIfNoLiftedHeapGrowth
            | &Instruction::CallGetAttributedVariableList
            | &Instruction::CallGetAttrVarQueueDelimiter
            | &Instruction::CallGetAttrVarQueueBeyond
            | &Instruction::CallGetBValue
            | &Instruction::CallGetContinuationChunk
            | &Instruction::CallGetNextOpDBRef
            | &Instruction::CallLookupDBRef
            | &Instruction::CallIsPartialString
            | &Instruction::CallHalt
            | &Instruction::CallGetLiftedHeapFromOffset
            | &Instruction::CallGetLiftedHeapFromOffsetDiff
            | &Instruction::CallGetSCCCleaner
            | &Instruction::CallHeadIsDynamic
            | &Instruction::CallInstallSCCCleaner
            | &Instruction::CallInstallInferenceCounter
            | &Instruction::CallInferenceCount
            | &Instruction::CallLiftedHeapLength
            | &Instruction::CallLoadLibraryAsStream
            | &Instruction::CallModuleExists
            | &Instruction::CallNextEP
            | &Instruction::CallNoSuchPredicate
            | &Instruction::CallNumberToChars
            | &Instruction::CallNumberToCodes
            | &Instruction::CallOpDeclaration
            | &Instruction::CallOpen
            | &Instruction::CallSetStreamOptions
            | &Instruction::CallNextStream
            | &Instruction::CallPartialStringTail
            | &Instruction::CallPeekByte
            | &Instruction::CallPeekChar
            | &Instruction::CallPeekCode
            | &Instruction::CallPointsToContinuationResetMarker
            | &Instruction::CallPutByte
            | &Instruction::CallPutChar
            | &Instruction::CallPutChars
            | &Instruction::CallPutCode
            | &Instruction::CallReadQueryTerm
            | &Instruction::CallReadTerm
            | &Instruction::CallRedoAttrVarBinding
            | &Instruction::CallRemoveCallPolicyCheck
            | &Instruction::CallRemoveInferenceCounter
            | &Instruction::CallResetContinuationMarker
            | &Instruction::CallRestoreCutPolicy
            | &Instruction::CallSetCutPoint(..)
            | &Instruction::CallSetInput
            | &Instruction::CallSetOutput
            | &Instruction::CallStoreBacktrackableGlobalVar
            | &Instruction::CallStoreGlobalVar
            | &Instruction::CallStreamProperty
            | &Instruction::CallSetStreamPosition
            | &Instruction::CallInferenceLevel
            | &Instruction::CallCleanUpBlock
            | &Instruction::CallFail
            | &Instruction::CallGetBall
            | &Instruction::CallGetCurrentBlock
            | &Instruction::CallGetCurrentSCCBlock
            | &Instruction::CallGetCutPoint
            | &Instruction::CallGetDoubleQuotes
            | &Instruction::CallGetUnknown
            | &Instruction::CallInstallNewBlock
            | &Instruction::CallRandomInteger
            | &Instruction::CallMaybe
            | &Instruction::CallCpuNow
            | &Instruction::CallDeterministicLengthRundown
            | &Instruction::CallHttpOpen
            | &Instruction::CallHttpListen
            | &Instruction::CallHttpListenStop
            | &Instruction::CallHttpAccept
            | &Instruction::CallHttpAnswer
            | &Instruction::CallLoadForeignLib
            | &Instruction::CallForeignCall
            | &Instruction::CallDefineForeignStruct
            | &Instruction::CallFfiAllocate
            | &Instruction::CallFfiReadPtr
            | &Instruction::CallFfiDeallocate
            | &Instruction::CallJsEval
            | &Instruction::CallPredicateDefined
            | &Instruction::CallStripModule
            | &Instruction::CallCurrentTime
            | &Instruction::CallQuotedToken
            | &Instruction::CallReadFromChars
            | &Instruction::CallReadTermFromChars
            | &Instruction::CallResetBlock
            | &Instruction::CallResetSCCBlock
            | &Instruction::CallReturnFromVerifyAttr
            | &Instruction::CallSetBall
            | &Instruction::CallPushBallStack
            | &Instruction::CallPopBallStack
            | &Instruction::CallPopFromBallStack
            | &Instruction::CallSetCutPointByDefault(..)
            | &Instruction::CallSetDoubleQuotes
            | &Instruction::CallSetUnknown
            | &Instruction::CallSetSeed
            | &Instruction::CallSkipMaxList
            | &Instruction::CallSleep
            | &Instruction::CallSocketClientOpen
            | &Instruction::CallSocketServerOpen
            | &Instruction::CallSocketServerAccept
            | &Instruction::CallSocketServerClose
            | &Instruction::CallTLSAcceptClient
            | &Instruction::CallTLSClientConnect
            | &Instruction::CallSucceed
            | &Instruction::CallTermAttributedVariables
            | &Instruction::CallTermVariables
            | &Instruction::CallTermVariablesUnderMaxDepth
            | &Instruction::CallTruncateLiftedHeapTo
            | &Instruction::CallUnifyWithOccursCheck
            | &Instruction::CallUnwindEnvironments
            | &Instruction::CallUnwindStack
            | &Instruction::CallWAMInstructions
            | &Instruction::CallInlinedInstructions
            | &Instruction::CallWriteTerm
            | &Instruction::CallWriteTermToChars
            | &Instruction::CallScryerPrologVersion
            | &Instruction::CallCryptoRandomByte
            | &Instruction::CallCryptoDataHash
            | &Instruction::CallCryptoHMAC
            | &Instruction::CallCryptoDataHKDF
            | &Instruction::CallCryptoPasswordHash
            | &Instruction::CallCryptoCurveScalarMult
            | &Instruction::CallCurve25519ScalarMult
            | &Instruction::CallFirstNonOctet
            | &Instruction::CallLoadHTML
            | &Instruction::CallLoadXML
            | &Instruction::CallGetEnv
            | &Instruction::CallSetEnv
            | &Instruction::CallUnsetEnv
            | &Instruction::CallShell
            | &Instruction::CallProcessCreate
            | &Instruction::CallProcessId
            | &Instruction::CallProcessWait
            | &Instruction::CallProcessKill
            | &Instruction::CallProcessRelease
            | &Instruction::CallPid
            | &Instruction::CallCharsBase64
            | &Instruction::CallDevourWhitespace
            | &Instruction::CallIsSTOEnabled
            | &Instruction::CallSetSTOAsUnify
            | &Instruction::CallSetNSTOAsUnify
            | &Instruction::CallSetSTOWithErrorAsUnify
            | &Instruction::CallHomeDirectory
            | &Instruction::CallDebugHook
            | &Instruction::CallAddDiscontiguousPredicate
            | &Instruction::CallAddDynamicPredicate
            | &Instruction::CallAddMultifilePredicate
            | &Instruction::CallAddGoalExpansionClause
            | &Instruction::CallAddTermExpansionClause
            | &Instruction::CallAddInSituFilenameModule
            | &Instruction::CallClauseToEvacuable
            | &Instruction::CallScopedClauseToEvacuable
            | &Instruction::CallConcludeLoad
            | &Instruction::CallDeclareModule
            | &Instruction::CallLoadCompiledLibrary
            | &Instruction::CallLoadContextSource
            | &Instruction::CallLoadContextFile
            | &Instruction::CallLoadContextDirectory
            | &Instruction::CallLoadContextModule
            | &Instruction::CallLoadContextStream
            | &Instruction::CallPopLoadContext
            | &Instruction::CallPopLoadStatePayload
            | &Instruction::CallPushLoadContext
            | &Instruction::CallPushLoadStatePayload
            | &Instruction::CallUseModule
            | &Instruction::CallBuiltInProperty
            | &Instruction::CallMetaPredicateProperty
            | &Instruction::CallIndexingProperty
            | &Instruction::CallMultifileProperty
            | &Instruction::CallDiscontiguousProperty
            | &Instruction::CallDynamicProperty
            | &Instruction::CallAbolishClause
            | &Instruction::CallAsserta
            | &Instruction::CallAssertz
            | &Instruction::CallRetract
            | &Instruction::CallIsConsistentWithTermQueue
            | &Instruction::CallFlushTermQueue
            | &Instruction::CallRemoveModuleExports
            | &Instruction::CallAddNonCountedBacktracking
            | &Instruction::CallPopCount
            | &Instruction::CallArgv
            | &Instruction::CallEd25519SignRaw
            | &Instruction::CallEd25519VerifyRaw
            | &Instruction::CallEd25519SeedToPublicKey => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("call"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            #[cfg(feature = "crypto-full")]
            &Instruction::CallCryptoDataEncrypt | &Instruction::CallCryptoDataDecrypt => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("call"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            &Instruction::CallBeta
            | &Instruction::CallBetaI
            | &Instruction::CallInvBetaI
            | &Instruction::CallGamma
            | &Instruction::CallGammP
            | &Instruction::CallGammQ
            | &Instruction::CallInvGammP
            | &Instruction::CallLnGamma
            | &Instruction::CallErf
            | &Instruction::CallErfc
            | &Instruction::CallInvErf
            | &Instruction::CallInvErfc => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("call"), [atom_as_cell(name), fixnum(arity)])
            }
            &Instruction::ExecuteAtomChars
            | &Instruction::ExecuteAtomCodes
            | &Instruction::ExecuteAtomLength
            | &Instruction::ExecuteBindFromRegister
            | &Instruction::ExecuteContinuation
            | &Instruction::ExecuteCharCode
            | &Instruction::ExecuteCharType
            | &Instruction::ExecuteCharsToNumber
            | &Instruction::ExecuteCodesToNumber
            | &Instruction::ExecuteCopyTermWithoutAttrVars
            | &Instruction::ExecuteCheckCutPoint
            | &Instruction::ExecuteClose
            | &Instruction::ExecuteCopyToLiftedHeap
            | &Instruction::ExecuteCreatePartialString
            | &Instruction::ExecuteCurrentHostname
            | &Instruction::ExecuteCurrentInput
            | &Instruction::ExecuteCurrentOutput
            | &Instruction::ExecuteDirectoryFiles
            | &Instruction::ExecuteFileSize
            | &Instruction::ExecuteFileExists
            | &Instruction::ExecuteDirectoryExists
            | &Instruction::ExecuteDirectorySeparator
            | &Instruction::ExecuteMakeDirectory
            | &Instruction::ExecuteMakeDirectoryPath
            | &Instruction::ExecuteDeleteFile
            | &Instruction::ExecuteRenameFile
            | &Instruction::ExecuteFileCopy
            | &Instruction::ExecuteWorkingDirectory
            | &Instruction::ExecuteDeleteDirectory
            | &Instruction::ExecutePathCanonical
            | &Instruction::ExecuteFileTime
            | &Instruction::ExecuteDynamicModuleResolution(..)
            | &Instruction::ExecutePrepareCallClause(..)
            | &Instruction::ExecuteCompileInlineOrExpandedGoal
            | &Instruction::ExecuteIsExpandedOrInlined
            | &Instruction::ExecuteGetFromAttributedVarList
            | &Instruction::ExecutePutToAttributedVarList
            | &Instruction::ExecuteDeleteFromAttributedVarList
            | &Instruction::ExecuteDeleteAllAttributesFromVar
            | &Instruction::ExecuteUnattributedVar
            | &Instruction::ExecuteGetDBRefs
            | &Instruction::ExecuteInferenceLimitExceeded
            | &Instruction::ExecuteFetchGlobalVar
            | &Instruction::ExecuteFirstStream
            | &Instruction::ExecuteFlushOutput
            | &Instruction::ExecuteGetByte
            | &Instruction::ExecuteGetChar
            | &Instruction::ExecuteGetNChars
            | &Instruction::ExecuteGetCode
            | &Instruction::ExecuteGetSingleChar
            | &Instruction::ExecuteTruncateIfNoLiftedHeapGrowthDiff
            | &Instruction::ExecuteTruncateIfNoLiftedHeapGrowth
            | &Instruction::ExecuteGetAttributedVariableList
            | &Instruction::ExecuteGetAttrVarQueueDelimiter
            | &Instruction::ExecuteGetAttrVarQueueBeyond
            | &Instruction::ExecuteGetBValue
            | &Instruction::ExecuteGetContinuationChunk
            | &Instruction::ExecuteGetNextOpDBRef
            | &Instruction::ExecuteLookupDBRef
            | &Instruction::ExecuteIsPartialString
            | &Instruction::ExecuteHalt
            | &Instruction::ExecuteGetLiftedHeapFromOffset
            | &Instruction::ExecuteGetLiftedHeapFromOffsetDiff
            | &Instruction::ExecuteGetSCCCleaner
            | &Instruction::ExecuteHeadIsDynamic
            | &Instruction::ExecuteInstallSCCCleaner
            | &Instruction::ExecuteInstallInferenceCounter
            | &Instruction::ExecuteInferenceCount
            | &Instruction::ExecuteLiftedHeapLength
            | &Instruction::ExecuteLoadLibraryAsStream
            | &Instruction::ExecuteModuleExists
            | &Instruction::ExecuteNextEP
            | &Instruction::ExecuteNoSuchPredicate
            | &Instruction::ExecuteNumberToChars
            | &Instruction::ExecuteNumberToCodes
            | &Instruction::ExecuteOpDeclaration
            | &Instruction::ExecuteOpen
            | &Instruction::ExecuteSetStreamOptions
            | &Instruction::ExecuteNextStream
            | &Instruction::ExecutePartialStringTail
            | &Instruction::ExecutePeekByte
            | &Instruction::ExecutePeekChar
            | &Instruction::ExecutePeekCode
            | &Instruction::ExecutePointsToContinuationResetMarker
            | &Instruction::ExecutePutByte
            | &Instruction::ExecutePutChar
            | &Instruction::ExecutePutChars
            | &Instruction::ExecutePutCode
            | &Instruction::ExecuteReadQueryTerm
            | &Instruction::ExecuteReadTerm
            | &Instruction::ExecuteRedoAttrVarBinding
            | &Instruction::ExecuteRemoveCallPolicyCheck
            | &Instruction::ExecuteRemoveInferenceCounter
            | &Instruction::ExecuteResetContinuationMarker
            | &Instruction::ExecuteRestoreCutPolicy
            | &Instruction::ExecuteSetCutPoint(_)
            | &Instruction::ExecuteSetInput
            | &Instruction::ExecuteSetOutput
            | &Instruction::ExecuteStoreBacktrackableGlobalVar
            | &Instruction::ExecuteStoreGlobalVar
            | &Instruction::ExecuteStreamProperty
            | &Instruction::ExecuteSetStreamPosition
            | &Instruction::ExecuteInferenceLevel
            | &Instruction::ExecuteCleanUpBlock
            | &Instruction::ExecuteFail
            | &Instruction::ExecuteGetBall
            | &Instruction::ExecuteGetCurrentBlock
            | &Instruction::ExecuteGetCurrentSCCBlock
            | &Instruction::ExecuteGetCutPoint
            | &Instruction::ExecuteGetDoubleQuotes
            | &Instruction::ExecuteGetUnknown
            | &Instruction::ExecuteInstallNewBlock
            | &Instruction::ExecuteRandomInteger
            | &Instruction::ExecuteMaybe
            | &Instruction::ExecuteCpuNow
            | &Instruction::ExecuteDeterministicLengthRundown
            | &Instruction::ExecuteHttpOpen
            | &Instruction::ExecuteHttpListen
            | &Instruction::ExecuteHttpListenStop
            | &Instruction::ExecuteHttpAccept
            | &Instruction::ExecuteHttpAnswer
            | &Instruction::ExecuteLoadForeignLib
            | &Instruction::ExecuteForeignCall
            | &Instruction::ExecuteDefineForeignStruct
            | &Instruction::ExecuteFfiAllocate
            | &Instruction::ExecuteFfiReadPtr
            | &Instruction::ExecuteFfiDeallocate
            | &Instruction::ExecuteJsEval
            | &Instruction::ExecutePredicateDefined
            | &Instruction::ExecuteStripModule
            | &Instruction::ExecuteCurrentTime
            | &Instruction::ExecuteQuotedToken
            | &Instruction::ExecuteReadFromChars
            | &Instruction::ExecuteReadTermFromChars
            | &Instruction::ExecuteResetBlock
            | &Instruction::ExecuteResetSCCBlock
            | &Instruction::ExecuteReturnFromVerifyAttr
            | &Instruction::ExecuteSetBall
            | &Instruction::ExecutePushBallStack
            | &Instruction::ExecutePopBallStack
            | &Instruction::ExecutePopFromBallStack
            | &Instruction::ExecuteSetCutPointByDefault(_)
            | &Instruction::ExecuteSetDoubleQuotes
            | &Instruction::ExecuteSetUnknown
            | &Instruction::ExecuteSetSeed
            | &Instruction::ExecuteSkipMaxList
            | &Instruction::ExecuteSleep
            | &Instruction::ExecuteSocketClientOpen
            | &Instruction::ExecuteSocketServerOpen
            | &Instruction::ExecuteSocketServerAccept
            | &Instruction::ExecuteSocketServerClose
            | &Instruction::ExecuteTLSAcceptClient
            | &Instruction::ExecuteTLSClientConnect
            | &Instruction::ExecuteSucceed
            | &Instruction::ExecuteTermAttributedVariables
            | &Instruction::ExecuteTermVariables
            | &Instruction::ExecuteTermVariablesUnderMaxDepth
            | &Instruction::ExecuteTruncateLiftedHeapTo
            | &Instruction::ExecuteUnifyWithOccursCheck
            | &Instruction::ExecuteUnwindEnvironments
            | &Instruction::ExecuteUnwindStack
            | &Instruction::ExecuteWAMInstructions
            | &Instruction::ExecuteInlinedInstructions
            | &Instruction::ExecuteWriteTerm
            | &Instruction::ExecuteWriteTermToChars
            | &Instruction::ExecuteScryerPrologVersion
            | &Instruction::ExecuteCryptoRandomByte
            | &Instruction::ExecuteCryptoDataHash
            | &Instruction::ExecuteCryptoHMAC
            | &Instruction::ExecuteCryptoDataHKDF
            | &Instruction::ExecuteCryptoPasswordHash
            | &Instruction::ExecuteCryptoCurveScalarMult
            | &Instruction::ExecuteCurve25519ScalarMult
            | &Instruction::ExecuteFirstNonOctet
            | &Instruction::ExecuteLoadHTML
            | &Instruction::ExecuteLoadXML
            | &Instruction::ExecuteGetEnv
            | &Instruction::ExecuteSetEnv
            | &Instruction::ExecuteUnsetEnv
            | &Instruction::ExecuteShell
            | &Instruction::ExecuteProcessCreate
            | &Instruction::ExecuteProcessId
            | &Instruction::ExecuteProcessWait
            | &Instruction::ExecuteProcessKill
            | &Instruction::ExecuteProcessRelease
            | &Instruction::ExecutePid
            | &Instruction::ExecuteCharsBase64
            | &Instruction::ExecuteDevourWhitespace
            | &Instruction::ExecuteIsSTOEnabled
            | &Instruction::ExecuteSetSTOAsUnify
            | &Instruction::ExecuteSetNSTOAsUnify
            | &Instruction::ExecuteSetSTOWithErrorAsUnify
            | &Instruction::ExecuteHomeDirectory
            | &Instruction::ExecuteDebugHook
            | &Instruction::ExecuteAddDiscontiguousPredicate
            | &Instruction::ExecuteAddDynamicPredicate
            | &Instruction::ExecuteAddMultifilePredicate
            | &Instruction::ExecuteAddGoalExpansionClause
            | &Instruction::ExecuteAddTermExpansionClause
            | &Instruction::ExecuteAddInSituFilenameModule
            | &Instruction::ExecuteClauseToEvacuable
            | &Instruction::ExecuteScopedClauseToEvacuable
            | &Instruction::ExecuteConcludeLoad
            | &Instruction::ExecuteDeclareModule
            | &Instruction::ExecuteLoadCompiledLibrary
            | &Instruction::ExecuteLoadContextSource
            | &Instruction::ExecuteLoadContextFile
            | &Instruction::ExecuteLoadContextDirectory
            | &Instruction::ExecuteLoadContextModule
            | &Instruction::ExecuteLoadContextStream
            | &Instruction::ExecutePopLoadContext
            | &Instruction::ExecutePopLoadStatePayload
            | &Instruction::ExecutePushLoadContext
            | &Instruction::ExecutePushLoadStatePayload
            | &Instruction::ExecuteUseModule
            | &Instruction::ExecuteBuiltInProperty
            | &Instruction::ExecuteMetaPredicateProperty
            | &Instruction::ExecuteIndexingProperty
            | &Instruction::ExecuteMultifileProperty
            | &Instruction::ExecuteDiscontiguousProperty
            | &Instruction::ExecuteDynamicProperty
            | &Instruction::ExecuteAbolishClause
            | &Instruction::ExecuteAsserta
            | &Instruction::ExecuteAssertz
            | &Instruction::ExecuteRetract
            | &Instruction::ExecuteIsConsistentWithTermQueue
            | &Instruction::ExecuteFlushTermQueue
            | &Instruction::ExecuteRemoveModuleExports
            | &Instruction::ExecuteAddNonCountedBacktracking
            | &Instruction::ExecutePopCount
            | &Instruction::ExecuteArgv
            | &Instruction::ExecuteEd25519SignRaw
            | &Instruction::ExecuteEd25519VerifyRaw
            | &Instruction::ExecuteEd25519SeedToPublicKey => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("execute"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            #[cfg(feature = "crypto-full")]
            &Instruction::ExecuteCryptoDataEncrypt | &Instruction::ExecuteCryptoDataDecrypt => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("execute"), [atom_as_cell(name), fixnum(arity)])
            }
            //
            &Instruction::ExecuteBeta
            | &Instruction::ExecuteBetaI
            | &Instruction::ExecuteInvBetaI
            | &Instruction::ExecuteGamma
            | &Instruction::ExecuteGammP
            | &Instruction::ExecuteGammQ
            | &Instruction::ExecuteInvGammP
            | &Instruction::ExecuteLnGamma
            | &Instruction::ExecuteErf
            | &Instruction::ExecuteErfc
            | &Instruction::ExecuteInvErf
            | &Instruction::ExecuteInvErfc => {
                let (name, arity) = self.to_name_and_arity();
                functor!(atom!("execute"), [atom_as_cell(name), fixnum(arity)])
            }
            &Instruction::Deallocate => {
                functor!(atom!("deallocate"))
            }
            &Instruction::JmpByCall(offset) => {
                functor!(atom!("jmp_by_call"), [fixnum(offset)])
            }
            &Instruction::RevJmpBy(offset) => {
                functor!(atom!("rev_jmp_by"), [fixnum(offset)])
            }
            &Instruction::Proceed => {
                functor!(atom!("proceed"))
            }
            &Instruction::GetConstant(lvl, lit, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_constant"),
                    [functor(lvl_stub), cell(lit), functor(rt_stub)]
                )
            }
            &Instruction::GetList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("get_list"), [functor(lvl_stub), functor(rt_stub)])
            }
            &Instruction::GetPartialString(lvl, ref s, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_partial_string"),
                    [functor(lvl_stub), string((s.to_string())), functor(rt_stub)]
                )
            }
            &Instruction::GetStructure(lvl, name, arity, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("get_structure"),
                    [
                        functor(lvl_stub),
                        atom_as_cell(name),
                        fixnum(arity),
                        functor(rt_stub)
                    ]
                )
            }
            &Instruction::GetValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_value"), [functor(rt_stub), fixnum(arg)])
            }
            &Instruction::GetVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("get_variable"), [functor(rt_stub), fixnum(arg)])
            }
            &Instruction::UnifyConstant(c) => {
                functor!(atom!("unify_constant"), [cell(c)])
            }
            &Instruction::UnifyLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("unify_local_value"), [functor(rt_stub)])
            }
            &Instruction::UnifyVariable(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("unify_variable"), [functor(rt_stub)])
            }
            &Instruction::UnifyValue(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("unify_value"), [functor(rt_stub)])
            }
            &Instruction::UnifyVoid(vars) => {
                functor!(atom!("unify_void"), [fixnum(vars)])
            }
            &Instruction::PutUnsafeValue(norm, arg) => {
                functor!(atom!("put_unsafe_value"), [fixnum(norm), fixnum(arg)])
            }
            &Instruction::PutConstant(lvl, c, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_constant"),
                    [functor(rt_stub), cell(c), functor(lvl_stub)]
                )
            }
            &Instruction::PutList(lvl, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("put_list"), [functor(lvl_stub), functor(rt_stub)])
            }
            &Instruction::PutPartialString(lvl, ref s, r) => {
                let lvl_stub = lvl.into_functor();
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_partial_string"),
                    [functor(lvl_stub), string((s.to_string())), functor(rt_stub)]
                )
            }
            &Instruction::PutStructure(name, arity, r) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(
                    atom!("put_structure"),
                    [atom_as_cell(name), fixnum(arity), functor(rt_stub)]
                )
            }
            &Instruction::PutValue(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("put_value"), [functor(rt_stub), fixnum(arg)])
            }
            &Instruction::PutVariable(r, arg) => {
                let rt_stub = reg_type_into_functor(r);

                functor!(atom!("put_variable"), [functor(rt_stub), fixnum(arg)])
            }
            &Instruction::SetConstant(c) => {
                functor!(atom!("set_constant"), [cell(c)])
            }
            &Instruction::SetLocalValue(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("set_local_value"), [functor(rt_stub)])
            }
            &Instruction::SetVariable(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("set_variable"), [functor(rt_stub)])
            }
            &Instruction::SetValue(r) => {
                let rt_stub = reg_type_into_functor(r);
                functor!(atom!("set_value"), [functor(rt_stub)])
            }
            &Instruction::SetVoid(vars) => {
                functor!(atom!("set_void"), [fixnum(vars)])
            }
            &Instruction::BreakFromDispatchLoop => {
                functor!(atom!("$break_from_dispatch_loop"))
            }
        }
    }

    #[allow(dead_code)]
    pub fn is_query_instr(&self) -> bool {
        matches!(
            self,
            &Instruction::GetVariable(..)
                | &Instruction::PutConstant(..)
                | &Instruction::PutList(..)
                | &Instruction::PutPartialString(..)
                | &Instruction::PutStructure(..)
                | &Instruction::PutUnsafeValue(..)
                | &Instruction::PutValue(..)
                | &Instruction::PutVariable(..)
                | &Instruction::SetConstant(..)
                | &Instruction::SetLocalValue(..)
                | &Instruction::SetVariable(..)
                | &Instruction::SetValue(..)
                | &Instruction::SetVoid(..)
        )
    }
}

impl CompareNumber {
    pub fn set_terms(&mut self, l_at_1: ArithmeticTerm, l_at_2: ArithmeticTerm) {
        match self {
            CompareNumber::NumberGreaterThan(at_1, at_2)
            | CompareNumber::NumberLessThan(at_1, at_2)
            | CompareNumber::NumberGreaterThanOrEqual(at_1, at_2)
            | CompareNumber::NumberLessThanOrEqual(at_1, at_2)
            | CompareNumber::NumberNotEqual(at_1, at_2)
            | CompareNumber::NumberEqual(at_1, at_2) => {
                *at_1 = l_at_1;
                *at_2 = l_at_2;
            }
        }
    }
}
