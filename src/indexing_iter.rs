use std::collections::VecDeque;
use std::fmt::Debug;

use fxhash::{FxBuildHasher, FxHasher};
use hashbrown::hash_table::*;
use indexmap::IndexSet;

use crate::atom_table::{Atom, AtomCell};
use crate::forms::{AppendOrPrepend, IndexingSpec, Level, OptArgIndexKey};
use crate::indexing::cap_choice_seq_with_trust;
use crate::instructions::*;
use crate::machine::machine_indices::IndexingSpecs;
use crate::offset_table::F64Table;
use crate::parser::ast::RegType;
use crate::types::HeapCellValue;

#[derive(Debug, Clone, Copy)]
pub(crate) enum InstructionArg {
    ArgedHead(usize, OptArgIndexKey), // arg_num, opt_arg_index_key
    ArglessHead,
    NonHead,
    Prologue,
}

pub(crate) fn extract_index_arg(instr: &Instruction) -> InstructionArg {
    if matches!(
        instr,
        Instruction::TryMeElse(..)
            | Instruction::Allocate(..)
            | Instruction::GetLevel(..)
            | Instruction::GetPrevLevel(..)
            | Instruction::GetCutPoint(..)
            | Instruction::DynamicElse(..)
            | Instruction::DynamicInternalElse(..)
            | Instruction::IndexingCode { .. }
            | Instruction::RevJmpBy(..)
            | Instruction::NeckCut
    ) {
        return InstructionArg::Prologue;
    }

    match instr {
        &Instruction::GetStructure(Level::Shallow, name, arity, RegType::Temp(arg)) => {
            InstructionArg::ArgedHead(arg, OptArgIndexKey::Structure(name, arity))
        }
        &Instruction::GetList(Level::Shallow, RegType::Temp(arg)) => {
            InstructionArg::ArgedHead(arg, OptArgIndexKey::List)
        }
        &Instruction::GetConstant(Level::Shallow, cell, RegType::Temp(arg)) => {
            InstructionArg::ArgedHead(arg, OptArgIndexKey::Literal(cell))
        }
        &Instruction::GetPartialString(Level::Shallow, ref _string, RegType::Temp(arg)) => {
            InstructionArg::ArgedHead(arg, OptArgIndexKey::List)
        }
        Instruction::GetVariable(..)
        | Instruction::GetValue(..)
        | Instruction::UnifyVariable(..)
        | Instruction::UnifyValue(..)
        | Instruction::UnifyLocalValue(..)
        | Instruction::UnifyVoid(..)
        | Instruction::UnifyConstant(..) => InstructionArg::ArglessHead,
        _ => InstructionArg::NonHead,
    }
}

#[inline]
fn cap_choice_seq(prelude: &mut [StaticIndexedChoiceInstructionOffset]) {
    if let Some(instr) = prelude.first_mut() {
        *instr = StaticIndexedChoiceInstructionOffset::Try(instr.offset());
    }

    if let Some(instr) = prelude.last_mut() {
        cap_choice_seq_with_trust(instr);
    }
}

#[inline]
fn uncap_choice_seq_with_try(instr: &mut StaticIndexedChoiceInstructionOffset, is_default: bool) {
    if let StaticIndexedChoiceInstructionOffset::Try(i) = instr {
        *instr = if is_default {
            StaticIndexedChoiceInstructionOffset::DefaultRetry(*i)
        } else {
            StaticIndexedChoiceInstructionOffset::Retry(*i)
        };
    }
}

// return the value of non_counted_bt for the predicate
#[inline]
fn uncap_choice_seq_with_trust(instr: &mut StaticIndexedChoiceInstructionOffset) -> bool {
    match instr {
        StaticIndexedChoiceInstructionOffset::Trust(i) => {
            *instr = StaticIndexedChoiceInstructionOffset::Retry(*i);
        }
        StaticIndexedChoiceInstructionOffset::DefaultTrust(i) => {
            *instr = StaticIndexedChoiceInstructionOffset::DefaultRetry(*i);
            return true;
        }
        _ => {}
    }

    false
}

pub(crate) fn on_demand_sub_table(
    arg_num: usize,
    specs: IndexingSpecs,
    arity: usize,
) -> Vec<IndexedChoiceInstructionTable> {
    let mut table = Vec::with_capacity(3 * (arity + 1 - arg_num));

    for arg_num in arg_num..=arity {
        if matches!(specs.get(arg_num - 1), IndexingSpec::NoIndexing) {
            continue;
        }

        table.push(IndexedChoiceInstructionTable::OnDemandTerm { arg_num });
    }

    table
}

// compute the OptArgIndexKey's for the arguments of a given compiled
// clause from an initial_arg_num.
pub(crate) fn collect_opt_arg_index_keys(code: &[Instruction]) -> Vec<OptArgIndexKey> {
    let mut keys = vec![];

    for instr in code {
        match extract_index_arg(instr) {
            InstructionArg::ArgedHead(arg_num, index_key) => {
                if arg_num - 1 > keys.len() {
                    keys.resize_with(arg_num - 1, || OptArgIndexKey::None);
                }

                keys.push(index_key);
            }
            InstructionArg::ArglessHead | InstructionArg::Prologue => {}
            InstructionArg::NonHead => break,
        }
    }

    keys
}

pub(crate) fn first_inst_arg_num(code: &[Instruction], index_loc_opt: Option<usize>) -> usize {
    index_loc_opt
        .and_then(|index_loc| code.get(index_loc))
        .and_then(|instr| {
            if let Instruction::IndexingCode { code, .. } = &instr {
                code.first()
            } else {
                None
            }
        })
        .and_then(|line| {
            line.tables()
                .front()
                .map(IndexedChoiceInstructionTable::arg_num)
        })
        .unwrap_or(0)
}

#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct TableLocation {
    pub(crate) table_loc: usize,
    pub(crate) table_offset: usize,
}

impl TableLocation {
    #[inline]
    pub(crate) fn skip_by(&self, offset: usize) -> Self {
        TableLocation {
            table_loc: self.table_loc,
            table_offset: self.table_offset + offset,
        }
    }
}

#[derive(Debug)]
pub(crate) struct IndexedClauseView<'a> {
    pub(crate) index: &'a mut Vec<IndexingLine>,
    pub(crate) rest: &'a [Instruction],
    pub(crate) arity: usize,
    pub(crate) specs: IndexingSpecs,
}

pub(crate) enum IndexingLineOffset<'a> {
    Static(&'a mut VecDeque<StaticIndexedChoiceInstructionOffset>),
    Dynamic(&'a mut VecDeque<Appended>),
}

impl<'code> IndexingLineOffset<'code> {
    #[inline]
    fn to_place(self, cursor: TableLocation) -> IndexingLinePlace<'code> {
        match self {
            IndexingLineOffset::Static(offsets) => {
                IndexingLinePlace::StaticOffsets(cursor, offsets)
            }
            IndexingLineOffset::Dynamic(offsets) => {
                IndexingLinePlace::DynamicOffsets(cursor, offsets)
            }
        }
    }

    fn add(&mut self, append_or_prepend: AppendOrPrepend, clause_offset: usize) {
        match self {
            IndexingLineOffset::Static(offsets) if append_or_prepend.is_append() => {
                let instr = if let Some(instr) = offsets.back_mut() {
                    if uncap_choice_seq_with_trust(instr) {
                        StaticIndexedChoiceInstructionOffset::DefaultTrust(clause_offset)
                    } else {
                        StaticIndexedChoiceInstructionOffset::Trust(clause_offset)
                    }
                } else {
                    StaticIndexedChoiceInstructionOffset::Try(clause_offset)
                };

                offsets.push_back(instr);
            }
            IndexingLineOffset::Static(offsets) => {
                if let Some(instr) = offsets.front_mut() {
                    uncap_choice_seq_with_try(instr, false);
                }

                offsets.push_front(StaticIndexedChoiceInstructionOffset::Try(clause_offset));
            }
            IndexingLineOffset::Dynamic(offsets) if append_or_prepend.is_append() => {
                offsets.push_back(Appended::Z(clause_offset));
            }
            IndexingLineOffset::Dynamic(offsets) => {
                offsets.push_front(Appended::A(clause_offset));
            }
        }
    }

    fn remove(&mut self, clause_offset: usize) {
        match self {
            IndexingLineOffset::Static(offsets) => {
                if let Ok(idx) = offsets
                    .make_contiguous()
                    .binary_search_by(|instr| instr.offset().cmp(&clause_offset))
                {
                    offsets.remove(idx);
                    cap_choice_seq(offsets.make_contiguous());
                }
            }
            IndexingLineOffset::Dynamic(offsets) => {
                if let Ok(idx) =
                    offsets
                        .make_contiguous()
                        .binary_search_by(|appended| match appended {
                            // suppose clause_offset is among the Z's..
                            Appended::A(_) => std::cmp::Ordering::Greater,
                            Appended::Z(x) => clause_offset.cmp(x),
                        })
                {
                    offsets.remove(idx);
                } else if let Ok(idx) =
                    offsets
                        .make_contiguous()
                        .binary_search_by(|appended| match appended {
                            // didn't find it? suppose it is among the A's
                            Appended::Z(_) => std::cmp::Ordering::Less,
                            Appended::A(x) => x.cmp(&clause_offset),
                        })
                {
                    offsets.remove(idx);
                }
            }
        }
    }
}

impl<'a> IndexedClauseView<'a> {
    pub(crate) fn try_from_code(code: &'a mut [Instruction]) -> Option<Self> {
        match code.split_at_mut_checked(1) {
            Some((
                [
                    Instruction::IndexingCode {
                        arity, code, specs, ..
                    },
                ],
                rest,
            )) => Some(Self {
                index: code,
                arity: *arity,
                specs: specs.clone(),
                rest,
            }),
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn stagger_rest_by(&mut self, offset: usize) {
        self.rest = &self.rest[offset..];
    }
}

pub(crate) enum FlattenedIndexLine<'a> {
    Table(
        &'a mut VecDeque<IndexedChoiceInstructionTable>,
        IndexingLineOffset<'a>,
    ),
}

pub(crate) fn flatten_indexing_line_at<'a>(
    index: &'a mut Vec<IndexingLine>,
    table_loc: usize,
) -> Option<FlattenedIndexLine<'a>> {
    index
        .get_mut(table_loc)
        .map(|indexing_line| match indexing_line {
            IndexingLine::StaticIndexedChoice(SecondLevelTable { tables, offsets }) => {
                FlattenedIndexLine::Table(tables, IndexingLineOffset::Static(offsets))
            }
            IndexingLine::DynamicIndexedChoice(SecondLevelTable { tables, offsets }) => {
                FlattenedIndexLine::Table(tables, IndexingLineOffset::Dynamic(offsets))
            }
        })
}

// expose, step by step, access to the components that must be
// modified (i.e. adding or removing indices), in order found
// according to clause data, e.g. a sequence of OptArgIndexKey
// values. and maintain "side" information as well, like access to
// try-retry-trust/dynamic_else sequences.
pub(crate) struct IndexingLineIter<'code> {
    pub(crate) stack: Vec<TableLocation>,
    pub(crate) view: IndexedClauseView<'code>,
    pub(crate) arg_num: usize,
}

pub(crate) enum IndexingLinePlace<'a> {
    SwitchOnNonePtr(TableLocation),
    SwitchOnConstantPtr(
        TableLocation,
        usize, // indexing_code_len
        HeapCellValue,
        &'a mut TermIndexingCodePtr<HeapCellValue>,
    ),
    SwitchOnStructurePtr(
        TableLocation,
        usize, // indexing_code_len
        Atom,  // name
        usize, // arity
        &'a mut TermIndexingCodePtr<(Atom, usize)>,
    ),
    SwitchOnListPtr(
        TableLocation,
        usize, // indexing_code_len,
        &'a mut Option<IndexingCodePtr>,
    ),
    DeadIndices(
        TableLocation,
        usize, // arg_num
        &'a mut IndexSet<usize, FxBuildHasher>,
    ),
    OnDemandInstr(TableLocation, usize), // cursor, indexing_code_len
    StaticOffsets(
        TableLocation,
        &'a mut VecDeque<StaticIndexedChoiceInstructionOffset>,
    ),
    DynamicOffsets(TableLocation, &'a mut VecDeque<Appended>),
}

enum MapPromotion {
    None,
    ExternalToInternal(usize),
    DynamicFailToInternal, // go from Fail to Internal in a dynamic predicate.
    Internal(usize),
}

impl From<IndexingCodePtr> for MapPromotion {
    #[inline]
    fn from(value: IndexingCodePtr) -> Self {
        match value {
            IndexingCodePtr::External(o) => MapPromotion::ExternalToInternal(o),
            IndexingCodePtr::Internal(i) => MapPromotion::Internal(i),
        }
    }
}

enum MapDemotion {
    None,
    ExternalToFail,
    Internal(usize),
}

impl<'code> IndexingLineIter<'code> {
    pub(crate) fn new(view: IndexedClauseView<'code>) -> Self {
        Self {
            stack: vec![TableLocation {
                table_loc: 0,
                table_offset: 0,
            }],
            view,
            arg_num: 1,
        }
    }

    // this isn't wrapped in an Iterator instance because there's no
    // way to reconcile the lifetimes of self and the Item type
    // within the trait.
    pub(crate) fn next<'a>(
        &'a mut self,
        keys: impl Fn(usize) -> OptArgIndexKey,
    ) -> Option<IndexingLinePlace<'a>> {
        let indexing_code_len = self.view.index.len();

        if let Some(cursor) = self.stack.pop() {
            match flatten_indexing_line_at(self.view.index, cursor.table_loc) {
                Some(FlattenedIndexLine::Table(tables, offsets)) => {
                    match tables.get_mut(cursor.table_offset) {
                        Some(next_instr) => {
                            match next_instr {
                                IndexedChoiceInstructionTable::SwitchOnTerm {
                                    arg_num,
                                    constants,
                                    structures,
                                    lists,
                                } => {
                                    self.arg_num = *arg_num;

                                    // self.keys.get(..) might fail because a
                                    // tail of keys for the clause may be
                                    // variadic which extract_index_arg can't
                                    // detect. the unspecified tail is always
                                    // variadic, so just return
                                    // OptArgIndexKey::None.
                                    let key_type = keys(self.arg_num);

                                    match key_type {
                                        OptArgIndexKey::Structure(name, arity) => {
                                            Some(IndexingLinePlace::SwitchOnStructurePtr(
                                                cursor,
                                                indexing_code_len,
                                                name,
                                                arity,
                                                structures,
                                            ))
                                        }
                                        OptArgIndexKey::Literal(cell) => {
                                            Some(IndexingLinePlace::SwitchOnConstantPtr(
                                                cursor,
                                                indexing_code_len,
                                                cell,
                                                constants,
                                            ))
                                        }
                                        OptArgIndexKey::List => {
                                            Some(IndexingLinePlace::SwitchOnListPtr(
                                                cursor,
                                                indexing_code_len,
                                                lists,
                                            ))
                                        }
                                        OptArgIndexKey::None => {
                                            Some(IndexingLinePlace::SwitchOnNonePtr(cursor))
                                        }
                                    }

                                    // let the client use the cursor to control the
                                    // next step of iteration, to permit, e.g. shallow
                                    // or deep iteration as needed
                                }
                                &mut IndexedChoiceInstructionTable::OnDemandTerm { arg_num } => {
                                    self.arg_num = arg_num;
                                    Some(IndexingLinePlace::OnDemandInstr(
                                        cursor,
                                        indexing_code_len,
                                    ))
                                }
                                IndexedChoiceInstructionTable::DeadIndices { arg_num, indices } => {
                                    self.arg_num = *arg_num;
                                    Some(IndexingLinePlace::DeadIndices(cursor, *arg_num, indices))
                                }
                            }
                        }
                        None => Some(offsets.to_place(cursor)),
                    }
                }
                None => None,
            }
        } else {
            None
        }
    }

    // return Some if a new table (i.e. an Internal pointer) was created
    // which must contain the argument of the former External pointer.
    #[must_use]
    fn promote_in_map<IndexKey: Clone + Debug>(
        key: IndexKey,
        hash_fn: impl Fn(&IndexKey) -> u64,
        eq_fn: impl Fn(&IndexKey, &IndexKey) -> bool,
        new_clause_offset: usize,
        is_dynamic: bool,
        indices: &mut HashTable<(IndexKey, IndexingCodePtr)>,
        indexing_code_len: usize,
    ) -> MapPromotion {
        let hash = hash_fn(&key);

        match indices.entry(
            hash,
            |(other_key, _)| eq_fn(&key, other_key),
            |(key, _)| hash_fn(key),
        ) {
            hashbrown::hash_table::Entry::Vacant(entry) => {
                if is_dynamic {
                    let ptr = IndexingCodePtr::Internal(indexing_code_len);
                    entry.insert((key, ptr));
                    MapPromotion::DynamicFailToInternal
                } else {
                    let ptr = IndexingCodePtr::External(new_clause_offset);
                    entry.insert((key, ptr));
                    MapPromotion::None
                }
            }
            hashbrown::hash_table::Entry::Occupied(mut entry) => {
                let val = entry.get_mut();
                match val.1 {
                    IndexingCodePtr::External(other_clause_offset) => {
                        val.1 = IndexingCodePtr::Internal(indexing_code_len);
                        MapPromotion::ExternalToInternal(other_clause_offset)
                    }
                    IndexingCodePtr::Internal(internal_loc) => MapPromotion::Internal(internal_loc),
                }
            }
        }
    }

    #[must_use]
    fn demote_at_key<IndexKey>(
        key: IndexKey,
        mut eq_fn: impl FnMut(&IndexKey) -> bool,
        hash_fn: impl Fn(&IndexKey) -> u64,
        indices: &mut HashTable<(IndexKey, IndexingCodePtr)>,
    ) -> MapDemotion {
        let hash = hash_fn(&key);

        match indices.entry(hash, |(key, _)| eq_fn(key), |(key, _)| hash_fn(key)) {
            hashbrown::hash_table::Entry::Vacant(_entry) => MapDemotion::None,
            hashbrown::hash_table::Entry::Occupied(entry) => match entry.get().1 {
                IndexingCodePtr::External(_) => {
                    entry.remove();
                    MapDemotion::ExternalToFail
                }
                IndexingCodePtr::Internal(internal_table_loc) => {
                    MapDemotion::Internal(internal_table_loc)
                }
            },
        }
    }

    fn implement_map_promotion(
        &mut self,
        map_promotion: MapPromotion,
        append_or_prepend: AppendOrPrepend,
        clause_offset: usize,
    ) {
        match map_promotion {
            MapPromotion::None => {}
            MapPromotion::DynamicFailToInternal => {
                // promote_in_map changed the map pointer to
                // Internal(indexing_code_len).
                self.view
                    .index
                    .push(fresh_on_demand_subtable::<DynamicIndexedChoiceInstruction>(
                        self.arg_num + 1,
                        self.view.specs.clone(),
                        std::iter::once(if append_or_prepend.is_append() {
                            Appended::Z(clause_offset)
                        } else {
                            Appended::A(clause_offset)
                        }),
                        self.view.arity,
                    ));
            }
            MapPromotion::ExternalToInternal(other_clause_offset) => {
                // promote_in_map changed the map pointer to Internal(indexing_code_len).
                self.view
                    .index
                    .push(fresh_on_demand_subtable::<StaticIndexedChoiceInstruction>(
                        self.arg_num + 1,
                        self.view.specs.clone(),
                        if append_or_prepend.is_append() {
                            [
                                StaticIndexedChoiceInstructionOffset::Try(other_clause_offset),
                                StaticIndexedChoiceInstructionOffset::Trust(clause_offset),
                            ]
                        } else {
                            [
                                StaticIndexedChoiceInstructionOffset::Try(clause_offset),
                                StaticIndexedChoiceInstructionOffset::Trust(other_clause_offset),
                            ]
                        }
                        .iter()
                        .cloned(),
                        self.view.arity,
                    ));
            }
            MapPromotion::Internal(internal_table_loc) => {
                *self.view.index[internal_table_loc].tables_mut() = VecDeque::from(
                    on_demand_sub_table(self.arg_num + 1, self.view.specs.clone(), self.view.arity),
                );

                self.view.index[internal_table_loc]
                    .offsets()
                    .add(append_or_prepend, clause_offset);
            }
        }
    }

    fn remove_from_internal_map(&mut self, internal_table_loc: usize, clause_offset: usize) {
        *self.view.index[internal_table_loc].tables_mut() = VecDeque::from(on_demand_sub_table(
            self.arg_num + 1,
            self.view.specs.clone(),
            self.view.arity,
        ));
        self.view.index[internal_table_loc]
            .offsets()
            .remove(clause_offset);
    }
}

impl IndexingLine {
    #[inline]
    fn offsets<'a>(&'a mut self) -> IndexingLineOffset<'a> {
        match self {
            IndexingLine::StaticIndexedChoice(tbl) => IndexingLineOffset::Static(&mut tbl.offsets),
            IndexingLine::DynamicIndexedChoice(tbl) => {
                IndexingLineOffset::Dynamic(&mut tbl.offsets)
            }
        }
    }
}

fn fresh_on_demand_subtable<I: SecondLevelIndexType>(
    arg_num: usize,
    specs: IndexingSpecs,
    iter: impl Iterator<Item = I::ThirdLevelIndex>,
    arity: usize,
) -> IndexingLine {
    let tables = VecDeque::from(on_demand_sub_table(arg_num, specs, arity));
    let offsets = VecDeque::from_iter(iter);

    I::to_indexing_line(SecondLevelTable { tables, offsets })
}

enum TermIndexingCodePtrMutDowncast<'a, IndexKey: Clone + Debug> {
    Ptr(IndexKey, IndexingCodePtr),
    Fail,
    Table(&'a mut HashTable<(IndexKey, IndexingCodePtr)>),
}

#[inline]
fn downcast_term_indexing_code_ptr_mut<'a, IndexKey: Copy + Debug>(
    term_ptr: &'a mut TermIndexingCodePtr<IndexKey>,
) -> TermIndexingCodePtrMutDowncast<'a, IndexKey> {
    match term_ptr {
        &mut TermIndexingCodePtr::External(k, e) => {
            TermIndexingCodePtrMutDowncast::Ptr(k, IndexingCodePtr::External(e))
        }
        TermIndexingCodePtr::Fail => TermIndexingCodePtrMutDowncast::Fail,
        &mut TermIndexingCodePtr::Internal(k, i) => {
            TermIndexingCodePtrMutDowncast::Ptr(k, IndexingCodePtr::Internal(i))
        }
        TermIndexingCodePtr::SwitchOnType(tbl) => TermIndexingCodePtrMutDowncast::Table(tbl),
    }
}

pub(crate) enum TermIndexingCodePtrDowncast<'a, IndexKey: Clone + Debug> {
    Ptr(IndexKey, IndexingCodePtr),
    Fail,
    Table(&'a HashTable<(IndexKey, IndexingCodePtr)>),
}

#[inline]
pub(crate) fn downcast_term_indexing_code_ptr<'a, IndexKey: Copy + Debug>(
    term_ptr: &'a TermIndexingCodePtr<IndexKey>,
) -> TermIndexingCodePtrDowncast<'a, IndexKey> {
    match term_ptr {
        &TermIndexingCodePtr::External(k, e) => {
            TermIndexingCodePtrDowncast::Ptr(k, IndexingCodePtr::External(e))
        }
        TermIndexingCodePtr::Fail => TermIndexingCodePtrDowncast::Fail,
        &TermIndexingCodePtr::Internal(k, i) => {
            TermIndexingCodePtrDowncast::Ptr(k, IndexingCodePtr::Internal(i))
        }
        TermIndexingCodePtr::SwitchOnType(tbl) => TermIndexingCodePtrDowncast::Table(tbl),
    }
}

impl IndexingCodePtr {
    #[inline]
    fn external_to_internal(&mut self, indexing_code_len: usize) -> MapPromotion {
        let old = *self;

        if matches!(self, IndexingCodePtr::External(_)) {
            // the *External assumptions rest on the iterator being
            // parked at the first element of clause_view.index
            // (Internal is always a relative offset).
            *self = IndexingCodePtr::Internal(indexing_code_len);
        }

        MapPromotion::from(old)
    }
}

impl<IndexKey: Copy + Debug> TermIndexingCodePtr<IndexKey> {
    fn promote_at_key(
        &mut self,
        key: IndexKey,
        hash_fn: impl Fn(&IndexKey) -> u64,
        eq_fn: impl Fn(&IndexKey, &IndexKey) -> bool,
        clause_offset: usize,
        is_dynamic: bool,
        indexing_code_len: usize,
    ) -> MapPromotion {
        match downcast_term_indexing_code_ptr_mut(self) {
            TermIndexingCodePtrMutDowncast::Ptr(other_key, mut indexing_code_ptr) => {
                if eq_fn(&key, &other_key) {
                    let result = indexing_code_ptr.external_to_internal(indexing_code_len);
                    *self = TermIndexingCodePtr::from((key, indexing_code_ptr));
                    result
                } else {
                    let mut indices = HashTable::new();
                    let other_hash = hash_fn(&other_key);

                    indices.insert_unique(other_hash, (other_key, indexing_code_ptr), |(k, _)| {
                        hash_fn(k)
                    });

                    let new_hash = hash_fn(&key);
                    let (result, ptr) = if is_dynamic {
                        (
                            MapPromotion::DynamicFailToInternal,
                            IndexingCodePtr::Internal(indexing_code_len),
                        )
                    } else {
                        (MapPromotion::None, IndexingCodePtr::External(clause_offset))
                    };

                    indices.insert_unique(new_hash, (key, ptr), |(k, _)| hash_fn(k));
                    *self = TermIndexingCodePtr::SwitchOnType(Box::new(indices));

                    result
                }
            }
            TermIndexingCodePtrMutDowncast::Fail if is_dynamic => {
                // newly introduced keys in dynamic tables are
                // immediately internalized to subtables to avoid on
                // demand regeneration at runtime, i.e. they never
                // contain IndexingCodePtr::External variants.
                *self = TermIndexingCodePtr::Internal(key, indexing_code_len);
                MapPromotion::DynamicFailToInternal
            }
            TermIndexingCodePtrMutDowncast::Fail => {
                let indexing_code_ptr = IndexingCodePtr::External(clause_offset);
                *self = TermIndexingCodePtr::from((key, indexing_code_ptr));
                MapPromotion::None
            }
            TermIndexingCodePtrMutDowncast::Table(tbl) => IndexingLineIter::promote_in_map(
                key,
                hash_fn,
                eq_fn,
                clause_offset,
                is_dynamic,
                tbl,
                indexing_code_len,
            ),
        }
    }
}

pub(crate) fn add_clause_index<'code>(
    clause_view: IndexedClauseView<'code>,
    f64_tbl: &F64Table,
    is_dynamic: bool,
    clause_offset: usize, // the absolute location of the new clause in the code vector.
    append_or_prepend: AppendOrPrepend,
) -> IndexedClauseView<'code> {
    let keys = collect_opt_arg_index_keys(clause_view.rest);
    let mut iter = IndexingLineIter::new(clause_view);
    let key_fn = |arg_num| {
        keys.get(arg_num - 1)
            .copied()
            .unwrap_or(OptArgIndexKey::None)
    };

    while let Some(place) = iter.next(key_fn) {
        let cursor = match place {
            IndexingLinePlace::DeadIndices(cursor, arg_num, indices) => {
                if matches!(key_fn(arg_num), OptArgIndexKey::None) {
                    indices.insert(clause_offset);
                }

                cursor
            }
            IndexingLinePlace::SwitchOnNonePtr(cursor) => {
                let mut indices = IndexSet::with_hasher(FxBuildHasher::default());
                indices.insert(clause_offset);

                iter.view.index[cursor.table_loc].tables_mut()[cursor.table_offset] =
                    IndexedChoiceInstructionTable::DeadIndices {
                        arg_num: iter.arg_num,
                        indices,
                    };

                cursor
            }
            IndexingLinePlace::SwitchOnConstantPtr(cursor, indexing_code_len, cell, term_ptr) => {
                let map_promotion = term_ptr.promote_at_key(
                    cell,
                    |cell| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                    |cell, other_cell| cell.syntactic_eq(f64_tbl, *other_cell),
                    clause_offset,
                    is_dynamic,
                    indexing_code_len,
                );

                iter.implement_map_promotion(map_promotion, append_or_prepend, clause_offset);
                cursor
            }
            IndexingLinePlace::SwitchOnStructurePtr(
                cursor,
                indexing_code_len,
                name,
                arity,
                term_ptr,
            ) => {
                let map_promotion = term_ptr.promote_at_key(
                    (name, arity),
                    |(name, arity)| {
                        let cell = atom_as_cell!(name, *arity);
                        cell.syntactic_hash(f64_tbl, FxHasher::default())
                    },
                    |key, other_key| key == other_key,
                    clause_offset,
                    is_dynamic,
                    indexing_code_len,
                );

                iter.implement_map_promotion(map_promotion, append_or_prepend, clause_offset);
                cursor
            }
            IndexingLinePlace::SwitchOnListPtr(cursor, indexing_code_len, indexing_code_ptr) => {
                let map_promotion = match indexing_code_ptr {
                    Some(indexing_code_ptr) => {
                        indexing_code_ptr.external_to_internal(indexing_code_len)
                    }
                    None if is_dynamic => {
                        *indexing_code_ptr = Some(IndexingCodePtr::Internal(indexing_code_len));
                        MapPromotion::DynamicFailToInternal
                    }
                    None => {
                        let succ_ptr = IndexingCodePtr::External(clause_offset);
                        *indexing_code_ptr = Some(succ_ptr);
                        MapPromotion::from(succ_ptr)
                    }
                };

                iter.implement_map_promotion(map_promotion, append_or_prepend, clause_offset);
                cursor
            }
            IndexingLinePlace::OnDemandInstr(cursor, _) => cursor,
            IndexingLinePlace::StaticOffsets(_cursor, offsets) => {
                IndexingLineOffset::Static(offsets).add(append_or_prepend, clause_offset);
                continue;
            }
            IndexingLinePlace::DynamicOffsets(_cursor, offsets) => {
                IndexingLineOffset::Dynamic(offsets).add(append_or_prepend, clause_offset);
                continue;
            }
        };

        iter.stack.push(cursor.skip_by(1));
    }

    iter.view
}

pub(crate) fn remove_clause_index<'code>(
    clause_view: IndexedClauseView<'code>,
    clause_offset: usize,
    f64_tbl: &F64Table,
) -> IndexedClauseView<'code> {
    let keys = collect_opt_arg_index_keys(clause_view.rest);
    let mut iter = IndexingLineIter::new(clause_view);
    let key_fn = |arg_num| {
        keys.get(arg_num - 1)
            .copied()
            .unwrap_or(OptArgIndexKey::None)
    };

    while let Some(place) = iter.next(key_fn) {
        let cursor = match place {
            IndexingLinePlace::SwitchOnNonePtr(cursor) => cursor,
            IndexingLinePlace::SwitchOnConstantPtr(cursor, _, cell, term_ptr) => {
                match term_ptr {
                    TermIndexingCodePtr::Fail => {}
                    TermIndexingCodePtr::External(..) => {
                        *term_ptr = TermIndexingCodePtr::Fail;
                    }
                    &mut TermIndexingCodePtr::Internal(_k, internal_table_loc) => {
                        iter.remove_from_internal_map(internal_table_loc, clause_offset);
                    }
                    TermIndexingCodePtr::SwitchOnType(indices) => {
                        let map_demotion = IndexingLineIter::demote_at_key(
                            cell,
                            |other_cell| cell.syntactic_eq(f64_tbl, *other_cell),
                            |cell| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                            indices,
                        );

                        if let MapDemotion::Internal(internal_table_loc) = map_demotion {
                            iter.remove_from_internal_map(internal_table_loc, clause_offset);
                        }
                    }
                }

                cursor
            }
            IndexingLinePlace::SwitchOnStructurePtr(cursor, _, name, arity, term_ptr) => {
                match term_ptr {
                    TermIndexingCodePtr::Fail => {}
                    TermIndexingCodePtr::External(..) => {
                        *term_ptr = TermIndexingCodePtr::Fail;
                    }
                    &mut TermIndexingCodePtr::Internal(_k, internal_table_loc) => {
                        iter.remove_from_internal_map(internal_table_loc, clause_offset);
                    }
                    TermIndexingCodePtr::SwitchOnType(tbl) => {
                        let map_demotion = IndexingLineIter::demote_at_key(
                            (name, arity),
                            |other_key| other_key == &(name, arity),
                            |(name, arity)| {
                                let cell = atom_as_cell!(name, *arity);
                                cell.syntactic_hash(f64_tbl, FxHasher::default())
                            },
                            tbl,
                        );

                        if let MapDemotion::Internal(internal_table_loc) = map_demotion {
                            iter.remove_from_internal_map(internal_table_loc, clause_offset);
                        }
                    }
                }

                cursor
            }
            IndexingLinePlace::SwitchOnListPtr(cursor, _, indexing_code_ptr) => {
                match *indexing_code_ptr {
                    Some(IndexingCodePtr::External(_)) => {
                        *indexing_code_ptr = None;
                    }
                    Some(IndexingCodePtr::Internal(internal_table_loc)) => {
                        iter.remove_from_internal_map(internal_table_loc, clause_offset);
                    }
                    None => unreachable!("the list must be indexed here"),
                }

                cursor
            }
            IndexingLinePlace::DeadIndices(cursor, arg_num, indices) => {
                indices.swap_remove(&clause_offset);

                if indices.is_empty() {
                    iter.view.index[cursor.table_loc].tables_mut()[cursor.table_offset] =
                        IndexedChoiceInstructionTable::OnDemandTerm { arg_num };
                }

                cursor
            }
            IndexingLinePlace::OnDemandInstr(cursor, _) => cursor,
            IndexingLinePlace::StaticOffsets(_cursor, offsets) => {
                IndexingLineOffset::Static(offsets).remove(clause_offset);
                continue;
            }
            IndexingLinePlace::DynamicOffsets(_cursor, offsets) => {
                IndexingLineOffset::Dynamic(offsets).remove(clause_offset);
                continue;
            }
        };

        iter.stack.push(cursor.skip_by(1));
    }

    iter.view
}

pub(crate) fn abolish_clause(
    clause_view: IndexedClauseView,
    f64_tbl: &F64Table,
    head_key: OptArgIndexKey,
) {
    let mut iter = IndexingLineIter::new(clause_view);
    let key_fn = |arg_num| {
        if arg_num == 1 {
            head_key
        } else {
            OptArgIndexKey::None
        }
    };

    while let Some(place) = iter.next(key_fn) {
        let cursor = match place {
            IndexingLinePlace::SwitchOnNonePtr(cursor) => cursor,
            IndexingLinePlace::SwitchOnConstantPtr(cursor, _, cell, term_ptr) => {
                match term_ptr {
                    TermIndexingCodePtr::SwitchOnType(indices) => {
                        let hash = cell.syntactic_hash(f64_tbl, FxHasher::default());

                        match indices.entry(
                            hash,
                            |(key, _)| cell.syntactic_eq(f64_tbl, *key),
                            |(cell, _)| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                        ) {
                            hashbrown::hash_table::Entry::Vacant(_entry) => {}
                            hashbrown::hash_table::Entry::Occupied(entry) => {
                                entry.remove();
                            }
                        }
                    }
                    _ => *term_ptr = TermIndexingCodePtr::Fail,
                }

                cursor
            }
            IndexingLinePlace::SwitchOnStructurePtr(cursor, _, name, arity, term_ptr) => {
                match term_ptr {
                    TermIndexingCodePtr::SwitchOnType(tbl) => {
                        let cell = atom_as_cell!(name, arity);
                        let hash = cell.syntactic_hash(f64_tbl, FxHasher::default());

                        match tbl.entry(
                            hash,
                            |(key, _)| key == &(name, arity),
                            |((name, arity), _)| {
                                let cell = atom_as_cell!(name, *arity);
                                cell.syntactic_hash(f64_tbl, FxHasher::default())
                            },
                        ) {
                            hashbrown::hash_table::Entry::Vacant(_entry) => {}
                            hashbrown::hash_table::Entry::Occupied(entry) => {
                                entry.remove();
                            }
                        }
                    }
                    _ => *term_ptr = TermIndexingCodePtr::Fail,
                }

                cursor
            }
            IndexingLinePlace::SwitchOnListPtr(cursor, ..) => cursor, // this cannot happen ..
            IndexingLinePlace::DeadIndices(cursor, ..) => cursor,     // .. nor this
            IndexingLinePlace::OnDemandInstr(cursor, _) => cursor,
            IndexingLinePlace::DynamicOffsets(_cursor, _offsets) => {
                // do nothing! since clause/2 execution can't reach
                // this section (since calling clause(H, B) with
                // var(H) throws an error) allowing clauses to
                // accumulate isn't an immediate problem since GC
                // will eventually clear them out.
                break;
            }
            _ => break,
        };

        iter.stack.push(cursor.skip_by(1));
    }
}
