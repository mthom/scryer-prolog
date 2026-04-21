use std::collections::VecDeque;
use std::hash::Hash;

use fxhash::FxHasher;
use hashbrown::hash_table::*;

use crate::atom_table::{Atom, AtomCell};
use crate::forms::{AppendOrPrepend, Level, OptArgIndexKey};
use crate::indexing::cap_choice_seq_with_trust;
use crate::instructions::*;
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

#[derive(Debug, Clone, Copy)]
pub(crate) enum OptArgIndexKeyType {
    Structure(Atom, usize),
    Literal(HeapCellValue),
    List,
}

pub(crate) fn extract_index_arg(instr: &Instruction) -> InstructionArg {
    if matches!(instr, Instruction::Allocate(..) |
                Instruction::GetLevel(..) |
                Instruction::GetPrevLevel(..) |
                Instruction::GetCutPoint(..) |
                Instruction::NeckCut) {
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
fn cap_choice_seq(prelude: &mut [IndexedChoiceInstructionOffset]) {
    if let Some(instr) = prelude.first_mut() {
        *instr = IndexedChoiceInstructionOffset::Try(instr.offset());
    }

    cap_choice_seq_with_trust(prelude);
}

#[inline]
fn uncap_choice_seq_with_trust(prelude: &mut [IndexedChoiceInstructionOffset]) {
    if let Some(instr) = prelude.last_mut() {
        match instr {
            IndexedChoiceInstructionOffset::Trust(i) => {
                *instr = IndexedChoiceInstructionOffset::Retry(*i);
            }
            IndexedChoiceInstructionOffset::DefaultTrust(i) => {
                *instr = IndexedChoiceInstructionOffset::DefaultRetry(*i);
            }
            _ => {}
        }
    }
}

#[inline]
fn uncap_choice_seq_with_try(prelude: &mut [IndexedChoiceInstructionOffset]) {
    if let Some(instr) = prelude.first_mut() {
        if let IndexedChoiceInstructionOffset::Try(i) = instr {
            *instr = IndexedChoiceInstructionOffset::Retry(*i);
        }
    }
}

// compute the OptArgIndexKey's for the arguments of a given compiled
// clause.
fn collect_opt_arg_index_keys(code: &[Instruction]) -> Vec<OptArgIndexKey> {
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

pub(crate) fn first_inst_arg(code: &[Instruction]) -> (usize, OptArgIndexKey) {
    for instr in code {
        match extract_index_arg(instr) {
            InstructionArg::ArgedHead(arg_num, opt_arg_index_key) => {
                return (arg_num, opt_arg_index_key);
            }
            InstructionArg::ArglessHead | InstructionArg::Prologue => {}
            InstructionArg::NonHead => break,
        }
    }

    (0, OptArgIndexKey::None)
}

#[derive(Copy, Clone, Debug, Default)]
struct TableLocation {
    table_loc: usize,
    table_offset: usize,
}

trait TryNextDelta<IndexPtr> {
    fn try_next_delta(&self, index: &IndexPtr) -> Option<Self>
    where
        Self: Sized;
}

impl TryNextDelta<TermIndexingCodePtr> for TableLocation {
    fn try_next_delta(&self, indexing_ptr: &TermIndexingCodePtr) -> Option<Self> {
        match indexing_ptr {
            TermIndexingCodePtr::Fail
            | TermIndexingCodePtr::External(_)
            | TermIndexingCodePtr::DynamicExternal(_) => None,
            &TermIndexingCodePtr::TableOffset(next_table_offset) => {
                Some(self.skip_by(next_table_offset))
            }
            &TermIndexingCodePtr::Internal(indexing_line_offset) => Some(TableLocation {
                table_loc: indexing_line_offset,
                table_offset: 0,
            }),
        }
    }
}

impl TryNextDelta<IndexingCodePtr> for TableLocation {
    fn try_next_delta(&self, indexing_ptr: &IndexingCodePtr) -> Option<Self> {
        match indexing_ptr {
            IndexingCodePtr::External(_) | IndexingCodePtr::DynamicExternal(_) => None,
            &IndexingCodePtr::Internal(indexing_line_offset) => Some(TableLocation {
                table_loc: indexing_line_offset,
                table_offset: 0,
            }),
        }
    }
}

impl TableLocation {
    #[inline]
    fn skip_by(&self, offset: usize) -> Self {
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
}

pub(crate) enum IndexingLineOffset<'a> {
    Static(&'a mut VecDeque<IndexedChoiceInstructionOffset>),
    Dynamic(&'a mut VecDeque<DynamicIndexedChoiceInstructionOffset>),
}

impl<'code> IndexingLineOffset<'code> {
    #[inline]
    fn to_place(self) -> IndexingLinePlace<'code> {
        match self {
            IndexingLineOffset::Static(offsets) => IndexingLinePlace::StaticOffsets(offsets),
            IndexingLineOffset::Dynamic(offsets) => IndexingLinePlace::DynamicOffsets(offsets),
        }
    }
}

impl<'a> IndexedClauseView<'a> {
    pub(crate) fn try_from_code(code: &'a mut [Instruction]) -> Option<Self> {
        match code.split_at_mut_checked(1) {
            Some(([Instruction::IndexingCode(var_offset, index)], rest)) => {
                Some(Self { index, rest: &rest[var_offset.offset() - 1 ..], })
            }
            _ => None,
        }
    }
}

pub(crate) fn try_split_indexing_line_at<'a>(
    index: &'a mut Vec<IndexingLine>,
    table_loc: usize,
) -> Option<(
    &'a mut VecDeque<IndexedChoiceInstructionTable>,
    IndexingLineOffset<'a>,
)> {
    index
        .get_mut(table_loc)
        .map(|indexing_line| match indexing_line {
            IndexingLine::IndexedChoice(SecondLevelTable { tables, offsets }) => {
                (tables, IndexingLineOffset::Static(offsets))
            }
            IndexingLine::DynamicIndexedChoice(SecondLevelTable { tables, offsets }) => {
                (tables, IndexingLineOffset::Dynamic(offsets))
            }
        })
}

// expose, step by step, access to the components that must be
// modified (i.e. adding or removing indices), in order found
// according to clause data, e.g. a sequence of OptArgIndexKey
// values. and maintain "side" information as well, like access to
// try-retry-trust/dynamic_else sequences.
pub(crate) struct IndexingLineIter<'code, 'keys> {
    stack: Vec<TableLocation>,
    view: IndexedClauseView<'code>,
    keys: &'keys [OptArgIndexKey],
    arg_num: usize,
}

pub(crate) enum IndexingLinePlace<'a> {
    SwitchOnTermPtr(
        &'a mut TermIndexingCodePtr,
        TableLocation,
        OptArgIndexKeyType,
        usize,
    ),
    SwitchOnConstantPtr(
        &'a mut HashTable<(HeapCellValue, IndexingCodePtr)>,
        usize,
        HeapCellValue,
    ),
    SwitchOnStructurePtr(
        &'a mut HashTable<((Atom, usize), IndexingCodePtr)>,
        usize,
        Atom,
        usize,
    ),
    OnDemandInstr, // a placeholder. currently OnDemand* instrs are unprocessed.
    StaticOffsets(&'a mut VecDeque<IndexedChoiceInstructionOffset>),
    DynamicOffsets(&'a mut VecDeque<DynamicIndexedChoiceInstructionOffset>),
}

impl<'code, 'keys> IndexingLineIter<'code, 'keys> {
    pub(crate) fn new(view: IndexedClauseView<'code>, keys: &'keys [OptArgIndexKey]) -> Self {
        Self {
            stack: vec![TableLocation {
                table_loc: 0,
                table_offset: 0,
            }],
            view,
            keys,
            arg_num: 1,
        }
    }

    // move a previously External pointer value to a new subtable,
    // and continue the iteration so that clause_offset to be indexed
    // is added to it in the next iteration.
    #[must_use]
    fn push_new_index(&mut self, is_dynamic: bool, offset: usize) {
        let tables = on_demand_sub_table(self.arg_num + 1, self.keys.len());
        let table_len = tables.len();
        let table_loc = self.view.index.len();

        let second_lvl_tbl = if is_dynamic {
            IndexingLine::DynamicIndexedChoice(SecondLevelTable {
                tables,
                offsets: VecDeque::from(vec![offset]),
            })
        } else {
            IndexingLine::IndexedChoice(SecondLevelTable {
                tables,
                offsets: VecDeque::from(vec![IndexedChoiceInstructionOffset::Try(offset)]),
            })
        };

        self.view.index.push(second_lvl_tbl);
        self.stack.push(TableLocation {
            table_loc,
            table_offset: table_len,
        });
    }

    // return Some if a new table (i.e. an Internal pointer) was created
    // which must contain the argument of the former External/DynamicExternal pointer.
    #[must_use]
    fn promote_in_map<IndexKey>(
        key: IndexKey,
        hash_fn: impl Fn(&IndexKey) -> u64,
        eq_fn: impl Fn(&IndexKey) -> bool,
        new_clause_offset: usize,
        is_dynamic: bool,
        indices: &mut HashTable<(IndexKey, IndexingCodePtr)>,
        indexing_code_len: usize,
    ) -> Option<usize> {
        let hash = hash_fn(&key);

        match indices.entry(hash, |(key, _)| eq_fn(key), |(key, _)| hash_fn(key)) {
            hashbrown::hash_table::Entry::Vacant(entry) => {
                let ptr = if is_dynamic {
                    IndexingCodePtr::DynamicExternal(new_clause_offset)
                } else {
                    IndexingCodePtr::External(new_clause_offset)
                };
                entry.insert((key, ptr));
                None
            }
            hashbrown::hash_table::Entry::Occupied(mut entry) => {
                let val = entry.get_mut();
                match val.1 {
                    IndexingCodePtr::External(other_clause_offset)
                    | IndexingCodePtr::DynamicExternal(other_clause_offset) => {
                        val.1 = IndexingCodePtr::Internal(indexing_code_len);
                        Some(other_clause_offset)
                    }
                    IndexingCodePtr::Internal(_) => None,
                }
            }
        }
    }

    fn switch_on<IndexKey>(
        &mut self,
        key: IndexKey,
        hash_fn: impl Fn(&IndexKey) -> u64,
        instr_fn: impl Fn(HashTable<(IndexKey, IndexingCodePtr)>) -> IndexedChoiceInstructionTable,
        table_loc: usize,
        indexing_ptr: IndexingCodePtr,
    ) {
        let hash = hash_fn(&key);
        let mut map: HashTable<(IndexKey, IndexingCodePtr)> = HashTable::new();

        map.insert_unique(hash, (key, indexing_ptr), |(key, _)| hash_fn(key));

        let indexing_code_len = self.view.index[table_loc].tables().len();

        self.view.index[table_loc]
            .tables_mut()
            .push_back(instr_fn(map));

        self.stack.push(TableLocation {
            table_loc,
            table_offset: indexing_code_len,
        });
    }

    #[must_use]
    fn promote_external_to_internal(
        &mut self,
        table_loc: usize,
        is_dynamic: bool,
        key_type: OptArgIndexKeyType,
        clause_offset: usize,
        f64_tbl: &F64Table,
    ) {
        match key_type {
            OptArgIndexKeyType::Literal(..) => {
                let other_key = search_constant(&self.view.rest[clause_offset - 1..], self.arg_num)
                    .expect("switch_on_term said this key must exist");

                self.switch_on(
                    other_key,
                    |cell| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                    IndexedChoiceInstructionTable::SwitchOnConstant,
                    table_loc,
                    if is_dynamic {
                        IndexingCodePtr::DynamicExternal(clause_offset)
                    } else {
                        IndexingCodePtr::External(clause_offset)
                    },
                );
            }
            OptArgIndexKeyType::Structure(..) => {
                let other_key =
                    search_structure(&self.view.rest[clause_offset - 1..], self.arg_num)
                        .expect("switch_on_term said this key must exist");

                self.switch_on(
                    other_key,
                    |(name, arity)| {
                        let cell = atom_as_cell!(name, *arity);
                        cell.syntactic_hash(f64_tbl, FxHasher::default())
                    },
                    IndexedChoiceInstructionTable::SwitchOnStructure,
                    table_loc,
                    if is_dynamic {
                        IndexingCodePtr::DynamicExternal(clause_offset)
                    } else {
                        IndexingCodePtr::External(clause_offset)
                    },
                );
            }
            OptArgIndexKeyType::List => {
                self.push_new_index(is_dynamic, clause_offset);
            }
        }
    }

    fn promote_offsets_jump_to_map(
        &mut self,
        table_loc: usize,
        key_type: OptArgIndexKeyType,
        internal_table_offset: usize,
        f64_tbl: &F64Table,
    ) {
        let clause_offset = match &self.view.index[table_loc + internal_table_offset] {
            IndexingLine::IndexedChoice(tbl) => tbl.offsets[0].offset(),
            IndexingLine::DynamicIndexedChoice(tbl) => tbl.offsets[0].offset(),
        };

        match key_type {
            OptArgIndexKeyType::Literal(..) => {
                let other_key = search_constant(&self.view.rest[clause_offset - 1..], self.arg_num)
                    .expect("switch_on_term said this key must exist");

                self.switch_on(
                    other_key,
                    |cell| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                    IndexedChoiceInstructionTable::SwitchOnConstant,
                    table_loc,
                    IndexingCodePtr::Internal(internal_table_offset),
                );
            }
            OptArgIndexKeyType::Structure(..) => {
                let other_key =
                    search_structure(&self.view.rest[clause_offset - 1..], self.arg_num)
                        .expect("switch_on_term said this key must exist");

                self.switch_on(
                    other_key,
                    |(name, arity)| {
                        let cell = atom_as_cell!(name, *arity);
                        cell.syntactic_hash(f64_tbl, FxHasher::default())
                    },
                    IndexedChoiceInstructionTable::SwitchOnStructure,
                    table_loc,
                    IndexingCodePtr::Internal(internal_table_offset),
                );
            }
            OptArgIndexKeyType::List => {
                self.stack.push(TableLocation {
                    table_loc: table_loc + internal_table_offset,
                    table_offset: 0,
                });
            }
        }
    }

    // this isn't wrapped in an Iterator instance because there's no
    // way to reconcile the lifetimes of self and the Item type
    // within the trait.
    pub(crate) fn next(&mut self, f64_tbl: &F64Table) -> Option<IndexingLinePlace> {
        let indexing_code_len = self.view.index.len();

        if let Some(cursor) = self.stack.pop() {
            match try_split_indexing_line_at(self.view.index, cursor.table_loc) {
                Some((tables, offsets)) => match tables.get_mut(cursor.table_offset) {
                    Some(next_instr) => match next_instr {
                        IndexedChoiceInstructionTable::SwitchOnTerm(
                            arg_num,
                            var_ptr,
                            constant_ptr,
                            list_ptr,
                            str_ptr,
                        ) => {
                            self.stack.push(cursor.skip_by(var_ptr.offset()));
                            self.arg_num = *arg_num;

                            let (key_type, indexing_ptr) = match &self.keys[self.arg_num - 1] {
                                &OptArgIndexKey::Structure(name, arity) => {
                                    (OptArgIndexKeyType::Structure(name, arity), str_ptr)
                                }
                                &OptArgIndexKey::Literal(literal) => {
                                    (OptArgIndexKeyType::Literal(literal), constant_ptr)
                                }
                                OptArgIndexKey::List => (OptArgIndexKeyType::List, list_ptr),
                                OptArgIndexKey::None => {
                                    unreachable!("arg_num cannot be None here")
                                }
                            };

                            if let Some(next_cursor) = cursor.try_next_delta(indexing_ptr) {
                                self.stack.push(next_cursor);
                            }

                            Some(IndexingLinePlace::SwitchOnTermPtr(
                                indexing_ptr,
                                cursor,
                                key_type,
                                indexing_code_len,
                            ))
                        }
                        IndexedChoiceInstructionTable::SwitchOnStructure(str_map) => {
                            if let OptArgIndexKey::Structure(name, arity) =
                                self.keys[self.arg_num - 1]
                            {
                                let cell = atom_as_cell!(name, arity);
                                let hash = cell.syntactic_hash(f64_tbl, FxHasher::default());

                                if let Some(next_cursor) = str_map
                                    .find(hash, |((name, arity), _indexing_code_ptr)| {
                                        let other_cell = atom_as_cell!(name, *arity);
                                        cell.syntactic_eq(f64_tbl, other_cell)
                                    })
                                    .and_then(|(_, indexing_ptr)| {
                                        cursor.try_next_delta(indexing_ptr)
                                    })
                                {
                                    self.stack.push(next_cursor);
                                }

                                Some(IndexingLinePlace::SwitchOnStructurePtr(
                                    str_map,
                                    indexing_code_len,
                                    name,
                                    arity,
                                ))
                            } else {
                                unreachable!(
                                    "there must a predicate indicator at arg_num {}",
                                    self.arg_num
                                )
                            }
                        }
                        IndexedChoiceInstructionTable::SwitchOnConstant(constant_map) => {
                            if let OptArgIndexKey::Literal(cell) = self.keys[self.arg_num - 1] {
                                let hash = cell.syntactic_hash(f64_tbl, FxHasher::default());

                                if let Some(next_cursor) = constant_map
                                    .find(hash, |(other_cell, _indexing_code_ptr)| {
                                        cell.syntactic_eq(f64_tbl, *other_cell)
                                    })
                                    .and_then(|(_, indexing_ptr)| {
                                        cursor.try_next_delta(indexing_ptr)
                                    })
                                {
                                    self.stack.push(next_cursor);
                                }

                                Some(IndexingLinePlace::SwitchOnConstantPtr(
                                    constant_map,
                                    indexing_code_len,
                                    cell,
                                ))
                            } else {
                                unreachable!("there must a Literal at arg_num {}", self.arg_num)
                            }
                        }
                        IndexedChoiceInstructionTable::OnDemandTerm { .. }
                        | IndexedChoiceInstructionTable::OnDemandStructure { .. }
                        | IndexedChoiceInstructionTable::OnDemandConstant { .. } => {
                            self.stack.push(cursor.skip_by(1));
                            Some(IndexingLinePlace::OnDemandInstr)
                        }
                    },
                    None => Some(offsets.to_place()),
                },
                None => None,
            }
        } else {
            None
        }
    }

    #[must_use]
    fn demote_second_level_map_key<IndexKey: Eq + Hash>(
        key: IndexKey,
        mut eq_fn: impl FnMut(&IndexKey) -> bool,
        hash_fn: impl Fn(&IndexKey) -> u64,
        indices: &mut HashTable<(IndexKey, IndexingCodePtr)>,
    ) -> Option<IndexingCodePtr> {
        let hash = hash_fn(&key);

        match indices.entry(hash, |(key, _)| eq_fn(key), |(key, _)| hash_fn(key)) {
            hashbrown::hash_table::Entry::Vacant(_entry) => None,
            hashbrown::hash_table::Entry::Occupied(entry) => {
                match entry.get().1 {
                    IndexingCodePtr::External(_) | IndexingCodePtr::DynamicExternal(_) => {
                        Some((entry.remove().0).1)
                    }
                    IndexingCodePtr::Internal(_) => {
                        // don't demote the Internal to External even if only
                        // one clause will remain at the Internal subtable after removal
                        // to allow indexing on remaining args.
                        None
                    }
                }
            }
        }
    }

    fn demote_switch_on_term_key(
        &mut self,
        switch_on_term_loc: TableLocation,
        key_type: OptArgIndexKeyType,
        removed_indexing_ptr_opt: Option<IndexingCodePtr>,
    ) {
        match &mut self.view.index[switch_on_term_loc.table_loc] {
            IndexingLine::IndexedChoice(SecondLevelTable { tables, .. })
            | IndexingLine::DynamicIndexedChoice(SecondLevelTable { tables, .. }) => {
                match &mut tables[switch_on_term_loc.table_offset] {
                    IndexedChoiceInstructionTable::SwitchOnTerm(_, _, c, l, s) => {
                        let indexing_code_ptr = match key_type {
                            OptArgIndexKeyType::Structure(..) => s,
                            OptArgIndexKeyType::Literal(..) => c,
                            OptArgIndexKeyType::List => l,
                        };

                        match indexing_code_ptr {
                            TermIndexingCodePtr::Fail => {}
                            TermIndexingCodePtr::External(_)
                            | TermIndexingCodePtr::DynamicExternal(_) => {
                                *indexing_code_ptr = TermIndexingCodePtr::Fail;
                            }
                            TermIndexingCodePtr::TableOffset(_)
                            | TermIndexingCodePtr::Internal(_) => {
                                if let Some(removed_indexing_ptr) = removed_indexing_ptr_opt {
                                    *indexing_code_ptr =
                                        TermIndexingCodePtr::from(removed_indexing_ptr);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

fn on_demand_sub_table(arg_num: usize, arity: usize) -> VecDeque<IndexedChoiceInstructionTable> {
    let mut table = Vec::with_capacity(3 * (arity + 1 - arg_num));

    for arg_num in arg_num..=arity {
        table.push(IndexedChoiceInstructionTable::OnDemandTerm {
            var_offset: 1,
            arg_num,
            arity,
        });
        table.push(IndexedChoiceInstructionTable::OnDemandConstant {
            reg_num: arg_num,
            arity,
        });
        table.push(IndexedChoiceInstructionTable::OnDemandStructure {
            reg_num: arg_num,
            arity,
        });
    }

    VecDeque::from(table)
}

fn search_constant(instrs: &[Instruction], arg_num: usize) -> Option<HeapCellValue> {
    for instr in instrs {
        match instr {
            &Instruction::GetConstant(Level::Shallow, literal, RegType::Temp(t))
                if t == arg_num =>
            {
                return Some(literal);
            }
            _ => {}
        }
    }

    None
}

fn search_structure(instrs: &[Instruction], arg_num: usize) -> Option<(Atom, usize)> {
    for instr in instrs {
        match instr {
            &Instruction::GetStructure(Level::Shallow, name, arity, RegType::Temp(t))
                if t == arg_num =>
            {
                return Some((name, arity));
            }
            _ => {}
        }
    }

    None
}

pub(crate) fn add_clause_index<'code>(
    clause_view: IndexedClauseView<'code>,
    f64_tbl: &F64Table,
    is_dynamic: bool,
    clause_offset: usize, // the absolute location of the new clause in the code vector.
    append_or_prepend: AppendOrPrepend,
) -> IndexedClauseView<'code> {
    let opt_arg_index_keys = collect_opt_arg_index_keys(clause_view.rest);
    let mut iter = IndexingLineIter::new(clause_view, &opt_arg_index_keys);

    while let Some(place) = iter.next(f64_tbl) {
        match place {
            IndexingLinePlace::SwitchOnTermPtr(
                indexing_code_ptr,
                sot_loc,
                key_type,
                indexing_code_len,
            ) => match *indexing_code_ptr {
                TermIndexingCodePtr::Fail => {
                    *indexing_code_ptr = if is_dynamic {
                        TermIndexingCodePtr::DynamicExternal(clause_offset)
                    } else {
                        TermIndexingCodePtr::External(clause_offset)
                    };
                }
                TermIndexingCodePtr::DynamicExternal(other_clause_offset)
                | TermIndexingCodePtr::External(other_clause_offset) => {
                    *indexing_code_ptr = match key_type {
                        OptArgIndexKeyType::List => {
                            TermIndexingCodePtr::Internal(indexing_code_len)
                        }
                        OptArgIndexKeyType::Literal(_) | OptArgIndexKeyType::Structure(..) => {
                            TermIndexingCodePtr::TableOffset(indexing_code_len - sot_loc.table_loc)
                        }
                    };

                    iter.promote_external_to_internal(
                        sot_loc.table_loc,
                        is_dynamic,
                        key_type,
                        other_clause_offset,
                        f64_tbl,
                    );
                }
                TermIndexingCodePtr::Internal(internal_table_loc) => {
                    iter.promote_offsets_jump_to_map(
                        sot_loc.table_loc,
                        key_type,
                        internal_table_loc,
                        f64_tbl,
                    );
                }
                TermIndexingCodePtr::TableOffset(_) => {}
            },
            IndexingLinePlace::SwitchOnConstantPtr(index_map, indexing_code_len, constant) => {
                let other_clause_offset_opt = IndexingLineIter::promote_in_map(
                    constant,
                    |cell| cell.syntactic_hash(f64_tbl, FxHasher::default()),
                    |other_cell| constant.syntactic_eq(f64_tbl, *other_cell),
                    clause_offset,
                    is_dynamic,
                    index_map,
                    indexing_code_len,
                );

                if let Some(other_clause_offset) = other_clause_offset_opt {
                    iter.push_new_index(is_dynamic, other_clause_offset);
                }
            }
            IndexingLinePlace::SwitchOnStructurePtr(index_map, indexing_code_len, name, arity) => {
                if let Some(other_clause_offset) = IndexingLineIter::promote_in_map(
                    (name, arity),
                    |(name, arity)| {
                        let cell = atom_as_cell!(name, *arity);
                        cell.syntactic_hash(f64_tbl, FxHasher::default())
                    },
                    |other_key| &(name, arity) == other_key,
                    clause_offset,
                    is_dynamic,
                    index_map,
                    indexing_code_len,
                ) {
                    iter.push_new_index(is_dynamic, other_clause_offset);
                }
            }
            IndexingLinePlace::StaticOffsets(offsets) => {
                if append_or_prepend.is_append() {
                    uncap_choice_seq_with_trust(offsets.make_contiguous());
                    offsets.push_back(IndexedChoiceInstructionOffset::Trust(clause_offset));
                } else {
                    uncap_choice_seq_with_try(offsets.make_contiguous());
                    offsets.push_front(IndexedChoiceInstructionOffset::Try(clause_offset));
                }
            }
            IndexingLinePlace::DynamicOffsets(offsets) => {
                if append_or_prepend.is_append() {
                    offsets.push_back(clause_offset);
                } else {
                    offsets.push_front(clause_offset);
                }
            }
            IndexingLinePlace::OnDemandInstr => {}
        }
    }

    iter.view
}

pub(crate) fn remove_clause_index<'code>(
    clause_view: IndexedClauseView<'code>,
    clause_offset: usize,
    f64_tbl: &F64Table,
) -> IndexedClauseView<'code> {
    let opt_arg_index_keys = collect_opt_arg_index_keys(clause_view.rest);
    let mut iter = IndexingLineIter::new(clause_view, &opt_arg_index_keys);
    let mut switch_on_term_loc = TableLocation::default();

    while let Some(place) = iter.next(f64_tbl) {
        match place {
            IndexingLinePlace::SwitchOnTermPtr(indexing_code_ptr, sot_loc, ..) => {
                match indexing_code_ptr {
                    TermIndexingCodePtr::Fail => {}
                    TermIndexingCodePtr::External(_) | TermIndexingCodePtr::DynamicExternal(_) => {
                        *indexing_code_ptr = TermIndexingCodePtr::Fail;
                    }
                    TermIndexingCodePtr::Internal(_) | TermIndexingCodePtr::TableOffset(_) => {
                        switch_on_term_loc = sot_loc;
                    }
                }
            }
            IndexingLinePlace::SwitchOnStructurePtr(index_map, _, name, arity) => {
                let removed_indexing_code_ptr_opt = IndexingLineIter::demote_second_level_map_key(
                    (name, arity),
                    |other_key| other_key == &(name, arity),
                    |(name, arity)| {
                        let cell = atom_as_cell!(name, *arity);
                        cell.syntactic_hash(f64_tbl, FxHasher::default())
                    },
                    index_map,
                );

                iter.demote_switch_on_term_key(
                    switch_on_term_loc,
                    OptArgIndexKeyType::Structure(name, arity),
                    removed_indexing_code_ptr_opt,
                );
            }
            IndexingLinePlace::SwitchOnConstantPtr(index_map, _, constant) => {
                let removed_indexing_code_ptr_opt = IndexingLineIter::demote_second_level_map_key(
                    constant,
                    |other_cell| constant.syntactic_eq(f64_tbl, *other_cell),
                    |constant| constant.syntactic_hash(f64_tbl, FxHasher::default()),
                    index_map,
                );

                iter.demote_switch_on_term_key(
                    switch_on_term_loc,
                    OptArgIndexKeyType::Literal(constant),
                    removed_indexing_code_ptr_opt,
                );
            }
            IndexingLinePlace::StaticOffsets(offsets) => {
                if let Ok(idx) =
                    offsets.binary_search_by(|instr| instr.offset().cmp(&clause_offset))
                {
                    offsets.remove(idx);
                    cap_choice_seq(offsets.make_contiguous());
                }
            }
            IndexingLinePlace::DynamicOffsets(offsets) => {
                if let Ok(idx) = offsets.binary_search(&clause_offset) {
                    offsets.remove(idx);
                }
            }
            IndexingLinePlace::OnDemandInstr => {}
        }
    }

    iter.view
}
