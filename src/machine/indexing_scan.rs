use fxhash::{FxBuildHasher, FxHasher};
use indexmap::IndexSet;

use crate::atom_table::*;
use crate::forms::{Number, OptArgIndexKey};
use crate::indexing::*;
use crate::indexing_iter::*;
use crate::instructions::*;
use crate::machine::*;
use crate::offset_table::F64Table;
use crate::types::*;

fn is_non_counted_bt(instrs: &[Instruction]) -> bool {
    if let &Instruction::TryMeElse(offset) = &instrs[0] {
        // use saturating_sub in case offset == 0, which can happen for,
        // e.g., stub choice instructions
        matches!(
            instrs[offset],
            Instruction::DefaultRetryMeElse(_) | Instruction::DefaultTrustMe(_)
        )
    } else {
        false
    }
}

trait PropagatingIndexer: Indexer {
    // preserve the offset but recompute surrounding try/retry/trust as needed
    fn recompute_index(
        index: Self::ThirdLevelIndex,
    ) -> impl FnOnce(bool, bool) -> Self::ThirdLevelIndex;
}

impl PropagatingIndexer for StaticIndexedChoiceInstruction {
    fn recompute_index(
        index: StaticIndexedChoiceInstructionOffset,
    ) -> impl FnOnce(bool, bool) -> Self::ThirdLevelIndex {
        let offset = index.offset() - 1;
        move |is_initial_index, non_counted_bt| {
            Self::compute_index(is_initial_index, offset, non_counted_bt)
        }
    }
}

impl PropagatingIndexer for DynamicIndexedChoiceInstruction {
    fn recompute_index(index: Appended) -> impl FnOnce(bool, bool) -> Self::ThirdLevelIndex {
        move |_is_initial_index, _non_counted_bt| {
            // must preserve prepend or append information
            index
        }
    }
}

enum OnDemandResult<'a, I: Indexer> {
    DeadIndices(Vec<usize>),
    CodeOffsets(CodeOffsets<'a, I>),
}

fn indices_of_arg<'a, I: PropagatingIndexer>(
    f64_tbl: &'a F64Table,
    arg_num: usize,
    offset_iter: impl Iterator<Item = I::ThirdLevelIndex>,
    arity: usize,
    rest: &[Instruction],
    clause_arg_data: &mut ClauseArgData,
) -> OnDemandResult<'a, I> {
    let is_non_counted_bt = is_non_counted_bt(rest);
    let mut var_offsets = vec![];

    // since subsequent OnDemand instructions should be generated for
    // remaining arg_num's < arity.
    let mut code_offsets = CodeOffsets::<I>::new(f64_tbl, is_non_counted_bt, arity);

    for offset_instr in offset_iter {
        let clause_offset = offset_instr.offset() - 1;
        let key_indices = clause_arg_data
            .entry(clause_offset)
            .or_insert_with(|| collect_opt_arg_index_keys(&rest[clause_offset..]));
        let index_key = key_indices
            .get(arg_num - 1)
            .copied()
            .unwrap_or(OptArgIndexKey::None);

        if matches!(index_key, OptArgIndexKey::None) {
            var_offsets.push(clause_offset + 1);
        } else if var_offsets.is_empty() {
            code_offsets.index_key(index_key, I::recompute_index(offset_instr));

            for arg_index in arg_num + 1..=arity {
                let index_key = key_indices
                    .get(arg_index - 1)
                    .copied()
                    .unwrap_or(OptArgIndexKey::None);
                code_offsets.map_clause_offset_to_arg_key(arg_index - 1, index_key, clause_offset);
            }
        }
    }

    if var_offsets.is_empty() {
        OnDemandResult::CodeOffsets(code_offsets)
    } else {
        OnDemandResult::DeadIndices(var_offsets)
    }
}

#[inline]
fn incr_internal_ptr(ptr: &mut IndexingCodePtr, internal_offset: usize) {
    if let IndexingCodePtr::Internal(i) = ptr {
        *i += internal_offset;
    }
}

#[inline]
fn incr_internal_term_ptr<IndexKey>(
    ptr: &mut TermIndexingCodePtr<IndexKey>,
    internal_offset: usize,
) {
    match ptr {
        TermIndexingCodePtr::Internal(i) => {
            *i += internal_offset;
        }
        TermIndexingCodePtr::SwitchOnType(tbl) => {
            for (_, indexing_code_ptr) in tbl.iter_mut() {
                incr_internal_ptr(indexing_code_ptr, internal_offset);
            }
        }
        _ => {}
    }
}

pub(crate) enum SwitchOnTermResult {
    Fail,
    DynamicExternal(Appended),
    DynamicInternal(usize),
    External(usize),
    Internal(usize),
    Variadic,
}

enum SwitchOnTermPtrResult {
    Continue(TableLocation),
    End(SwitchOnTermResult),
}

fn switch_on_indexing_code_ptr(
    cursor: TableLocation,
    indexing_code_ptr: IndexingCodePtr,
) -> SwitchOnTermPtrResult {
    match indexing_code_ptr {
        IndexingCodePtr::DynamicExternal(o) => {
            SwitchOnTermPtrResult::End(SwitchOnTermResult::DynamicExternal(o))
        }
        IndexingCodePtr::External(o) => SwitchOnTermPtrResult::End(SwitchOnTermResult::External(o)),
        IndexingCodePtr::Internal(o) => SwitchOnTermPtrResult::Continue(TableLocation {
            table_loc: cursor.table_loc + o,
            table_offset: 0,
        }),
    }
}

fn switch_on_term_ptr<IndexKey>(
    key: IndexKey,
    hash_fn: impl Fn(&IndexKey) -> u64,
    eq_fn: impl Fn(&IndexKey, &IndexKey) -> bool,
    cursor: TableLocation,
    term_ptr: &TermIndexingCodePtr<IndexKey>,
) -> SwitchOnTermPtrResult {
    match downcast_term_indexing_code_ptr(term_ptr) {
        TermIndexingCodePtrDowncast::Ptr(indexing_code_ptr) => {
            switch_on_indexing_code_ptr(cursor, indexing_code_ptr)
        }
        TermIndexingCodePtrDowncast::Fail => SwitchOnTermPtrResult::End(SwitchOnTermResult::Fail),
        TermIndexingCodePtrDowncast::Table(tbl) => {
            let indexing_code_ptr = match tbl
                .find(hash_fn(&key), |(other_key, _indexing_code_ptr)| {
                    eq_fn(&key, other_key)
                }) {
                Some(&(_, indexing_code_ptr)) => indexing_code_ptr,
                None => {
                    return SwitchOnTermPtrResult::End(SwitchOnTermResult::Fail);
                }
            };

            match indexing_code_ptr {
                IndexingCodePtr::External(o) => {
                    SwitchOnTermPtrResult::End(SwitchOnTermResult::External(o))
                }
                IndexingCodePtr::DynamicExternal(o) => {
                    SwitchOnTermPtrResult::End(SwitchOnTermResult::DynamicExternal(o))
                }
                IndexingCodePtr::Internal(o) => SwitchOnTermPtrResult::Continue(TableLocation {
                    table_loc: cursor.table_loc + o,
                    table_offset: 0,
                }),
            }
        }
    }
}

impl MachineState {
    #[inline(always)]
    pub(crate) fn switch_on_term(
        &self,
        clause_view: IndexedClauseView,
        is_extensible: bool,
    ) -> SwitchOnTermResult {
        let mut clause_arg_data = ClauseArgData::with_hasher(FxBuildHasher::default());
        let mut iter = IndexingLineIter::new(clause_view);
        let key_fn = |arg_num| {
            let cell = self.store(self.deref(self.registers[arg_num]));

            read_heap_cell!(cell,
                (HeapCellValueTag::Str, s_offset) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s_offset]).get_name_and_arity();

                    if name == atom!(".") && arity == 2 {
                        OptArgIndexKey::List
                    } else {
                        OptArgIndexKey::Structure(name, arity)
                    }
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                    OptArgIndexKey::None
                }
                (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                    OptArgIndexKey::List
                }
                (HeapCellValueTag::Atom) => {
                    OptArgIndexKey::Literal(cell)
                }
                _ => {
                    if Number::try_from((cell, &self.arena.f64_tbl)).is_ok() {
                        OptArgIndexKey::Literal(cell)
                    } else {
                        OptArgIndexKey::None
                    }
                }
            )
        };

        while let Some(place) = iter.next(key_fn) {
            match place {
                IndexingLinePlace::SwitchOnNonePtr(cursor) => {
                    iter.stack.push(cursor.skip_by(1));
                }
                IndexingLinePlace::SwitchOnConstantPtr(cursor, _, cell, term_ptr) => {
                    match switch_on_term_ptr(
                        cell,
                        |&cell| cell.syntactic_hash(&self.arena.f64_tbl, FxHasher::default()),
                        |&cell_1, &cell_2| cell_1.syntactic_eq(&self.arena.f64_tbl, cell_2),
                        cursor,
                        term_ptr,
                    ) {
                        SwitchOnTermPtrResult::Continue(cursor) => iter.stack.push(cursor),
                        SwitchOnTermPtrResult::End(result) => return result,
                    }
                }
                IndexingLinePlace::SwitchOnStructurePtr(cursor, _, name, arity, term_ptr) => {
                    match switch_on_term_ptr(
                        (name, arity),
                        |&(name, arity)| {
                            let cell = atom_as_cell!(name, arity);
                            cell.syntactic_hash(&self.arena.f64_tbl, FxHasher::default())
                        },
                        |pi_1, pi_2| pi_1 == pi_2,
                        cursor,
                        term_ptr,
                    ) {
                        SwitchOnTermPtrResult::Continue(cursor) => iter.stack.push(cursor),
                        SwitchOnTermPtrResult::End(result) => return result,
                    }
                }
                IndexingLinePlace::SwitchOnListPtr(cursor, _, indexing_code_ptr_opt) => {
                    if let Some(indexing_code_ptr) = *indexing_code_ptr_opt {
                        match switch_on_indexing_code_ptr(cursor, indexing_code_ptr) {
                            SwitchOnTermPtrResult::Continue(cursor) => {
                                iter.stack.push(cursor);
                            }
                            SwitchOnTermPtrResult::End(result) => {
                                return result;
                            }
                        }
                    }
                }
                IndexingLinePlace::DeadIndices(cursor, ..) => {
                    iter.stack.push(cursor.skip_by(1));
                }
                IndexingLinePlace::StaticOffsets(cursor, _offsets) => {
                    return if cursor.table_loc == 0 {
                        SwitchOnTermResult::Variadic
                    } else {
                        SwitchOnTermResult::Internal(cursor.table_loc)
                    };
                }
                IndexingLinePlace::DynamicOffsets(cursor, _offsets) => {
                    return if cursor.table_loc == 0 {
                        SwitchOnTermResult::Variadic
                    } else {
                        SwitchOnTermResult::DynamicInternal(cursor.table_loc)
                    };
                }
                IndexingLinePlace::OnDemandInstr(cursor, indexing_code_len) => {
                    let cell = self.store(self.deref(self.registers[iter.arg_num]));

                    if cell.is_var() {
                        iter.stack.push(cursor.skip_by(1));
                        continue;
                    }

                    let (_var_offset, mut indices) = match &mut iter.view.index[cursor.table_loc] {
                        IndexingLine::StaticIndexedChoice(SecondLevelTable { offsets, .. }) => {
                            let result = indices_of_arg::<StaticIndexedChoiceInstruction>(
                                &self.arena.f64_tbl,
                                iter.arg_num,
                                offsets.iter().cloned(),
                                iter.view.arity,
                                iter.view.rest,
                                &mut clause_arg_data,
                            );

                            match result {
                                OnDemandResult::DeadIndices(items) => {
                                    let mut indices =
                                        IndexSet::with_hasher(FxBuildHasher::default());
                                    indices.extend(items);

                                    iter.view.index[cursor.table_loc].tables_mut()
                                        [cursor.table_offset] =
                                        IndexedChoiceInstructionTable::DeadIndices {
                                            arg_num: iter.arg_num,
                                            indices,
                                        };
                                    iter.stack.push(cursor.skip_by(1));
                                    continue;
                                }
                                OnDemandResult::CodeOffsets(code_offsets) => {
                                    // false to skip_stub_try_me_else
                                    code_offsets.compute_indices(
                                        is_extensible,
                                        iter.arg_num - 1,
                                        &iter.view.specs,
                                        false,
                                    )
                                }
                            }
                        }
                        IndexingLine::DynamicIndexedChoice(SecondLevelTable {
                            offsets, ..
                        }) => {
                            let result = indices_of_arg::<DynamicIndexedChoiceInstruction>(
                                &self.arena.f64_tbl,
                                iter.arg_num,
                                offsets.iter().cloned(),
                                iter.view.arity,
                                iter.view.rest,
                                &mut clause_arg_data,
                            );

                            match result {
                                OnDemandResult::DeadIndices(items) => {
                                    let mut indices =
                                        IndexSet::with_hasher(FxBuildHasher::default());
                                    indices.extend(items);

                                    iter.view.index[cursor.table_loc].tables_mut()
                                        [cursor.table_offset] =
                                        IndexedChoiceInstructionTable::DeadIndices {
                                            arg_num: iter.arg_num,
                                            indices,
                                        };
                                    iter.stack.push(cursor.skip_by(1));
                                    continue;
                                }
                                OnDemandResult::CodeOffsets(code_offsets) => {
                                    // false to skip_stub_try_me_else
                                    code_offsets.compute_indices(
                                        is_extensible,
                                        iter.arg_num - 1,
                                        &iter.view.specs,
                                        false,
                                    )
                                }
                            }
                        }
                    };

                    let internal_offset = indexing_code_len - cursor.table_loc - 1;
                    let leading_instr = std::mem::replace(
                        &mut indices[0].tables_mut()[0],
                        IndexedChoiceInstructionTable::OnDemandTerm { arg_num: 0 },
                    );

                    match leading_instr {
                        IndexedChoiceInstructionTable::SwitchOnTerm {
                            arg_num,
                            mut constants,
                            lists: mut lists_opt,
                            mut structures,
                        } => {
                            // this order reflects that of the compute_indices function
                            // and so shouldn't be changed.
                            if let Some(lists) = &mut lists_opt {
                                incr_internal_ptr(lists, internal_offset);
                            }

                            incr_internal_term_ptr(&mut structures, internal_offset);
                            incr_internal_term_ptr(&mut constants, internal_offset);

                            iter.view.index[cursor.table_loc].tables_mut()[cursor.table_offset] =
                                IndexedChoiceInstructionTable::SwitchOnTerm {
                                    arg_num,
                                    constants,
                                    lists: lists_opt,
                                    structures,
                                };

                            iter.view.index.extend(indices.drain(1..));
                        }
                        _ => unreachable!(
                            "CodeOffsets::compute_indices must have generated something"
                        ),
                    }

                    // return to the newly generated SwitchOnTerm
                    iter.stack.push(cursor);
                }
            }
        }

        SwitchOnTermResult::Fail
    }
}
