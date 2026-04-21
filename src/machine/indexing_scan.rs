use fxhash::FxHasher;
use hashbrown::HashTable;

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

fn indices_of_arg<'a, I: Indexer>(
    f64_tbl: &'a F64Table,
    arg_num: usize,
    offsets: &[I::ThirdLevelIndex],
    arity: usize,
    rest: &[Instruction],
) -> CodeOffsets<'a, I> {
    let is_non_counted_bt = is_non_counted_bt(rest);

    // since subsequent OnDemand instructions should be generated for remaining
    // arg_num's < arity, we should consider the predicate to be extensible here,
    // even if it's not under the old definition.
    let mut code_offsets = CodeOffsets::<I>::new(f64_tbl, is_non_counted_bt, arity, true);

    for offset_instr in offsets {
        let clause_offset = offset_instr.offset() - 1;
        let index_key = rest[clause_offset..]
            .iter()
            .find_map(|head_instr| {
                match extract_index_arg(head_instr) {
                    InstructionArg::ArgedHead(instr_arg_num, index_key) if arg_num == instr_arg_num => {
                        Some(Ok(index_key))
                    }
                    InstructionArg::NonHead => Some(Err(())), // stop, can find nothing beyond this point
                    _ => None,
                }
            });

        let index_key = match index_key {
            Some(Ok(index_key)) => index_key,
            _ => continue,
        };

        match index_key {
            OptArgIndexKey::Structure(name, arity) => {
                code_offsets.index_structure(name, arity, clause_offset);
            }
            OptArgIndexKey::Literal(constant) => {
                code_offsets.index_constant(constant, clause_offset);
            }
            OptArgIndexKey::List => {
                code_offsets.index_list(clause_offset);
            }
            OptArgIndexKey::None => {
            }
        }
    }

    code_offsets
}

#[inline]
fn incr_internal_term_ptr(ptr: &mut TermIndexingCodePtr, internal_offset: &mut usize) {
    if let TermIndexingCodePtr::Internal(i) = ptr {
        *i += *internal_offset;
        *internal_offset += 1;
    }
}

#[inline]
fn incr_internal_ptr(ptr: &mut IndexingCodePtr, internal_offset: &mut usize) {
    if let IndexingCodePtr::Internal(i) = ptr {
        *i += *internal_offset;
        *internal_offset += 1;
    }
}

pub(crate) enum SwitchOnTermResult {
    Fail,
    DynamicExternal(usize),
    External(usize),
    Internal(usize),
    DynamicInternal(usize),
    Variadic,
}

impl MachineState {
    #[inline(always)]
    pub(crate) fn switch_on_term(&self, view: &mut IndexedClauseView) -> SwitchOnTermResult {
        let mut oip = 0; // external index

        'outer: while oip < view.index.len() {
            let mut iip = 0; // internal index
            let mut key_type = None;

            loop {
                let index_len = view.index.len();

                match view.index[oip].tables_mut().get_mut(iip) {
                    Some(IndexedChoiceInstructionTable::SwitchOnTerm(reg_num, v, c, l, s)) => {
                        key_type = None;

                        let cell = self.store(self.deref(self.registers[*reg_num]));
                        let term_ptr;

                        (key_type, term_ptr) = read_heap_cell!(cell,
                            (HeapCellValueTag::Str, s_offset) => {
                                let (name, arity) = cell_as_atom_cell!(self.heap[s_offset]).get_name_and_arity();

                                if name == atom!(".") && arity == 2 {
                                    (Some(OptArgIndexKeyType::List), *l)
                                } else {
                                    (Some(OptArgIndexKeyType::Structure(name, arity)), *s)
                                }
                            }
                            (HeapCellValueTag::AttrVar |
                             HeapCellValueTag::StackVar |
                             HeapCellValueTag::Var) => {
                                iip += *v;
                                continue;
                            }
                            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                                (Some(OptArgIndexKeyType::List), *l)
                            }
                            (HeapCellValueTag::Atom) => {
                                (Some(OptArgIndexKeyType::Literal(cell)), *c)
                            }
                            _ => {
                                if Number::try_from((cell, &self.arena.f64_tbl)).is_ok() {
                                    (Some(OptArgIndexKeyType::Literal(cell)), *c)
                                } else {
                                    iip += *v;
                                    continue;
                                }
                            }
                        );

                        match term_ptr {
                            TermIndexingCodePtr::Fail => {
                                return SwitchOnTermResult::Fail;
                            }
                            TermIndexingCodePtr::External(o) => {
                                return SwitchOnTermResult::External(o);
                            }
                            TermIndexingCodePtr::DynamicExternal(o) => {
                                return SwitchOnTermResult::DynamicExternal(o);
                            }
                            TermIndexingCodePtr::TableOffset(iip_delta) => {
                                iip += iip_delta;
                            }
                            TermIndexingCodePtr::Internal(oip_delta) => {
                                oip += oip_delta;
                                continue 'outer;
                            }
                        }
                    }
                    Some(instr) => {
                        let indexing_code_ptr = match instr {
                            IndexedChoiceInstructionTable::SwitchOnConstant(constant_map) => {
                                if let Some(OptArgIndexKeyType::Literal(cell)) = key_type {
                                    let hash = cell
                                        .syntactic_hash(&self.arena.f64_tbl, FxHasher::default());

                                    match constant_map.find(
                                        hash,
                                        |(other_cell, _indexing_code_ptr)| {
                                            cell.syntactic_eq(&self.arena.f64_tbl, *other_cell)
                                        },
                                    ) {
                                        Some(&(_, indexing_code_ptr)) => indexing_code_ptr,
                                        None => {
                                            return SwitchOnTermResult::Fail;
                                        }
                                    }
                                } else {
                                    iip += 1;
                                    continue;
                                }
                            }
                            IndexedChoiceInstructionTable::SwitchOnStructure(str_map) => {
                                if let Some(OptArgIndexKeyType::Structure(name, arity)) = key_type {
                                    let cell = atom_as_cell!(name, arity);
                                    let hash = cell
                                        .syntactic_hash(&self.arena.f64_tbl, FxHasher::default());

                                    match str_map.find(
                                        hash,
                                        |((name, arity), _indexing_code_ptr)| {
                                            let other_cell = atom_as_cell!(name, *arity);
                                            cell.syntactic_eq(&self.arena.f64_tbl, other_cell)
                                        },
                                    ) {
                                        Some(&(_, indexing_code_ptr)) => indexing_code_ptr,
                                        None => {
                                            return SwitchOnTermResult::Fail;
                                        }
                                    }
                                } else {
                                    iip += 1;
                                    continue;
                                }
                            }
                            &mut IndexedChoiceInstructionTable::OnDemandTerm {
                                var_offset,
                                arg_num,
                                arity,
                            } => {
                                let cell = self.store(self.deref(self.registers[arg_num]));

                                if cell.is_var() {
                                    iip += var_offset;
                                    continue;
                                }

                                let (_var_offset, mut indices) = match &mut view.index[oip] {
                                    IndexingLine::IndexedChoice(SecondLevelTable { offsets, .. }) => {
                                        let code_offsets = indices_of_arg::<IndexedChoiceInstruction>(
                                            &self.arena.f64_tbl,
                                            arg_num,
                                            offsets.make_contiguous(),
                                            arity,
                                            &view.rest,
                                        );

                                        // false to skip_stub_try_me_else
                                        code_offsets.compute_indices(arg_num - 1, false)
                                    }
                                    IndexingLine::DynamicIndexedChoice(SecondLevelTable { offsets, .. }) => {
                                        let code_offsets = indices_of_arg::<DynamicIndexedChoiceInstruction>(
                                            &self.arena.f64_tbl,
                                            arg_num,
                                            offsets.make_contiguous(),
                                            arity,
                                            &view.rest,
                                        );

                                        // false to skip_stub_try_me_else
                                        code_offsets.compute_indices(arg_num - 1, false)
                                    }
                                };

                                let mut internal_offset = index_len - oip - 1;
                                // it's important we don't modify iip in what follows.
                                // we still need a local cursor however.
                                let mut local_iip = iip;

                                for table in indices[0].tables_mut().drain(..) {
                                    match table {
                                        IndexedChoiceInstructionTable::SwitchOnTerm(
                                            arg_num, var_offset, mut c, mut l, mut s,
                                        ) => {
                                            // this order reflects that of the compute_indices function
                                            // and so shouldn't be changed.
                                            incr_internal_term_ptr(&mut l, &mut internal_offset);
                                            incr_internal_term_ptr(&mut s, &mut internal_offset);
                                            incr_internal_term_ptr(&mut c, &mut internal_offset);

                                            view.index[oip].tables_mut()[local_iip] =
                                                IndexedChoiceInstructionTable::SwitchOnTerm(arg_num, var_offset, c, l, s);
                                            local_iip += 1;
                                        }
                                        IndexedChoiceInstructionTable::SwitchOnConstant(mut constant_map) => {
                                            for (_, value) in constant_map.iter_mut() {
                                                incr_internal_ptr(value, &mut internal_offset);
                                            }

                                            view.index[oip].tables_mut()[local_iip] =
                                                IndexedChoiceInstructionTable::SwitchOnConstant(constant_map);
                                            local_iip += 1;
                                        }
                                        IndexedChoiceInstructionTable::SwitchOnStructure(mut structure_map) => {
                                            for (_, value) in structure_map.iter_mut() {
                                                incr_internal_ptr(value, &mut internal_offset);
                                            }

                                            view.index[oip].tables_mut()[local_iip] =
                                                IndexedChoiceInstructionTable::SwitchOnStructure(structure_map);
                                            local_iip += 1;
                                        }
                                        _ => break,
                                    }
                                }

                                view.index.extend(indices.drain(1 ..));
                                continue;
                            }
                            IndexedChoiceInstructionTable::OnDemandConstant { .. } => {
                                // change this to an empty static table in case the predicate is extensible and
                                // this instruction remains after its preceding OnDemandTerm was changed to SwitchOnTerm
                                view.index[oip].tables_mut()[iip] = IndexedChoiceInstructionTable::SwitchOnConstant(
                                    HashTable::new(),
                                );
                                continue;
                            }
                            IndexedChoiceInstructionTable::OnDemandStructure { .. } => {
                                // likewise.
                                view.index[oip].tables_mut()[iip] = IndexedChoiceInstructionTable::SwitchOnStructure(
                                    HashTable::new(),
                                );
                                continue;
                            }
                            IndexedChoiceInstructionTable::SwitchOnTerm(..) => {
                                unreachable!();
                            }
                        };

                        match indexing_code_ptr {
                            IndexingCodePtr::External(o) => {
                                return SwitchOnTermResult::External(o);
                            }
                            IndexingCodePtr::DynamicExternal(o) => {
                                return SwitchOnTermResult::DynamicExternal(o)
                            }
                            IndexingCodePtr::Internal(oip_delta) => {
                                oip += oip_delta;
                            }
                        }
                    }
                    None => break 'outer,
                }
            }
        }

        if oip == 0 {
            // resort to ordinary
            // try_me/retry_me_else/trust_me if no
            // eligible indices are found
            SwitchOnTermResult::Variadic
        } else {
            match &view.index[oip] {
                IndexingLine::IndexedChoice(..) => SwitchOnTermResult::Internal(oip),
                IndexingLine::DynamicIndexedChoice(..) => SwitchOnTermResult::DynamicInternal(oip),
            }
        }
    }
}
