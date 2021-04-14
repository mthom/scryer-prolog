use prolog_parser::ast::*;
use prolog_parser::clause_name;
use prolog_parser::tabled_rc::*;

use crate::forms::*;
use crate::instructions::*;

use crate::rug::Integer;
use indexmap::IndexMap;

use slice_deque::{sdeq, SliceDeque};

use std::convert::TryFrom;
use std::hash::Hash;
use std::iter::once;
use std::mem;
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
pub(crate) enum IndexingCodePtr {
    External(usize), // the index points past the indexing instruction prelude.
    DynamicExternal(usize), // an External index of a dynamic predicate, potentially invalidated by retraction.
    Fail,
    Internal(usize), // the index points into the indexing instruction prelude.
}

#[derive(Debug, Clone, Copy)]
enum OptArgIndexKeyType {
    Structure,
    Constant,
    // List,
}

impl OptArgIndexKey {
    #[inline]
    fn has_key_type(&self, key_type: OptArgIndexKeyType) -> bool {
        match (self, key_type) {
            (OptArgIndexKey::Constant(..), OptArgIndexKeyType::Constant)
            | (OptArgIndexKey::Structure(..), OptArgIndexKeyType::Structure)
            // | (OptArgIndexKey::List(..), OptArgIndexKeyType::List)
            => true,
            _ => false,
        }
    }
}

#[inline]
fn search_skeleton_for_first_key_type(
    skeleton: &[ClauseIndexInfo],
    key_type: OptArgIndexKeyType,
    append_or_prepend: AppendOrPrepend,
) -> Option<&OptArgIndexKey> {
    if append_or_prepend.is_append() {
        for clause_index_info in skeleton.iter().rev() {
            if clause_index_info.opt_arg_index_key.has_key_type(key_type) {
                return Some(&clause_index_info.opt_arg_index_key);
            }
        }
    } else {
        for clause_index_info in skeleton.iter() {
            if clause_index_info.opt_arg_index_key.has_key_type(key_type) {
                return Some(&clause_index_info.opt_arg_index_key);
            }
        }
    }

    None
}

struct IndexingCodeMergingPtr<'a> {
    skeleton: &'a mut [ClauseIndexInfo],
    indexing_code: &'a mut Vec<IndexingLine>,
    offset: usize,
    append_or_prepend: AppendOrPrepend,
    is_dynamic: bool,
}

impl<'a> IndexingCodeMergingPtr<'a> {
    #[inline]
    fn new(
        skeleton: &'a mut [ClauseIndexInfo],
        indexing_code: &'a mut Vec<IndexingLine>,
        append_or_prepend: AppendOrPrepend,
    ) -> Self {
        let is_dynamic = match &indexing_code[0] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, ..)) => {
                match v {
                    IndexingCodePtr::External(_) => false,
                    IndexingCodePtr::DynamicExternal(_) => true,
                    _ => unreachable!()
                }
            }
            _ => unreachable!()
        };

        Self {
            skeleton,
            indexing_code,
            offset: 0,
            append_or_prepend,
            is_dynamic,
        }
    }

    fn internalize_constant(&mut self, constant_ptr: IndexingCodePtr) {
        let constant_key = search_skeleton_for_first_key_type(
            self.skeleton,
            OptArgIndexKeyType::Constant,
            self.append_or_prepend,
        );

        let mut constants = IndexMap::new();

        match constant_key {
            Some(OptArgIndexKey::Constant(_, _, ref constant, _)) => {
                constants.insert(constant.clone(), constant_ptr);
            }
            _ => {
                if let IndexingCodePtr::DynamicExternal(_) = constant_ptr {
                    // this must be a defunct clause, because it's been deleted
                    // from the skeleton.
                } else {
                    unreachable!()
                }
            }
        }

        if let IndexingCodePtr::Internal(_) = constant_ptr {
            let last_index = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnConstant(constants),
            ));

            self.indexing_code.swap(self.offset, last_index);
        } else {
            self.offset = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnConstant(constants),
            ));
        }
    }

    fn add_static_indexed_choice_for_constant(
        &mut self,
        external: usize,
        constant: Constant,
        index: usize,
    ) {
        let third_level_index = if self.append_or_prepend.is_append() {
            sdeq![
                IndexedChoiceInstruction::Try(external),
                IndexedChoiceInstruction::Trust(index)
            ]
        } else {
            sdeq![
                IndexedChoiceInstruction::Try(index),
                IndexedChoiceInstruction::Trust(external)
            ]
        };

        let indexing_code_len = self.indexing_code.len();
        self.indexing_code.push(IndexingLine::IndexedChoice(third_level_index));

        match &mut self.indexing_code[self.offset] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref mut constants)) => {
                constants.insert(
                    constant,
                    IndexingCodePtr::Internal(indexing_code_len - self.offset),
                );
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn add_dynamic_indexed_choice_for_constant(
        &mut self,
        external: usize,
        constant: Constant,
        index: usize,
    ) {
        let third_level_index = if self.append_or_prepend.is_append() {
            sdeq![external, index]
        } else {
            sdeq![index, external]
        };

        let indexing_code_len = self.indexing_code.len();
        self.indexing_code.push(IndexingLine::DynamicIndexedChoice(third_level_index));

        match &mut self.indexing_code[self.offset] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref mut constants)) => {
                constants.insert(
                    constant,
                    IndexingCodePtr::Internal(indexing_code_len - self.offset),
                );
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn extend_indexed_choice(&mut self, index: usize) {
        match &mut self.indexing_code[self.offset] {
            IndexingLine::IndexedChoice(ref mut indexed_choice_instrs)
                if self.append_or_prepend.is_append() =>
            {
                uncap_choice_seq_with_trust(indexed_choice_instrs);
                indexed_choice_instrs.push_back(IndexedChoiceInstruction::Trust(index));
            }
            IndexingLine::IndexedChoice(ref mut indexed_choice_instrs) => {
                uncap_choice_seq_with_try(indexed_choice_instrs);
                indexed_choice_instrs.push_front(IndexedChoiceInstruction::Try(index));
            }
            IndexingLine::DynamicIndexedChoice(ref mut indexed_choice_instrs)
                if self.append_or_prepend.is_append() =>
            {
                indexed_choice_instrs.push_back(index);
            }
            IndexingLine::DynamicIndexedChoice(ref mut indexed_choice_instrs) => {
                indexed_choice_instrs.push_front(index);
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn index_overlapping_constant(
        &mut self,
        orig_constant: &Constant,
        overlapping_constant: Constant,
        index: usize,
    ) {
        loop {
            let indexing_code_len = self.indexing_code.len();

            match &mut self.indexing_code[self.offset] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, ref mut c, ..)) => {
                    match *c {
                        IndexingCodePtr::Fail if self.is_dynamic => {
                            *c = IndexingCodePtr::DynamicExternal(index);
                            break;
                        }
                        IndexingCodePtr::Fail => {
                            *c = IndexingCodePtr::External(index);
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(_) | IndexingCodePtr::External(_) => {
                            let mut constants = IndexMap::new();
                            constants.insert(orig_constant.clone(), *c);

                            *c = IndexingCodePtr::Internal(indexing_code_len);

                            self.indexing_code.push(IndexingLine::Indexing(
                                IndexingInstruction::SwitchOnConstant(constants),
                            ));

                            self.offset = indexing_code_len;
                        }
                        IndexingCodePtr::Internal(o) => {
                            self.offset += o;
                        }
                    }
                }
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(constants)) => {
                    match constants.get(&overlapping_constant).cloned() {
                        None | Some(IndexingCodePtr::Fail) if self.is_dynamic => {
                            constants.insert(
                                overlapping_constant,
                                IndexingCodePtr::DynamicExternal(index),
                            );
                        }
                        None | Some(IndexingCodePtr::Fail) => {
                            constants.insert(
                                overlapping_constant,
                                IndexingCodePtr::External(index),
                            );
                        }
                        Some(IndexingCodePtr::DynamicExternal(o)) => {
                            self.add_dynamic_indexed_choice_for_constant(o, overlapping_constant, index);
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_static_indexed_choice_for_constant(o, overlapping_constant, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) | IndexingLine::DynamicIndexedChoice(_) => {
                    self.internalize_constant(IndexingCodePtr::Internal(
                        indexing_code_len - self.offset,
                    ));
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn index_constant(&mut self, constant: Constant, index: usize) {
        loop {
            let indexing_code_len = self.indexing_code.len();

            match &mut self.indexing_code[self.offset] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, ref mut c, ..)) => {
                    match *c {
                        IndexingCodePtr::Fail if self.is_dynamic => {
                            *c = IndexingCodePtr::DynamicExternal(index);
                            break;
                        }
                        IndexingCodePtr::Fail => {
                            *c = IndexingCodePtr::External(index);
                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            *c = IndexingCodePtr::Internal(indexing_code_len - self.offset);
                            self.internalize_constant(IndexingCodePtr::External(o));
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            *c = IndexingCodePtr::Internal(indexing_code_len - self.offset);
                            self.internalize_constant(IndexingCodePtr::DynamicExternal(o));
                        }
                        IndexingCodePtr::Internal(o) => {
                            self.offset += o;
                        }
                    }
                }
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(constants)) => {
                    match constants.get(&constant).cloned() {
                        None | Some(IndexingCodePtr::Fail) if self.is_dynamic => {
                            constants.insert(constant, IndexingCodePtr::DynamicExternal(index));
                        }
                        None | Some(IndexingCodePtr::Fail) => {
                            constants.insert(constant, IndexingCodePtr::External(index));
                        }
                        Some(IndexingCodePtr::DynamicExternal(o)) => {
                            self.add_dynamic_indexed_choice_for_constant(o, constant, index);
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_static_indexed_choice_for_constant(o, constant, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) | IndexingLine::DynamicIndexedChoice(_) => {
                    self.internalize_constant(IndexingCodePtr::Internal(
                        indexing_code_len - self.offset,
                    ));
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn internalize_structure(&mut self, structure_ptr: IndexingCodePtr) {
        let structure_key = search_skeleton_for_first_key_type(
            self.skeleton,
            OptArgIndexKeyType::Structure,
            self.append_or_prepend,
        );

        let mut structures = IndexMap::new();

        match structure_key {
            Some(OptArgIndexKey::Structure(_, _, ref name, ref arity)) => {
                structures.insert((name.clone(), *arity), structure_ptr);
            }
            _ => {
                if let IndexingCodePtr::DynamicExternal(_) = structure_ptr {
                    // this must be a defunct clause, because it's been deleted
                    // from the skeleton.
                } else {
                    unreachable!()
                }
            }
        }

        if let IndexingCodePtr::Internal(_) = structure_ptr {
            let last_index = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnStructure(structures),
            ));

            self.indexing_code.swap(self.offset, last_index);
        } else {
            self.offset = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnStructure(structures),
            ));
        }
    }

    fn add_static_indexed_choice_for_structure(
        &mut self,
        external: usize,
        key: PredicateKey,
        index: usize,
    ) {
        let third_level_index = if self.append_or_prepend.is_append() {
            sdeq![
                IndexedChoiceInstruction::Try(external),
                IndexedChoiceInstruction::Trust(index)
            ]
        } else {
            sdeq![
                IndexedChoiceInstruction::Try(index),
                IndexedChoiceInstruction::Trust(external)
            ]
        };

        let indexing_code_len = self.indexing_code.len();
        self.indexing_code
            .push(IndexingLine::IndexedChoice(third_level_index));

        match &mut self.indexing_code[self.offset] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref mut structures)) => {
                structures.insert(
                    key,
                    IndexingCodePtr::Internal(indexing_code_len - self.offset),
                );
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn add_dynamic_indexed_choice_for_structure(
        &mut self,
        external: usize,
        key: PredicateKey,
        index: usize,
    ) {
        let third_level_index = if self.append_or_prepend.is_append() {
            sdeq![external, index]
        } else {
            sdeq![index, external]
        };

        let indexing_code_len = self.indexing_code.len();
        self.indexing_code.push(IndexingLine::DynamicIndexedChoice(third_level_index));

        match &mut self.indexing_code[self.offset] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref mut structures)) => {
                structures.insert(
                    key,
                    IndexingCodePtr::Internal(indexing_code_len - self.offset),
                );
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn index_structure(&mut self, key: PredicateKey, index: usize) {
        loop {
            let indexing_code_len = self.indexing_code.len();

            match &mut self.indexing_code[self.offset] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                    _,
                    _,
                    _,
                    _,
                    ref mut s,
                )) => match *s {
                    IndexingCodePtr::Fail if self.is_dynamic => {
                        *s = IndexingCodePtr::DynamicExternal(index);
                        break;
                    }
                    IndexingCodePtr::Fail => {
                        *s = IndexingCodePtr::External(index);
                        break;
                    }
                    IndexingCodePtr::DynamicExternal(o) => {
                        *s = IndexingCodePtr::Internal(indexing_code_len - self.offset);
                        self.internalize_structure(IndexingCodePtr::DynamicExternal(o));
                    }
                    IndexingCodePtr::External(o) => {
                        *s = IndexingCodePtr::Internal(indexing_code_len - self.offset);
                        self.internalize_structure(IndexingCodePtr::External(o));
                    }
                    IndexingCodePtr::Internal(o) => {
                        self.offset += o;
                    }
                },
                IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(structures)) => {
                    match structures.get(&key).cloned() {
                        None | Some(IndexingCodePtr::Fail) if self.is_dynamic => {
                            structures.insert(key, IndexingCodePtr::DynamicExternal(index));
                        }
                        None | Some(IndexingCodePtr::Fail) => {
                            structures.insert(key, IndexingCodePtr::External(index));
                        }
                        Some(IndexingCodePtr::DynamicExternal(o)) => {
                            self.add_dynamic_indexed_choice_for_structure(o, key, index);
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_static_indexed_choice_for_structure(o, key, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) | IndexingLine::DynamicIndexedChoice(_) => {
                    // replace this value, at self.offset, with
                    // SwitchOnStructures, and swap this IndexedChoice
                    // vector to the end of self.indexing_code.
                    self.internalize_structure(IndexingCodePtr::Internal(
                        indexing_code_len - self.offset,
                    ));
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn index_list(&mut self, index: usize) {
        let indexing_code_len = self.indexing_code.len();

        match &mut self.indexing_code[self.offset] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, _, ref mut l, _)) => {
                match *l {
                    IndexingCodePtr::Fail if self.is_dynamic => {
                        *l = IndexingCodePtr::DynamicExternal(index);
                    }
                    IndexingCodePtr::Fail => {
                        *l = IndexingCodePtr::External(index);
                    }
                    IndexingCodePtr::DynamicExternal(o) => {
                        *l = IndexingCodePtr::Internal(indexing_code_len - self.offset);

                        let third_level_index = if self.append_or_prepend.is_append() {
                            sdeq![o, index]
                        } else {
                            sdeq![index, o]
                        };

                        self.indexing_code
                            .push(IndexingLine::DynamicIndexedChoice(third_level_index));
                    }
                    IndexingCodePtr::External(o) => {
                        *l = IndexingCodePtr::Internal(indexing_code_len - self.offset);

                        let third_level_index = if self.append_or_prepend.is_append() {
                            sdeq![
                                IndexedChoiceInstruction::Try(o),
                                IndexedChoiceInstruction::Trust(index)
                            ]
                        } else {
                            sdeq![
                                IndexedChoiceInstruction::Try(index),
                                IndexedChoiceInstruction::Trust(o)
                            ]
                        };

                        self.indexing_code
                            .push(IndexingLine::IndexedChoice(third_level_index));
                    }
                    IndexingCodePtr::Internal(o) => {
                        self.offset += o;
                        self.extend_indexed_choice(index);
                    }
                }
            }
            _ => {
                unreachable!()
            }
        }
    }
}

pub(crate) fn merge_clause_index(
    target_indexing_code: &mut Vec<IndexingLine>,
    skeleton: &mut [ClauseIndexInfo], // the clause to be merged is the last element in the skeleton.
    new_clause_loc: usize,            // the absolute location of the new clause in the code vector.
    append_or_prepend: AppendOrPrepend,
) {
    let opt_arg_index_key = match append_or_prepend {
        AppendOrPrepend::Append => skeleton.last_mut().unwrap().opt_arg_index_key.take(),
        AppendOrPrepend::Prepend => skeleton.first_mut().unwrap().opt_arg_index_key.take(),
    };

    let mut merging_ptr = IndexingCodeMergingPtr::new(
        skeleton,
        target_indexing_code,
        append_or_prepend,
    );

    match &opt_arg_index_key {
        OptArgIndexKey::Constant(_, index_loc, ref constant, ref overlapping_constants) => {
            let offset = new_clause_loc - index_loc + 1;
            merging_ptr.index_constant(constant.clone(), offset);

            for overlapping_constant in overlapping_constants {
                merging_ptr.offset = 0;

                merging_ptr.index_overlapping_constant(
                    constant,
                    overlapping_constant.clone(),
                    offset,
                );
            }
        }
        OptArgIndexKey::Structure(_, index_loc, ref name, ref arity) => {
            merging_ptr.index_structure((name.clone(), *arity), new_clause_loc - index_loc + 1);
        }
        OptArgIndexKey::List(_, index_loc) => {
            merging_ptr.index_list(new_clause_loc - index_loc + 1);
        }
        OptArgIndexKey::None => {
            unreachable!()
        }
    }

    match append_or_prepend {
        AppendOrPrepend::Append => {
            skeleton.last_mut().unwrap().opt_arg_index_key = opt_arg_index_key;
        }
        AppendOrPrepend::Prepend => {
            skeleton.first_mut().unwrap().opt_arg_index_key = opt_arg_index_key;
        }
    }
}

pub(crate) fn remove_constant_indices(
    constant: &Constant,
    overlapping_constants: &[Constant],
    indexing_code: &mut Vec<IndexingLine>,
    offset: usize,
) {
    let mut index = 0;
    let iter = once(constant).chain(overlapping_constants.iter());

    match &mut indexing_code[index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, ref mut c, ..)) => {
            match *c {
                IndexingCodePtr::DynamicExternal(_) | IndexingCodePtr::External(_) => {
                    *c = IndexingCodePtr::Fail;
                    return;
                }
                IndexingCodePtr::Internal(o) => {
                    index += o;
                }
                IndexingCodePtr::Fail => {
                    return;
                }
            }
        }
        _ => {
            unreachable!()
        }
    }

    let mut constants_index = 0;

    for constant in iter {
        loop {
            match &mut indexing_code[index] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(
                    ref mut constants,
                )) => {
                    constants_index = index;

                    match constants.get(constant).cloned() {
                        Some(IndexingCodePtr::DynamicExternal(_)) |
                        Some(IndexingCodePtr::External(_)) |
                        Some(IndexingCodePtr::Fail) => {
                            constants.remove(constant);
                            break;
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            index += o;
                        }
                        None => {
                            break;
                        }
                    }
                }
                IndexingLine::IndexedChoice(ref mut indexed_choice_instrs) => {
                    StaticCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

                    if indexed_choice_instrs.len() == 1 {
                        if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                            let ext = IndexingCodePtr::External(
                                indexed_choice_instr.offset()
                            );

                            match &mut indexing_code[constants_index] {
                                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                    _,
                                    _,
                                    ref mut c,
                                    ..,
                                )) => {
                                    *c = ext;
                                }
                                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(
                                    ref mut constants,
                                )) => {
                                    constants.insert(constant.clone(), ext);
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                    }

                    break;
                }
                IndexingLine::DynamicIndexedChoice(ref mut indexed_choice_instrs) => {
                    DynamicCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

                    if indexed_choice_instrs.len() == 1 {
                        if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                            let ext = IndexingCodePtr::DynamicExternal(indexed_choice_instr);

                            match &mut indexing_code[constants_index] {
                                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                    _,
                                    _,
                                    ref mut c,
                                    ..,
                                )) => {
                                    *c = ext;
                                }
                                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(
                                    ref mut constants,
                                )) => {
                                    constants.insert(constant.clone(), ext);
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                        }
                    }

                    break;
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    match &indexing_code[constants_index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref constants))
            if constants.is_empty() =>
        {
            match &mut indexing_code[0] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, ref mut c, ..)) => {
                    *c = IndexingCodePtr::Fail;
                }
                _ => {
                    unreachable!()
                }
            }
        }
        _ => {}
    }
}

pub(crate) fn remove_structure_index(
    name: &ClauseName,
    arity: usize,
    indexing_code: &mut Vec<IndexingLine>,
    offset: usize,
) {
    let mut index = 0;

    match &mut indexing_code[index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, _, _, ref mut s)) => {
            match *s {
                IndexingCodePtr::DynamicExternal(_) | IndexingCodePtr::External(_) => {
                    *s = IndexingCodePtr::Fail;
                    return;
                }
                IndexingCodePtr::Internal(o) => {
                    index += o;
                }
                IndexingCodePtr::Fail => {
                    return;
                }
            }
        }
        _ => {
            unreachable!()
        }
    }

    let mut structures_index = 0;

    loop {
        match &mut indexing_code[index] {
            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref mut structures)) => {
                structures_index = index;

                match structures.get(&(name.clone(), arity)).cloned() {
                    Some(IndexingCodePtr::DynamicExternal(_)) | Some(IndexingCodePtr::External(_)) => {
                        structures.remove(&(name.clone(), arity));
                        break;
                    }
                    Some(IndexingCodePtr::Internal(o)) => {
                        index += o;
                    }
                    Some(IndexingCodePtr::Fail) | None => {
                        return;
                    }
                }
            }
            IndexingLine::IndexedChoice(ref mut indexed_choice_instrs) => {
                StaticCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

                if indexed_choice_instrs.len() == 1 {
                    if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                        let ext = IndexingCodePtr::External(indexed_choice_instr.offset());

                        match &mut indexing_code[structures_index] {
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                _,
                                _,
                                _,
                                _,
                                ref mut s,
                            )) => {
                                *s = ext;
                            }
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(
                                ref mut structures,
                            )) => {
                                structures.insert((name.clone(), arity), ext);
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                }

                break;
            }
            IndexingLine::DynamicIndexedChoice(ref mut indexed_choice_instrs) => {
                DynamicCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

                if indexed_choice_instrs.len() == 1 {
                    if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                        let ext = IndexingCodePtr::DynamicExternal(indexed_choice_instr);

                        match &mut indexing_code[structures_index] {
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                _,
                                _,
                                _,
                                _,
                                ref mut s,
                            )) => {
                                *s = ext;
                            }
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(
                                ref mut structures,
                            )) => {
                                structures.insert((name.clone(), arity), ext);
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                }

                break;
            }
            _ => {
                unreachable!()
            }
        }
    }

    match &indexing_code[structures_index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref structures))
            if structures.is_empty() =>
        {
            match &mut indexing_code[0] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                    _,
                    _,
                    _,
                    _,
                    ref mut s,
                )) => {
                    *s = IndexingCodePtr::Fail;
                }
                _ => {
                    unreachable!()
                }
            }
        }
        _ => {}
    }
}

pub(crate) fn remove_list_index(indexing_code: &mut Vec<IndexingLine>, offset: usize) {
    let mut index = 0;

    match &mut indexing_code[index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, _, ref mut l, _)) => {
            match *l {
                IndexingCodePtr::DynamicExternal(_) | IndexingCodePtr::External(_) => {
                    *l = IndexingCodePtr::Fail;
                    return;
                }
                IndexingCodePtr::Internal(o) => {
                    index += o;
                }
                IndexingCodePtr::Fail => {
                    return;
                }
            }
        }
        _ => {
            unreachable!()
        }
    }

    match &mut indexing_code[index] {
        IndexingLine::IndexedChoice(ref mut indexed_choice_instrs) => {
            StaticCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

            if indexed_choice_instrs.len() == 1 {
                if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                    let ext = IndexingCodePtr::External(indexed_choice_instr.offset());

                    match &mut indexing_code[0] {
                        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                            _,
                            _,
                            _,
                            ref mut l,
                            _,
                        )) => {
                            *l = ext;
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }
            }
        }
        IndexingLine::DynamicIndexedChoice(ref mut indexed_choice_instrs) => {
            DynamicCodeIndices::remove_instruction_with_offset(indexed_choice_instrs, offset);

            if indexed_choice_instrs.len() == 1 {
                if let Some(indexed_choice_instr) = indexed_choice_instrs.pop_back() {
                    let ext = IndexingCodePtr::DynamicExternal(indexed_choice_instr);

                    match &mut indexing_code[0] {
                        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                            _,
                            _,
                            _,
                            ref mut l,
                            _,
                        )) => {
                            *l = ext;
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }
            }
        }
        _ => {
            unreachable!()
        }
    }
}

pub(crate) fn remove_index(
    opt_arg_index_key: &OptArgIndexKey,
    indexing_code: &mut Vec<IndexingLine>,
    clause_loc: usize,
) {
    match opt_arg_index_key {
        OptArgIndexKey::Constant(_, _, ref constant, ref overlapping_constants) => {
            remove_constant_indices(
                constant,
                overlapping_constants,
                indexing_code,
                clause_loc,
            );
        }
        OptArgIndexKey::Structure(_, _, ref name, ref arity) => {
            remove_structure_index(
                name,
                *arity,
                indexing_code,
                clause_loc,
            );
        }
        OptArgIndexKey::List(..) => {
            remove_list_index(
                indexing_code,
                clause_loc,
            );
        }
        OptArgIndexKey::None => {
            unreachable!()
        }
    }
}

#[inline]
fn cap_choice_seq(prelude: &mut [IndexedChoiceInstruction]) {
    prelude.first_mut().map(|instr| {
        *instr = IndexedChoiceInstruction::Try(instr.offset());
    });

    cap_choice_seq_with_trust(prelude);
}

#[inline]
fn cap_choice_seq_with_trust(prelude: &mut [IndexedChoiceInstruction]) {
    prelude.last_mut().map(|instr| {
        if let IndexedChoiceInstruction::Retry(i) = instr {
            *instr = IndexedChoiceInstruction::Trust(*i);
        }
    });
}

#[inline]
fn uncap_choice_seq_with_trust(prelude: &mut [IndexedChoiceInstruction]) {
    prelude.last_mut().map(|instr| {
        if let IndexedChoiceInstruction::Trust(i) = instr {
            *instr = IndexedChoiceInstruction::Retry(*i);
        }
    });
}

#[inline]
fn uncap_choice_seq_with_try(prelude: &mut [IndexedChoiceInstruction]) {
    prelude.first_mut().map(|instr| {
        if let IndexedChoiceInstruction::Try(i) = instr {
            *instr = IndexedChoiceInstruction::Retry(*i);
        }
    });
}

pub(crate) fn constant_key_alternatives(constant: &Constant, atom_tbl: TabledData<Atom>) -> Vec<Constant> {
    let mut constants = vec![];

    match constant {
        Constant::Atom(ref name, ref op) => {
            if name.is_char() {
                let c = name.as_str().chars().next().unwrap();
                constants.push(Constant::Char(c));
            }

            if op.is_some() {
                constants.push(Constant::Atom(name.clone(), None));
            }
        }
        Constant::Char(c) => {
            let atom = clause_name!(c.to_string(), atom_tbl);
            constants.push(Constant::Atom(atom, None));
        }
        Constant::Fixnum(ref n) => {
            constants.push(Constant::Integer(Rc::new(Integer::from(*n))));

            if *n >= 0 {
                if let Ok(n) = usize::try_from(*n) {
                    constants.push(Constant::Usize(n));
                }
            }
        }
        Constant::Integer(ref n) => {
            if let Some(n) = n.to_isize() {
                constants.push(Constant::Fixnum(n));
            }

            if let Some(n) = n.to_usize() {
                constants.push(Constant::Usize(n));
            }
        }
        Constant::Usize(n) => {
            constants.push(Constant::Integer(Rc::new(Integer::from(*n))));

            if let Ok(n) = isize::try_from(*n) {
                constants.push(Constant::Fixnum(n));
            }
        }
        _ => {}
    }

    constants
}

#[derive(Debug)]
pub(crate) struct StaticCodeIndices {
    constants: IndexMap<Constant, SliceDeque<IndexedChoiceInstruction>>,
    lists: SliceDeque<IndexedChoiceInstruction>,
    structures: IndexMap<(ClauseName, usize), SliceDeque<IndexedChoiceInstruction>>,
}

#[derive(Debug)]
pub(crate) struct DynamicCodeIndices {
    constants: IndexMap<Constant, SliceDeque<usize>>,
    lists: SliceDeque<usize>,
    structures: IndexMap<(ClauseName, usize), SliceDeque<usize>>,
}

pub(crate) trait Indexer {
    type ThirdLevelIndex;

    fn new() -> Self;

    fn constants(&mut self) -> &mut IndexMap<Constant, SliceDeque<Self::ThirdLevelIndex>>;
    fn lists(&mut self) -> &mut SliceDeque<Self::ThirdLevelIndex>;
    fn structures(&mut self) -> &mut IndexMap<(ClauseName, usize), SliceDeque<Self::ThirdLevelIndex>>;

    fn compute_index(is_initial_index: bool, index: usize) -> Self::ThirdLevelIndex;

    fn second_level_index<IndexKey: Eq + Hash>(
        indices: IndexMap<IndexKey, SliceDeque<Self::ThirdLevelIndex>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexMap<IndexKey, IndexingCodePtr>;

    fn switch_on<IndexKey: Eq + Hash>(
        instr_fn: impl FnMut(IndexMap<IndexKey, IndexingCodePtr>) -> IndexingInstruction,
        index: &mut IndexMap<IndexKey, SliceDeque<Self::ThirdLevelIndex>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr;

    fn switch_on_list(
        lists: &mut SliceDeque<Self::ThirdLevelIndex>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr;

    fn remove_instruction_with_offset(
        code: &mut SliceDeque<Self::ThirdLevelIndex>,
        offset: usize,
    );

    fn var_offset_wrapper(var_offset: usize) -> IndexingCodePtr;
}

impl Indexer for StaticCodeIndices {
    type ThirdLevelIndex = IndexedChoiceInstruction;

    #[inline]
    fn new() -> Self {
        Self {
            constants: IndexMap::new(),
            lists: sdeq![],
            structures: IndexMap::new(),
        }
    }

    #[inline]
    fn constants(&mut self) -> &mut IndexMap<Constant, SliceDeque<IndexedChoiceInstruction>> {
        &mut self.constants
    }

    #[inline]
    fn lists(&mut self) -> &mut SliceDeque<IndexedChoiceInstruction> {
        &mut self.lists
    }

    #[inline]
    fn structures(&mut self) -> &mut IndexMap<(ClauseName, usize), SliceDeque<IndexedChoiceInstruction>> {
        &mut self.structures
    }

    fn compute_index(is_initial_index: bool, index: usize) -> IndexedChoiceInstruction {
        if is_initial_index {
            IndexedChoiceInstruction::Try(index + 1)
        } else {
            IndexedChoiceInstruction::Retry(index + 1)
        }
    }

    fn second_level_index<IndexKey: Eq + Hash>(
        indices: IndexMap<IndexKey, SliceDeque<IndexedChoiceInstruction>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexMap<IndexKey, IndexingCodePtr> {
        let mut index_locs = IndexMap::new();

        for (key, mut code) in indices.into_iter() {
            if code.len() > 1 {
                index_locs.insert(key, IndexingCodePtr::Internal(prelude.len() + 1));
                cap_choice_seq_with_trust(&mut code);
                prelude.push_back(IndexingLine::from(code));
            } else {
                code.first().map(|i| {
                    index_locs.insert(key, IndexingCodePtr::External(i.offset()));
                });
            }
        }

        index_locs
    }

    fn switch_on<IndexKey: Eq + Hash>(
        mut instr_fn: impl FnMut(IndexMap<IndexKey, IndexingCodePtr>) -> IndexingInstruction,
        index: &mut IndexMap<IndexKey, SliceDeque<IndexedChoiceInstruction>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr {
        let index = mem::replace(index, IndexMap::new());
        let index = Self::second_level_index(index, prelude);

        if index.len() > 1 {
            let instr = instr_fn(index);
            prelude.push_front(IndexingLine::from(instr));

            IndexingCodePtr::Internal(1)
        } else {
            index
                .into_iter()
                .next()
                .map(|(_, v)| v)
                .unwrap_or(IndexingCodePtr::Fail)
        }
    }

    fn switch_on_list(
        lists: &mut SliceDeque<IndexedChoiceInstruction>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr {
        if lists.len() > 1 {
            cap_choice_seq_with_trust(lists);
            let lists = mem::replace(lists, sdeq![]);
            prelude.push_back(IndexingLine::from(lists));

            IndexingCodePtr::Internal(1)
        } else {
            lists
                .first()
                .map(|i| IndexingCodePtr::External(i.offset()))
                .unwrap_or(IndexingCodePtr::Fail)
        }
    }

    #[inline]
    fn remove_instruction_with_offset(code: &mut SliceDeque<IndexedChoiceInstruction>, offset: usize) {
        for (index, line) in code.iter().enumerate() {
            if offset == line.offset() {
                code.remove(index);
                cap_choice_seq(code);
                return;
            }
        }
    }

    #[inline]
    fn var_offset_wrapper(var_offset: usize) -> IndexingCodePtr {
        IndexingCodePtr::External(var_offset)
    }
}

impl Indexer for DynamicCodeIndices {
    type ThirdLevelIndex = usize;

    #[inline]
    fn new() -> Self {
        Self {
            constants: IndexMap::new(),
            lists: sdeq![],
            structures: IndexMap::new(),
        }
    }

    #[inline]
    fn constants(&mut self) -> &mut IndexMap<Constant, SliceDeque<usize>> {
        &mut self.constants
    }

    #[inline]
    fn lists(&mut self) -> &mut SliceDeque<usize> {
        &mut self.lists
    }

    #[inline]
    fn structures(&mut self) -> &mut IndexMap<(ClauseName, usize), SliceDeque<usize>> {
        &mut self.structures
    }

    #[inline]
    fn compute_index(_: bool, index: usize) -> usize {
        index + 1
    }

    fn second_level_index<IndexKey: Eq + Hash>(
        indices: IndexMap<IndexKey, SliceDeque<usize>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexMap<IndexKey, IndexingCodePtr> {
        let mut index_locs = IndexMap::new();

        for (key, code) in indices.into_iter() {
            if code.len() > 1 {
                index_locs.insert(key, IndexingCodePtr::Internal(prelude.len() + 1));
                prelude.push_back(IndexingLine::DynamicIndexedChoice(code));
            } else {
                code.first().map(|i| {
                    index_locs.insert(key, IndexingCodePtr::DynamicExternal(*i));
                });
            }
        }

        index_locs
    }

    fn switch_on<IndexKey: Eq + Hash>(
        mut instr_fn: impl FnMut(IndexMap<IndexKey, IndexingCodePtr>) -> IndexingInstruction,
        index: &mut IndexMap<IndexKey, SliceDeque<usize>>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr {
        let index = mem::replace(index, IndexMap::new());
        let index = Self::second_level_index(index, prelude);

        if index.len() > 1 {
            let instr = instr_fn(index);
            prelude.push_front(IndexingLine::from(instr));

            IndexingCodePtr::Internal(1)
        } else {
            index
                .into_iter()
                .next()
                .map(|(_, v)| v)
                .unwrap_or(IndexingCodePtr::Fail)
        }
    }

    fn switch_on_list(
        lists: &mut SliceDeque<usize>,
        prelude: &mut SliceDeque<IndexingLine>,
    ) -> IndexingCodePtr {
        if lists.len() > 1 {
            let lists = mem::replace(lists, sdeq![]);
            prelude.push_back(IndexingLine::DynamicIndexedChoice(lists));
            IndexingCodePtr::Internal(1)
        } else {
            lists
                .first()
                .map(|i| IndexingCodePtr::DynamicExternal(*i))
                .unwrap_or(IndexingCodePtr::Fail)
        }
    }

    #[inline]
    fn remove_instruction_with_offset(code: &mut SliceDeque<usize>, offset: usize) {
        for (index, line) in code.iter().enumerate() {
            if offset == *line {
                code.remove(index);
                return;
            }
        }
    }

    #[inline]
    fn var_offset_wrapper(var_offset: usize) -> IndexingCodePtr {
        IndexingCodePtr::DynamicExternal(var_offset)
    }
}

#[derive(Debug)]
pub(crate) struct CodeOffsets<I: Indexer> {
    atom_tbl: TabledData<Atom>,
    indices: I,
    optimal_index: usize,
}

impl<I: Indexer> CodeOffsets<I> {
    pub(crate) fn new(
        atom_tbl: TabledData<Atom>,
        indices: I,
        optimal_index: usize,
    ) -> Self {
        CodeOffsets {
            atom_tbl,
            indices,
            optimal_index,
        }
    }

    fn index_list(&mut self, index: usize) {
        let is_initial_index = self.indices.lists().is_empty();
        let index = I::compute_index(is_initial_index, index);
        self.indices.lists().push_back(index);
    }

    fn index_constant(&mut self, constant: &Constant, index: usize) -> Vec<Constant> {
        let overlapping_constants = constant_key_alternatives(constant, self.atom_tbl.clone());
        let code = self.indices.constants().entry(constant.clone()).or_insert(sdeq![]);

        let is_initial_index = code.is_empty();
        code.push_back(I::compute_index(is_initial_index, index));

        for constant in &overlapping_constants {
            let code = self.indices.constants().entry(constant.clone()).or_insert(sdeq![]);

            let is_initial_index = code.is_empty();
            let index = I::compute_index(is_initial_index, index);

            code.push_back(index);
        }

        overlapping_constants
    }

    fn index_structure(&mut self, name: &ClauseName, arity: usize, index: usize) -> usize {
        let code = self.indices
            .structures()
            .entry((name.clone(), arity))
            .or_insert(sdeq![]);

        let code_len = code.len();
        let is_initial_index = code.is_empty();

        code.push_back(I::compute_index(is_initial_index, index));
        code_len
    }

    pub(crate) fn index_term(
        &mut self,
        optimal_arg: &Term,
        index: usize,
        clause_index_info: &mut ClauseIndexInfo,
    ) {
        match optimal_arg {
            &Term::Clause(_, ref name, ref terms, _) => {
                clause_index_info.opt_arg_index_key =
                    OptArgIndexKey::Structure(self.optimal_index, 0, name.clone(), terms.len());

                self.index_structure(name, terms.len(), index);
            }
            &Term::Cons(..) | &Term::Constant(_, Constant::String(_)) => {
                clause_index_info.opt_arg_index_key = OptArgIndexKey::List(self.optimal_index, 0);

                self.index_list(index);
            }
            &Term::Constant(_, ref constant) => {
                let overlapping_constants = self.index_constant(constant, index);

                clause_index_info.opt_arg_index_key = OptArgIndexKey::Constant(
                    self.optimal_index,
                    0,
                    constant.clone(),
                    overlapping_constants,
                );
            }
            _ => {}
        }
    }

    pub(crate) fn no_indices(&mut self) -> bool {
        let no_constants = self.indices.constants().is_empty();
        let no_structures = self.indices.structures().is_empty();
        let no_lists = self.indices.lists().is_empty();

        no_constants && no_structures && no_lists
    }

    pub(crate) fn compute_indices(mut self, skip_stub_try_me_else: bool) -> Vec<IndexingLine> {
        if self.no_indices() {
            return vec![];
        }

        let mut prelude = sdeq![];

        let mut emitted_switch_on_structure = false;
        let mut emitted_switch_on_constant = false;

        let mut lst_loc = I::switch_on_list(self.indices.lists(), &mut prelude);

        let mut str_loc = I::switch_on(
            |index| {
                emitted_switch_on_structure = true;
                IndexingInstruction::SwitchOnStructure(index)
            },
            self.indices.structures(),
            &mut prelude,
        );

        let con_loc = I::switch_on(
            |index| {
                emitted_switch_on_constant = true;
                IndexingInstruction::SwitchOnConstant(index)
            },
            self.indices.constants(),
            &mut prelude,
        );

        match &mut str_loc {
            IndexingCodePtr::Internal(ref mut i) => {
                *i += emitted_switch_on_constant as usize; // con_loc.is_internal() as usize;
            }
            _ => {}
        };

        match &mut lst_loc {
            IndexingCodePtr::Internal(ref mut i) => {
                *i += emitted_switch_on_constant as usize; // con_loc.is_internal() as usize;
                *i += emitted_switch_on_structure as usize; // str_loc.is_internal() as usize;
            }
            _ => {}
        };

        let var_offset = 1 + skip_stub_try_me_else as usize;

        prelude.push_front(IndexingLine::from(IndexingInstruction::SwitchOnTerm(
            self.optimal_index,
            I::var_offset_wrapper(var_offset),
            con_loc,
            lst_loc,
            str_loc,
        )));

        prelude.into_iter().collect()
    }
}
