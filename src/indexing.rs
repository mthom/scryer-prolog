use crate::prolog_parser_rebis::ast::*;
use crate::prolog_parser_rebis::clause_name;
use crate::prolog_parser_rebis::tabled_rc::*;

use crate::forms::*;
use crate::instructions::*;

use crate::indexmap::IndexMap;
use crate::rug::Integer;

use slice_deque::{sdeq, SliceDeque};

use std::convert::TryFrom;
use std::hash::Hash;
use std::iter::once;
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
pub enum IndexingCodePtr {
    External(usize), // the index points past the indexing instruction prelude.
    Fail,
    Internal(usize), // the index points into the indexing instruction prelude.
}

impl IndexingCodePtr {
    #[inline]
    fn is_internal(self) -> bool {
        if let IndexingCodePtr::Internal(_) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum OptArgIndexKeyType {
    Structure,
    Constant,
    List,
}

impl OptArgIndexKey {
    #[inline]
    fn has_key_type(&self, key_type: OptArgIndexKeyType) -> bool {
        match (self, key_type) {
            (OptArgIndexKey::Constant(..), OptArgIndexKeyType::Constant)
            | (OptArgIndexKey::Structure(..), OptArgIndexKeyType::Structure)
            | (OptArgIndexKey::List(..), OptArgIndexKeyType::List) => true,
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
    // merged_clause_index: usize,
    indexing_code: &'a mut Vec<IndexingLine>,
    offset: usize,
    append_or_prepend: AppendOrPrepend,
}

impl<'a> IndexingCodeMergingPtr<'a> {
    #[inline]
    fn new(
        skeleton: &'a mut [ClauseIndexInfo],
        indexing_code: &'a mut Vec<IndexingLine>,
        append_or_prepend: AppendOrPrepend,
    ) -> Self {
        Self {
            skeleton,
            indexing_code,
            offset: 0,
            append_or_prepend,
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
                unreachable!()
            }
        }

        if let IndexingCodePtr::Internal(_) = constant_ptr {
            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnConstant(constants),
            ));

            let last_index = self.indexing_code.len() - 1;
            self.indexing_code.swap(self.offset, last_index);
        } else {
            self.offset = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnConstant(constants),
            ));
        }
    }

    fn add_indexed_choice_for_constant(
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
        self.indexing_code
            .push(IndexingLine::IndexedChoice(third_level_index));

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
                        IndexingCodePtr::Fail => {
                            *c = IndexingCodePtr::External(index);
                            break;
                        }
                        IndexingCodePtr::External(_) => {
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
                        None | Some(IndexingCodePtr::Fail) => {
                            constants
                                .insert(overlapping_constant, IndexingCodePtr::External(index));
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_indexed_choice_for_constant(o, overlapping_constant, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) => {
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
                        IndexingCodePtr::Fail => {
                            *c = IndexingCodePtr::External(index);
                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            *c = IndexingCodePtr::Internal(indexing_code_len - self.offset);
                            self.internalize_constant(IndexingCodePtr::External(o));
                        }
                        IndexingCodePtr::Internal(o) => {
                            self.offset += o;
                        }
                    }
                }
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(constants)) => {
                    match constants.get(&constant).cloned() {
                        None | Some(IndexingCodePtr::Fail) => {
                            constants.insert(constant, IndexingCodePtr::External(index));
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_indexed_choice_for_constant(o, constant, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) => {
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
                unreachable!()
            }
        }

        if let IndexingCodePtr::Internal(_) = structure_ptr {
            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnStructure(structures),
            ));

            let last_index = self.indexing_code.len() - 1;
            self.indexing_code.swap(self.offset, last_index);
        } else {
            self.offset = self.indexing_code.len();

            self.indexing_code.push(IndexingLine::Indexing(
                IndexingInstruction::SwitchOnStructure(structures),
            ));
        }
    }

    fn add_indexed_choice_for_structure(
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
                    IndexingCodePtr::Fail => {
                        *s = IndexingCodePtr::External(index);
                        break;
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
                        None | Some(IndexingCodePtr::Fail) => {
                            structures.insert(key, IndexingCodePtr::External(index));
                        }
                        Some(IndexingCodePtr::External(o)) => {
                            self.add_indexed_choice_for_structure(o, key, index);
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            self.offset += o;
                            self.extend_indexed_choice(index);
                        }
                    }

                    break;
                }
                IndexingLine::IndexedChoice(_) => {
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
                    IndexingCodePtr::Fail => {
                        *l = IndexingCodePtr::External(index);
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

pub fn merge_clause_index(
    target_indexing_code: &mut Vec<IndexingLine>,
    skeleton: &mut [ClauseIndexInfo], // the clause to be merged is the last element in the skeleton.
    new_clause_loc: usize,            // the absolute location of the new clause in the code vector.
    append_or_prepend: AppendOrPrepend,
) {
    let opt_arg_index_key = match append_or_prepend {
        AppendOrPrepend::Append => skeleton.last_mut().unwrap().opt_arg_index_key.take(),
        AppendOrPrepend::Prepend => skeleton.first_mut().unwrap().opt_arg_index_key.take(),
    };

    let mut merging_ptr =
        IndexingCodeMergingPtr::new(skeleton, target_indexing_code, append_or_prepend);

    match &opt_arg_index_key {
        OptArgIndexKey::Constant(_, index_loc, ref constant, ref overlapping_constants) => {
            let offset = new_clause_loc - index_loc + 1;
            merging_ptr.index_constant(constant.clone(), offset);

            for overlapping_constant in overlapping_constants {
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

pub fn remove_constant_indices(
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
                IndexingCodePtr::External(_) => {
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
        // (constant, index_loc) in iter.zip(index_locs.iter()) {
        loop {
            match &mut indexing_code[index] {
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(
                    ref mut constants,
                )) => {
                    constants_index = index;

                    match constants.get(constant).cloned() {
                        Some(IndexingCodePtr::External(_)) => {
                            constants.remove(constant);
                            break;
                        }
                        Some(IndexingCodePtr::Internal(o)) => {
                            index += o;
                        }
                        Some(IndexingCodePtr::Fail) | None => {
                            unreachable!()
                        }
                    }
                }
                IndexingLine::IndexedChoice(ref mut indexed_choice_instrs) => {
                    remove_instruction_with_offset(indexed_choice_instrs, offset);

                    if indexed_choice_instrs.len() == 1 {
                        let ext = IndexingCodePtr::External(
                            indexed_choice_instrs.pop_back().unwrap().offset(),
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

pub fn remove_structure_index(
    name: &ClauseName,
    arity: usize,
    indexing_code: &mut Vec<IndexingLine>,
    offset: usize,
) {
    let mut index = 0;

    match &mut indexing_code[index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, _, _, ref mut s)) => {
            match *s {
                IndexingCodePtr::External(_) => {
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
                    Some(IndexingCodePtr::External(_)) => {
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
                remove_instruction_with_offset(indexed_choice_instrs, offset);

                if indexed_choice_instrs.len() == 1 {
                    let ext = IndexingCodePtr::External(
                        indexed_choice_instrs.pop_back().unwrap().offset(),
                    );

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

pub fn remove_list_index(indexing_code: &mut Vec<IndexingLine>, offset: usize) {
    let mut index = 0;

    match &mut indexing_code[index] {
        IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, _, _, ref mut l, _)) => {
            match *l {
                IndexingCodePtr::External(_) => {
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
            remove_instruction_with_offset(indexed_choice_instrs, offset);

            if indexed_choice_instrs.len() == 1 {
                let ext =
                    IndexingCodePtr::External(indexed_choice_instrs.pop_back().unwrap().offset());

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
        _ => {
            unreachable!()
        }
    }
}

pub fn remove_index(
    //skeleton: &[ClauseIndexInfo],
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
                //&skeleton[index].index_locs,
            );
        }
        OptArgIndexKey::Structure(_, _, ref name, ref arity) => {
            remove_structure_index(
                name,
                *arity,
                indexing_code,
                clause_loc,
                //&skeleton[index].index_locs,
            );
        }
        OptArgIndexKey::List(..) => {
            remove_list_index(
                indexing_code,
                clause_loc,
                //&skeleton[index].index_locs,
            );
        }
        OptArgIndexKey::None => {
            unreachable!()
        }
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
    instr_fn: impl Fn(IndexMap<IndexKey, IndexingCodePtr>) -> IndexingInstruction,
    index: IndexMap<IndexKey, SliceDeque<IndexedChoiceInstruction>>,
    prelude: &mut SliceDeque<IndexingLine>,
) -> IndexingCodePtr {
    let index = second_level_index(index, prelude);

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
    mut lists: SliceDeque<IndexedChoiceInstruction>,
    prelude: &mut SliceDeque<IndexingLine>,
) -> IndexingCodePtr {
    if lists.len() > 1 {
        cap_choice_seq_with_trust(&mut lists);
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

fn compute_index(is_first_index: bool, index: usize) -> IndexedChoiceInstruction {
    // in either case, increment index to skip the IndexingLine vector.
    if is_first_index {
        IndexedChoiceInstruction::Try(index + 1)
    } else {
        IndexedChoiceInstruction::Retry(index + 1)
    }
}

pub fn constant_key_alternatives(constant: &Constant, atom_tbl: TabledData<Atom>) -> Vec<Constant> {
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
pub struct CodeOffsets {
    atom_tbl: TabledData<Atom>,
    pub constants: IndexMap<Constant, SliceDeque<IndexedChoiceInstruction>>,
    pub lists: SliceDeque<IndexedChoiceInstruction>,
    pub structures: IndexMap<(ClauseName, usize), SliceDeque<IndexedChoiceInstruction>>,
    optimal_index: usize,
}

impl CodeOffsets {
    pub fn new(atom_tbl: TabledData<Atom>, optimal_index: usize) -> Self {
        CodeOffsets {
            atom_tbl,
            constants: IndexMap::new(),
            lists: sdeq![],
            structures: IndexMap::new(),
            optimal_index,
        }
    }

    fn index_list(&mut self, index: usize) {
        let is_initial_index = self.lists.is_empty();
        self.lists.push_back(compute_index(is_initial_index, index));
    }

    fn index_constant(&mut self, constant: &Constant, index: usize) -> Vec<Constant> {
        let overlapping_constants = constant_key_alternatives(constant, self.atom_tbl.clone());

        let code = self.constants.entry(constant.clone()).or_insert(sdeq![]);

        let is_initial_index = code.is_empty();
        code.push_back(compute_index(is_initial_index, index));

        for constant in &overlapping_constants {
            let code = self.constants.entry(constant.clone()).or_insert(sdeq![]);

            let is_initial_index = code.is_empty();
            let index = compute_index(is_initial_index, index);

            code.push_back(index);
        }

        overlapping_constants
    }

    fn index_structure(&mut self, name: &ClauseName, arity: usize, index: usize) -> usize {
        let code = self
            .structures
            .entry((name.clone(), arity))
            .or_insert(sdeq![]);

        let code_len = code.len();
        let is_initial_index = code.is_empty();

        code.push_back(compute_index(is_initial_index, index));
        code_len
    }

    pub fn index_term(
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

    pub fn no_indices(&self) -> bool {
        let no_constants = self.constants.is_empty();
        let no_structures = self.structures.is_empty();
        let no_lists = self.lists.is_empty();

        no_constants && no_structures && no_lists
    }

    pub fn compute_indices(self, skip_stub_try_me_else: bool) -> Vec<IndexingLine> {
        if self.no_indices() {
            return vec![];
        }

        let mut prelude = sdeq![];

        let mut lst_loc = switch_on_list(self.lists, &mut prelude);

        let mut str_loc = switch_on(
            IndexingInstruction::SwitchOnStructure,
            self.structures,
            &mut prelude,
        );

        let con_loc = switch_on(
            IndexingInstruction::SwitchOnConstant,
            self.constants,
            &mut prelude,
        );

        match &mut str_loc {
            IndexingCodePtr::Internal(ref mut i) => {
                *i += con_loc.is_internal() as usize;
            }
            _ => {}
        };

        match &mut lst_loc {
            IndexingCodePtr::Internal(ref mut i) => {
                *i += con_loc.is_internal() as usize;
                *i += str_loc.is_internal() as usize;
            }
            _ => {}
        };

        let var_offset = 1 + skip_stub_try_me_else as usize;

        prelude.push_front(IndexingLine::from(IndexingInstruction::SwitchOnTerm(
            self.optimal_index,
            var_offset,
            con_loc,
            lst_loc,
            str_loc,
        )));

        prelude.into_iter().collect()
    }
}
