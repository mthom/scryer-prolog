use crate::atom_table::*;
use crate::offset_table::F64Table;
use crate::parser::ast::*;

use crate::forms::*;
use crate::instructions::*;
use crate::types::HeapCellValue;

use fxhash::{FxBuildHasher, FxHasher};
use hashbrown::hash_table::*;
use indexmap::IndexMap;

use std::collections::VecDeque;

#[inline]
pub(crate) fn cap_choice_seq_with_trust(prelude: &mut [IndexedChoiceInstructionOffset]) {
    if let Some(instr) = prelude.last_mut() {
        match instr {
            IndexedChoiceInstructionOffset::Retry(i) => {
                *instr = IndexedChoiceInstructionOffset::Trust(*i);
            }
            IndexedChoiceInstructionOffset::DefaultRetry(i) => {
                *instr = IndexedChoiceInstructionOffset::DefaultTrust(*i);
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy)]
enum NumberOfKeys {
    Fail,
    External(HeapCellValue),
    Internal,
}

impl NumberOfKeys {
    fn extend(&mut self, cell: HeapCellValue) {
        *self = match *self {
            NumberOfKeys::Fail => NumberOfKeys::External(cell),
            NumberOfKeys::External(other_cell) => {
                if other_cell == cell {
                    *self
                } else {
                    NumberOfKeys::Internal
                }
            }
            _ => *self,
        };
    }

    #[inline]
    fn is_internal(&self) -> bool {
        matches!(self, NumberOfKeys::Internal)
    }
}

#[derive(Debug)]
pub(crate) struct CodeIndices<I: SecondLevelIndexType> {
    constants: HashTable<(HeapCellValue, SecondLevelTable<I>)>,
    lists: SecondLevelTable<I>,
    structures: HashTable<((Atom, usize), SecondLevelTable<I>)>,
}

impl<I: SecondLevelIndexType> CodeIndices<I> {
    fn new() -> Self {
        Self {
            constants: HashTable::new(),
            lists: SecondLevelTable::new(),
            structures: HashTable::new(),
        }
    }
}

pub(crate) trait Indexer: SecondLevelIndexType {
    fn compute_index(
        is_initial_index: bool,
        index: usize,
        non_counted_bt: bool,
    ) -> Self::ThirdLevelIndex;

    fn second_level_index<IndexKey>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> HashTable<(IndexKey, IndexingCodePtr)>;

    fn switch_on<IndexKey>(
        instr_fn: impl FnMut(HashTable<(IndexKey, IndexingCodePtr)>) -> IndexedChoiceInstructionTable,
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        leading: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr;

    fn switch_on_list(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr;

    fn var_offset_wrapper(var_offset: usize) -> ExternalIndexingCodePtr;
}

impl Indexer for IndexedChoiceInstruction {
    fn compute_index(
        is_initial_index: bool,
        index: usize,
        non_counted_bt: bool,
    ) -> IndexedChoiceInstructionOffset {
        if is_initial_index {
            IndexedChoiceInstructionOffset::Try(index + 1)
        } else if non_counted_bt {
            IndexedChoiceInstructionOffset::DefaultRetry(index + 1)
        } else {
            IndexedChoiceInstructionOffset::Retry(index + 1)
        }
    }

    fn second_level_index<IndexKey>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> HashTable<(IndexKey, IndexingCodePtr)> {
        let mut index_locs = HashTable::new();

        for (key, mut code) in indices.drain() {
            debug_assert!(matches!(
                code.offsets[0],
                IndexedChoiceInstructionOffset::Try(_)
            ));

            let hash = hash_fn(&key);

            if code.offsets.len() > 1 {
                index_locs.insert_unique(
                    hash,
                    (key, IndexingCodePtr::Internal(prelude.len() + 1)),
                    |(key, _)| hash_fn(key),
                );

                // index_locs.insert(key, IndexingCodePtr::Internal(prelude.len() + 1));
                cap_choice_seq_with_trust(code.offsets.make_contiguous());
                prelude.push_back(IndexingLine::IndexedChoice(code));
            } else {
                index_locs.insert_unique(
                    hash,
                    (key, IndexingCodePtr::External(code.offsets[0].offset())),
                    |(key, _)| hash_fn(key),
                );
            }
        }

        index_locs
    }

    fn switch_on<IndexKey>(
        mut instr_fn: impl FnMut(
            HashTable<(IndexKey, IndexingCodePtr)>,
        ) -> IndexedChoiceInstructionTable,
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        leading: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr {
        let indices = Self::second_level_index(indices, hash_fn, prelude);

        if indices.len() > 1 {
            leading.tables.push_front(instr_fn(indices));
            TermIndexingCodePtr::TableOffset(1)
        } else {
            indices
                .into_iter()
                .next()
                .map(|(_, v)| TermIndexingCodePtr::from(v))
                .unwrap_or(TermIndexingCodePtr::Fail)
        }
    }

    fn switch_on_list(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr {
        if lists.offsets.len() > 1 {
            cap_choice_seq_with_trust(lists.offsets.make_contiguous());
            let lists = std::mem::replace(lists, SecondLevelTable::new());
            prelude.push_back(IndexingLine::IndexedChoice(lists));

            TermIndexingCodePtr::Internal(1)
        } else {
            lists
                .offsets
                .front()
                .map(|i| TermIndexingCodePtr::External(i.offset()))
                .unwrap_or(TermIndexingCodePtr::Fail)
        }
    }

    #[inline]
    fn var_offset_wrapper(var_offset: usize) -> ExternalIndexingCodePtr {
        ExternalIndexingCodePtr::Static(var_offset)
    }
}

impl Indexer for DynamicIndexedChoiceInstruction {
    #[inline]
    fn compute_index(_: bool, index: usize, _: bool) -> Self::ThirdLevelIndex {
        index + 1
    }

    fn second_level_index<IndexKey>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> HashTable<(IndexKey, IndexingCodePtr)> {
        let mut index_locs = HashTable::new();

        for (key, code) in indices.drain() {
            let hash = hash_fn(&key);

            if code.offsets.len() > 1 {
                index_locs.insert_unique(
                    hash,
                    (key, IndexingCodePtr::Internal(prelude.len() + 1)),
                    |(key, _)| hash_fn(key),
                );

                // index_locs.insert(key, IndexingCodePtr::Internal(prelude.len() + 1));
                // cap_choice_seq_with_trust(code.offsets.make_contiguous());
                prelude.push_back(IndexingLine::DynamicIndexedChoice(code));
            } else {
                index_locs.insert_unique(
                    hash,
                    (
                        key,
                        IndexingCodePtr::DynamicExternal(code.offsets[0].offset()),
                    ),
                    |(key, _)| hash_fn(key),
                );
            }
        }

        index_locs
    }

    fn switch_on<IndexKey>(
        mut instr_fn: impl FnMut(
            HashTable<(IndexKey, IndexingCodePtr)>,
        ) -> IndexedChoiceInstructionTable,
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        leading: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr {
        let indices = Self::second_level_index(indices, hash_fn, prelude);

        if indices.len() > 1 {
            leading.tables.push_front(instr_fn(indices));
            TermIndexingCodePtr::TableOffset(1)
        } else {
            indices
                .into_iter()
                .next()
                .map(|(_, v)| TermIndexingCodePtr::from(v))
                .unwrap_or(TermIndexingCodePtr::Fail)
        }
    }

    fn switch_on_list(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr {
        if lists.offsets.len() > 1 {
            let lists = std::mem::replace(lists, SecondLevelTable::new());
            prelude.push_back(IndexingLine::DynamicIndexedChoice(lists));
            TermIndexingCodePtr::Internal(1)
        } else {
            lists
                .offsets
                .front()
                .map(|i| TermIndexingCodePtr::DynamicExternal(i.offset()))
                .unwrap_or(TermIndexingCodePtr::Fail)
        }
    }

    #[inline]
    fn var_offset_wrapper(var_offset: usize) -> ExternalIndexingCodePtr {
        ExternalIndexingCodePtr::Dynamic(var_offset)
    }
}

#[derive(Debug)]
pub(crate) struct CodeOffsets<'a, I: Indexer> {
    indices: CodeIndices<I>,
    f64_tbl: &'a F64Table,
    clause_offsets_to_arg_keys: IndexMap<usize, Vec<OptArgIndexKey>, FxBuildHasher>,
    arity: usize,
    non_counted_bt: bool,
    is_extensible: bool,
}

impl<'a, I: Indexer> CodeOffsets<'a, I> {
    pub(crate) fn new(
        f64_tbl: &'a F64Table,
        non_counted_bt: bool,
        arity: usize,
        is_extensible: bool,
    ) -> Self {
        CodeOffsets {
            indices: CodeIndices::new(),
            f64_tbl,
            clause_offsets_to_arg_keys: IndexMap::with_hasher(FxBuildHasher::default()),
            arity,
            non_counted_bt,
            is_extensible,
        }
    }

    fn map_offsets_to_index_keys(
        optimal_index: usize,
    ) -> impl for<'b> FnOnce(
        &'b [I::ThirdLevelIndex],
        &'b IndexMap<usize, Vec<OptArgIndexKey>, FxBuildHasher>,
    ) -> Box<dyn Iterator<Item = (usize, OptArgIndexKey)> + 'b> {
        move |code, clause_offsets_to_arg_keys| {
            let iter = code
                .iter()
                .map(|instr| instr.offset())
                .filter_map(|offset| clause_offsets_to_arg_keys.get(&offset))
                .flat_map(move |v| v.iter().copied().enumerate().skip(optimal_index + 1));
            // optimal_index is 0-indexed so must add 1 to skip it as well

            Box::new(iter)
        }
    }

    fn map_clause_offset_to_arg_key(
        &mut self,
        arg_index: usize,
        key: OptArgIndexKey,
        clause_offset: usize,
    ) {
        let entry = self
            .clause_offsets_to_arg_keys
            .entry(clause_offset + 1)  // 1 to offset incoming IndexingCode at front
            .or_insert_with(|| vec![OptArgIndexKey::None; self.arity]);

        entry[arg_index] = key;
    }

    fn on_demand_second_level_index(
        code: &mut SecondLevelTable<I>,
        optimal_index: usize,
        clause_offsets_to_arg_keys: &IndexMap<usize, Vec<OptArgIndexKey>, FxBuildHasher>,
        arity: usize,
        is_extensible: bool,
    ) {
        let map_offsets_to_index_keys = Self::map_offsets_to_index_keys(optimal_index);

        /*
        if is_extensible {
            for arg_index in optimal_index + 1..arity {
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandStructure {
                        reg_num: arg_index + 1,
                        arity,
                    });
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandConstant {
                        reg_num: arg_index + 1,
                        arity,
                    });
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandTerm {
                        var_offset: 3,
                        arg_num: arg_index + 1,
                        arity,
                    });
            }

            return;
        }
        */

        let mut arg_structure_keys = vec![NumberOfKeys::Fail; arity];
        let mut arg_constant_keys = vec![NumberOfKeys::Fail; arity];
        let mut arg_list_keys = vec![false; arity];

        for (arg_index, arg_key) in
            map_offsets_to_index_keys(code.offsets.make_contiguous(), clause_offsets_to_arg_keys)
        {
            match arg_key {
                OptArgIndexKey::Structure(name, arity) => {
                    arg_structure_keys[arg_index].extend(atom_as_cell!(name, arity));
                }
                OptArgIndexKey::Literal(literal) => {
                    arg_constant_keys[arg_index].extend(HeapCellValue::from(literal));
                }
                OptArgIndexKey::List => {
                    arg_list_keys[arg_index] = true;
                }
                _ => {}
            };
        }

        for arg_index in optimal_index + 1..arity {
            let mut var_offset = 1;

            if arg_structure_keys[arg_index].is_internal() {
                var_offset += 1;
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandStructure {
                        reg_num: arg_index + 1,
                        arity,
                    });
            }

            if arg_constant_keys[arg_index].is_internal() {
                var_offset += 1;
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandConstant {
                        reg_num: arg_index + 1,
                        arity,
                    });
            }

            if arg_constant_keys[arg_index].is_internal()
                || arg_structure_keys[arg_index].is_internal()
                || arg_list_keys[arg_index]
            {
                code.tables
                    .push_front(IndexedChoiceInstructionTable::OnDemandTerm {
                        var_offset,
                        arg_num: arg_index + 1,
                        arity,
                    });
            }
        }
    }

    pub(crate) fn index_list(&mut self, clause_offset: usize) {
        let is_initial_index = self.indices.lists.offsets.is_empty();
        let offset_instr = I::compute_index(is_initial_index, clause_offset, self.non_counted_bt);
        self.indices.lists.offsets.push_back(offset_instr);
    }

    pub(crate) fn index_constant(&mut self, cell: HeapCellValue, clause_offset: usize) {
        let hash = cell.syntactic_hash(self.f64_tbl, FxHasher::default());

        let mut binding = self
            .indices
            .constants
            .entry(
                hash,
                |(existing_cell, _)| cell.syntactic_eq(self.f64_tbl, *existing_cell),
                |(existing_cell, _)| {
                    existing_cell.syntactic_hash(self.f64_tbl, FxHasher::default())
                },
            )
            .or_insert_with(|| (cell, SecondLevelTable::new()));

        let code = &mut binding.get_mut().1;
        let is_initial_index = code.offsets.is_empty();

        code.offsets.push_back(I::compute_index(
            is_initial_index,
            clause_offset,
            self.non_counted_bt,
        ));
    }

    pub(crate) fn index_structure(&mut self, name: Atom, arity: usize, clause_offset: usize) -> usize {
        let cell = atom_as_cell!(name, arity);
        let hash = cell.syntactic_hash(self.f64_tbl, FxHasher::default());

        let mut binding = self
            .indices
            .structures
            .entry(
                hash,
                |((name, arity), _tbl)| {
                    let existing_pair = atom_as_cell!(name, *arity);
                    cell.syntactic_eq(self.f64_tbl, existing_pair)
                },
                |((name, arity), _tbl)| {
                    let existing_pair = atom_as_cell!(name, *arity);
                    existing_pair.syntactic_hash(self.f64_tbl, FxHasher::default())
                },
            )
            .or_insert_with(|| ((name, arity), SecondLevelTable::new()));

        let code = &mut binding.get_mut().1;
        let code_len = code.offsets.len();
        let is_initial_index = code.offsets.is_empty();

        code.offsets.push_back(I::compute_index(
            is_initial_index,
            clause_offset,
            self.non_counted_bt,
        ));

        code_len
    }

    pub(crate) fn index_term(
        &mut self,
        arg_index: usize,
        arg: &Term,
        clause_offset: usize,
        optimal_index: usize,
    ) {
        let index_key = match arg {
            &Term::Clause(_, atom!("."), ref terms) if terms.len() == 2 => {
                if arg_index == optimal_index {
                    self.index_list(clause_offset);
                }

                OptArgIndexKey::List
            }
            &Term::Cons(..) | &Term::PartialString(..) | &Term::CompleteString(..) => {
                if arg_index == optimal_index {
                    self.index_list(clause_offset);
                }

                OptArgIndexKey::List
            }
            &Term::Clause(_, name, ref terms) => {
                if arg_index == optimal_index {
                    self.index_structure(name, terms.len(), clause_offset);
                }

                OptArgIndexKey::Structure(name, terms.len())
            }
            &Term::Literal(_, constant) => {
                let literal = HeapCellValue::from(constant);

                if arg_index == optimal_index {
                    self.index_constant(literal, clause_offset)
                }

                OptArgIndexKey::Literal(literal)
            }
            _ => return,
        };

        self.map_clause_offset_to_arg_key(
            arg_index,
            index_key,
            clause_offset,
        );
    }

    pub(crate) fn no_indices(&mut self) -> bool {
        let no_constants = self.indices.constants.is_empty();
        let no_structures = self.indices.structures.is_empty();
        let no_lists = self.indices.lists.offsets.is_empty();

        no_constants && no_structures && no_lists
    }

    pub(crate) fn compute_indices(
        mut self,
        optimal_index: usize,
        skip_stub_try_me_else: bool,
    ) -> (ExternalIndexingCodePtr, Vec<IndexingLine>) {
        let mut leading = SecondLevelTable::<I>::new();
        let mut prelude = VecDeque::new();

        let mut emitted_switch_on_structure = false;
        let mut emitted_switch_on_constant = false;

        leading.offsets.extend(
            // these are for on_demand_second_level_index to work on leading.
            // the first and third arguments (is_initial_index, non_counted_bt)
            // do not matter because they're only used to contain the offsets.
            self.clause_offsets_to_arg_keys
                .keys()
                .cloned()
                .map(|index| I::compute_index(true, index - 1, self.non_counted_bt)),
            // subtract 1 to compensate for compute_index action of + 1
        );

        Self::on_demand_second_level_index(
            &mut leading,
            optimal_index,
            &self.clause_offsets_to_arg_keys,
            self.arity,
            self.is_extensible,
        );

        Self::on_demand_second_level_index(
            &mut self.indices.lists,
            optimal_index,
            &self.clause_offsets_to_arg_keys,
            self.arity,
            self.is_extensible,
        );

        let mut lst_loc = I::switch_on_list(&mut self.indices.lists, &mut prelude);

        for (_, code) in self.indices.structures.iter_mut() {
            Self::on_demand_second_level_index(
                code,
                optimal_index,
                &self.clause_offsets_to_arg_keys,
                self.arity,
                self.is_extensible,
            );
        }

        let mut str_loc = I::switch_on(
            |index| {
                emitted_switch_on_structure = true;
                IndexedChoiceInstructionTable::SwitchOnStructure(index)
            },
            &mut self.indices.structures,
            |(name, arity)| {
                let cell = atom_as_cell!(name, *arity);
                cell.syntactic_hash(self.f64_tbl, FxHasher::default())
            },
            &mut leading,
            &mut prelude,
        );

        for (_, code) in self.indices.constants.iter_mut() {
            Self::on_demand_second_level_index(
                code,
                optimal_index,
                &self.clause_offsets_to_arg_keys,
                self.arity,
                self.is_extensible,
            );
        }

        let con_loc = I::switch_on(
            |index| {
                emitted_switch_on_constant = true;
                IndexedChoiceInstructionTable::SwitchOnConstant(index)
            },
            &mut self.indices.constants,
            |cell| cell.syntactic_hash(self.f64_tbl, FxHasher::default()),
            &mut leading,
            &mut prelude,
        );

        if let TermIndexingCodePtr::TableOffset(i) = &mut str_loc {
            *i += emitted_switch_on_constant as usize;
        }

        if let TermIndexingCodePtr::TableOffset(i) = &mut lst_loc {
            *i += emitted_switch_on_constant as usize;
            *i += emitted_switch_on_structure as usize;
        }

        let var_offset = 1 + skip_stub_try_me_else as usize;

        leading
            .tables
            .push_front(IndexedChoiceInstructionTable::SwitchOnTerm(
                optimal_index + 1, // from the WAM perspective, register indices are 1-indexed
                1 + emitted_switch_on_structure as usize + emitted_switch_on_constant as usize,
                con_loc,
                lst_loc,
                str_loc,
            ));

        prelude.push_front(I::to_indexing_line(leading));
        (I::var_offset_wrapper(var_offset), prelude.into())
    }
}
