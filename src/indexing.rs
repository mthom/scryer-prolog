use crate::atom_table::*;
use crate::machine::machine_indices::IndexingSpecs;
use crate::offset_table::F64Table;

use crate::forms::*;
use crate::instructions::*;
use crate::types::HeapCellValue;

use fxhash::{FxBuildHasher, FxHasher};
use hashbrown::hash_table::*;
use indexmap::IndexMap;
use indexmap::IndexSet;

use std::collections::VecDeque;
use std::fmt::Debug;

pub(crate) type ClauseArgData = IndexMap<usize, Vec<OptArgIndexKey>, FxBuildHasher>;

#[inline]
pub(crate) fn cap_choice_seq_with_trust(instr: &mut StaticIndexedChoiceInstructionOffset) {
    match instr {
        StaticIndexedChoiceInstructionOffset::Retry(i) => {
            *instr = StaticIndexedChoiceInstructionOffset::Trust(*i);
        }
        StaticIndexedChoiceInstructionOffset::DefaultRetry(i) => {
            *instr = StaticIndexedChoiceInstructionOffset::DefaultTrust(*i);
        }
        _ => {}
    }
}

#[derive(Debug)]
pub(crate) struct CodeIndices<I: SecondLevelIndexType> {
    constants: HashTable<(HeapCellValue, SecondLevelTable<I>)>,
    lists: SecondLevelTable<I>,
    structures: HashTable<((Atom, usize), SecondLevelTable<I>)>,
}

impl<I: Indexer> CodeIndices<I> {
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

    fn populate_root_offsets<Iter: Iterator<Item = Self::ThirdLevelIndex>>(
        iter: Iter,
    ) -> VecDeque<Self::ThirdLevelIndex>;

    fn second_level_index<IndexKey>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> HashTable<(IndexKey, IndexingCodePtr)>;

    fn switch_on<IndexKey: Clone + Debug>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> TermIndexingCodePtr<IndexKey> {
        let indices = Self::second_level_index(indices, hash_fn, prelude);

        if indices.len() > 1 {
            TermIndexingCodePtr::SwitchOnType(Box::new(indices))
        } else {
            indices
                .into_iter()
                .next()
                .map(TermIndexingCodePtr::from)
                .unwrap_or(TermIndexingCodePtr::Fail)
        }
    }

    fn switch_on_lists(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> Option<IndexingCodePtr>;

    fn var_offset_wrapper(var_offset: usize) -> ExternalIndexingCodePtr;
}

impl Indexer for StaticIndexedChoiceInstruction {
    fn compute_index(
        is_initial_index: bool,
        index: usize,
        non_counted_bt: bool,
    ) -> StaticIndexedChoiceInstructionOffset {
        if is_initial_index {
            StaticIndexedChoiceInstructionOffset::Try(index + 1)
        } else if non_counted_bt {
            StaticIndexedChoiceInstructionOffset::DefaultRetry(index + 1)
        } else {
            StaticIndexedChoiceInstructionOffset::Retry(index + 1)
        }
    }

    fn populate_root_offsets<Iter: Iterator<Item = Self::ThirdLevelIndex>>(
        iter: Iter,
    ) -> VecDeque<Self::ThirdLevelIndex> {
        let mut offsets = VecDeque::from_iter(iter);

        if offsets.len() > 1
            && let Some(instr) = offsets.back_mut()
        {
            cap_choice_seq_with_trust(instr);
        }

        offsets
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
                StaticIndexedChoiceInstructionOffset::Try(_)
            ));

            let hash = hash_fn(&key);

            if code.offsets.len() > 1 {
                index_locs.insert_unique(
                    hash,
                    (key, IndexingCodePtr::internal(prelude.len() + 1)),
                    |(key, _)| hash_fn(key),
                );

                if let Some(instr) = code.offsets.back_mut() {
                    cap_choice_seq_with_trust(instr);
                }
                prelude.push_back(IndexingLine::StaticIndexedChoice(code));
            } else {
                index_locs.insert_unique(
                    hash,
                    (key, IndexingCodePtr::external(code.offsets[0].offset())),
                    |(key, _)| hash_fn(key),
                );
            }
        }

        index_locs
    }

    fn switch_on_lists(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> Option<IndexingCodePtr> {
        if lists.offsets.len() > 1 {
            let mut lists = std::mem::replace(lists, SecondLevelTable::new());
            let internal_offset = prelude.len() + 1; // compensate for leading at front

            if let Some(instr) = lists.offsets.back_mut() {
                cap_choice_seq_with_trust(instr);
            }

            prelude.push_back(IndexingLine::StaticIndexedChoice(lists));
            Some(IndexingCodePtr::internal(internal_offset))
        } else {
            lists
                .offsets
                .front()
                .map(|i| IndexingCodePtr::external(i.offset()))
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
        Appended::Z(index + 1)
    }

    fn populate_root_offsets<Iter: Iterator<Item = Self::ThirdLevelIndex>>(
        iter: Iter,
    ) -> VecDeque<Self::ThirdLevelIndex> {
        VecDeque::from_iter(iter)
    }

    fn second_level_index<IndexKey>(
        indices: &mut HashTable<(IndexKey, SecondLevelTable<Self>)>,
        hash_fn: impl Fn(&IndexKey) -> u64,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> HashTable<(IndexKey, IndexingCodePtr)> {
        let mut index_locs = HashTable::new();

        for (key, code) in indices.drain() {
            let hash = hash_fn(&key);

            index_locs.insert_unique(
                hash,
                (key, IndexingCodePtr::internal(prelude.len() + 1)),
                |(key, _)| hash_fn(key),
            );

            prelude.push_back(IndexingLine::DynamicIndexedChoice(code));
        }

        index_locs
    }

    fn switch_on_lists(
        lists: &mut SecondLevelTable<Self>,
        prelude: &mut VecDeque<IndexingLine>,
    ) -> Option<IndexingCodePtr> {
        let lists = std::mem::replace(lists, SecondLevelTable::new());
        let internal_offset = prelude.len() + 1; // compensate for leading at front

        prelude.push_back(IndexingLine::DynamicIndexedChoice(lists));
        Some(IndexingCodePtr::internal(internal_offset))
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
    clause_offsets_to_arg_keys: ClauseArgData,
    arity: usize,
    non_counted_bt: bool,
}

impl<'a, I: Indexer> CodeOffsets<'a, I> {
    pub(crate) fn new(f64_tbl: &'a F64Table, non_counted_bt: bool, arity: usize) -> Self {
        CodeOffsets {
            indices: CodeIndices::new(),
            f64_tbl,
            clause_offsets_to_arg_keys: ClauseArgData::with_hasher(FxBuildHasher::default()),
            arity,
            non_counted_bt,
        }
    }

    pub(crate) fn map_clause_offset_to_arg_key(
        &mut self,
        arg_index: usize,
        key: OptArgIndexKey,
        clause_offset: usize,
    ) {
        let entry = self
            .clause_offsets_to_arg_keys
            .entry(clause_offset + 1) // 1 to offset incoming IndexingCode at front
            .or_insert_with(|| vec![OptArgIndexKey::None; self.arity]);

        entry[arg_index] = key;
    }

    fn map_offsets_to_index_keys(
        optimal_index: usize,
    ) -> impl for<'b> FnOnce(
        &'b [I::ThirdLevelIndex],
        &'b ClauseArgData,
    ) -> Box<dyn Iterator<Item = (usize, OptArgIndexKey, usize)> + 'b> {
        move |code, clause_offsets_to_arg_keys| {
            let iter = code
                .iter()
                .filter_map(|instr| {
                    let offset = instr.offset();
                    clause_offsets_to_arg_keys
                        .get(&offset)
                        .map(|keys| (keys, offset))
                })
                .flat_map(move |(v, offset)| {
                    v.iter()
                        .copied()
                        .map(move |key| (key, offset))
                        .enumerate()
                        .skip(optimal_index + 1)
                        .map(|(idx, (key, offset))| (idx, key, offset))
                });
            // optimal_index is 0-indexed so must add 1 to skip it as well

            Box::new(iter)
        }
    }

    fn on_demand_second_level_index(
        code: &mut SecondLevelTable<I>,
        optimal_index: usize,
        clause_offsets_to_arg_keys: &ClauseArgData,
        arity: usize,
        specs: &IndexingSpecs,
        is_extensible: bool,
    ) {
        let map_offsets_to_index_keys = Self::map_offsets_to_index_keys(optimal_index);
        let mut arg_var_keys = vec![IndexSet::with_hasher(FxBuildHasher::new()); arity];

        for (arg_index, arg_key, offset) in
            map_offsets_to_index_keys(code.offsets.make_contiguous(), clause_offsets_to_arg_keys)
        {
            if matches!(specs.get(arg_index), IndexingSpec::NoIndexing) {
                continue;
            }

            if let OptArgIndexKey::None = arg_key {
                arg_var_keys[arg_index].insert(offset);
            }
        }

        for (arg_index, dead_indices) in
            (optimal_index + 1..=arity).zip(arg_var_keys.drain(optimal_index + 1..))
        {
            if matches!(specs.get(arg_index), IndexingSpec::NoIndexing) {
                continue;
            }

            if !is_extensible && !dead_indices.is_empty() {
                // if there are any variables among the columns, don't
                // generate an OnDemandTerm or child instructions.
                continue;
            }

            if dead_indices.is_empty() {
                code.tables
                    .push_back(IndexedChoiceInstructionTable::OnDemandTerm {
                        arg_num: arg_index + 1,
                    });
            } else {
                debug_assert!(is_extensible);
                code.tables
                    .push_back(IndexedChoiceInstructionTable::DeadIndices {
                        arg_num: arg_index + 1,
                        indices: dead_indices,
                    });
            }
        }
    }

    fn index_list(&mut self, to_offset_instr: impl FnOnce(bool, bool) -> I::ThirdLevelIndex) {
        let is_initial_index = self.indices.lists.offsets.is_empty();
        let offset_instr = to_offset_instr(is_initial_index, self.non_counted_bt);
        self.indices.lists.offsets.push_back(offset_instr);
    }

    fn index_constant(
        &mut self,
        cell: HeapCellValue,
        to_offset_instr: impl FnOnce(bool, bool) -> I::ThirdLevelIndex,
    ) {
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

        let offset_instr = to_offset_instr(is_initial_index, self.non_counted_bt);
        code.offsets.push_back(offset_instr);
    }

    fn index_structure(
        &mut self,
        name: Atom,
        arity: usize,
        to_offset_instr: impl FnOnce(bool, bool) -> I::ThirdLevelIndex,
    ) {
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
        let is_initial_index = code.offsets.is_empty();

        let offset_instr = to_offset_instr(is_initial_index, self.non_counted_bt);
        code.offsets.push_back(offset_instr);
    }

    pub(crate) fn index_key(
        &mut self,
        index_key: OptArgIndexKey,
        to_offset_instr: impl FnOnce(bool, bool) -> I::ThirdLevelIndex,
    ) {
        match index_key {
            OptArgIndexKey::Structure(name, arity) => {
                self.index_structure(name, arity, to_offset_instr)
            }
            OptArgIndexKey::List => self.index_list(to_offset_instr),
            OptArgIndexKey::Literal(literal) => self.index_constant(literal, to_offset_instr),
            OptArgIndexKey::None => {}
        };
    }

    pub(crate) fn no_indices(&mut self) -> bool {
        let no_constants = self.indices.constants.is_empty();
        let no_structures = self.indices.structures.is_empty();
        let no_lists = self.indices.lists.offsets.is_empty();

        no_constants && no_structures && no_lists
    }

    pub(crate) fn compute_indices(
        mut self,
        is_extensible: bool,
        optimal_index: usize,
        specs: &IndexingSpecs,
        skip_stub_try_me_else: bool,
    ) -> (ExternalIndexingCodePtr, Vec<IndexingLine>) {
        let mut leading = SecondLevelTable::<I>::new();
        let mut prelude = VecDeque::new();

        leading.offsets =
            I::populate_root_offsets(self.clause_offsets_to_arg_keys.iter().enumerate().map(
                |(n, (&index, _keys))| {
                    let is_initial_index = n == 0;
                    // subtract 1 to compensate for compute_index action of + 1
                    I::compute_index(is_initial_index, index - 1, self.non_counted_bt)
                },
            ));

        for table in [&mut leading, &mut self.indices.lists] {
            Self::on_demand_second_level_index(
                table,
                optimal_index,
                &self.clause_offsets_to_arg_keys,
                self.arity,
                specs,
                is_extensible,
            );
        }

        let lists = I::switch_on_lists(&mut self.indices.lists, &mut prelude);

        for (_, code) in self.indices.structures.iter_mut() {
            Self::on_demand_second_level_index(
                code,
                optimal_index,
                &self.clause_offsets_to_arg_keys,
                self.arity,
                specs,
                is_extensible,
            );
        }

        let structures = I::switch_on(
            &mut self.indices.structures,
            |(name, arity)| {
                let cell = atom_as_cell!(name, *arity);
                cell.syntactic_hash(self.f64_tbl, FxHasher::default())
            },
            &mut prelude,
        );

        for (_, code) in self.indices.constants.iter_mut() {
            Self::on_demand_second_level_index(
                code,
                optimal_index,
                &self.clause_offsets_to_arg_keys,
                self.arity,
                specs,
                is_extensible,
            );
        }

        let constants = I::switch_on(
            &mut self.indices.constants,
            |cell| cell.syntactic_hash(self.f64_tbl, FxHasher::default()),
            &mut prelude,
        );

        let switch_on_term = IndexedChoiceInstructionTable::SwitchOnTerm {
            arg_num: optimal_index + 1, // in the WAM, register indices are 1-indexed
            constants,
            structures,
            lists,
        };

        let var_offset = 1 + skip_stub_try_me_else as usize;

        leading.tables.push_front(switch_on_term);
        prelude.push_front(I::to_indexing_line(leading));

        (I::var_offset_wrapper(var_offset), prelude.into())
    }
}
