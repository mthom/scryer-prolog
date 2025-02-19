use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::fact_iterator;
use crate::machine::heap::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::CompilationError;
use crate::machine::preprocessor::*;
use crate::machine::Stack;
use crate::parser::ast::*;
use crate::parser::dashu::Rational;
use crate::types::*;
use crate::variable_records::*;

use dashu::Integer;
use indexmap::{IndexMap, IndexSet};

use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)] //, PartialOrd, PartialEq, Eq, Hash)]
pub struct BranchNumber {
    branch_num: Rational,
    delta: Rational,
}

impl Default for BranchNumber {
    fn default() -> Self {
        Self {
            branch_num: Rational::from(1u64 << 63),
            delta: Rational::from(1),
        }
    }
}

impl PartialEq<BranchNumber> for BranchNumber {
    #[inline]
    fn eq(&self, rhs: &BranchNumber) -> bool {
        self.branch_num == rhs.branch_num
    }
}

impl Eq for BranchNumber {}

impl Hash for BranchNumber {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.branch_num.hash(hasher)
    }
}

impl PartialOrd<BranchNumber> for BranchNumber {
    #[inline]
    fn partial_cmp(&self, rhs: &BranchNumber) -> Option<Ordering> {
        self.branch_num.partial_cmp(&rhs.branch_num)
    }
}

impl BranchNumber {
    fn split(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone() + &self.delta / Rational::from(2),
            delta: &self.delta / Rational::from(4),
        }
    }

    fn incr_by_delta(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone() + &self.delta,
            delta: self.delta.clone(),
        }
    }

    fn halve_delta(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone(),
            delta: &self.delta / Rational::from(2),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClassifiedVar {
    Anon { term_loc: usize },
    InSitu { var_num: usize },
    Generated { term_loc: usize },
}

impl ClassifiedVar {
    fn term_loc(&self) -> Option<usize> {
        if let &ClassifiedVar::Generated { term_loc } = self {
            Some(term_loc)
        } else {
            None
        }
    }
}

fn to_classified_var(inverse_var_locs: &InverseVarLocs, term_loc: usize) -> ClassifiedVar {
    if inverse_var_locs.contains_key(&term_loc) {
        ClassifiedVar::Generated { term_loc }
    } else {
        ClassifiedVar::Anon { term_loc }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarInfo {
    var: ClassifiedVar,
    chunk_type: ChunkType,
    classify_info: ClassifyInfo,
    lvl: Level,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChunkInfo {
    term_loc: GenContext,
    // pointer to incidence, term occurrence arity.
    vars: Vec<VarInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BranchInfo {
    branch_num: BranchNumber,
    chunks: Vec<ChunkInfo>,
}

impl BranchInfo {
    fn new(branch_num: BranchNumber) -> Self {
        Self {
            branch_num,
            chunks: vec![],
        }
    }
}

type BranchMapInt = IndexMap<ClassifiedVar, Vec<BranchInfo>>;

#[derive(Debug, Clone)]
pub struct BranchMap(BranchMapInt);

impl Deref for BranchMap {
    type Target = BranchMapInt;

    #[inline(always)]
    fn deref(&self) -> &BranchMapInt {
        &self.0
    }
}

impl DerefMut for BranchMap {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut BranchMapInt {
        &mut self.0
    }
}

type RootSet = IndexSet<BranchNumber>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassifyInfo {
    arg_c: usize,
    arity: usize,
}

enum TraversalState {
    // construct a QueryTerm::Branch with number of disjuncts, reset
    // the chunk type to that of the chunk preceding the disjunct and the chunk_num.
    BuildDisjunct(usize),
    // add the last disjunct to a QueryTerm::Branch, continuing from
    // where it leaves off.
    BuildFinalDisjunct(usize),
    Fail,
    Succeed,
    GetCutPoint {
        var_num: usize,
        prev_b: bool,
    },
    Cut {
        var_num: usize,
        is_global: bool,
    },
    CutPrev(usize),
    ResetCallPolicy(CallPolicy),
    Term {
        subterm: HeapCellValue,
        term_loc: usize,
    },
    OverrideGlobalCutVar(usize),
    ResetGlobalCutVarOverride(Option<usize>),
    RemoveBranchNum,            // pop the current_branch_num and from the root set.
    AddBranchNum(BranchNumber), // set current_branch_num, add it to the root set
    RepBranchNum(BranchNumber), // replace current_branch_num and the latest in the root set
}

#[derive(Debug)]
pub struct VariableClassifier {
    call_policy: CallPolicy,
    current_branch_num: BranchNumber,
    branch_map: BranchMap,
    var_num: usize,
    root_set: RootSet,
    global_cut_var_num: Option<usize>,
    global_cut_var_num_override: Option<usize>,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct VarPtrIndex {
    pub chunk_num: usize,
    pub term_loc: usize,
}

#[derive(Debug)]
pub enum VarPtr {
    Numbered(usize),
    Anon,
}

#[derive(Debug, Default)]
pub struct VarLocsToNums {
    map: IndexMap<VarPtrIndex, usize>,
}

impl VarLocsToNums {
    pub fn insert(&mut self, key: VarPtrIndex, var_num: usize) {
        self.map.insert(key, var_num);
    }

    pub fn get(&self, idx: VarPtrIndex) -> VarPtr {
        self.map
            .get(&idx)
            .cloned()
            .map(VarPtr::Numbered)
            .unwrap_or_else(|| VarPtr::Anon)
    }
}

#[derive(Debug, Default)]
pub struct VarData {
    pub records: VariableRecords,
    pub global_cut_var_num: Option<usize>,
    pub allocates: bool,
    pub var_locs_to_nums: VarLocsToNums,
}

impl VarData {
    fn emit_initial_get_level(&mut self, build_stack: &mut ChunkedTermVec) {
        let global_cut_var_num = if let &Some(global_cut_var_num) = &self.global_cut_var_num {
            match &self.records[global_cut_var_num].allocation {
                VarAlloc::Perm { .. } => Some(global_cut_var_num),
                VarAlloc::Temp { term_loc, .. } if term_loc.chunk_num() > 0 => {
                    Some(global_cut_var_num)
                }
                _ => None,
            }
        } else {
            None
        };

        if let Some(global_cut_var_num) = global_cut_var_num {
            let term = QueryTerm::GetLevel(global_cut_var_num);
            self.records[global_cut_var_num].allocation = VarAlloc::Perm {
                reg: 0,
                allocation: PermVarAllocation::Pending,
            };

            match build_stack.front_mut() {
                Some(ChunkedTerms::Branch(_)) => {
                    build_stack.push_front(ChunkedTerms::Chunk {
                        chunk_num: 0,
                        terms: VecDeque::from(vec![term]),
                    });
                }
                Some(ChunkedTerms::Chunk { terms, .. }) => {
                    terms.push_front(term);
                }
                None => {
                    unreachable!()
                }
            }
        }
    }
}

pub type ClassifyFactResult = VarData;
pub type ClassifyRuleResult = (ChunkedTermVec, VarData);

fn merge_branch_seq(branches: impl Iterator<Item = BranchInfo>) -> BranchInfo {
    let mut branch_info = BranchInfo::new(BranchNumber::default());

    for mut branch in branches {
        branch_info.branch_num = branch.branch_num;
        branch_info.chunks.append(&mut branch.chunks);
    }

    branch_info.branch_num.delta = branch_info.branch_num.delta * Integer::from(2);
    branch_info.branch_num.branch_num -= &branch_info.branch_num.delta;

    branch_info
}

fn flatten_into_disjunct(build_stack: &mut ChunkedTermVec, preceding_len: usize) {
    let branch_vec = build_stack.drain(preceding_len + 1..).collect();

    if let ChunkedTerms::Branch(ref mut disjuncts) = &mut build_stack[preceding_len] {
        disjuncts.push(branch_vec);
    } else {
        unreachable!();
    }
}

impl VariableClassifier {
    pub fn new(call_policy: CallPolicy) -> Self {
        Self {
            call_policy,
            current_branch_num: BranchNumber::default(),
            branch_map: BranchMap(BranchMapInt::new()),
            root_set: RootSet::new(),
            var_num: 0,
            global_cut_var_num: None,
            global_cut_var_num_override: None,
        }
    }

    pub fn classify_fact<'a, LS: LoadState<'a>>(
        mut self,
        loader: &mut Loader<'a, LS>,
        term: &TermWriteResult,
    ) -> Result<ClassifyFactResult, CompilationError> {
        self.classify_head_variables(loader, term, term.focus)?;
        Ok(self.branch_map.separate_and_classify_variables(
            self.var_num,
            self.global_cut_var_num,
            0,
        ))
    }

    pub fn classify_rule<'a, LS: LoadState<'a>>(
        mut self,
        loader: &mut Loader<'a, LS>,
        term: &TermWriteResult,
    ) -> Result<ClassifyRuleResult, CompilationError> {
        let heap = &mut LS::machine_st(&mut loader.payload).heap;

        let head_loc = term_nth_arg(heap, term.focus, 1).unwrap();
        let body_loc = term_nth_arg(heap, term.focus, 2).unwrap();

        self.classify_head_variables(loader, term, head_loc)?;
        self.root_set.insert(self.current_branch_num.clone());

        let mut query_terms = self.classify_body_variables(loader, term, body_loc)?;

        self.merge_branches();

        let mut var_data = self.branch_map.separate_and_classify_variables(
            self.var_num,
            self.global_cut_var_num,
            query_terms.current_chunk_num,
        );

        var_data.emit_initial_get_level(&mut query_terms);

        Ok((query_terms, var_data))
    }

    fn merge_branches(&mut self) {
        for branches in self.branch_map.values_mut() {
            let mut old_branches = std::mem::take(branches);

            while let Some(last_branch_num) = old_branches.last().map(|bi| &bi.branch_num) {
                let mut old_branches_len = old_branches.len();

                for (rev_idx, bi) in old_branches.iter().rev().enumerate() {
                    if &bi.branch_num > last_branch_num {
                        old_branches_len = old_branches.len() - rev_idx;
                    }
                }

                let iter = old_branches.drain(old_branches_len - 1..);
                branches.push(merge_branch_seq(iter));
            }

            branches.reverse();
        }
    }

    fn probe_body_term(
        &mut self,
        arg_c: usize,
        arity: usize,
        term: &mut FocusedHeapRefMut,
        inverse_var_locs: &InverseVarLocs,
        context: GenContext,
    ) {
        let classify_info = ClassifyInfo { arg_c, arity };

        let mut lvl = Level::Shallow;
        let mut stack = Stack::uninitialized();
        let iter = fact_iterator::<false>(term.heap, &mut stack, term.focus);

        // second arg is true to iterate the root, which may be a variable
        for subterm in iter {
            if !subterm.is_var() {
                lvl = Level::Deep;
                continue;
            }

            let var_loc = subterm.get_value() as usize;
            let var = to_classified_var(inverse_var_locs, var_loc);

            self.probe_body_var(
                context,
                VarInfo {
                    var,
                    lvl,
                    classify_info,
                    chunk_type: context.chunk_type(),
                },
            );
        }
    }

    fn probe_body_var(&mut self, context: GenContext, var_info: VarInfo) {
        let chunk_num = context.chunk_num();
        let branch_info_v = self.branch_map.entry(var_info.var).or_default();

        let needs_new_branch = if let Some(last_bi) = branch_info_v.last() {
            !self.root_set.contains(&last_bi.branch_num)
        } else {
            true
        };

        if needs_new_branch {
            branch_info_v.push(BranchInfo::new(self.current_branch_num.clone()));
        }

        let branch_info = branch_info_v.last_mut().unwrap();

        let needs_new_chunk = if let Some(last_ci) = branch_info.chunks.last() {
            last_ci.term_loc.chunk_num() != chunk_num
        } else {
            true
        };

        if needs_new_chunk {
            branch_info.chunks.push(ChunkInfo {
                term_loc: context,
                vars: vec![],
            });
        }

        let chunk_info = branch_info.chunks.last_mut().unwrap();
        chunk_info.vars.push(var_info);
    }

    fn probe_in_situ_var(&mut self, context: GenContext, var_num: usize) {
        let classify_info = ClassifyInfo { arg_c: 1, arity: 1 };

        let var_info = VarInfo {
            var: ClassifiedVar::InSitu { var_num },
            classify_info,
            chunk_type: context.chunk_type(),
            lvl: Level::Shallow,
        };

        self.probe_body_var(context, var_info);
    }

    fn classify_head_variables<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: &TermWriteResult,
        head_loc: usize,
    ) -> Result<(), CompilationError> {
        let heap = &mut LS::machine_st(&mut loader.payload).heap;
        let arity = term_predicate_key(heap, head_loc)
            .map(|(_, arity)| arity)
            .ok_or(CompilationError::InvalidRuleHead)?;

        let mut classify_info = ClassifyInfo { arg_c: 1, arity };

        if arity > 0 {
            let (_term_loc, value) = subterm_index(heap, head_loc);
            let str_offset = value.get_value() as usize;

            debug_assert_eq!(value.get_tag(), HeapCellValueTag::Str);

            for idx in str_offset + 1..=str_offset + arity {
                let mut lvl = Level::Shallow;
                let mut stack = Stack::uninitialized();
                let iter = fact_iterator::<false>(heap, &mut stack, idx);

                for subterm in iter {
                    if !subterm.is_var() {
                        lvl = Level::Deep;
                        continue;
                    }

                    let term_loc = subterm.get_value() as usize;
                    let var = to_classified_var(&term.inverse_var_locs, term_loc);

                    // the body of the if let here is an inlined
                    // "probe_head_var". note the difference between it
                    // and "probe_body_var".
                    let branch_info_v = self.branch_map.entry(var).or_default();
                    let needs_new_branch = branch_info_v.is_empty();

                    if needs_new_branch {
                        branch_info_v.push(BranchInfo::new(self.current_branch_num.clone()));
                    }

                    let branch_info = branch_info_v.last_mut().unwrap();
                    let needs_new_chunk = branch_info.chunks.is_empty();

                    if needs_new_chunk {
                        branch_info.chunks.push(ChunkInfo {
                            term_loc: GenContext::Head,
                            vars: vec![],
                        });
                    }

                    let chunk_info = branch_info.chunks.last_mut().unwrap();
                    let var_info = VarInfo {
                        var,
                        classify_info,
                        chunk_type: ChunkType::Head,
                        lvl,
                    };

                    chunk_info.vars.push(var_info);
                }

                classify_info.arg_c += 1;
            }
        }

        Ok(())
    }

    fn new_cut_state(&mut self, context: GenContext) -> TraversalState {
        let (var_num, is_global) = if let Some(var_num) = self.global_cut_var_num_override {
            (var_num, false)
        } else if let Some(var_num) = self.global_cut_var_num {
            (var_num, true)
        } else {
            let var_num = self.var_num;

            self.global_cut_var_num = Some(var_num);
            self.var_num += 1;

            (var_num, true)
        };

        self.probe_in_situ_var(context, var_num);

        TraversalState::Cut { var_num, is_global }
    }

    fn classify_body_variables<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        terms: &TermWriteResult,
        term_loc: usize,
    ) -> Result<ChunkedTermVec, CompilationError> {
        let mut state_stack = vec![TraversalState::Term {
            subterm: loader.machine_heap()[term_loc],
            term_loc,
        }];
        let mut build_stack = ChunkedTermVec::new();

        'outer: while let Some(traversal_st) = state_stack.pop() {
            match traversal_st {
                TraversalState::AddBranchNum(branch_num) => {
                    self.root_set.insert(branch_num.clone());
                    self.current_branch_num = branch_num;
                }
                TraversalState::RemoveBranchNum => {
                    self.root_set.pop();
                }
                TraversalState::RepBranchNum(branch_num) => {
                    self.root_set.pop();
                    self.root_set.insert(branch_num.clone());
                    self.current_branch_num = branch_num;
                }
                TraversalState::ResetCallPolicy(call_policy) => {
                    self.call_policy = call_policy;
                }
                TraversalState::BuildDisjunct(preceding_len) => {
                    flatten_into_disjunct(&mut build_stack, preceding_len);

                    build_stack.current_chunk_type = ChunkType::Mid;
                    build_stack.current_chunk_num += 1;
                }
                TraversalState::BuildFinalDisjunct(preceding_len) => {
                    flatten_into_disjunct(&mut build_stack, preceding_len);

                    build_stack.current_chunk_type = ChunkType::Mid;
                    build_stack.current_chunk_num += 1;
                }
                TraversalState::GetCutPoint { var_num, prev_b } => {
                    if build_stack.try_set_chunk_at_inlined_boundary() {
                        build_stack.add_chunk();
                    }

                    let context = build_stack.current_gen_context();
                    self.probe_in_situ_var(context, var_num);
                    build_stack.push_chunk_term(QueryTerm::GetCutPoint { var_num, prev_b });
                }
                TraversalState::OverrideGlobalCutVar(var_num) => {
                    self.global_cut_var_num_override = Some(var_num);
                }
                TraversalState::ResetGlobalCutVarOverride(old_override) => {
                    self.global_cut_var_num_override = old_override;
                }
                TraversalState::Cut { var_num, is_global } => {
                    if build_stack.try_set_chunk_at_inlined_boundary() {
                        build_stack.add_chunk();
                    }

                    let context = build_stack.current_gen_context();
                    self.probe_in_situ_var(context, var_num);

                    build_stack.push_chunk_term(if is_global {
                        QueryTerm::GlobalCut(var_num)
                    } else {
                        QueryTerm::LocalCut {
                            var_num,
                            cut_prev: false,
                        }
                    });
                }
                TraversalState::CutPrev(var_num) => {
                    if build_stack.try_set_chunk_at_inlined_boundary() {
                        build_stack.add_chunk();
                    }

                    let context = build_stack.current_gen_context();
                    self.probe_in_situ_var(context, var_num);

                    build_stack.push_chunk_term(QueryTerm::LocalCut {
                        var_num,
                        cut_prev: true,
                    });
                }
                TraversalState::Fail => {
                    build_stack.push_chunk_term(QueryTerm::Fail);
                }
                TraversalState::Succeed => {
                    build_stack.push_chunk_term(QueryTerm::Succeed);
                }
                TraversalState::Term {
                    mut subterm,
                    mut term_loc,
                } => {
                    // return true iff new chunk should be added.
                    let update_chunk_data =
                        |build_stack: &mut ChunkedTermVec, key: PredicateKey| {
                            if ClauseType::is_inlined(key.0, key.1) {
                                build_stack.try_set_chunk_at_inlined_boundary()
                            } else {
                                build_stack.try_set_chunk_at_call_boundary()
                            }
                        };

                    macro_rules! add_chunk {
                        ($key:expr, $tag:expr, $term_loc:expr) => {{
                            if update_chunk_data(&mut build_stack, $key) {
                                build_stack.add_chunk();
                            }

                            let context = build_stack.current_gen_context();

                            for (arg_c, term_loc) in
                                ($term_loc + 1..=$term_loc + $key.1).enumerate()
                            {
                                let mut term =
                                    FocusedHeapRefMut::from(loader.machine_heap(), term_loc);

                                self.probe_body_term(
                                    arg_c + 1,
                                    $key.1,
                                    &mut term,
                                    &terms.inverse_var_locs,
                                    context,
                                );
                            }

                            build_stack.push_chunk_term(QueryTerm::Clause(clause_to_query_term(
                                loader,
                                $key,
                                &terms,
                                HeapCellValue::build_with($tag, $term_loc as u64),
                                self.call_policy,
                            )));
                        }};
                    }

                    macro_rules! add_qualified_chunk {
                        ($module_name:expr, $key:expr, $tag:expr, $term_loc:expr) => {{
                            if update_chunk_data(&mut build_stack, $key) {
                                build_stack.add_chunk();
                            }

                            let context = build_stack.current_gen_context();

                            for (arg_c, term_loc) in
                                ($term_loc + 1..=$term_loc + $key.1).enumerate()
                            {
                                let mut term =
                                    FocusedHeapRefMut::from(loader.machine_heap(), term_loc);

                                self.probe_body_term(
                                    arg_c + 1,
                                    $key.1,
                                    &mut term,
                                    &terms.inverse_var_locs,
                                    context,
                                );
                            }

                            build_stack.push_chunk_term(QueryTerm::Clause(
                                qualified_clause_to_query_term(
                                    loader,
                                    $key,
                                    $module_name,
                                    &terms,
                                    HeapCellValue::build_with($tag, $term_loc as u64),
                                    self.call_policy,
                                ),
                            ));
                        }};
                    }

                    loop {
                        let heap = loader.machine_heap();

                        read_heap_cell!(subterm,
                            (HeapCellValueTag::Str, subterm_loc) => {
                                let (name, arity) = cell_as_atom_cell!(heap[subterm_loc])
                                    .get_name_and_arity();

                                match (name, arity) {
                                    (atom!("->") | atom!(";") | atom!(","), 3) => {
                                        if blunt_index_ptr(heap, (name, 2), subterm_loc) {
                                            subterm = heap[subterm_loc];
                                            continue;
                                        }

                                        add_chunk!((name, 2), HeapCellValueTag::Str, subterm_loc);
                                    }
                                    (atom!(","), 2) => {
                                        let head_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let tail_loc = term_nth_arg(heap, subterm_loc, 2).unwrap();
                                        let head = heap[head_loc];

                                        let iter = unfold_by_str_locs(heap, tail_loc, atom!(","))
                                            .into_iter()
                                            .rev()
                                            .chain(std::iter::once((head, head_loc)))
                                            .map(|(subterm, term_loc)| {
                                                TraversalState::Term { subterm, term_loc }
                                            });
                                        state_stack.extend(iter);
                                    }
                                    (atom!(";"), 2) => {
                                        let head_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let tail_loc = term_nth_arg(heap, subterm_loc, 2).unwrap();

                                        let head = heap[head_loc];

                                        let first_branch_num = self.current_branch_num.split();
                                        let branches: Vec<_> = std::iter::once((head, head_loc))
                                            .chain(
                                                unfold_by_str_locs(heap, tail_loc, atom!(";"))
                                                    .into_iter(),
                                            )
                                            .collect();

                                        let mut branch_numbers = vec![first_branch_num];

                                        for idx in 1..branches.len() {
                                            let succ_branch_number = branch_numbers[idx - 1].incr_by_delta();

                                            branch_numbers.push(if idx + 1 < branches.len() {
                                                succ_branch_number.split()
                                            } else {
                                                succ_branch_number
                                            });
                                        }

                                        let build_stack_len = build_stack.len();
                                        build_stack.reserve_branch(branches.len());

                                        state_stack.push(TraversalState::RepBranchNum(
                                            self.current_branch_num.halve_delta(),
                                        ));

                                        let iter = branches.into_iter().zip(branch_numbers.into_iter());
                                        let final_disjunct_loc = state_stack.len();

                                        for ((subterm, term_loc), branch_num) in iter.rev() {
                                            state_stack.push(TraversalState::BuildDisjunct(build_stack_len));
                                            state_stack.push(TraversalState::RemoveBranchNum);
                                            state_stack.push(TraversalState::Term { subterm, term_loc });
                                            state_stack.push(TraversalState::AddBranchNum(branch_num));
                                        }

                                        if let TraversalState::BuildDisjunct(build_stack_len) =
                                            state_stack[final_disjunct_loc]
                                        {
                                            state_stack[final_disjunct_loc] =
                                                TraversalState::BuildFinalDisjunct(build_stack_len);
                                        }

                                        build_stack.current_chunk_type = ChunkType::Mid;
                                        build_stack.current_chunk_num += 1;
                                    }
                                    (atom!("->"), 2) => {
                                        let if_term_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let then_term_loc = term_nth_arg(heap, subterm_loc, 2).unwrap();

                                        let if_term = heap[if_term_loc];
                                        let then_term = heap[then_term_loc];

                                        let prev_b = if matches!(
                                            state_stack.last(),
                                            Some(TraversalState::RemoveBranchNum)
                                        ) {
                                            // check if the second-to-last element
                                            // is a regular BuildDisjunct, as we
                                            // don't want to add GetPrevLevel in
                                            // case of a TrustMe.
                                            match state_stack.iter().rev().nth(1) {
                                                Some(&TraversalState::BuildDisjunct(preceding_len)) => {
                                                    preceding_len + 1 == build_stack.len()
                                                }
                                                _ => false,
                                            }
                                        } else {
                                            false
                                        };

                                        state_stack.push(TraversalState::Term {
                                            subterm: then_term,
                                            term_loc: then_term_loc,
                                        });
                                        state_stack.push(TraversalState::Cut {
                                            var_num: self.var_num,
                                            is_global: false,
                                        });
                                        state_stack.push(TraversalState::Term {
                                            subterm: if_term,
                                            term_loc: if_term_loc,
                                        });
                                        state_stack.push(TraversalState::GetCutPoint {
                                            var_num: self.var_num,
                                            prev_b,
                                        });

                                        self.var_num += 1;
                                    }
                                    (atom!("\\+"), 1) => {
                                        let not_term_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let not_term = heap[not_term_loc];
                                        let build_stack_len = build_stack.len();

                                        build_stack.reserve_branch(2);

                                        let branch_num = self.current_branch_num.split();
                                        let succ_branch_num = branch_num.incr_by_delta();

                                        state_stack.push(TraversalState::BuildFinalDisjunct(build_stack_len));
                                        state_stack.push(TraversalState::Succeed);
                                        state_stack.push(TraversalState::BuildDisjunct(build_stack_len));
                                        state_stack.push(TraversalState::RepBranchNum(succ_branch_num));
                                        state_stack.push(TraversalState::Fail);
                                        state_stack.push(TraversalState::CutPrev(self.var_num));
                                        state_stack.push(TraversalState::ResetGlobalCutVarOverride(
                                            self.global_cut_var_num_override,
                                        ));
                                        state_stack.push(TraversalState::Term {
                                            subterm: not_term,
                                            term_loc: not_term_loc,
                                        });
                                        state_stack.push(TraversalState::OverrideGlobalCutVar(self.var_num));
                                        state_stack.push(TraversalState::GetCutPoint {
                                            var_num: self.var_num,
                                            prev_b: false,
                                        });
                                        state_stack.push(TraversalState::AddBranchNum(branch_num));

                                        build_stack.current_chunk_type = ChunkType::Mid;
                                        build_stack.current_chunk_num += 1;

                                        self.var_num += 1;
                                    }
                                    (atom!(":"), 2) => {
                                        let module_name_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let predicate_term_loc = term_nth_arg(heap, subterm_loc, 2).unwrap();
                                        let mut focused = FocusedHeapRefMut::from(heap, module_name_loc);

                                        let module_name = focused.deref_loc(module_name_loc);
                                        let predicate_term = focused.deref_loc(predicate_term_loc);

                                        read_heap_cell!(module_name,
                                            (HeapCellValueTag::Atom, (module_name, arity)) => {
                                                if arity == 0 {
                                                    read_heap_cell!(predicate_term,
                                                        (HeapCellValueTag::Str, s) => {
                                                            let key = cell_as_atom_cell!(heap[s])
                                                                .get_name_and_arity();

                                                            add_qualified_chunk!(
                                                                module_name,
                                                                key,
                                                                HeapCellValueTag::Str,
                                                                s
                                                            );
                                                        }
                                                        (HeapCellValueTag::Atom, (predicate_name, predicate_arity)) => {
                                                            debug_assert_eq!(predicate_arity, 0);
                                                            let key = (predicate_name, predicate_arity);

                                                            add_qualified_chunk!(
                                                                module_name,
                                                                key,
                                                                HeapCellValueTag::Str,
                                                                predicate_term_loc
                                                            );
                                                        }
                                                        _ => {}
                                                    );

                                                    continue 'outer;
                                                }
                                            }
                                            _ => {}
                                        );

                                        if update_chunk_data(&mut build_stack, (atom!("call"), 2)) {
                                            build_stack.add_chunk();
                                        }

                                        let context = build_stack.current_gen_context();

                                        focused.focus = module_name_loc;

                                        self.probe_body_term(
                                            1, 0, &mut focused, &terms.inverse_var_locs, context,
                                        );

                                        focused.focus = predicate_term_loc;

                                        self.probe_body_term(
                                            2, 0, &mut focused, &terms.inverse_var_locs, context,
                                        );

                                        let h = heap.cell_len();

                                        heap.push_cell(atom_as_cell!(atom!("call"), 1))
                                            .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;
                                        heap.push_cell(str_loc_as_cell!(subterm_loc))
                                            .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

                                        build_stack.push_chunk_term(QueryTerm::Clause(clause_to_query_term(
                                            loader,
                                            (atom!("call"), 1),
                                            terms,
                                            str_loc_as_cell!(h),
                                            self.call_policy,
                                        )));
                                    }
                                    (atom!("$call_with_inference_counting"), 1) => {
                                        let term_loc = term_nth_arg(heap, subterm_loc, 1).unwrap();
                                        let heap = loader.machine_heap();
                                        let subterm = heap_bound_store(
                                            heap,
                                            heap_bound_deref(heap, heap[term_loc]),
                                        );

                                        state_stack.push(TraversalState::ResetCallPolicy(self.call_policy));
                                        state_stack.push(TraversalState::Term { subterm, term_loc });

                                        self.call_policy = CallPolicy::Counted;
                                    }
                                    (name, arity) => {
                                        add_chunk!((name, arity), HeapCellValueTag::Str, subterm_loc);
                                    }
                                }
                            }
                            (HeapCellValueTag::Atom, (name, arity)) => {
                                debug_assert_eq!(arity, 0);

                                if name == atom!("!") {
                                    let context = build_stack.current_gen_context();
                                    state_stack.push(self.new_cut_state(context));
                                } else {
                                    add_chunk!((name, 0), HeapCellValueTag::Var, term_loc);
                                }
                            }
                            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                                if h != term_loc {
                                    subterm = heap[h];
                                    term_loc = h;
                                    continue;
                                }

                                add_chunk!((atom!("call"), 1), HeapCellValueTag::Var, h);
                            }
                            _ => {
                                return Err(CompilationError::InadmissibleQueryTerm);
                            }
                        );

                        break;
                    }
                }
            }
        }

        Ok(build_stack)
    }
}

impl BranchMap {
    pub fn separate_and_classify_variables(
        &mut self,
        var_num: usize,
        global_cut_var_num: Option<usize>,
        current_chunk_num: usize,
    ) -> VarData {
        let mut var_data = VarData {
            records: VariableRecords::new(var_num),
            global_cut_var_num,
            allocates: current_chunk_num > 0,
            var_locs_to_nums: VarLocsToNums::default(),
        };

        for (var, branches) in self.iter_mut() {
            let (mut var_num, var_num_incr) = match var {
                &ClassifiedVar::InSitu { var_num } => (var_num, false),
                _ => (var_data.records.len(), true),
            };

            for branch in branches.iter_mut() {
                if var_num_incr {
                    var_num = var_data.records.len();
                    var_data.records.push(VariableRecord::default());
                }

                if branch.chunks.len() <= 1 {
                    // true iff var is a temporary variable.
                    debug_assert_eq!(branch.chunks.len(), 1);

                    let chunk = &mut branch.chunks[0];
                    let mut temp_var_data = TempVarData::new();

                    for var_info in chunk.vars.iter_mut() {
                        if var_info.lvl == Level::Shallow {
                            let context = var_info
                                .chunk_type
                                .to_gen_context(chunk.term_loc.chunk_num());

                            temp_var_data
                                .use_set
                                .insert((context, var_info.classify_info.arg_c));
                        }
                    }

                    var_data.records[var_num].allocation = VarAlloc::Temp {
                        term_loc: chunk.term_loc,
                        temp_reg: 0,
                        temp_var_data,
                        safety: VarSafetyStatus::Needed,
                        to_perm_var_num: None,
                    };
                } // else VarAlloc is already a Perm variant, as it's the default.

                for chunk in branch.chunks.iter_mut() {
                    var_data.records[var_num].num_occurrences += chunk.vars.len();

                    if let Some(term_loc) = var.term_loc() {
                        let chunk_num = chunk.term_loc.chunk_num();

                        var_data.var_locs_to_nums.insert(
                            VarPtrIndex {
                                chunk_num,
                                term_loc,
                            },
                            var_num,
                        );
                    }
                }
            }
        }

        var_data.records.populate_restricting_sets();
        var_data
    }
}
