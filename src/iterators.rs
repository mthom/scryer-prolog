use crate::atom_table::AtomCell;
use crate::forms::*;
use crate::heap_iter::*;
use crate::machine::heap::*;
use crate::machine::stack::*;
use crate::types::*;

use bit_set::*;
use fxhash::FxBuildHasher;
use indexmap::IndexMap;

use std::collections::VecDeque;
use std::iter::*;
use std::ops::Deref;
use std::vec::Vec;

pub(crate) trait TermIterator: Deref<Target = Heap> + Iterator<Item = HeapCellValue> {
    fn focus(&self) -> IterStackLoc;
    fn level(&mut self) -> Level;
}

#[derive(Debug)]
pub(crate) struct TargetIterator<I: FocusedHeapIter, const SKIP_ROOT: bool> {
    shallow_terms: IndexMap<usize, BitSet<usize>, FxBuildHasher>,
    root_terms: BitSet<usize>,
    iter: I,
    arg_c: usize,
}

fn record_path(
    heap: &impl SizedHeap,
    root_terms: &mut BitSet<usize>,
    mut root_loc: usize,
) -> usize {
    loop {
        let cell = heap[root_loc];
        root_terms.insert(root_loc);

        read_heap_cell!(cell,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                if h == root_loc {
                    break;
                } else {
                    root_loc = h;
                }
            }
            (HeapCellValueTag::Lis) => {
		        root_terms.insert(root_loc);
		        break;
	        }
            _ => {
                if cell.is_ref() {
                    root_terms.insert(cell.get_value() as usize);
                }

                break;
            }
        );
    }

    root_loc
}

fn find_root_terms(heap: &impl SizedHeap, root_loc: usize) -> (usize, BitSet<usize>) {
    let mut root_terms = BitSet::<usize>::default();
    let root_loc = record_path(heap, &mut root_terms, root_loc);
    (root_loc, root_terms)
}

fn find_shallow_terms(
    heap: &impl SizedHeap,
    root_loc: usize,
) -> IndexMap<usize, BitSet<usize>, FxBuildHasher> {
    let mut shallow_terms_map = IndexMap::with_hasher(FxBuildHasher::default());

    let (h, arity) = read_heap_cell!(heap[root_loc],
        (HeapCellValueTag::Str, s) => {
            (s+1, cell_as_atom_cell!(heap[s]).get_arity())
        }
        (HeapCellValueTag::Lis, l) => {
            (l, 2)
        }
        (HeapCellValueTag::Atom, (_name, arity)) => {
            (root_loc + 1, arity)
        }
        _ => {
            (root_loc, 0)
        }
    );

    for idx in 0..arity {
        let mut shallow_terms = BitSet::default();
        record_path(heap, &mut shallow_terms, h + idx);
        shallow_terms_map.insert(idx + 1, shallow_terms);
    }

    shallow_terms_map
}

impl<I: FocusedHeapIter, const SKIP_ROOT: bool> TargetIterator<I, SKIP_ROOT> {
    fn new(iter: I, root_loc: usize, arg_c: usize) -> Self {
        let (derefed_root_loc, root_terms) = find_root_terms(iter.deref(), root_loc);
        let shallow_terms = find_shallow_terms(iter.deref(), derefed_root_loc);

        Self {
            shallow_terms,
            root_terms,
            iter,
            arg_c,
        }
    }

    fn current_level(&self, arg_c_inc: usize) -> Level {
        let current_focus = self.iter.focus().value() as usize;

        if self.root_terms.contains(current_focus) {
            return Level::Root;
        }

        if let Some(shallow_terms) = self.shallow_terms.get(&(self.arg_c + arg_c_inc)) {
            if shallow_terms.contains(current_focus) {
                return Level::Shallow;
            }
        }

        Level::Deep
    }
}

impl<'a, const SKIP_ROOT: bool> TermIterator for FactIterator<'a, SKIP_ROOT> {
    fn focus(&self) -> IterStackLoc {
        self.iter.focus()
    }

    fn level(&mut self) -> Level {
        let lvl = self.current_level(1);

        if let Level::Shallow = lvl {
            self.arg_c += 1;
        }

        lvl
    }
}

impl<'a, const SKIP_ROOT: bool> TermIterator for QueryIterator<'a, SKIP_ROOT> {
    fn focus(&self) -> IterStackLoc {
        self.iter.focus()
    }

    fn level(&mut self) -> Level {
        let lvl = self.current_level(0);

        if let Level::Shallow = lvl {
            self.arg_c += 1;
        }

        lvl
    }
}

impl<I: FocusedHeapIter, const SKIP_ROOT: bool> Iterator for TargetIterator<I, SKIP_ROOT> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next_term = self.iter.next();

            if next_term.is_none() {
                return None;
            }

            let focus = self.iter.focus().value() as usize;

            if SKIP_ROOT && self.root_terms.contains(focus) {
                continue;
            } else {
                return next_term;
            }
        }
    }
}

impl<I: FocusedHeapIter, const SKIP_ROOT: bool> Deref for TargetIterator<I, SKIP_ROOT> {
    type Target = Heap;

    fn deref(&self) -> &Self::Target {
        self.iter.deref()
    }
}

impl<I: FocusedHeapIter, const SKIP_ROOT: bool> FocusedHeapIter for TargetIterator<I, SKIP_ROOT> {
    fn focus(&self) -> IterStackLoc {
        self.iter.focus()
    }
}

pub(crate) type FactIterator<'a, const SKIP_ROOT: bool> =
    TargetIterator<StackfulPreOrderHeapIter<'a, NonListElider>, SKIP_ROOT>;

pub(crate) fn fact_iterator<'a, const SKIP_ROOT: bool>(
    heap: &'a mut Heap,
    stack: &'a mut Stack,
    root_loc: usize,
) -> FactIterator<'a, SKIP_ROOT> {
    TargetIterator::new(stackful_preorder_iter(heap, stack, root_loc), root_loc, 0)
}

pub(crate) type QueryIterator<'a, const SKIP_ROOT: bool> =
    TargetIterator<PostOrderIterator<StackfulPreOrderHeapIter<'a, NonListElider>>, SKIP_ROOT>;

pub(crate) fn query_iterator<'a, const SKIP_ROOT: bool>(
    heap: &'a mut Heap,
    stack: &'a mut Stack,
    root_loc: usize,
) -> QueryIterator<'a, SKIP_ROOT> {
    TargetIterator::new(stackful_post_order_iter(heap, stack, root_loc), root_loc, 1)
}

#[derive(Debug, Copy, Clone)]
enum ClauseIteratorState<'a> {
    RemainingChunks(&'a VecDeque<ChunkedTerms>, usize),
    RemainingBranches(&'a Vec<VecDeque<ChunkedTerms>>, usize),
}

#[derive(Debug, Clone)]
pub(crate) enum ClauseItem<'a> {
    FirstBranch(usize),
    NextBranch,
    BranchEnd(usize),
    Chunk { chunk_num: usize, terms: &'a VecDeque<QueryTerm> },
}

#[derive(Debug)]
pub(crate) struct ClauseIterator<'a> {
    state_stack: Vec<ClauseIteratorState<'a>>,
    remaining_chunks_on_stack: usize,
}

fn state_from_chunked_terms(chunk_vec: &'_ VecDeque<ChunkedTerms>) -> ClauseIteratorState {
    if chunk_vec.len() == 1 {
        if let Some(ChunkedTerms::Branch(ref branches)) = chunk_vec.front() {
            return ClauseIteratorState::RemainingBranches(branches, 0);
        }
    }

    ClauseIteratorState::RemainingChunks(chunk_vec, 0)
}

impl<'a> ClauseIterator<'a> {
    pub fn new(clauses: &'a ChunkedTermVec) -> Self {
        match state_from_chunked_terms(&clauses.chunk_vec) {
            state @ ClauseIteratorState::RemainingBranches(..) => Self {
                state_stack: vec![state],
                remaining_chunks_on_stack: 0,
            },
            state @ ClauseIteratorState::RemainingChunks(..) => Self {
                state_stack: vec![state],
                remaining_chunks_on_stack: 1,
            },
        }
    }

    #[inline(always)]
    pub fn in_tail_position(&self) -> bool {
        self.remaining_chunks_on_stack == 0
    }

    fn branch_end_depth(&mut self) -> usize {
        let mut depth = 1;

        while let Some(state) = self.state_stack.pop() {
            match state {
                ClauseIteratorState::RemainingBranches(terms, focus)
                    if terms.len() == focus => {
                        depth += 1;
                    }
                _ => {
                    self.state_stack.push(state);
                    break;
                }
            }
        }

        depth
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = ClauseItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_stack.pop() {
            match state {
                ClauseIteratorState::RemainingChunks(chunks, focus)
                    if focus < chunks.len() => {
                        if focus + 1 < chunks.len() {
                            self.state_stack
                                .push(ClauseIteratorState::RemainingChunks(chunks, focus + 1));
                        } else {
                            self.remaining_chunks_on_stack -= 1;
                        }

                        match &chunks[focus] {
                            ChunkedTerms::Branch(branches) => {
                                self.state_stack
                                    .push(ClauseIteratorState::RemainingBranches(branches, 0));
                            }
                            &ChunkedTerms::Chunk { chunk_num, ref terms } => {
                                return Some(ClauseItem::Chunk { chunk_num, terms });
                            }
                        }
                    }
                ClauseIteratorState::RemainingChunks(chunks, focus) => {
                    debug_assert_eq!(chunks.len(), focus);
                }
                ClauseIteratorState::RemainingBranches(branches, focus)
                    if focus < branches.len() =>
                {
                    self.state_stack
                        .push(ClauseIteratorState::RemainingBranches(branches, focus + 1));
                    let state = state_from_chunked_terms(&branches[focus]);

                    if let ClauseIteratorState::RemainingChunks(..) = &state {
                        self.remaining_chunks_on_stack += 1;
                    }

                    self.state_stack.push(state);

                    return if focus == 0 {
                        Some(ClauseItem::FirstBranch(branches.len()))
                    } else {
                        Some(ClauseItem::NextBranch)
                    };
                }
                ClauseIteratorState::RemainingBranches(branches, focus) => {
                    debug_assert_eq!(branches.len(), focus);
                    return Some(ClauseItem::BranchEnd(self.branch_end_depth()));
                }
            }
        }

        None
    }
}
