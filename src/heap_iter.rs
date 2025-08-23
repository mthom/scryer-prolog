#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

#[cfg(test)]
pub(crate) use crate::machine::gc::StacklessPreOrderHeapIter;

use crate::atom_table::*;
use crate::machine::cycle_detection::*;
use crate::machine::heap::*;
use crate::machine::stack::*;
use crate::types::*;

use core::marker::PhantomData;
use scryer_modular_bitfield::prelude::*;

use std::ops::Deref;
use std::vec::Vec;

#[inline(always)]
pub fn eager_stackful_preorder_iter(
    heap: &mut Heap,
    value: HeapCellValue,
) -> EagerStackfulPreOrderHeapIter<'_> {
    EagerStackfulPreOrderHeapIter::new(heap, value)
}

/*
 * Unlike StackfulPreOrderHeapIter, this iterator not only marks
 * cyclic terms for the sake of skipping them at the second visit but
 * leaves them marked until it is dropped. This makes for, e.g., more
 * efficient ground/1 and term_variables/2 definitions.
*/

pub struct EagerStackfulPreOrderHeapIter<'a> {
    start_value: HeapCellValue,
    iter_stack: Vec<HeapCellValue>,
    mark_phase: bool,
    heap: &'a mut Heap,
}

impl<'a> Drop for EagerStackfulPreOrderHeapIter<'a> {
    fn drop(&mut self) {
        self.mark_phase = false;

        self.iter_stack.clear();
        self.start_value.set_mark_bit(true);
        self.iter_stack.push(self.start_value);

        while self.follow().is_some() {}
    }
}

impl<'a> EagerStackfulPreOrderHeapIter<'a> {
    pub fn new(heap: &'a mut Heap, value: HeapCellValue) -> Self {
        Self {
            start_value: value,
            iter_stack: vec![value],
            mark_phase: true,
            heap,
        }
    }

    #[inline]
    fn is_self_ref_var(&self, value: HeapCellValue) -> bool {
        if value.is_var() {
            let h = value.get_value() as usize;

            if self.heap[h].is_var() && self.heap[h].get_value() as usize == h {
                return true;
            }
        }

        false
    }

    fn follow(&mut self) -> Option<HeapCellValue> {
        while let Some(value) = self.iter_stack.pop() {
            if value.get_mark_bit() == self.mark_phase {
                // follow marked variables to their end. only marked
                // non-variables are ignored.
                if self.is_self_ref_var(value) {
                    return Some(unmark_cell_bits!(value));
                } else if !value.is_var() {
                    continue;
                }
            }

            read_heap_cell!(value,
                (HeapCellValueTag::Str, s) => {
                    let arity = cell_as_atom_cell!(self.heap[s]).get_arity();

                    for idx in (s + 1 .. s + arity + 1).rev() {
                        if self.heap[idx].get_mark_bit() != self.mark_phase {
                            self.iter_stack.push(self.heap[idx]);
                            self.heap[idx].set_mark_bit(self.mark_phase);
                        }
                    }
                }
                (HeapCellValueTag::Lis, l) => {
                    if self.heap[l+1].get_mark_bit() != self.mark_phase {
                        self.iter_stack.push(self.heap[l+1]);
                        self.heap[l+1].set_mark_bit(self.mark_phase);
                    }

                    if self.heap[l].get_mark_bit() != self.mark_phase {
                        self.iter_stack.push(self.heap[l]);
                        self.heap[l].set_mark_bit(self.mark_phase);
                    }
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    let var_value = self.heap[h];
                    self.heap[h].set_mark_bit(self.mark_phase);

                    if var_value.get_mark_bit() || !(self.heap[h].is_var() && self.heap[h].get_value() as usize == h) {
                        self.iter_stack.push(var_value);
                        continue;
                    }
                }
                (HeapCellValueTag::PStrLoc, h) => {
                    let tail_idx = self.heap.scan_slice_to_str(h).tail_idx;

                    self.heap[tail_idx].set_mark_bit(self.mark_phase);
                    self.iter_stack.push(self.heap[tail_idx]);
                }
                _ => {
                }
            );

            return Some(value);
        }

        None
    }
}

impl<'a> Iterator for EagerStackfulPreOrderHeapIter<'a> {
    type Item = HeapCellValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.follow()
    }
}

#[derive(BitfieldSpecifier, Clone, Copy, Debug, PartialEq, Eq)]
#[bits = 2]
enum IterStackLocTag {
    Iterable,
    Marked,
    PendingMark,
}

#[derive(BitfieldSpecifier, Clone, Copy, Debug, PartialEq, Eq)]
#[bits = 1]
pub enum HeapOrStackTag {
    Heap,
    Stack,
}

#[bitfield]
#[repr(u64)]
#[derive(Clone, Copy, Debug)]
pub struct IterStackLoc {
    pub value: B61,
    tag: IterStackLocTag,
    heap_or_stack: HeapOrStackTag,
}

impl IterStackLoc {
    #[inline]
    pub fn iterable_loc(h: usize, heap_or_stack: HeapOrStackTag) -> Self {
        IterStackLoc::new()
            .with_tag(IterStackLocTag::Iterable)
            .with_heap_or_stack(heap_or_stack)
            .with_value(h as u64)
    }

    #[inline]
    pub fn marked_loc(h: usize, heap_or_stack: HeapOrStackTag) -> Self {
        IterStackLoc::new()
            .with_tag(IterStackLocTag::Marked)
            .with_heap_or_stack(heap_or_stack)
            .with_value(h as u64)
    }

    #[inline]
    fn pending_marked_loc(h: usize, heap_or_stack: HeapOrStackTag) -> Self {
        IterStackLoc::new()
            .with_tag(IterStackLocTag::PendingMark)
            .with_heap_or_stack(heap_or_stack)
            .with_value(h as u64)
    }

    #[inline]
    pub fn is_marked(self) -> bool {
        self.tag() == IterStackLocTag::Marked
    }

    #[inline]
    pub fn is_pending_mark(self) -> bool {
        self.tag() == IterStackLocTag::PendingMark
    }

    #[inline]
    pub fn as_ref(self) -> Ref {
        match self.heap_or_stack() {
            HeapOrStackTag::Heap => Ref::heap_cell(self.value() as usize),
            HeapOrStackTag::Stack => Ref::stack_cell(self.value() as usize),
        }
    }
}

pub trait ListElisionPolicy {
    fn elide_lists() -> bool;
}

#[derive(Debug)]
pub struct ListElider {}

impl ListElisionPolicy for ListElider {
    #[inline(always)]
    fn elide_lists() -> bool {
        true
    }
}

#[derive(Debug)]
pub struct NonListElider {}

impl ListElisionPolicy for NonListElider {
    #[inline(always)]
    fn elide_lists() -> bool {
        false
    }
}

#[derive(Debug)]
pub struct StackfulPreOrderHeapIter<'a, ElideLists> {
    pub heap: &'a mut Heap,
    pub machine_stack: &'a mut Stack,
    stack: Vec<IterStackLoc>,
    h: IterStackLoc,
    _marker: PhantomData<ElideLists>,
}

impl<'a, ElideLists> Drop for StackfulPreOrderHeapIter<'a, ElideLists> {
    fn drop(&mut self) {
        while let Some(h) = self.stack.pop() {
            let cell = self.read_cell_mut(h);

            cell.set_forwarding_bit(false);
            cell.set_mark_bit(false);
        }
    }
}

pub trait FocusedHeapIter: Iterator<Item = HeapCellValue> {
    fn focus(&self) -> IterStackLoc;
}

impl<'a, ElideLists: ListElisionPolicy> FocusedHeapIter
    for StackfulPreOrderHeapIter<'a, ElideLists>
{
    #[inline]
    fn focus(&self) -> IterStackLoc {
        self.h
    }
}

impl<'a, ElideLists> StackfulPreOrderHeapIter<'a, ElideLists> {
    #[inline]
    pub fn read_cell_mut(&mut self, loc: IterStackLoc) -> &mut HeapCellValue {
        match loc.heap_or_stack() {
            HeapOrStackTag::Heap => &mut self.heap[loc.value() as usize],
            HeapOrStackTag::Stack => &mut self.machine_stack[loc.value() as usize],
        }
    }

    #[inline]
    pub fn read_cell(&self, loc: IterStackLoc) -> HeapCellValue {
        match loc.heap_or_stack() {
            HeapOrStackTag::Heap => self.heap[loc.value() as usize],
            HeapOrStackTag::Stack => self.machine_stack[loc.value() as usize],
        }
    }

    #[inline]
    pub fn push_stack(&mut self, h: IterStackLoc) {
        self.stack.push(h);
    }

    #[inline]
    pub fn stack_last(&self) -> Option<IterStackLoc> {
        for h in self.stack.iter().rev() {
            let is_readable_marked = h.is_marked();
            let cell = self.read_cell(*h);

            if cell.get_forwarding_bit() {
                return Some(*h);
            } else if cell.get_mark_bit() && !is_readable_marked {
                continue;
            }

            return Some(*h);
        }

        None
    }

    #[inline]
    pub fn pop_stack(&mut self) -> Option<HeapCellValue> {
        while let Some(h) = self.stack.pop() {
            let is_readable_marked = h.is_marked();

            self.h = h;
            let cell = self.read_cell_mut(h);

            if cell.get_forwarding_bit() {
                cell.set_forwarding_bit(false);
            } else if cell.get_mark_bit() && !is_readable_marked {
                cell.set_mark_bit(false);
                continue;
            }

            return Some(*cell);
        }

        None
    }

    fn push_if_unmarked(&mut self, loc: IterStackLoc) {
        let cell = self.read_cell_mut(loc);

        if !cell.get_mark_bit() {
            cell.set_mark_bit(true);
            self.stack.push(IterStackLoc::iterable_loc(
                loc.value() as usize,
                loc.heap_or_stack(),
            ));
        }
    }
}

impl<'a, ElideLists: ListElisionPolicy> StackfulPreOrderHeapIter<'a, ElideLists> {
    #[inline]
    fn new(heap: &'a mut Heap, stack: &'a mut Stack, root_loc: usize) -> Self {
        let h = IterStackLoc::iterable_loc(root_loc, HeapOrStackTag::Heap);

        Self {
            heap,
            h,
            machine_stack: stack,
            stack: vec![h],
            _marker: PhantomData,
        }
    }

    #[inline]
    fn forward_if_referent_marked(&mut self, loc: IterStackLoc) {
        let cell = self.read_cell(loc);

        read_heap_cell!(cell,
            (HeapCellValueTag::Lis, vh) => {
                let forward = if ElideLists::elide_lists() { true } else { cell.get_mark_bit() };

                if forward && self.heap[vh].get_mark_bit() {
                    self.read_cell_mut(loc).set_forwarding_bit(true);
                }
            }
            (HeapCellValueTag::Str |
             HeapCellValueTag::AttrVar |
             HeapCellValueTag::Var, vh) => {
                if self.heap[vh].get_mark_bit() {
                    self.read_cell_mut(loc).set_forwarding_bit(true);
                }
            }
            (HeapCellValueTag::StackVar, vs) => {
                if self.machine_stack[vs].get_mark_bit() {
                    self.read_cell_mut(loc).set_forwarding_bit(true);
                }
            }
            _ => {}
        );
    }

    fn follow(&mut self) -> Option<HeapCellValue> {
        while let Some(h) = self.stack.pop() {
            if h.is_pending_mark() {
                self.push_if_unmarked(h);
                self.stack.push(IterStackLoc::marked_loc(
                    h.value() as usize,
                    h.heap_or_stack(),
                ));

                self.forward_if_referent_marked(h);
                continue;
            }

            self.h = h;

            let is_readable_marked = h.is_marked();
            let cell = self.read_cell_mut(h);

            if cell.get_forwarding_bit() {
                let copy = *cell;
                cell.set_forwarding_bit(false);
                return Some(copy);
            } else if cell.get_mark_bit() && !is_readable_marked {
                cell.set_mark_bit(false);
                continue;
            }

            read_heap_cell!(*cell,
               (HeapCellValueTag::Str, vh) => {
                   let loc = IterStackLoc::iterable_loc(vh, HeapOrStackTag::Heap);

                   self.push_if_unmarked(loc);
                   self.stack.push(IterStackLoc::marked_loc(vh, HeapOrStackTag::Heap));
               }
               (HeapCellValueTag::Lis, vh) => {
                   let loc = IterStackLoc::iterable_loc(vh, HeapOrStackTag::Heap);

                   self.forward_if_referent_marked(loc);

                   if self.read_cell(h).get_forwarding_bit() {
                       self.stack.push(h);
                       continue;
                   }

                   self.push_if_unmarked(loc);

                   self.stack.push(IterStackLoc::pending_marked_loc(vh + 1, HeapOrStackTag::Heap));
                   self.stack.push(IterStackLoc::marked_loc(vh, HeapOrStackTag::Heap));

                   return Some(self.read_cell(h));
               }
               (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, vh) => {
                   let loc = IterStackLoc::iterable_loc(vh, HeapOrStackTag::Heap);

                   self.forward_if_referent_marked(loc);
                   self.push_if_unmarked(loc);
                   self.stack.push(IterStackLoc::marked_loc(vh, HeapOrStackTag::Heap));
               }
               (HeapCellValueTag::StackVar, vs) => {
                   let loc = IterStackLoc::iterable_loc(vs, HeapOrStackTag::Stack);

                   self.forward_if_referent_marked(loc);
                   self.push_if_unmarked(loc);
                   self.stack.push(IterStackLoc::marked_loc(vs, HeapOrStackTag::Stack));
               }
               (HeapCellValueTag::PStrLoc, vh) => {
                   let cell = *cell;
                   let tail_idx = self.heap.scan_slice_to_str(vh).tail_idx;

                   if self.heap[tail_idx - 1].get_mark_bit() {
                       self.read_cell_mut(h).set_forwarding_bit(true);
                       self.stack.push(h);

                       continue;
                   } else {
                       self.heap[tail_idx - 1].set_mark_bit(true);
                   }

                   self.stack.push(IterStackLoc::iterable_loc(tail_idx - 1, HeapOrStackTag::Heap));
                   self.stack.push(IterStackLoc::pending_marked_loc(tail_idx, HeapOrStackTag::Heap));

                   return Some(cell);
               }
               (HeapCellValueTag::Atom, (_name, arity)) => {
                   let l = h.value() as usize;

                   for l in (l + 2 .. l + arity + 1).rev() {
                       self.stack.push(IterStackLoc::pending_marked_loc(l, HeapOrStackTag::Heap));
                   }

                   if arity > 0 {
                       let first_arg_loc = IterStackLoc::iterable_loc(l+1, HeapOrStackTag::Heap);

                       self.push_if_unmarked(first_arg_loc);
                       self.stack.push(IterStackLoc::marked_loc(l+1, HeapOrStackTag::Heap));
                       self.forward_if_referent_marked(first_arg_loc);
                   }

                   return Some(self.read_cell(h));
               }
               _ => {
                   return Some(*cell);
               }
            )
        }

        None
    }
}

impl<'a, ElideLists: ListElisionPolicy> Iterator for StackfulPreOrderHeapIter<'a, ElideLists> {
    type Item = HeapCellValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.follow()
    }
}

#[inline(always)]
pub(crate) fn cycle_detecting_stackless_preorder_iter(
    heap: &'_ mut Heap,
    start: usize,
) -> CycleDetectingIter<'_, true> {
    // const generics argument of true so that cycle discovery stops
    // the iterator.
    CycleDetectingIter::new(heap, start)
}

#[inline(always)]
pub(crate) fn stackful_preorder_iter<'a, ElideLists: ListElisionPolicy>(
    heap: &'a mut Heap,
    stack: &'a mut Stack,
    root_loc: usize,
) -> StackfulPreOrderHeapIter<'a, ElideLists> {
    StackfulPreOrderHeapIter::new(heap, stack, root_loc)
}

#[derive(Debug)]
pub(crate) struct PostOrderIterator<Iter: FocusedHeapIter> {
    focus: IterStackLoc,
    pub(crate) base_iter: Iter,
    base_iter_valid: bool,
    parent_stack: Vec<(usize, HeapCellValue, IterStackLoc)>, // number of children, parent node, focus.
}

impl<Iter: FocusedHeapIter> Deref for PostOrderIterator<Iter> {
    type Target = Iter;

    fn deref(&self) -> &Self::Target {
        &self.base_iter
    }
}

impl<Iter: FocusedHeapIter> PostOrderIterator<Iter> {
    pub(crate) fn new(base_iter: Iter) -> Self {
        PostOrderIterator {
            focus: IterStackLoc::iterable_loc(0, HeapOrStackTag::Heap),
            base_iter,
            base_iter_valid: true,
            parent_stack: vec![],
        }
    }
}

impl<Iter: FocusedHeapIter> Iterator for PostOrderIterator<Iter> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((child_count, node, focus)) = self.parent_stack.pop() {
                if child_count == 0 {
                    self.focus = focus;
                    return Some(node);
                }

                self.parent_stack.push((child_count - 1, node, focus));
            }

            if self.base_iter_valid {
                if let Some(item) = self.base_iter.next() {
                    let focus = self.base_iter.focus();

                    read_heap_cell!(item,
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            self.parent_stack.push((arity, item, focus));
                        }
                        (HeapCellValueTag::Lis) => {
                            self.parent_stack.push((2, item, focus));
                        }
                        (HeapCellValueTag::PStrLoc) => { // HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset) => {
                            self.parent_stack.push((1, item, focus));
                        }
                        _ => {
                            self.focus = focus;
                            return Some(item);
                        }
                    );

                    continue;
                } else {
                    self.base_iter_valid = false;
                }
            }

            if self.parent_stack.is_empty() {
                return None;
            }
        }
    }
}

impl<Iter: FocusedHeapIter> FocusedHeapIter for PostOrderIterator<Iter> {
    #[inline(always)]
    fn focus(&self) -> IterStackLoc {
        self.focus
    }
}

pub(crate) type LeftistPostOrderHeapIter<'a, ElideLists> =
    PostOrderIterator<StackfulPreOrderHeapIter<'a, ElideLists>>;

impl<ElideLists: ListElisionPolicy> LeftistPostOrderHeapIter<'_, ElideLists> {
    #[inline]
    pub fn pop_stack(&mut self) {
        if let Some((child_count, ..)) = self.parent_stack.last() {
            for _ in 0..*child_count {
                self.base_iter.pop_stack();
            }

            self.parent_stack.pop();
        }
    }

    #[inline]
    pub fn parent_stack_len(&self) -> usize {
        self.parent_stack.len()
    }
}

#[inline]
pub(crate) fn stackful_post_order_iter<'a, ElideLists: ListElisionPolicy>(
    heap: &'a mut Heap,
    stack: &'a mut Stack,
    root_loc: usize,
) -> LeftistPostOrderHeapIter<'a, ElideLists> {
    PostOrderIterator::new(StackfulPreOrderHeapIter::new(heap, stack, root_loc))
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::functor_macro::*;
    use crate::machine::gc::IteratorUMP;
    use crate::machine::mock_wam::*;

    pub(crate) type RightistPostOrderHeapIter<'a> =
        PostOrderIterator<StacklessPreOrderHeapIter<'a, IteratorUMP>>;

    #[inline(always)]
    pub(crate) fn stackless_preorder_iter(
        heap: &mut Heap,
        start: usize,
    ) -> StacklessPreOrderHeapIter<'_, IteratorUMP> {
        StacklessPreOrderHeapIter::<IteratorUMP>::new(heap, start)
    }

    #[inline]
    pub(crate) fn stackless_post_order_iter(
        heap: &'_ mut Heap,
        start: usize,
    ) -> RightistPostOrderHeapIter<'_> {
        PostOrderIterator::new(stackless_preorder_iter(heap, start))
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn heap_stackless_iter_tests() {
        let mut wam = MockWAM::new();

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [atom_as_cell(a_atom), atom_as_cell(b_atom)]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 3);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 2)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom, 0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom, 0)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(a_atom),
                str_loc_as_cell(0)
            ]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();

        wam.machine_st.heap.push_cell(cell).unwrap();

        for _ in 0..20 {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 5);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 4)
            );
            assert_eq!(unmark_cell_bits!(iter.next().unwrap()), str_loc_as_cell!(0));
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        {
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        // term  is: [a, b]
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(b_atom));
            section.push_cell(empty_list_as_cell!());
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        // now make the list cyclic.
        wam.machine_st.heap[4] = heap_loc_as_cell!(0);

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        // first a 'dangling' partial string, later modified to be a
        // two-part complete string, then a three-part cyclic string
        // involving an uncompacted list of chars.

        wam.machine_st.heap.allocate_pstr("abc ").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 2);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1),
            );
            assert!(iter.next().is_none());
        }

        wam.machine_st.heap[1] = pstr_loc_as_cell!(heap_index!(3));

        wam.machine_st.heap.allocate_pstr("def").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(4)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 5);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(4),
            );
            assert!(iter.next().is_none());
        }

        wam.machine_st.heap[4] = pstr_loc_as_cell!(heap_index!(3) + 2);

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 5);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3) + 2)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(empty_list_as_cell!());
        });

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(b_atom)
            ]
        ));

        functor_writer(&mut wam.machine_st.heap).unwrap();

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            // drop the iterator before the iteration is complete to test
            // that modified heap cells are restored to their
            // pre-traversal state by the stackless iterator's Drop
            // instance.
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], list_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], str_loc_as_cell!(5));
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], str_loc_as_cell!(5));
        assert_eq!(wam.machine_st.heap[4], empty_list_as_cell!());

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            // drop the iterator before the iteration is complete to test
            // that modified heap cells are restored to their
            // pre-traversal state by the stackless iterator's Drop
            // instance.
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], list_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], str_loc_as_cell!(5));
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], str_loc_as_cell!(5));
        assert_eq!(wam.machine_st.heap[4], empty_list_as_cell!());

        wam.machine_st.heap[4] = list_loc_as_cell!(1);

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1),
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(heap_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(0));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 4);

            assert_eq!(iter.next().unwrap(), heap_loc_as_cell!(3));
            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            heap_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            heap_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            heap_loc_as_cell!(3)
        );

        wam.machine_st.heap.clear();

        // print L = [L|L].
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(iter.next().unwrap(), list_loc_as_cell!(1));
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(1)
        );

        wam.machine_st.heap.clear();

        // term is [X,f(Y),Z].
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(3)); // 2
            section.push_cell(list_loc_as_cell!(4)); // 3
            section.push_cell(str_loc_as_cell!(6)); // 4
            section.push_cell(heap_loc_as_cell!(8));
            section.push_cell(atom_as_cell!(f_atom, 1)); // 6
            section.push_cell(heap_loc_as_cell!(11)); // 7
            section.push_cell(list_loc_as_cell!(9));
            section.push_cell(heap_loc_as_cell!(9));
            section.push_cell(empty_list_as_cell!());

            section.push_cell(attr_var_as_cell!(11)); // linked from 7.
            section.push_cell(heap_loc_as_cell!(12));
            section.push_cell(heap_loc_as_cell!(0));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 13);

            assert_eq!(iter.next().unwrap(), list_loc_as_cell!(1));

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(4)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(9)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(9)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                attr_var_as_cell!(11)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );
            assert_eq!(iter.next(), None);
        }

        // now populate the attributes list. the iteration must not change.
        let clpz_atom = atom!("clpz");
        let p_atom = atom!("p");

        wam.machine_st.heap.truncate(12);

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(13)); // 12
            section.push_cell(list_loc_as_cell!(14)); // 13
            section.push_cell(str_loc_as_cell!(16)); // 14
            section.push_cell(heap_loc_as_cell!(19)); // 15
            section.push_cell(atom_as_cell!(clpz_atom, 2)); // 16
            section.push_cell(atom_as_cell!(a_atom)); // 17
            section.push_cell(atom_as_cell!(b_atom)); // 18
            section.push_cell(list_loc_as_cell!(20)); // 19
            section.push_cell(str_loc_as_cell!(22)); // 20
            section.push_cell(empty_list_as_cell!()); // 21
            section.push_cell(atom_as_cell!(p_atom, 1)); // 22
            section.push_cell(heap_loc_as_cell!(23)); // 23
            section.push_cell(heap_loc_as_cell!(0));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 24);

            assert_eq!(iter.next().unwrap(), list_loc_as_cell!(1));

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(4)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(9)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(9)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                attr_var_as_cell!(11)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );
            assert_eq!(iter.next(), None);
        }

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            heap_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            list_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            str_loc_as_cell!(6)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            heap_loc_as_cell!(8)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(f_atom, 1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            heap_loc_as_cell!(11)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            list_loc_as_cell!(9)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[9]),
            heap_loc_as_cell!(9)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[10]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[11]),
            attr_var_as_cell!(11)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[12]),
            heap_loc_as_cell!(13)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[13]),
            list_loc_as_cell!(14)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[14]),
            str_loc_as_cell!(16)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[15]),
            heap_loc_as_cell!(19)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[16]),
            atom_as_cell!(clpz_atom, 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[17]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[18]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[19]),
            list_loc_as_cell!(20)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[20]),
            str_loc_as_cell!(22)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[21]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[22]),
            atom_as_cell!(p_atom, 1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[23]),
            heap_loc_as_cell!(23)
        );

        wam.machine_st.heap.clear();

        {
            wam.machine_st
                .heap
                .push_cell(fixnum_as_cell!(Fixnum::build_with(0)))
                .unwrap();

            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                fixnum_as_cell!(Fixnum::build_with(0))
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(str_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("g"), 2));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(atom_as_cell!(atom!("y")));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("g"), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("y"))
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert!(iter.next().is_none());
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("g"), 2));
            section.push_cell(str_loc_as_cell!(0));
            section.push_cell(atom_as_cell!(atom!("y")));
            section.push_cell(str_loc_as_cell!(0));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 3);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("g"), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("y"))
            );

            assert_eq!(unmark_cell_bits!(iter.next().unwrap()), str_loc_as_cell!(0));

            assert!(iter.next().is_none());
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(str_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("g"), 2));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(atom_as_cell!(atom!("y")));
            section.push_cell(atom_as_cell!(atom!("="), 2));
            section.push_cell(atom_as_cell!(atom!("X")));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(str_loc_as_cell!(4));
            section.push_cell(empty_list_as_cell!());
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 7);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(8)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("="), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("g"), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("y"))
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("X"))
            );

            assert!(iter.next().is_none());
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], str_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(atom!("g"), 2));
        assert_eq!(wam.machine_st.heap[2], heap_loc_as_cell!(0));
        assert_eq!(wam.machine_st.heap[3], atom_as_cell!(atom!("y")));
        assert_eq!(wam.machine_st.heap[4], atom_as_cell!(atom!("="), 2));
        assert_eq!(wam.machine_st.heap[5], atom_as_cell!(atom!("X")));
        assert_eq!(wam.machine_st.heap[6], heap_loc_as_cell!(0));
        assert_eq!(wam.machine_st.heap[7], list_loc_as_cell!(8));
        assert_eq!(wam.machine_st.heap[8], str_loc_as_cell!(4));
        assert_eq!(wam.machine_st.heap[9], empty_list_as_cell!());

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("f"), 2));
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(0));
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 3);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("f"), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );

            assert!(iter.next().is_none());
        }

        assert_eq!(wam.machine_st.heap[0], atom_as_cell!(atom!("f"), 2));
        assert_eq!(wam.machine_st.heap[1], heap_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[2], heap_loc_as_cell!(1));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        // representation of one of the heap terms as in issue #1384.
        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(7)); // 0
            section.push_cell(heap_loc_as_cell!(0)); // 1
            section.push_cell(list_loc_as_cell!(3)); // 2
            section.push_cell(list_loc_as_cell!(5)); // 3
            section.push_cell(empty_list_as_cell!()); // 4
            section.push_cell(heap_loc_as_cell!(2)); // 5
            section.push_cell(heap_loc_as_cell!(2)); // 6
            section.push_cell(empty_list_as_cell!()); // 7
            section.push_cell(heap_loc_as_cell!(3)); // 8
            section.push_cell(heap_loc_as_cell!(0)); // 9
        });

        {
            let mut iter = stackless_preorder_iter(&mut wam.machine_st.heap, 9);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(7)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(5)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn heap_stackful_iter_tests() {
        let mut wam = MockWAM::new();

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [atom_as_cell(a_atom), atom_as_cell(b_atom)]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                h,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 2)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(a_atom),
                str_loc_as_cell(0)
            ]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(cell).unwrap();

        for _ in 0..20 {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                h,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 4)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(unmark_cell_bits!(iter.next().unwrap()), str_loc_as_cell!(0));
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            let mut var = heap_loc_as_cell!(0);

            // self-referencing variables are copied with their forwarding
            // and marking bits set to true. it suffices to check only the
            // forwarding bit to detect cycles of all kinds, including
            // unbound/self-referencing variables.

            var.set_forwarding_bit(true);
            var.set_mark_bit(true);

            assert_eq!(iter.next().unwrap(), var);
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            // mutually referencing variables.
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        // term  is: [a, b]
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(b_atom));
            section.push_cell(empty_list_as_cell!());
        });

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(iter.next(), None);
        }

        // now make the list cyclic.
        wam.machine_st.heap[4] = heap_loc_as_cell!(0);

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                4,
            );

            // the cycle will be iterated twice before being detected.
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            // cut the iteration short to check that all cells are
            // unmarked and unforwarded by the Drop instance of
            // StackfulPreOrderHeapIter.

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], list_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], atom_as_cell!(b_atom));
        assert_eq!(wam.machine_st.heap[4], heap_loc_as_cell!(0));

        wam.machine_st.heap.clear();

        // first a 'dangling' partial string, later modified to be a
        // two-part complete string, then a three-part cyclic string
        // involving an uncompacted list of chars.

        wam.machine_st.heap.allocate_pstr("abc ").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                2,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );
            assert!(iter.next().is_none());
        }

        wam.machine_st.heap[1] = pstr_loc_as_cell!(heap_index!(3));
        wam.machine_st.heap.allocate_pstr("def").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(4)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackful_preorder_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                5,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(4),
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap[4] = pstr_loc_as_cell!(heap_index!(3) + 2);

        {
            let mut iter = stackful_preorder_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                5,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3) + 2)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let functor = functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(b_atom)
            ]
        );

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(empty_list_as_cell!());
        });

        let mut functor_writer = Heap::functor_writer(functor);
        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();

        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap[4] = list_loc_as_cell!(1);

        {
            let mut iter = stackful_preorder_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            let mut link_back = list_loc_as_cell!(1);

            link_back.set_forwarding_bit(true);
            link_back.set_mark_bit(true);

            assert_eq!(iter.next().unwrap(), link_back);

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
        });

        {
            let mut iter = StackfulPreOrderHeapIter::<NonListElider>::new(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            let mut cyclic_link = list_loc_as_cell!(1);

            cyclic_link.set_forwarding_bit(true);
            cyclic_link.set_mark_bit(true);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );
            assert_eq!(iter.next().unwrap(), cyclic_link);
            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_pstr("a string");
            section.push_cell(empty_list_as_cell!());
            section.push_cell(pstr_loc_as_cell!(0));
        });

        assert_eq!(wam.machine_st.heap.cell_len(), 4);

        {
            let mut iter = stackful_preorder_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                3,
            );

            assert_eq!(iter.heap.slice_to_str(0, "a string".len()), "a string");
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(iter.next(), None);
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "a string".len()),
            "a string"
        );
        assert_eq!(
            wam.machine_st.heap[1],
            HeapCellValue::build_with(HeapCellValueTag::Cons, 0)
        );

        for idx in 2..=3 {
            assert!(!wam.machine_st.heap[idx].get_mark_bit());
            assert!(!wam.machine_st.heap[idx].get_forwarding_bit());
        }

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(str_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("g"), 2));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(atom_as_cell!(atom!("y")));
            section.push_cell(atom_as_cell!(atom!("="), 2));
            section.push_cell(atom_as_cell!(atom!("X")));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(str_loc_as_cell!(4));
            section.push_cell(empty_list_as_cell!());
            section.push_cell(heap_loc_as_cell!(0));
        });

        {
            let mut iter = stackful_preorder_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                10,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("g"), 2)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(atom!("y"))
            );

            assert!(iter.next().is_none());
        }
    }

    #[test]
    fn heap_stackful_post_order_iter() {
        let mut wam = MockWAM::new();

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [atom_as_cell(a_atom), atom_as_cell(b_atom)]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                h,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 2)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(a_atom),
                str_loc_as_cell(0)
            ]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(cell).unwrap();

        for _ in 0..20 {
            // 0000 {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                h,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(unmark_cell_bits!(iter.next().unwrap()), str_loc_as_cell!(0));
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 4)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            let mut var = heap_loc_as_cell!(0);

            // self-referencing variables are copied with their forwarding
            // and marking bits set to true. it suffices to check only the
            // forwarding bit to detect cycles of all kinds, including
            // unbound/self-referencing variables.

            var.set_forwarding_bit(true);
            var.set_mark_bit(true);

            assert_eq!(iter.next().unwrap(), var);
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            // mutually referencing variables.
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                1,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        // term  is: [a, b]
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(b_atom));
            section.push_cell(empty_list_as_cell!());
        });

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        // now make the list cyclic.
        wam.machine_st.heap[4] = heap_loc_as_cell!(0);

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                4,
            );

            // the cycle will be iterated twice before being detected.
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            // cut the iteration short to check that all cells are
            // unmarked and unforwarded by the Drop instance of
            // StackfulPreOrderHeapIter.

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], list_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], atom_as_cell!(b_atom));
        assert_eq!(wam.machine_st.heap[4], heap_loc_as_cell!(0));

        wam.machine_st.heap.clear();

        // first a 'dangling' partial string, later modified to be a
        // two-part complete string, then a three-part cyclic string
        // involving an uncompacted list of chars.

        wam.machine_st.heap.allocate_pstr("abc ").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                2,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1),
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap[1] = pstr_loc_as_cell!(heap_index!(3));
        wam.machine_st.heap.allocate_pstr("def").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(4)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                5,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(4),
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap[4] = pstr_loc_as_cell!(heap_index!(3) + 2);

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                5,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3) + 2)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3))
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let functor = functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(b_atom)
            ]
        );

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(empty_list_as_cell!());
        });

        let mut functor_writer = Heap::functor_writer(functor);
        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();

        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap[4] = list_loc_as_cell!(1);

        {
            let mut iter = stackful_post_order_iter::<NonListElider>(
                &mut wam.machine_st.heap,
                &mut wam.machine_st.stack,
                0,
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            let mut link_back = list_loc_as_cell!(1);

            link_back.set_forwarding_bit(true);
            link_back.set_mark_bit(true);

            assert_eq!(iter.next().unwrap(), link_back);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);
        wam.machine_st.heap.clear();
    }

    #[test]
    fn heap_stackless_post_order_iter() {
        let mut wam = MockWAM::new();

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [atom_as_cell(a_atom), atom_as_cell(b_atom)]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        wam.machine_st.heap.push_cell(cell).unwrap();

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 3);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 2)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(a_atom),
                str_loc_as_cell(0)
            ]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        wam.machine_st.heap.push_cell(cell).unwrap();

        for _ in 0..20 {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 5);

            assert_eq!(unmark_cell_bits!(iter.next().unwrap()), str_loc_as_cell!(0));

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 4)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        {
            // mutually referencing variables.
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
            wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap.clear();

        // term  is: [a, b]
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(b_atom));
            section.push_cell(empty_list_as_cell!());
        });

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        // now make the list cyclic.
        wam.machine_st.heap[4] = heap_loc_as_cell!(0);

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            // the cycle will be iterated twice before being detected.
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            // cut the iteration short to check that all cells are
            // unmarked and unforwarded by the Drop instance of
            // StacklessPreOrderHeapIter.

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(0)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
        }

        all_cells_unmarked(&wam.machine_st.heap);

        assert_eq!(wam.machine_st.heap[0], list_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], atom_as_cell!(b_atom));
        assert_eq!(wam.machine_st.heap[4], heap_loc_as_cell!(0));

        wam.machine_st.heap.clear();
    }

    #[test]
    fn heap_stackless_post_order_iter_pstr() {
        let mut wam = MockWAM::new();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        // first a 'dangling' partial string, later modified to be a
        // two-part complete string, then a three-part cyclic string
        // involving an uncompacted list of chars.

        wam.machine_st.heap.allocate_pstr("abc ").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();
        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 2);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1),
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );

            assert_eq!(iter.next(), None);
        }

        wam.machine_st.heap[2] = heap_loc_as_cell!(2);
        assert_eq!(wam.machine_st.heap.cell_len(), 3);

        wam.machine_st.heap.allocate_pstr("def").unwrap();
        assert_eq!(wam.machine_st.heap.cell_len(), 4);

        wam.machine_st.heap.push_cell(pstr_loc_as_cell!(0)).unwrap();
        assert_eq!(wam.machine_st.heap.cell_len(), 5);

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 4);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                heap_loc_as_cell!(1),
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(0)
            );
            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap[4] = pstr_loc_as_cell!(heap_index!(3) + 2);

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 4);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                pstr_loc_as_cell!(heap_index!(3) + 2)
            );
            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        let functor = functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(b_atom)
            ]
        );

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(str_loc_as_cell!(5));
            section.push_cell(empty_list_as_cell!());
        });

        let mut functor_writer = Heap::functor_writer(functor);
        functor_writer(&mut wam.machine_st.heap).unwrap();

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                empty_list_as_cell!()
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);

        wam.machine_st.heap[4] = list_loc_as_cell!(1);

        {
            let mut iter = stackless_post_order_iter(&mut wam.machine_st.heap, 0);

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(b_atom)
            );
            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(a_atom)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                atom_as_cell!(f_atom, 3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(3)
            );

            assert_eq!(
                unmark_cell_bits!(iter.next().unwrap()),
                list_loc_as_cell!(1)
            );

            assert_eq!(iter.next(), None);
        }

        all_cells_unmarked(&wam.machine_st.heap);
    }
}
