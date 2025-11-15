#[cfg(test)]
use fxhash::FxBuildHasher;
#[cfg(test)]
use indexmap::IndexMap;
#[cfg(test)]
use std::collections::BTreeMap;

#[cfg(test)]
use crate::atom_table::*;
#[cfg(test)]
use crate::machine::heap::*;
#[cfg(test)]
use crate::types::*;

#[cfg(test)]
use crate::heap_iter::{FocusedHeapIter, HeapOrStackTag, IterStackLoc};

#[cfg(test)]
pub(crate) trait UnmarkPolicy {
    fn forward_attr_var(iter: &mut StacklessPreOrderHeapIter<Self>) -> Option<HeapCellValue>
    where
        Self: Sized;
    fn invert_marker(iter: &mut StacklessPreOrderHeapIter<Self>)
    where
        Self: Sized;
    fn mark_phase(&self) -> bool;
    #[inline]
    fn report_var_link(iter: &StacklessPreOrderHeapIter<Self>) -> bool
    where
        Self: Sized,
    {
        iter.heap[iter.next as usize].get_mark_bit() == iter.iter_state.mark_phase()
    }
    #[inline(always)]
    fn record_focus(_iter: &mut StacklessPreOrderHeapIter<Self>)
    where
        Self: Sized,
    {
    }
}

#[cfg(test)]
pub(crate) struct IteratorUMP {
    mark_phase: bool,
}

#[cfg(test)]
fn invert_marker<UMP: UnmarkPolicy>(iter: &mut StacklessPreOrderHeapIter<UMP>) {
    if iter.heap[iter.start].get_forwarding_bit() {
        while !iter.backward() {}
    }

    iter.heap[iter.start].set_forwarding_bit(true);

    iter.next = iter.heap[iter.start].get_value();
    iter.current = iter.start;

    while iter.forward().is_some() {}
}

#[cfg(test)]
impl UnmarkPolicy for IteratorUMP {
    #[inline(always)]
    fn forward_attr_var(iter: &mut StacklessPreOrderHeapIter<Self>) -> Option<HeapCellValue> {
        iter.forward_var()
    }

    #[inline]
    fn invert_marker(iter: &mut StacklessPreOrderHeapIter<Self>) {
        iter.iter_state.mark_phase = false;
        invert_marker(iter);
    }

    #[inline]
    fn mark_phase(&self) -> bool {
        self.mark_phase
    }
}

#[cfg(test)]
struct MarkerUMP {}

#[cfg(test)]
impl UnmarkPolicy for MarkerUMP {
    #[inline(always)]
    fn forward_attr_var(iter: &mut StacklessPreOrderHeapIter<Self>) -> Option<HeapCellValue> {
        if iter.heap[iter.current + 1].get_forwarding_bit() {
            return iter.forward_var();
        }

        let temp = iter.heap[iter.current].get_value();

        iter.heap[iter.current].set_value(iter.next);
        iter.current += 1;

        iter.next = iter.heap[iter.current].get_value();
        iter.heap[iter.current].set_value(temp);

        iter.heap[iter.current].set_forwarding_bit(true); // forward the attr vars list.
        None
    }

    fn invert_marker(_iter: &mut StacklessPreOrderHeapIter<Self>) {}

    #[inline(always)]
    fn mark_phase(&self) -> bool {
        true
    }
}

#[cfg(test)]
#[derive(Debug)]
struct PStrLocValuesMap {
    hit_set: BTreeMap<usize, usize>,
    pstr_loc_locs: IndexMap<usize, usize, FxBuildHasher>,
}

#[cfg(test)]
impl PStrLocValuesMap {
    #[inline]
    fn new() -> Self {
        Self {
            hit_set: BTreeMap::default(),
            pstr_loc_locs: IndexMap::with_hasher(FxBuildHasher::default()),
        }
    }

    fn progress_pstr_marking(&mut self, heap_slice: &[u8], pstr_loc: usize) -> usize {
        match self.hit_set.range(..=pstr_loc).next_back() {
            Some((_prev_pstr_loc, &tail_idx)) if pstr_loc < heap_index!(tail_idx) => {
                return tail_idx;
            }
            _ => {}
        }

        let delimiter = match self.hit_set.range(pstr_loc + 1..).next() {
            Some((&prev_pstr_loc, _)) => prev_pstr_loc,
            None => heap_slice.len(),
        };

        match heap_slice[pstr_loc..delimiter]
            .iter()
            .position(|b| *b == 0u8)
        {
            Some(zero_byte_offset) => {
                let tail_idx = if (zero_byte_offset + 1) % Heap::heap_cell_alignment() == 0 {
                    cell_index!(pstr_loc + zero_byte_offset) + 2
                } else {
                    cell_index!(pstr_loc + zero_byte_offset) + 1
                };
                self.hit_set.insert(pstr_loc, tail_idx);
                tail_idx
            }
            None => {
                let tail_idx = self.hit_set.remove(&delimiter).unwrap();
                self.hit_set.insert(pstr_loc, tail_idx);
                tail_idx //None
            }
        }
    }

    #[inline]
    fn pstr_loc_loc_value(&self, pstr_loc_loc: usize) -> Option<usize> {
        self.pstr_loc_locs.get(&pstr_loc_loc).cloned()
    }

    #[inline]
    fn insert_pstr_loc_value(&mut self, pstr_loc_loc: usize, pstr_loc: usize) {
        self.pstr_loc_locs.insert(pstr_loc_loc, pstr_loc);
    }
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) struct StacklessPreOrderHeapIter<'a, UMP: UnmarkPolicy> {
    pub(crate) heap: &'a mut Heap,
    start: usize,
    current: usize,
    next: u64,
    iter_state: UMP,
    pstr_loc_values: PStrLocValuesMap,
}

#[cfg(test)]
impl<'a> FocusedHeapIter for StacklessPreOrderHeapIter<'a, IteratorUMP> {
    #[inline]
    fn focus(&self) -> IterStackLoc {
        IterStackLoc::iterable_loc(self.current, HeapOrStackTag::Heap)
    }
}

#[cfg(test)]
impl<'a, UMP: UnmarkPolicy> Drop for StacklessPreOrderHeapIter<'a, UMP> {
    fn drop(&mut self) {
        UMP::invert_marker(self);

        if self.current == self.start {
            return;
        }

        while !self.backward() {}
    }
}

#[cfg(test)]
impl<'a> StacklessPreOrderHeapIter<'a, MarkerUMP> {
    pub(crate) fn new(heap: &'a mut Heap, start: usize) -> Self {
        heap[start].set_forwarding_bit(true);
        let next = heap[start].get_value();

        Self {
            heap,
            start,
            current: start,
            next,
            iter_state: MarkerUMP {},
            pstr_loc_values: PStrLocValuesMap::new(),
        }
    }
}

#[cfg(test)]
impl<'a> StacklessPreOrderHeapIter<'a, IteratorUMP> {
    #[cfg(test)]
    pub(crate) fn new(heap: &'a mut Heap, start: usize) -> Self {
        heap[start].set_forwarding_bit(true);
        let next = heap[start].get_value();

        Self {
            heap,
            start,
            current: start,
            next,
            iter_state: IteratorUMP { mark_phase: true },
            pstr_loc_values: PStrLocValuesMap::new(),
        }
    }
}

#[cfg(test)]
impl<'a, UMP: UnmarkPolicy> StacklessPreOrderHeapIter<'a, UMP> {
    fn backward_and_return(&mut self) -> HeapCellValue {
        let mut current = self.heap[self.current];
        current.set_value(self.next);

        if self.backward() {
            // set the f and m bits on the heap cell at start
            // so we invoke backward() and return None next call.

            self.heap[self.current].set_forwarding_bit(true);
            self.heap[self.current].set_mark_bit(self.iter_state.mark_phase());
        }

        current
    }

    fn forward_var(&mut self) -> Option<HeapCellValue> {
        if self.heap[self.next as usize].get_forwarding_bit() {
            return Some(self.backward_and_return());
        }

        let temp = self.heap[self.next as usize].get_value();

        self.heap[self.next as usize].set_value(self.current as u64);
        self.current = self.next as usize;
        self.next = temp;

        None
    }

    fn forward(&mut self) -> Option<HeapCellValue> {
        loop {
            if self.heap[self.current].get_mark_bit() != self.iter_state.mark_phase() {
                self.heap[self.current].set_mark_bit(self.iter_state.mark_phase());

                UMP::record_focus(self);

                match self.heap[self.current].get_tag() {
                    HeapCellValueTag::AttrVar => {
                        let next = self.next as usize;

                        if let Some(cell) = UMP::forward_attr_var(self) {
                            return Some(cell);
                        }

                        if self.next < self.heap.cell_len() as u64 && UMP::report_var_link(self) {
                            let tag = HeapCellValueTag::AttrVar;
                            return Some(HeapCellValue::build_with(tag, next as u64));
                        }
                    }
                    HeapCellValueTag::Var => {
                        let next = self.next as usize;

                        if let Some(cell) = self.forward_var() {
                            return Some(cell);
                        }

                        if self.next < self.heap.cell_len() as u64 && UMP::report_var_link(self) {
                            let tag = HeapCellValueTag::Var;
                            return Some(HeapCellValue::build_with(tag, next as u64));
                        }
                    }
                    HeapCellValueTag::Str => {
                        if self.heap[self.next as usize + 1].get_forwarding_bit() {
                            return Some(self.backward_and_return());
                        }

                        let h = self.next as usize;
                        let cell = self.heap[h];

                        let arity = cell_as_atom_cell!(self.heap[h]).get_arity();

                        for idx in h + 1..=h + arity {
                            self.heap[idx].set_forwarding_bit(true);
                        }

                        let last_cell_loc = h + arity;

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        return Some(cell);
                    }
                    HeapCellValueTag::Lis => {
                        let last_cell_loc = self.next as usize + 1;

                        if self.heap[last_cell_loc].get_forwarding_bit() {
                            return Some(self.backward_and_return());
                        }

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        self.heap[last_cell_loc].set_forwarding_bit(true);

                        return Some(list_loc_as_cell!(last_cell_loc - 1));
                    }
                    HeapCellValueTag::PStrLoc => {
                        let pstr_loc = self.next as usize;

                        let tail_idx = self
                            .pstr_loc_values
                            .progress_pstr_marking(self.heap.as_slice(), pstr_loc);

                        self.pstr_loc_values
                            .insert_pstr_loc_value(self.current, pstr_loc);

                        if self.heap[tail_idx].get_forwarding_bit() {
                            return Some(self.backward_and_return());
                        }

                        self.next = self.heap[tail_idx].get_value();
                        self.heap[tail_idx].set_value(self.current as u64);
                        self.current = tail_idx;

                        self.heap[tail_idx].set_forwarding_bit(true);

                        return Some(pstr_loc_as_cell!(pstr_loc));
                    }
                    tag @ HeapCellValueTag::Atom => {
                        let cell = HeapCellValue::build_with(tag, self.next);
                        let arity = AtomCell::from_bytes(cell.into_bytes()).get_arity();

                        if arity == 0 {
                            return Some(self.backward_and_return());
                        } else if self.backward() {
                            return None;
                        }
                    }
                    HeapCellValueTag::Cons => {
                        match self
                            .pstr_loc_values
                            .hit_set
                            .range(..heap_index!(self.current + 1))
                            .next_back()
                        {
                            Some((_prev_pstr_loc, &tail_idx)) if self.current + 1 == tail_idx => {
                                let pstr_loc_loc = self.heap[self.current].get_value() as usize;
                                let pstr_loc_val = self
                                    .pstr_loc_values
                                    .pstr_loc_loc_value(pstr_loc_loc)
                                    .unwrap();

                                self.heap[self.current].set_value(self.next);

                                self.next = pstr_loc_val as u64;
                                self.current = pstr_loc_loc;

                                if self.backward() {
                                    return None;
                                }
                            }
                            _ => {
                                return Some(self.backward_and_return());
                            }
                        }
                    }
                    _ => {
                        return Some(self.backward_and_return());
                    }
                }
            } else if self.backward() {
                return None;
            }
        }
    }

    fn backward(&mut self) -> bool {
        while !self.heap[self.current].get_forwarding_bit() {
            let temp = self.heap[self.current].get_value();

            self.heap[self.current].set_value(self.next);

            self.next = self.current as u64;
            self.current = temp as usize;
        }

        self.heap[self.current].set_forwarding_bit(false);

        if self.current == self.start {
            return true;
        }

        self.current -= 1;

        let temp = self.heap[self.current + 1].get_value();

        self.heap[self.current + 1].set_value(self.next);
        self.next = self.heap[self.current].get_value();
        self.heap[self.current].set_value(temp);

        false
    }
}

#[cfg(test)]
impl<'a, UMP: UnmarkPolicy> Iterator for StacklessPreOrderHeapIter<'a, UMP> {
    type Item = HeapCellValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.forward()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::functor_macro::*;
    use crate::machine::mock_wam::*;

    fn mark_cells(heap: &mut Heap, start: usize) {
        let mut iter = StacklessPreOrderHeapIter::<MarkerUMP>::new(heap, start);
        while iter.forward().is_some() {}
    }

    #[test]
    fn heap_marking_tests() {
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

        mark_cells(&mut wam.machine_st.heap, h);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            str_loc_as_cell!(0)
        );

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(f_atom, 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            atom_as_cell!(b_atom)
        );

        wam.machine_st.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [
                atom_as_cell(a_atom),
                atom_as_cell(b_atom),
                atom_as_cell(a_atom),
                str_loc_as_cell(1)
            ]
        ));

        let cell = functor_writer(&mut wam.machine_st.heap).unwrap();
        let h = wam.machine_st.heap.cell_len();

        wam.machine_st.heap.push_cell(cell).unwrap();

        mark_cells(&mut wam.machine_st.heap, h);
        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            str_loc_as_cell!(0)
        );

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(f_atom, 4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(a_atom)
        );

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        // make the structure doubly cyclic.
        wam.machine_st.heap[1] = str_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, h);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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

        mark_cells(&mut wam.machine_st.heap, h);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            str_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(f_atom, 4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            str_loc_as_cell!(0)
        );

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(0)).unwrap();

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            heap_loc_as_cell!(0)
        );

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            // term is: [a, b]
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(b_atom));
            section.push_cell(empty_list_as_cell!());
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            empty_list_as_cell!()
        );

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        // now make the list cyclic.
        wam.machine_st.heap[4] = heap_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            heap_loc_as_cell!(0)
        );

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        // make the list doubly cyclic.
        wam.machine_st.heap[3] = heap_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        wam.machine_st.heap.clear();

        // term is: [a, <stream ptr>]
        let stream = Stream::from_static_string("test", &mut wam.machine_st.arena);
        let stream_cell =
            HeapCellValue::from(ConsPtr::build_with(stream.as_ptr(), ConsPtrMaskTag::Cons));

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(a_atom));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(stream_cell);
            section.push_cell(empty_list_as_cell!());
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(3)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[3]), stream_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            empty_list_as_cell!()
        );

        wam.machine_st.heap.clear();

        // now a cycle of variables.

        let mut writer = wam.machine_st.heap.reserve(16).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(heap_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(0));
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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
            heap_loc_as_cell!(0)
        );

        wam.machine_st.heap.clear();

        // first a 'dangling' partial string, later modified to be a
        // two-part complete string, then a three-part cyclic string
        // involving an uncompacted list of chars.

        let pstr_cell = wam.machine_st.heap.allocate_pstr("abc ").unwrap();

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(1)).unwrap();

        let pstr_cell_loc = wam.machine_st.heap.cell_len();

        wam.machine_st
            .heap
            .push_cell(pstr_loc_as_cell!(heap_index!(0)))
            .unwrap();

        mark_cells(&mut wam.machine_st.heap, pstr_cell_loc);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 1);

        unmark_all_cells(&mut wam.machine_st.heap, 1);

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(0), "abc ".len()),
            "abc "
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[pstr_cell_loc]),
            pstr_cell
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(1)
        );

        wam.machine_st.heap[1] = pstr_loc_as_cell!(heap_index!(3));

        wam.machine_st.heap.allocate_pstr("abcdef ").unwrap();
        wam.machine_st.heap.push_cell(heap_loc_as_cell!(5)).unwrap();

        mark_cells(&mut wam.machine_st.heap, 2);

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(!wam.machine_st.heap[0].get_forwarding_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(!wam.machine_st.heap[1].get_forwarding_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[2].get_forwarding_bit());

        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(!wam.machine_st.heap[4].get_forwarding_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[5].get_forwarding_bit());

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(0), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(3), "abcdef ".len()),
            "abcdef "
        );
        assert_eq!(wam.machine_st.heap[5], heap_loc_as_cell!(5));

        // create a cycle offset two characters into the partial string at 0
        wam.machine_st.heap[5] = pstr_loc_as_cell!(heap_index!(0) + 2);

        mark_cells(&mut wam.machine_st.heap, 2);

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(!wam.machine_st.heap[0].get_forwarding_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(!wam.machine_st.heap[1].get_forwarding_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[2].get_forwarding_bit());

        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(!wam.machine_st.heap[4].get_forwarding_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[5].get_forwarding_bit());

        wam.machine_st.heap[0].set_mark_bit(false);
        wam.machine_st.heap[1].set_mark_bit(false);
        wam.machine_st.heap[2].set_mark_bit(false);
        wam.machine_st.heap[4].set_mark_bit(false);
        wam.machine_st.heap[5].set_mark_bit(false);

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(3), "abcdef ".len()),
            "abcdef "
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(0) + 2)
        );

        wam.machine_st.heap[5] = heap_loc_as_cell!(2);
        wam.machine_st.heap.push_cell(heap_loc_as_cell!(2)).unwrap();

        mark_cells(&mut wam.machine_st.heap, 6);

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(!wam.machine_st.heap[0].get_forwarding_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(!wam.machine_st.heap[1].get_forwarding_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[2].get_forwarding_bit());

        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(!wam.machine_st.heap[4].get_forwarding_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[5].get_forwarding_bit());
        assert!(wam.machine_st.heap[6].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_forwarding_bit());

        wam.machine_st.heap[0].set_mark_bit(false);
        wam.machine_st.heap[1].set_mark_bit(false);
        wam.machine_st.heap[2].set_mark_bit(false);
        wam.machine_st.heap[4].set_mark_bit(false);
        wam.machine_st.heap[5].set_mark_bit(false);
        wam.machine_st.heap[6].set_mark_bit(false);

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(3), "abcdef ".len()),
            "abcdef "
        );
        assert_eq!(wam.machine_st.heap[5], heap_loc_as_cell!(2));
        assert_eq!(wam.machine_st.heap[6], heap_loc_as_cell!(2));

        wam.machine_st.heap[5] = pstr_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, 2);

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());

        assert!(!wam.machine_st.heap[0].get_forwarding_bit());
        assert!(!wam.machine_st.heap[1].get_forwarding_bit());
        assert!(!wam.machine_st.heap[2].get_forwarding_bit());
        assert!(!wam.machine_st.heap[3].get_forwarding_bit());
        assert!(!wam.machine_st.heap[4].get_forwarding_bit());
        assert!(!wam.machine_st.heap[5].get_forwarding_bit());
        assert!(!wam.machine_st.heap[6].get_forwarding_bit());

        wam.machine_st.heap[0].set_mark_bit(false);
        wam.machine_st.heap[1].set_mark_bit(false);
        wam.machine_st.heap[2].set_mark_bit(false);
        wam.machine_st.heap[4].set_mark_bit(false);
        wam.machine_st.heap[5].set_mark_bit(false);

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(3), "abcdef ".len()),
            "abcdef "
        );
        assert_eq!(wam.machine_st.heap[5], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(wam.machine_st.heap[6], heap_loc_as_cell!(2));

        wam.machine_st.heap.truncate(5);

        let mut writer = wam.machine_st.heap.reserve(2).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("irrelevant stuff")));
            section.push_cell(pstr_loc_as_cell!(heap_index!(0) + 2)); // offset two chars into pstr at 0
        });

        wam.machine_st.heap.push_cell(heap_loc_as_cell!(6)).unwrap();

        mark_cells(&mut wam.machine_st.heap, 7);

        // indices 0 and 3 - 4 are the beginning of one-cell partial
        // strings, and they should be marked! despite the
        // HeapCellValue casts otherwise not being sensible.
        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(!wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(0)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(3), "abcdef ".len()),
            "abcdef "
        );
        assert_eq!(
            wam.machine_st.heap[5],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st.heap[6],
            pstr_loc_as_cell!(heap_index!(0) + 2)
        );
        assert_eq!(wam.machine_st.heap[7], heap_loc_as_cell!(6));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("irrelevant stuff")));
            section.push_pstr("abc ");
            section.push_cell(pstr_loc_as_cell!(heap_index!(4)));
            section.push_cell(atom_as_cell!(atom!("irrelevant stuff")));
            section.push_pstr("def");
            section.push_cell(pstr_loc_as_cell!(heap_index!(1) + 2));
            section.push_cell(atom_as_cell!(atom!("irrelevant stuff")));
            section.push_cell(pstr_loc_as_cell!(heap_index!(1) + 2));
        });

        mark_cells(&mut wam.machine_st.heap, 7);

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());

        assert!(!wam.machine_st.heap[0].get_forwarding_bit());
        assert!(!wam.machine_st.heap[1].get_forwarding_bit());
        assert!(!wam.machine_st.heap[2].get_forwarding_bit());
        assert!(!wam.machine_st.heap[3].get_forwarding_bit());
        assert!(!wam.machine_st.heap[4].get_forwarding_bit());
        assert!(!wam.machine_st.heap[5].get_forwarding_bit());
        assert!(!wam.machine_st.heap[6].get_forwarding_bit());

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(
            wam.machine_st.heap[0],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(1), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(4)));
        assert_eq!(
            wam.machine_st.heap[3],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(4), "def".len()),
            "def"
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(1) + 2)
        );
        assert_eq!(
            wam.machine_st.heap[6],
            atom_as_cell!(atom!("irrelevant stuff"))
        );

        wam.machine_st.heap[7] = heap_loc_as_cell!(2);

        mark_cells(&mut wam.machine_st.heap, 7);

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        for idx in 0..=6 {
            assert!(!wam.machine_st.heap[idx].get_forwarding_bit());
        }

        assert_eq!(
            wam.machine_st.heap[0],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(1), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(4)));
        assert_eq!(
            wam.machine_st.heap[3],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(4), "def".len()),
            "def"
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(1) + 2)
        );
        assert_eq!(
            wam.machine_st.heap[6],
            atom_as_cell!(atom!("irrelevant stuff"))
        );

        wam.machine_st.heap[7] = pstr_loc_as_cell!(heap_index!(4));

        mark_cells(&mut wam.machine_st.heap, 7);

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        for idx in 0..=6 {
            assert!(!wam.machine_st.heap[idx].get_forwarding_bit());
        }

        assert_eq!(
            wam.machine_st.heap[0],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(1), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[2], pstr_loc_as_cell!(heap_index!(4)));
        assert_eq!(
            wam.machine_st.heap[3],
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(4), "def".len()),
            "def"
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(1) + 2)
        );
        assert_eq!(
            wam.machine_st.heap[6],
            atom_as_cell!(atom!("irrelevant stuff"))
        );

        wam.machine_st.heap.clear();

        // embedded cyclic partial string

        let mut writer = wam.machine_st.heap.reserve(8).unwrap();

        writer.write_with(|section| {
            section.push_pstr("abc ");
            section.push_cell(pstr_loc_as_cell!(heap_index!(0) + 3)); // 3 character offset into pstr_cell
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(pstr_loc_as_cell!(0));
            section.push_cell(empty_list_as_cell!());
            section.push_cell(heap_loc_as_cell!(2));
        });

        mark_cells(&mut wam.machine_st.heap, 5);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(0), "abc ".len()),
            "abc "
        );
        assert_eq!(
            wam.machine_st.heap[1],
            pstr_loc_as_cell!(heap_index!(0) + 3)
        );
        assert_eq!(wam.machine_st.heap[2], list_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(0));
        assert_eq!(wam.machine_st.heap[4], empty_list_as_cell!());
        assert_eq!(wam.machine_st.heap[5], heap_loc_as_cell!(2));

        wam.machine_st.heap.clear();

        // a chain of variables, ending in a self-referential variable.

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(heap_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(3));
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        unmark_all_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(wam.machine_st.heap[0], heap_loc_as_cell!(1));
        assert_eq!(wam.machine_st.heap[1], heap_loc_as_cell!(2));
        assert_eq!(wam.machine_st.heap[2], heap_loc_as_cell!(3));
        assert_eq!(wam.machine_st.heap[3], heap_loc_as_cell!(3));

        wam.machine_st.heap.clear();

        // print L = [L|L].

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(list_loc_as_cell!(1));
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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
        // Z is an attributed variable, but has a variable attributes list.

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
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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
            heap_loc_as_cell!(12)
        );

        // now populate the attributes list.
        let clpz_atom = atom!("clpz");
        let p_atom = atom!("p");

        for idx in 0..wam.machine_st.heap.cell_len() {
            let cell = &mut wam.machine_st.heap[idx];
            cell.set_mark_bit(false);
            cell.set_forwarding_bit(false);
        }

        wam.machine_st.heap[12] = heap_loc_as_cell!(13);

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
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
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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

        for idx in 0..wam.machine_st.heap.cell_len() {
            let cell = &mut wam.machine_st.heap[idx];

            cell.set_mark_bit(false);
            cell.set_forwarding_bit(false);
        }

        // push some unrelated nonsense cells to the heap and check that they
        // are unmarked after the marker has finished at 0.
        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(5));
            section.push_cell(heap_loc_as_cell!(5));
            section.push_cell(list_loc_as_cell!(5));
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        for idx in 0..24 {
            assert!(wam.machine_st.heap[idx].get_mark_bit());
            assert!(!wam.machine_st.heap[idx].get_forwarding_bit());
        }

        for idx in 24..wam.machine_st.heap.cell_len() {
            assert!(!wam.machine_st.heap[idx].get_mark_bit());
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
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[24]),
            heap_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[25]),
            heap_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[26]),
            list_loc_as_cell!(5)
        );

        wam.machine_st.heap.clear();
        wam.machine_st
            .heap
            .push_cell(fixnum_as_cell!(Fixnum::build_with(0)))
            .unwrap();

        mark_cells(&mut wam.machine_st.heap, 0);

        assert_eq!(wam.machine_st.heap.cell_len(), 1);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

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

        mark_cells(&mut wam.machine_st.heap, 7);

        assert_eq!(wam.machine_st.heap.cell_len(), 10);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            str_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(atom!("g"), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            heap_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("y"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            atom_as_cell!(atom!("="), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            atom_as_cell!(atom!("X"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            heap_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            list_loc_as_cell!(8)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            str_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[9]),
            empty_list_as_cell!()
        );

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("f"), 2));
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(heap_loc_as_cell!(1));
            section.push_cell(str_loc_as_cell!(0));
        });

        mark_cells(&mut wam.machine_st.heap, 3);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("f"), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            heap_loc_as_cell!(1)
        );

        wam.machine_st.heap.clear();

        // representation of one of the heap terms as in issue #1384.

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(empty_list_as_cell!());
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(empty_list_as_cell!());
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(list_loc_as_cell!(5));
        });

        mark_cells(&mut wam.machine_st.heap, 7);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            heap_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            heap_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            heap_loc_as_cell!(2)
        );

        wam.machine_st.heap.clear();

        // representation of one of the heap terms as in issue #1384.

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(7));
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(list_loc_as_cell!(3)); // A = [B|[]].
            section.push_cell(list_loc_as_cell!(5)); // B = [A|A].
            section.push_cell(empty_list_as_cell!());
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(heap_loc_as_cell!(2));
            section.push_cell(empty_list_as_cell!()); // C = [[]|B].
            section.push_cell(heap_loc_as_cell!(3));
            section.push_cell(heap_loc_as_cell!(0));
        });

        mark_cells(&mut wam.machine_st.heap, 9);

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(!wam.machine_st.heap[1].get_mark_bit());

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 2);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            list_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            list_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            list_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            heap_loc_as_cell!(2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            heap_loc_as_cell!(2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            empty_list_as_cell!()
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            heap_loc_as_cell!(3)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[9]),
            heap_loc_as_cell!(0)
        );

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(str_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("+"), 2));
            section.push_cell(str_loc_as_cell!(4));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(2)));
            section.push_cell(atom_as_cell!(atom!("-"), 2));
            section.push_cell(str_loc_as_cell!(7));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(1)));
            section.push_cell(atom_as_cell!(atom!("+"), 2));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(3)));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(4)));
        });

        mark_cells(&mut wam.machine_st.heap, 0);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap, 0);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            str_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(atom!("+"), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            str_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            atom_as_cell!(atom!("-"), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            str_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            fixnum_as_cell!(Fixnum::build_with(1))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            atom_as_cell!(atom!("+"), 2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(3))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[9]),
            fixnum_as_cell!(Fixnum::build_with(4))
        );
    }
}
