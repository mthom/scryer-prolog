use crate::atom_table::*;
use crate::machine::heap::*;
use crate::types::*;

#[cfg(test)]
use crate::heap_iter::{FocusedHeapIter, HeapOrStackTag, IterStackLoc};

use core::marker::PhantomData;

pub(crate) trait UnmarkPolicy {
    fn unmark(heap: &mut [HeapCellValue], current: usize);
    fn mark(heap: &mut [HeapCellValue], current: usize);
    fn forward_attr_var(iter: &mut StacklessPreOrderHeapIter<Self>) -> Option<HeapCellValue>
    where
        Self: Sized;
}

pub(crate) struct IteratorUMP;

impl UnmarkPolicy for IteratorUMP {
    #[inline(always)]
    fn unmark(heap: &mut [HeapCellValue], current: usize) {
        heap[current].set_mark_bit(false);
    }

    #[inline(always)]
    fn mark(_heap: &mut [HeapCellValue], _current: usize) {}

    #[inline(always)]
    fn forward_attr_var(iter: &mut StacklessPreOrderHeapIter<Self>) -> Option<HeapCellValue> {
        iter.forward_var()
    }
}

struct MarkerUMP {}

impl UnmarkPolicy for MarkerUMP {
    #[inline(always)]
    fn unmark(_heap: &mut [HeapCellValue], _current: usize) {}

    #[inline(always)]
    fn mark(heap: &mut [HeapCellValue], current: usize) {
        heap[current].set_mark_bit(true);
    }

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
}

#[derive(Debug)]
pub(crate) struct StacklessPreOrderHeapIter<'a, UMP: UnmarkPolicy> {
    pub(crate) heap: &'a mut Vec<HeapCellValue>,
    orig_heap_len: usize,
    start: usize,
    current: usize,
    next: u64,
    _marker: PhantomData<UMP>,
}

#[cfg(test)]
impl<'a> FocusedHeapIter for StacklessPreOrderHeapIter<'a, IteratorUMP> {
    #[inline]
    fn focus(&self) -> IterStackLoc {
        IterStackLoc::iterable_loc(self.current, HeapOrStackTag::Heap)
    }
}

impl<'a, UMP: UnmarkPolicy> Drop for StacklessPreOrderHeapIter<'a, UMP> {
    fn drop(&mut self) {
        if self.current == self.start {
            self.heap.truncate(self.orig_heap_len);
            return;
        }

        while !self.backward() {}

        self.heap.truncate(self.orig_heap_len);
    }
}

impl<'a> StacklessPreOrderHeapIter<'a, MarkerUMP> {
    pub(crate) fn new(heap: &'a mut Vec<HeapCellValue>, cell: HeapCellValue) -> Self {
        let orig_heap_len = heap.len();
        let start = orig_heap_len;

        heap.push(cell);

        heap[start].set_forwarding_bit(true);
        let next = heap[start].get_value();

        Self {
            heap,
            orig_heap_len,
            start,
            current: start,
            next,
            _marker: PhantomData,
        }
    }
}

impl<'a> StacklessPreOrderHeapIter<'a, IteratorUMP> {
    #[cfg(test)]
    pub(crate) fn new(heap: &'a mut Vec<HeapCellValue>, cell: HeapCellValue) -> Self {
        let orig_heap_len = heap.len();
        let start = orig_heap_len + 1;

        heap.push(cell);
        heap.push(heap_loc_as_cell!(orig_heap_len));

        heap[start].set_forwarding_bit(true);
        let next = heap[start].get_value();

        Self {
            heap,
            orig_heap_len,
            start,
            current: start,
            next,
            _marker: PhantomData,
        }
    }
}

impl<'a, UMP: UnmarkPolicy> StacklessPreOrderHeapIter<'a, UMP> {
    fn backward_and_return(&mut self) -> Option<HeapCellValue> {
        let current = self.current;

        if self.backward() {
            // set the f and m bits on the heap cell at start
            // so we invoke backward() and return None next call.

            self.heap[self.current].set_forwarding_bit(true);
            self.heap[self.current].set_mark_bit(true);
        }

        Some(self.heap[current])
    }

    fn forward_var(&mut self) -> Option<HeapCellValue> {
        if self.heap[self.next as usize].get_forwarding_bit() {
            return self.backward_and_return();
        }

        let temp = self.heap[self.next as usize].get_value();

        self.heap[self.next as usize].set_value(self.current as u64);
        self.current = self.next as usize;
        self.next = temp;

        None
    }

    fn forward(&mut self) -> Option<HeapCellValue> {
        loop {
            if !self.heap[self.current].get_mark_bit() {
                self.heap[self.current].set_mark_bit(true);

                match self.heap[self.current].get_tag() {
                    HeapCellValueTag::AttrVar => {
                        if let Some(cell) = UMP::forward_attr_var(self) {
                            return Some(cell);
                        }

                        if self.heap[self.next as usize].get_mark_bit() {
                            return Some(attr_var_as_cell!(self.current));
                        }
                    }
                    HeapCellValueTag::Var => {
                        if let Some(cell) = self.forward_var() {
                            return Some(cell);
                        }

                        if self.heap[self.next as usize].get_mark_bit() {
                            return Some(heap_loc_as_cell!(self.current));
                        }
                    }
                    HeapCellValueTag::Str => {
                        if self.heap[self.next as usize + 1].get_forwarding_bit() {
                            return self.backward_and_return();
                        }

                        let h = self.next as usize;
                        let cell = self.heap[h];

                        let arity = cell_as_atom_cell!(self.heap[h]).get_arity();

                        for cell in &mut self.heap[h + 1..h + arity + 1] {
                            cell.set_forwarding_bit(true);
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
                            return self.backward_and_return();
                        }

                        self.heap[last_cell_loc].set_forwarding_bit(true);

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        return Some(list_loc_as_cell!(last_cell_loc - 1));
                    }
                    HeapCellValueTag::PStrLoc => {
                        let h = self.next as usize;
                        let cell = self.heap[h];

                        if self.heap[h + 1].get_forwarding_bit() {
                            return self.backward_and_return();
                        }

                        if self.heap[h].get_tag() == HeapCellValueTag::PStr {
                            let last_cell_loc = h + 1;
                            self.heap[last_cell_loc].set_forwarding_bit(true);

                            self.next = self.heap[last_cell_loc].get_value();
                            self.heap[last_cell_loc].set_value(self.current as u64);
                            self.current = last_cell_loc;
                        } else {
                            debug_assert!(self.heap[h].get_tag() == HeapCellValueTag::PStrOffset);

                            self.next = self.heap[h].get_value();
                            self.heap[h].set_value(self.current as u64);
                            self.current = h;

                            if self.heap[h].get_mark_bit() {
                                continue;
                            }
                        }

                        return Some(cell);
                    }
                    HeapCellValueTag::PStrOffset => {
                        let h = self.next as usize;
                        let cell = self.heap[h];

                        // mark the Fixnum offset.
                        UMP::mark(self.heap, self.current + 1);

                        let last_cell_loc = h + 1;

                        if self.heap[last_cell_loc].get_forwarding_bit() {
                            return self.backward_and_return();
                        }

                        if self.heap[h].get_tag() == HeapCellValueTag::PStr {
                            self.heap[last_cell_loc].set_forwarding_bit(true);

                            self.next = self.heap[last_cell_loc].get_value();
                            self.heap[last_cell_loc].set_value(self.current as u64);
                            self.current = last_cell_loc;
                        } else {
                            debug_assert!(self.heap[h].get_tag() == HeapCellValueTag::CStr);

                            self.next = self.heap[h].get_value();
                            self.heap[h].set_value(self.current as u64);
                            self.current = h;
                        }

                        return Some(cell);
                    }
                    tag @ HeapCellValueTag::Atom => {
                        let cell = HeapCellValue::build_with(tag, self.next);
                        let arity = AtomCell::from_bytes(cell.into_bytes()).get_arity();

                        if arity == 0 {
                            return self.backward_and_return();
                        } else if self.backward() {
                            return None;
                        }
                    }
                    HeapCellValueTag::PStr => {
                        if self.backward() {
                            return None;
                        }
                    }
                    _ => {
                        return self.backward_and_return();
                    }
                }
            } else {
                if self.backward() {
                    return None;
                }
            }
        }
    }

    fn backward(&mut self) -> bool {
        while !self.heap[self.current].get_forwarding_bit() {
            let temp = self.heap[self.current].get_value();

            UMP::unmark(self.heap, self.current);

            self.heap[self.current].set_value(self.next);
            self.next = self.current as u64;
            self.current = temp as usize;
        }

        self.heap[self.current].set_forwarding_bit(false);
        UMP::unmark(self.heap, self.current);

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

impl<'a, UMP: UnmarkPolicy> Iterator for StacklessPreOrderHeapIter<'a, UMP> {
    type Item = HeapCellValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.forward()
    }
}

pub fn mark_cells(heap: &mut Heap, cell: HeapCellValue) {
    let mut iter = StacklessPreOrderHeapIter::<MarkerUMP>::new(heap, cell);
    while let Some(_) = iter.forward() {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::mock_wam::*;

    #[test]
    fn heap_marking_tests() {
        let mut wam = MockWAM::new();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        wam.machine_st
            .heap
            .extend(functor!(f_atom, [atom(a_atom), atom(b_atom)]));

        mark_cells(&mut wam.machine_st.heap, str_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.extend(functor!(
            f_atom,
            [
                atom(a_atom),
                atom(b_atom),
                atom(a_atom),
                cell(str_loc_as_cell!(0))
            ]
        ));

        mark_cells(&mut wam.machine_st.heap, str_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        // make the structure doubly cyclic.
        wam.machine_st.heap[2] = str_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, str_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(str_loc_as_cell!(1));

        wam.machine_st.heap.extend(functor!(
            f_atom,
            [
                atom(a_atom),
                atom(b_atom),
                atom(a_atom),
                cell(str_loc_as_cell!(1))
            ]
        ));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            str_loc_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            atom_as_cell!(f_atom, 4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(b_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            atom_as_cell!(a_atom)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            str_loc_as_cell!(1)
        );

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(heap_loc_as_cell!(0));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            heap_loc_as_cell!(0)
        );

        wam.machine_st.heap.clear();

        // term is: [a, b]
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(atom_as_cell!(a_atom));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(atom_as_cell!(b_atom));
        wam.machine_st.heap.push(empty_list_as_cell!());

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.pop();

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        // now make the list cyclic.
        wam.machine_st.heap.push(heap_loc_as_cell!(0));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        // make the list doubly cyclic.
        wam.machine_st.heap[3] = heap_loc_as_cell!(0);

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        // term is: [a, <stream ptr>]
        let stream = Stream::from_static_string("test", &mut wam.machine_st.arena);
        let stream_cell =
            HeapCellValue::from(ConsPtr::build_with(stream.as_ptr(), ConsPtrMaskTag::Cons));

        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(atom_as_cell!(a_atom));
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(stream_cell);
        wam.machine_st.heap.push(empty_list_as_cell!());

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        let pstr_var_cell = put_partial_string(
            &mut wam.machine_st.heap,
            "abc ",
            &mut wam.machine_st.atom_tbl.blocking_write(),
        );
        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            heap_loc_as_cell!(1)
        );

        wam.machine_st.heap.pop();

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        wam.machine_st.heap.push(pstr_loc_as_cell!(2));

        let pstr_second_var_cell = put_partial_string(
            &mut wam.machine_st.heap,
            "def",
            &mut wam.machine_st.atom_tbl.blocking_write(),
        );
        let pstr_second_cell = wam.machine_st.heap[pstr_second_var_cell.get_value() as usize];

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            heap_loc_as_cell!(3)
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(pstr_loc_as_cell!(4));
        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(2)));

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(4));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(3));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(2));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(1));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        wam.machine_st.heap.truncate(4);

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        wam.machine_st
            .heap
            .push(atom_as_cell!(atom!("irrelevant stuff")));
        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(2)));

        wam.machine_st.heap[3] = pstr_loc_as_cell!(5);

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(5));

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(wam.machine_st.heap[3].get_mark_bit());
        assert!(!wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(wam.machine_st.heap[6].get_mark_bit());

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[2]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            pstr_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        wam.machine_st.heap.clear();

        wam.machine_st
            .heap
            .push(atom_as_cell!(atom!("irrelevant stuff")));
        wam.machine_st.heap.push(pstr_cell);
        wam.machine_st.heap.push(pstr_loc_as_cell!(4));
        wam.machine_st
            .heap
            .push(atom_as_cell!(atom!("irrelevant stuff")));
        wam.machine_st.heap.push(pstr_second_cell);
        wam.machine_st.heap.push(pstr_loc_as_cell!(7));
        wam.machine_st
            .heap
            .push(atom_as_cell!(atom!("irrelevant stuff")));
        wam.machine_st.heap.push(pstr_offset_as_cell!(1));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(2)));

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(7));

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());
        assert!(wam.machine_st.heap[8].get_mark_bit());

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[1]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[4]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            pstr_offset_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(5));

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());
        assert!(wam.machine_st.heap[8].get_mark_bit());

        for cell in &wam.machine_st.heap {
            assert!(!cell.get_forwarding_bit());
        }

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[1]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[4]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            pstr_offset_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(4));

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());
        assert!(wam.machine_st.heap[8].get_mark_bit());

        for cell in &wam.machine_st.heap {
            assert!(!cell.get_forwarding_bit());
        }

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[1]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[4]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            pstr_offset_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(2));

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());
        assert!(wam.machine_st.heap[8].get_mark_bit());

        for cell in &wam.machine_st.heap {
            assert!(!cell.get_forwarding_bit());
        }

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[1]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[4]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            pstr_offset_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        mark_cells(&mut wam.machine_st.heap, pstr_loc_as_cell!(1));

        assert!(!wam.machine_st.heap[0].get_mark_bit());
        assert!(wam.machine_st.heap[1].get_mark_bit());
        assert!(wam.machine_st.heap[2].get_mark_bit());
        assert!(!wam.machine_st.heap[3].get_mark_bit());
        assert!(wam.machine_st.heap[4].get_mark_bit());
        assert!(wam.machine_st.heap[5].get_mark_bit());
        assert!(!wam.machine_st.heap[6].get_mark_bit());
        assert!(wam.machine_st.heap[7].get_mark_bit());
        assert!(wam.machine_st.heap[8].get_mark_bit());

        for cell in &wam.machine_st.heap {
            assert!(!cell.get_forwarding_bit());
        }

        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[0]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[1]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_loc_as_cell!(4)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[4]), pstr_second_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(7)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            atom_as_cell!(atom!("irrelevant stuff"))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[7]),
            pstr_offset_as_cell!(1)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[8]),
            fixnum_as_cell!(Fixnum::build_with(2))
        );

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        wam.machine_st.heap.clear();

        // embedded cyclic partial string.

        wam.machine_st.heap.push(pstr_cell);
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));
        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(3)));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(pstr_loc_as_cell!(0));
        wam.machine_st.heap.push(empty_list_as_cell!());

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(4));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            fixnum_as_cell!(Fixnum::build_with(3))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            list_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            empty_list_as_cell!()
        );

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(pstr_cell);
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));
        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(3)));
        wam.machine_st.heap.push(list_loc_as_cell!(5));
        wam.machine_st.heap.push(pstr_loc_as_cell!(0));
        wam.machine_st.heap.push(heap_loc_as_cell!(4));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(4));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
        }

        assert_eq!(unmark_cell_bits!(wam.machine_st.heap[0]), pstr_cell);
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[1]),
            pstr_loc_as_cell!(2)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[2]),
            pstr_offset_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[3]),
            fixnum_as_cell!(Fixnum::build_with(3))
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[4]),
            list_loc_as_cell!(5)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[5]),
            pstr_loc_as_cell!(0)
        );
        assert_eq!(
            unmark_cell_bits!(wam.machine_st.heap[6]),
            heap_loc_as_cell!(4)
        );

        wam.machine_st.heap.clear();

        // a chain of variables, ending in a self-referential variable.

        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(3));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(list_loc_as_cell!(1));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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
        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(heap_loc_as_cell!(3)); // 2
        wam.machine_st.heap.push(list_loc_as_cell!(4)); // 3
        wam.machine_st.heap.push(str_loc_as_cell!(6)); // 4
        wam.machine_st.heap.push(heap_loc_as_cell!(8));
        wam.machine_st.heap.push(atom_as_cell!(f_atom, 1)); // 6
        wam.machine_st.heap.push(heap_loc_as_cell!(11)); // 7
        wam.machine_st.heap.push(list_loc_as_cell!(9));
        wam.machine_st.heap.push(heap_loc_as_cell!(9));
        wam.machine_st.heap.push(empty_list_as_cell!());
        wam.machine_st.heap.push(attr_var_as_cell!(11)); // linked from 7.
        wam.machine_st.heap.push(heap_loc_as_cell!(12));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
            cell.set_forwarding_bit(false);
        }

        wam.machine_st.heap.pop();

        wam.machine_st.heap.push(heap_loc_as_cell!(13)); // 12
        wam.machine_st.heap.push(list_loc_as_cell!(14)); // 13
        wam.machine_st.heap.push(str_loc_as_cell!(16)); // 14
        wam.machine_st.heap.push(heap_loc_as_cell!(19)); // 15
        wam.machine_st.heap.push(atom_as_cell!(clpz_atom, 2)); // 16
        wam.machine_st.heap.push(atom_as_cell!(a_atom)); // 17
        wam.machine_st.heap.push(atom_as_cell!(b_atom)); // 18
        wam.machine_st.heap.push(list_loc_as_cell!(20)); // 19
        wam.machine_st.heap.push(str_loc_as_cell!(22)); // 20
        wam.machine_st.heap.push(empty_list_as_cell!()); // 21
        wam.machine_st.heap.push(atom_as_cell!(p_atom, 1)); // 22
        wam.machine_st.heap.push(heap_loc_as_cell!(23)); // 23

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        for cell in &mut wam.machine_st.heap {
            cell.set_mark_bit(false);
            cell.set_forwarding_bit(false);
        }

        // push some unrelated nonsense cells to the heap and check that they
        // are unmarked after the marker has finished at 0.
        wam.machine_st.heap.push(heap_loc_as_cell!(5));
        wam.machine_st.heap.push(heap_loc_as_cell!(5));
        wam.machine_st.heap.push(list_loc_as_cell!(5));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&mut wam.machine_st.heap[0..24]);

        for cell in &wam.machine_st.heap[24..] {
            assert_eq!(cell.get_mark_bit(), false);
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
            .push(fixnum_as_cell!(Fixnum::build_with(0)));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        assert_eq!(wam.machine_st.heap.len(), 1);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(str_loc_as_cell!(1));
        wam.machine_st.heap.push(atom_as_cell!(atom!("g"), 2));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));
        wam.machine_st.heap.push(atom_as_cell!(atom!("y")));
        wam.machine_st.heap.push(atom_as_cell!(atom!("="), 2));
        wam.machine_st.heap.push(atom_as_cell!(atom!("X")));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));
        wam.machine_st.heap.push(list_loc_as_cell!(8));
        wam.machine_st.heap.push(str_loc_as_cell!(4));
        wam.machine_st.heap.push(empty_list_as_cell!());

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(7));

        assert_eq!(wam.machine_st.heap.len(), 10);

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.push(atom_as_cell!(atom!("f"), 2));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));
        wam.machine_st.heap.push(heap_loc_as_cell!(1));

        mark_cells(&mut wam.machine_st.heap, str_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.push(list_loc_as_cell!(1));
        wam.machine_st.heap.push(empty_list_as_cell!());
        wam.machine_st.heap.push(list_loc_as_cell!(3));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));
        wam.machine_st.heap.push(empty_list_as_cell!());
        wam.machine_st.heap.push(heap_loc_as_cell!(2));

        mark_cells(&mut wam.machine_st.heap, list_loc_as_cell!(5));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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

        wam.machine_st.heap.push(list_loc_as_cell!(7));
        wam.machine_st.heap.push(heap_loc_as_cell!(0));
        wam.machine_st.heap.push(list_loc_as_cell!(3)); // A = [B|[]].
        wam.machine_st.heap.push(list_loc_as_cell!(5)); // B = [A|A].
        wam.machine_st.heap.push(empty_list_as_cell!());
        wam.machine_st.heap.push(heap_loc_as_cell!(2));
        wam.machine_st.heap.push(heap_loc_as_cell!(2));
        wam.machine_st.heap.push(empty_list_as_cell!()); // C = [[]|B].
        wam.machine_st.heap.push(heap_loc_as_cell!(3));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        assert!(wam.machine_st.heap[0].get_mark_bit());
        assert!(!wam.machine_st.heap[1].get_mark_bit());

        all_cells_marked_and_unforwarded(&wam.machine_st.heap[2..]);

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

        wam.machine_st.heap.clear();

        wam.machine_st.heap.push(str_loc_as_cell!(1));
        wam.machine_st.heap.push(atom_as_cell!(atom!("+"), 2));
        wam.machine_st.heap.push(str_loc_as_cell!(4));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(2)));
        wam.machine_st.heap.push(atom_as_cell!(atom!("-"), 2));
        wam.machine_st.heap.push(str_loc_as_cell!(7));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(1)));
        wam.machine_st.heap.push(atom_as_cell!(atom!("+"), 2));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(3)));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(4)));

        mark_cells(&mut wam.machine_st.heap, heap_loc_as_cell!(0));

        all_cells_marked_and_unforwarded(&wam.machine_st.heap);

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
