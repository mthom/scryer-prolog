use crate::atom_table::*;
use crate::types::*;

/* Use the pointer reversal technique of the Deutsch-Schorr-Waite
 * algorithm to detect cycles in Prolog terms.
 *
 * Much of the structure and nomenclature of the GC marking algorithm
 * is adapted here but there are a few significant changes:
 *
 * - Forwarded cells now form a trail of bread crumbs leading back to self.start
 * - Cells are only marked during the backward phase
 * - Visiting subterms of a visited compound does not immediately shift to the backward phase
 * - The heads of LIS structures are both marked and forwarded rather
 *   than just forwarded to distinguish them from tails;
 *   continue_forwarding() checks for this before entering the forward
 *   phase
 *
 * Commonalities with the GC marking algorithm:
 * - The contents of forwarded cells are modified only when they are unforwarded
 * - Marked (but unforwarded!) cells immediately shift to the backward phase
 */

#[derive(Debug)]
pub(crate) struct CycleDetectingIter<'a, const STOP_AT_CYCLES: bool> {
    pub(crate) heap: &'a mut [HeapCellValue],
    start: usize,
    current: usize,
    next: u64,
    cycle_found: bool,
    mark_phase: bool,
}

impl<'a, const STOP_AT_CYCLES: bool> CycleDetectingIter<'a, STOP_AT_CYCLES> {
    pub(crate) fn new(heap: &'a mut [HeapCellValue], start: usize) -> Self {
        heap[start].set_forwarding_bit(true);
        let next = heap[start].get_value();

        Self {
            heap,
            start,
            current: start,
            next,
            cycle_found: false,
            mark_phase: true,
        }
    }

    #[inline]
    pub(crate) fn cycle_found(&self) -> bool {
        self.cycle_found
    }

    #[inline]
    fn cycle_detection_active(&self) -> bool {
        STOP_AT_CYCLES && self.mark_phase && !self.cycle_found
    }

    fn backward_and_return(&mut self) -> HeapCellValue {
        let mut current = self.heap[self.current];
        current.set_value(self.next);

        if self.backward() {
            // set the f and m bits on the heap cell at start
            // so we invoke backward() and return None next call.

            self.heap[self.current].set_forwarding_bit(false);
            self.heap[self.current].set_mark_bit(self.mark_phase);
        }

        current
    }

    fn traverse_subterm(&mut self, h: usize, arity: usize) -> Option<usize> {
        let mut last_cell_loc = h + arity - 1;

        for idx in (h .. h + arity).rev() {
            if self.heap[idx].get_forwarding_bit() {
                if self.cycle_detection_active() {
                    self.cycle_found = true;
                    return None;
                }

                last_cell_loc -= 1;
            } else if self.heap[idx].get_mark_bit() == self.mark_phase {
                last_cell_loc -= 1;
            } else {
                break;
            }
        }

        Some(last_cell_loc)
    }

    #[inline]
    fn continue_forwarding(&self) -> bool {
        self.heap[self.current].get_mark_bit() != self.mark_phase ||
            self.heap[self.current].get_forwarding_bit()
    }

    fn forward(&mut self) -> Option<HeapCellValue> {
        loop {
            if self.continue_forwarding() {
                match self.heap[self.current].get_tag() {
                    tag @ HeapCellValueTag::AttrVar | tag @ HeapCellValueTag::Var => {
                        let next = self.next as usize;

                        if self.heap[next].get_forwarding_bit() {
                            return if self.current != next {
                                if self.cycle_detection_active() {
                                    self.cycle_found = true;
                                    None
                                } else {
                                    Some(self.backward_and_return())
                                }
                            } else {
                                Some(self.backward_and_return())
                            };
                        } else if self.heap[next].get_mark_bit() == self.mark_phase {
                            return Some(self.backward_and_return());
                        }

                        self.heap[next].set_forwarding_bit(true);

                        let temp = self.heap[next].get_value();

                        self.heap[next].set_value(self.current as u64);
                        self.current = next;
                        self.next = temp;

                        if self.next < self.heap.len() as u64 {
                            return Some(HeapCellValue::build_with(tag, next as u64));
                        }
                    }
                    HeapCellValueTag::Str => {
                        let h = self.next as usize;
                        let cell = self.heap[h];
                        let arity = cell_as_atom_cell!(self.heap[h]).get_arity();

                        let last_cell_loc = match self.traverse_subterm(h + 1, arity) {
                            Some(last_cell_loc) => last_cell_loc,
                            None => return None,
                        };

                        if last_cell_loc == h {
                            if self.backward() {
                                return None;
                            }

                            continue;
                        }

                        if self.cycle_detection_active() {
                            for idx in (h + 1 .. last_cell_loc).rev() {
                                if self.heap[idx].get_forwarding_bit() {
                                    self.cycle_found = true;
                                    return None;
                                }
                            }
                        }

                        self.heap[last_cell_loc].set_forwarding_bit(true);

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        return Some(cell);
                    }
                    HeapCellValueTag::Lis => {
                        let mut cell = self.heap[self.current];
                        cell.set_value(self.next);

                        let last_cell_loc = match self.traverse_subterm(self.next as usize, 2) {
                            Some(last_cell_loc) => last_cell_loc,
                            None => return None,
                        };

                        if self.cycle_detection_active() {
                            for idx in (self.next as usize .. last_cell_loc).rev() {
                                if self.heap[idx].get_forwarding_bit() {
                                    self.cycle_found = true;
                                    return None;
                                }
                            }
                        }

                        if (last_cell_loc + 1) as u64 == self.next {
                            if self.backward() {
                                return None;
                            }

                            continue;
                        } else if last_cell_loc as u64 == self.next {
                            // car cells of lists are both marked and forwarded.
                            self.heap[last_cell_loc].set_mark_bit(self.mark_phase);
                        }

                        self.heap[last_cell_loc].set_forwarding_bit(true);

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        return Some(cell);
                    }
                    HeapCellValueTag::PStrLoc => {
                        let h = self.next as usize;
                        let cell = self.heap[h];
                        let last_cell_loc = h + 1;

                        if self.heap[last_cell_loc].get_forwarding_bit() {
                            if self.cycle_detection_active() {
                                self.cycle_found = true;
                                return None;
                            } else if self.backward() {
                                return None;
                            }

                            continue;
                        }

                        self.heap[last_cell_loc].set_forwarding_bit(true);

                        self.next = self.heap[last_cell_loc].get_value();
                        self.heap[last_cell_loc].set_value(self.current as u64);
                        self.current = last_cell_loc;

                        return Some(cell);
                    }
                    HeapCellValueTag::PStrOffset => {
                        let h = self.next as usize;
                        let cell = self.heap[h];
                        let last_cell_loc = h + 1;

                        if self.heap[h].get_tag() == HeapCellValueTag::PStr {
                            if self.heap[last_cell_loc].get_forwarding_bit() {
                                if self.cycle_detection_active() {
                                    self.cycle_found = true;
                                    return None;
                                } else if self.backward() {
                                    return None;
                                }

                                continue;
                            }

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
                            return Some(self.backward_and_return());
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
                        return Some(self.backward_and_return());
                    }
                }
            } else if self.backward() {
                return None;
            }
        }
    }

    fn pivot_subterm(&mut self) {
        self.current -= 1;

        let temp = self.heap[self.current + 1].get_value();

        self.heap[self.current + 1].set_value(self.next);
        self.next = self.heap[self.current].get_value();
        self.heap[self.current].set_value(temp);

        self.heap[self.current].set_forwarding_bit(true);
    }

    fn continue_backward(&mut self) -> bool {
        self.heap[self.current].set_forwarding_bit(false);

        if self.current == self.start {
            return false;
        }

        let temp = self.heap[self.current].get_value();

        match self.heap[temp as usize].get_tag() {
            HeapCellValueTag::Str => {
                let mut new_str_back_link = self.current;

                for idx in (0 .. self.current).rev() {
                    if self.heap[idx].get_tag() == HeapCellValueTag::Atom {
                        if cell_as_atom_cell!(self.heap[idx]).get_arity() > 0 {
                            new_str_back_link = idx;
                            break;
                        }
                    }

                    if self.heap[idx].get_mark_bit() != self.mark_phase {
                        if !self.heap[idx].get_forwarding_bit() {
                            new_str_back_link = idx;
                            break;
                        }
                    }
                }

                self.heap[self.current].set_mark_bit(self.mark_phase);
                self.heap[self.current].set_value(self.next);

                let back_link_cell = self.heap[new_str_back_link];

                self.next = back_link_cell.get_value();
                self.heap[new_str_back_link].set_value(temp);
                self.current = new_str_back_link;

                read_heap_cell!(back_link_cell,
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity > 0 {
                            self.heap[self.current].set_mark_bit(self.mark_phase);
                            return true;
                        }
                    }
                    _ => {}
                );

                self.heap[self.current].set_forwarding_bit(true);
                false
            }
            HeapCellValueTag::Lis => {
                if self.heap[self.current].get_mark_bit() == self.mark_phase {
                    true
                } else {
                    self.heap[self.current - 1].set_mark_bit(self.mark_phase);
                    self.heap[self.current].set_mark_bit(self.mark_phase);

                    if self.heap[self.current - 1].get_forwarding_bit() {
                        self.heap[self.current].set_value(self.next);
                        self.next = self.current as u64 - 1;
                        self.current = temp as usize;

                        true
                    } else {
                        self.pivot_subterm();
                        false
                    }
                }
            }
            _ => {
                self.heap[self.current].set_mark_bit(self.mark_phase);
                true
            }
        }
    }

    fn backward(&mut self) -> bool {
        while self.continue_backward() {
            let temp = self.heap[self.current].get_value();

            self.heap[self.current].set_value(self.next);
            self.next = self.current as u64;
            self.current = temp as usize;
        }

        if self.current == self.start {
            return true;
        }

        false
    }

    fn invert_marker(&mut self) {
        self.cycle_found = false;

        if self.heap[self.start].get_forwarding_bit() {
            while !self.backward() {}
        }

        self.mark_phase = false;
        self.heap[self.start].set_forwarding_bit(true);

        self.next = self.heap[self.start].get_value();
        self.current = self.start;

        while let Some(_) = self.forward() {}
    }
}

impl<'a, const STOP_AT_CYCLES: bool> Iterator for CycleDetectingIter<'a, STOP_AT_CYCLES> {
    type Item = HeapCellValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.forward()
    }
}


impl<'a, const STOP_AT_CYCLES: bool> Drop for CycleDetectingIter<'a, STOP_AT_CYCLES> {
    fn drop(&mut self) {
        self.invert_marker();

        if self.current == self.start {
            return;
        }

        while !self.backward() {}
    }
}
