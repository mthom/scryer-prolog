use crate::atom_table::*;
use crate::machine::get_structure_index;
use crate::machine::stack::*;
use crate::types::*;

use std::mem;
use std::ops::IndexMut;

type Trail = Vec<(Ref, HeapCellValue)>;

#[derive(Debug, Clone, Copy)]
pub enum AttrVarPolicy {
    DeepCopy,
    StripAttributes,
}

pub trait CopierTarget: IndexMut<usize, Output = HeapCellValue> {
    fn store(&self, value: HeapCellValue) -> HeapCellValue;
    fn deref(&self, value: HeapCellValue) -> HeapCellValue;
    fn push(&mut self, value: HeapCellValue);
    fn push_attr_var_queue(&mut self, attr_var_loc: usize);
    fn stack(&mut self) -> &mut Stack;
    fn threshold(&self) -> usize;
}

pub(crate) fn copy_term<T: CopierTarget>(
    target: T,
    addr: HeapCellValue,
    attr_var_policy: AttrVarPolicy,
) {
    let mut copy_term_state = CopyTermState::new(target, attr_var_policy);

    copy_term_state.copy_term_impl(addr);
    copy_term_state.copy_attr_var_lists();
    copy_term_state.unwind_trail();
}

#[derive(Debug)]
struct CopyTermState<T: CopierTarget> {
    trail: Trail,
    scan: usize,
    old_h: usize,
    target: T,
    attr_var_policy: AttrVarPolicy,
    attr_var_list_locs: Vec<(usize, HeapCellValue)>,
}

impl<T: CopierTarget> CopyTermState<T> {
    fn new(target: T, attr_var_policy: AttrVarPolicy) -> Self {
        CopyTermState {
            trail: Trail::new(),
            scan: 0,
            old_h: target.threshold(),
            target,
            attr_var_policy,
            attr_var_list_locs: vec![],
        }
    }

    #[inline]
    fn value_at_scan(&mut self) -> &mut HeapCellValue {
        &mut self.target[self.scan]
    }

    fn trail_list_cell(&mut self, addr: usize, threshold: usize) {
        let trail_item = mem::replace(&mut self.target[addr], list_loc_as_cell!(threshold));
        self.trail.push((Ref::heap_cell(addr), trail_item));
    }

    fn copy_list(&mut self, addr: usize) {
        for offset in 0..2 {
            read_heap_cell!(self.target[addr + offset],
                (HeapCellValueTag::Lis, h) => {
                    if h >= self.old_h {
                        *self.value_at_scan() = list_loc_as_cell!(h);
                        self.scan += 1;
                        return;
                    }
                }
                _ => {
                }
            )
        }

        let threshold = self.target.threshold();

        *self.value_at_scan() = list_loc_as_cell!(threshold);

        for i in 0..2 {
            let hcv = self.target[addr + i];
            self.target.push(hcv);
        }

        let cdr = self
            .target
            .store(self.target.deref(heap_loc_as_cell!(addr + 1)));

        if !cdr.is_var() {
            // mark addr + 1 as a list back edge in the cdr of the list
            self.trail_list_cell(addr + 1, threshold);
            self.target[addr + 1].set_mark_bit(true);
            self.target[addr + 1].set_forwarding_bit(true);
        } else {
            let car = self
                .target
                .store(self.target.deref(heap_loc_as_cell!(addr)));

            if !car.is_var() {
                // mark addr as a list back edge in the car of the list
                self.trail_list_cell(addr, threshold);
                self.target[addr].set_mark_bit(true);
            }
        }

        self.scan += 1;
    }

    fn copy_partial_string(&mut self, scan_tag: HeapCellValueTag, pstr_loc: usize) {
        read_heap_cell!(self.target[pstr_loc],
            (HeapCellValueTag::PStrLoc, h) => {
                debug_assert!(h >= self.old_h);

                *self.value_at_scan() = match scan_tag {
                    HeapCellValueTag::PStrLoc => {
                        pstr_loc_as_cell!(h)
                    }
                    tag => {
                        debug_assert_eq!(tag, HeapCellValueTag::PStrOffset);
                        pstr_offset_as_cell!(h)
                    }
                };

                self.scan += 1;
                return;
            }
            (HeapCellValueTag::Var, h) => {
                debug_assert!(h >= self.old_h);
                debug_assert_eq!(scan_tag, HeapCellValueTag::PStrOffset);

                *self.value_at_scan() = pstr_offset_as_cell!(h);
                self.scan += 1;

                return;
            }
            _ => {}
        );

        let threshold = self.target.threshold();

        let replacement = read_heap_cell!(self.target[pstr_loc],
            (HeapCellValueTag::CStr) => {
                debug_assert_eq!(scan_tag, HeapCellValueTag::PStrOffset);

                *self.value_at_scan() = pstr_offset_as_cell!(threshold);
                self.target.push(self.target[pstr_loc]);

                heap_loc_as_cell!(threshold)
            }
            _ => {
                *self.value_at_scan() = if scan_tag == HeapCellValueTag::PStrLoc {
                    pstr_loc_as_cell!(threshold)
                } else {
                    debug_assert_eq!(scan_tag, HeapCellValueTag::PStrOffset);
                    pstr_offset_as_cell!(threshold)
                };

                self.target.push(self.target[pstr_loc]);
                self.target.push(self.target[pstr_loc + 1]);

                pstr_loc_as_cell!(threshold)
            }
        );

        self.scan += 1;

        let trail_item = mem::replace(&mut self.target[pstr_loc], replacement);
        self.trail.push((Ref::heap_cell(pstr_loc), trail_item));
    }

    fn copy_attr_var_lists(&mut self) {
        while !self.attr_var_list_locs.is_empty() {
            let iter = std::mem::take(&mut self.attr_var_list_locs);

            for (threshold, list_loc) in iter {
                self.target[threshold] = list_loc_as_cell!(self.target.threshold());
                self.target.push_attr_var_queue(threshold - 1);
                self.copy_attr_var_list(list_loc);
            }
        }
    }

    /*
     * Attributed variable attribute lists adhere to a particular
     * structure which is ensured by this function and not at all by
     * the vanilla copier.
     */
    fn copy_attr_var_list(&mut self, mut list_addr: HeapCellValue) {
        while let HeapCellValueTag::Lis = list_addr.get_tag() {
            let threshold = self.target.threshold();
            let heap_loc = list_addr.get_value() as usize;
            let str_loc = self.target[heap_loc].get_value() as usize;

            self.target.push(heap_loc_as_cell!(threshold + 2));
            self.target.push(heap_loc_as_cell!(threshold + 1));

            read_heap_cell!(self.target[str_loc],
                (HeapCellValueTag::Atom) => {
                    self.target.push(self.target[str_loc]);
                }
                (HeapCellValueTag::Str) => {
                    self.copy_term_impl(self.target[str_loc]);
                }
                _ => {
                    unreachable!();
                }
            );

            list_addr = self.target[heap_loc + 1];

            if HeapCellValueTag::Lis == list_addr.get_tag() {
                self.target[threshold + 1] = list_loc_as_cell!(self.target.threshold());
            }
        }
    }

    fn reinstantiate_var(&mut self, addr: HeapCellValue, frontier: usize) {
        read_heap_cell!(addr,
            (HeapCellValueTag::Var, h) => {
                self.target[frontier] = heap_loc_as_cell!(frontier);
                self.target[h] = heap_loc_as_cell!(frontier);

                self.trail.push((Ref::heap_cell(h), heap_loc_as_cell!(h)));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.target[frontier] = heap_loc_as_cell!(frontier);
                self.target.stack()[s] = heap_loc_as_cell!(frontier);

                self.trail.push((Ref::stack_cell(s), stack_loc_as_cell!(s)));
            }
            (HeapCellValueTag::AttrVar, h) => {
                let threshold = if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    self.target.threshold()
                } else {
                    frontier
                };

                self.target[frontier] = heap_loc_as_cell!(threshold);
                self.target[h] = heap_loc_as_cell!(threshold);

                self.trail.push((Ref::attr_var(h), attr_var_as_cell!(h)));

                if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    self.target.push(attr_var_as_cell!(threshold));
                    self.target.push(heap_loc_as_cell!(threshold + 1));

                    let old_list_link = self.target[h + 1];
                    self.trail.push((Ref::heap_cell(h + 1), old_list_link));
                    self.target[h + 1] = heap_loc_as_cell!(threshold + 1);

                    if old_list_link.get_tag() == HeapCellValueTag::Lis {
                        self.attr_var_list_locs.push((threshold + 1, old_list_link));
                    }
                }
            }
            _ => {
                unreachable!()
            }
        );
    }

    fn copy_var(&mut self, addr: HeapCellValue) {
        let index = addr.get_value() as usize;
        let rd = self.target.deref(addr);
        let ra = self.target.store(rd);

        read_heap_cell!(ra,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                if h >= self.old_h {
                    *self.value_at_scan() = ra;
                    self.scan += 1;
                    return;
                }
            }
            (HeapCellValueTag::Lis, h) => {
                if h >= self.old_h && self.target[index].get_mark_bit() {
                    *self.value_at_scan() = heap_loc_as_cell!(
                        if ra.get_forwarding_bit() {
                            h + 1
                        } else {
                            h
                        }
                    );

                    self.scan += 1;
                    return;
                }
            }
            _ => {}
        );

        if rd == ra {
            self.reinstantiate_var(ra, self.scan);
            self.scan += 1;
        } else {
            *self.value_at_scan() = ra;
        }
    }

    fn copy_structure(&mut self, addr: usize) {
        read_heap_cell!(self.target[addr],
            (HeapCellValueTag::Atom, (name, arity)) => {
                let threshold = self.target.threshold();

                *self.value_at_scan() = str_loc_as_cell!(threshold);

                let trail_item = mem::replace(
                    &mut self.target[addr],
                    str_loc_as_cell!(threshold),
                );

                self.trail.push((Ref::heap_cell(addr), trail_item));
                self.target.push(atom_as_cell!(name, arity));

                for i in 0..arity {
                    let hcv = self.target[addr + 1 + i];
                    self.target.push(hcv);
                }

                let index_cell = self.target[addr + 1 + arity];

                if get_structure_index(index_cell).is_some() {
                    // copy the index pointer trailing this
                    // inlined or expanded goal.
                    self.target.push(index_cell);
                }
            }
            (HeapCellValueTag::Str, h) => {
                *self.value_at_scan() = str_loc_as_cell!(h);
            }
            _ => {
                unreachable!()
            }
        );

        self.scan += 1;
    }

    fn copy_term_impl(&mut self, addr: HeapCellValue) {
        self.scan = self.target.threshold();
        self.target.push(addr);

        while self.scan < self.target.threshold() {
            let addr = *self.value_at_scan();

            read_heap_cell!(addr,
                (HeapCellValueTag::Lis, h) => {
                    if h >= self.old_h {
                        self.scan += 1;
                    } else {
                        self.copy_list(h);
                    }
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var) => {
                    self.copy_var(addr);
                }
                (HeapCellValueTag::Str, h) => {
                    self.copy_structure(h);
                }
                (HeapCellValueTag::PStrLoc | HeapCellValueTag::PStrOffset, pstr_loc) => {
                    self.copy_partial_string(addr.get_tag(), pstr_loc);
                }
                _ => {
                    self.scan += 1;
                }
            );
        }
    }

    fn unwind_trail(mut self) {
        for (r, value) in self.trail {
            let index = r.get_value() as usize;

            match r.get_tag() {
                RefTag::AttrVar | RefTag::HeapCell => {
                    self.target[index] = value;
                    self.target[index].set_mark_bit(false);
                    self.target[index].set_forwarding_bit(false);
                }
                RefTag::StackCell => self.target.stack()[index] = value,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::mock_wam::*;

    #[test]
    fn copier_tests() {
        let mut wam = MockWAM::new();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        wam.machine_st
            .heap
            .extend(functor!(f_atom, [atom(a_atom), atom(b_atom)]));

        assert_eq!(wam.machine_st.heap[0], atom_as_cell!(f_atom, 2));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], atom_as_cell!(b_atom));

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, str_loc_as_cell!(0), AttrVarPolicy::DeepCopy);
        }

        // check that the original heap state is still intact.
        assert_eq!(wam.machine_st.heap[0], atom_as_cell!(f_atom, 2));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], atom_as_cell!(b_atom));

        assert_eq!(wam.machine_st.heap[3], str_loc_as_cell!(4));
        assert_eq!(wam.machine_st.heap[4], atom_as_cell!(f_atom, 2));
        assert_eq!(wam.machine_st.heap[5], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[6], atom_as_cell!(b_atom));

        wam.machine_st.heap.clear();

        let pstr_var_cell =
            put_partial_string(&mut wam.machine_st.heap, "abc ", &wam.machine_st.atom_tbl);
        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));

        let pstr_second_var_cell =
            put_partial_string(&mut wam.machine_st.heap, "def", &wam.machine_st.atom_tbl);
        let pstr_second_cell = wam.machine_st.heap[pstr_second_var_cell.get_value() as usize];

        wam.machine_st.heap.pop();
        wam.machine_st
            .heap
            .push(pstr_loc_as_cell!(wam.machine_st.heap.len() + 1));

        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st
            .heap
            .push(fixnum_as_cell!(Fixnum::build_with(0i64)));

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(0), AttrVarPolicy::DeepCopy);
        }

        print_heap_terms(wam.machine_st.heap[6..].iter(), 6);

        assert_eq!(wam.machine_st.heap[0], pstr_cell);
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(2));
        assert_eq!(wam.machine_st.heap[2], pstr_second_cell);
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(4));
        assert_eq!(wam.machine_st.heap[4], pstr_offset_as_cell!(0));
        assert_eq!(
            wam.machine_st.heap[5],
            fixnum_as_cell!(Fixnum::build_with(0i64))
        );

        assert_eq!(wam.machine_st.heap[7], pstr_cell);
        assert_eq!(wam.machine_st.heap[8], pstr_loc_as_cell!(9));
        assert_eq!(wam.machine_st.heap[9], pstr_second_cell);
        assert_eq!(wam.machine_st.heap[10], pstr_loc_as_cell!(11));
        assert_eq!(wam.machine_st.heap[11], pstr_offset_as_cell!(7));
        assert_eq!(
            wam.machine_st.heap[12],
            fixnum_as_cell!(Fixnum::build_with(0i64))
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

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, str_loc_as_cell!(0), AttrVarPolicy::DeepCopy);
        }

        assert_eq!(wam.machine_st.heap[0], atom_as_cell!(f_atom, 4));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], atom_as_cell!(b_atom));
        assert_eq!(wam.machine_st.heap[3], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[4], str_loc_as_cell!(0));

        assert_eq!(wam.machine_st.heap[5], str_loc_as_cell!(6));
        assert_eq!(wam.machine_st.heap[6], atom_as_cell!(f_atom, 4));
        assert_eq!(wam.machine_st.heap[7], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[8], atom_as_cell!(b_atom));
        assert_eq!(wam.machine_st.heap[9], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[10], str_loc_as_cell!(6));
    }
}
