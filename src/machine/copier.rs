use crate::atom_table::*;
use crate::machine::get_structure_index;
use crate::machine::heap::*;
use crate::machine::stack::*;
use crate::types::*;

use std::mem;
use std::ops::{IndexMut, Range};

type Trail = Vec<(Ref, HeapCellValue)>;

#[derive(Debug, Clone, Copy)]
pub enum AttrVarPolicy {
    DeepCopy,
    StripAttributes,
}

pub trait CopierTarget: IndexMut<usize, Output = HeapCellValue> {
    fn store(&self, value: HeapCellValue) -> HeapCellValue;
    fn deref(&self, value: HeapCellValue) -> HeapCellValue;
    // fn push_cell(&mut self, value: HeapCellValue) -> Result<(), usize>;
    fn push_attr_var_queue(&mut self, attr_var_loc: usize);
    fn stack(&mut self) -> &mut Stack;
    fn threshold(&self) -> usize;
    // returns the tail location of the pstr on success
    fn copy_pstr_to_threshold(&mut self, pstr_loc: usize) -> Result<usize, usize>;
    fn pstr_head_cell_index(&self, pstr_loc: usize) -> usize;
    fn pstr_at(&self, loc: usize) -> bool;
    fn next_non_pstr_cell_index(&self, loc: usize) -> usize;
    fn reserve(&mut self, num_cells: usize) -> Result<HeapWriter, usize>;
    fn copy_slice_to_end(&mut self, bounds: Range<usize>) -> Result<(), usize>;
}

pub(crate) fn copy_term<T: CopierTarget>(
    target: T,
    addr: HeapCellValue,
    attr_var_policy: AttrVarPolicy,
) -> Result<(), usize> {
    let mut copy_term_state = CopyTermState::new(target, attr_var_policy);

    copy_term_state.copy_term_impl(addr)?;
    copy_term_state.copy_attr_var_lists()?;
    copy_term_state.unwind_trail();

    Ok(())
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

    fn copy_list(&mut self, addr: usize) -> Result<(), usize> {
        for offset in 0..2 {
            read_heap_cell!(self.target[addr + offset],
                (HeapCellValueTag::Lis, h) => {
                    if h >= self.old_h {
                        *self.value_at_scan() = list_loc_as_cell!(h);
                        self.scan += 1;
                        return Ok(());
                    }
                }
                _ => {
                }
            )
        }

        let threshold = self.target.threshold();
        self.target.copy_slice_to_end(addr .. addr + 2)?;

        *self.value_at_scan() = list_loc_as_cell!(threshold);

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
        Ok(())
    }

    /*
     * write a null byte to the first word of a partial string to
     * flag that it has been copied followed by the copied
     * string's index in the next 7 bytes. write the bytes in big
     * endian order so that the null byte is at index 0.
     */
    fn write_pstr_index(&mut self, head_cell_idx: usize, threshold: usize) {
        let bytes = u64::to_be_bytes(threshold as u64);
        debug_assert_eq!(bytes[0], 0);
        self.target[head_cell_idx] = HeapCellValue::from_bytes(bytes);
    }

    fn copy_partial_string(&mut self, pstr_loc: usize) -> Result<(), usize> {
        let head_cell_idx = self.target.pstr_head_cell_index(pstr_loc);
        let head_byte_idx = heap_index!(head_cell_idx);
        let pstr_offset = pstr_loc - head_byte_idx;

        // if a partial string has been copied previously, we
        // track it by writing a null byte to its first word, which is trailed,
        // and then the new pstr_loc in the word's remaining 7 bytes. see write_pstr_index
        // comment.

        if self.target[head_cell_idx].into_bytes()[0] == 0u8 {
            let head_bytes = self.target[head_cell_idx].into_bytes();
            let new_pstr_loc = u64::from_be_bytes(head_bytes) as usize;

            *self.value_at_scan() = pstr_loc_as_cell!(heap_index!(new_pstr_loc) + pstr_offset);
            self.scan += 1;
            return Ok(());
        }

        let threshold = self.target.threshold();
        let tail_loc = self.target.copy_pstr_to_threshold(head_byte_idx)?;

        *self.value_at_scan() = pstr_loc_as_cell!(heap_index!(threshold) + pstr_offset);

        self.trail.push((Ref::heap_cell(head_cell_idx), self.target[head_cell_idx]));
        self.write_pstr_index(head_cell_idx, threshold);

        let tail_cell = self.target[tail_loc];
        let mut writer = self.target.reserve(1)?;

        writer.write_with(|section| {
            section.push_cell(tail_cell);
        });

        self.scan += 1;

        Ok(())
    }

    fn copy_attr_var_lists(&mut self) -> Result<(), usize> {
        while !self.attr_var_list_locs.is_empty() {
            let mut list_loc_vec = std::mem::take(&mut self.attr_var_list_locs);

            while let Some((threshold, list_loc)) = list_loc_vec.pop() {
                self.target[threshold] = list_loc_as_cell!(self.target.threshold());
                self.target.push_attr_var_queue(threshold - 1);
                self.copy_attr_var_list(list_loc)?;
            }
        }

        Ok(())
    }

    /*
     * Attributed variable attribute lists adhere to a particular
     * structure which is ensured by this function and not at all by
     * the vanilla copier.
     */
    fn copy_attr_var_list(&mut self, mut list_addr: HeapCellValue) -> Result<(), usize> {
        while let HeapCellValueTag::Lis = list_addr.get_tag() {
            let threshold = self.target.threshold();
            let heap_loc = list_addr.get_value() as usize;
            let str_loc = self.target[heap_loc].get_value() as usize;
            let str_cell = self.target[str_loc];
            let mut writer = self.target.reserve(3).unwrap();

            writer.write_with(|section| {
                section.push_cell(heap_loc_as_cell!(threshold + 2));
                section.push_cell(heap_loc_as_cell!(threshold + 1));

                if str_cell.to_atom().is_some() {
                    section.push_cell(str_cell);
                }
            });

            debug_assert_eq!(str_cell.get_tag(), HeapCellValueTag::Str);
            self.copy_term_impl(str_cell)?;
            list_addr = self.target[heap_loc + 1];

            if HeapCellValueTag::Lis == list_addr.get_tag() {
                self.target[threshold + 1] = list_loc_as_cell!(self.target.threshold());
            }
        }

        Ok(())
    }

    fn reinstantiate_var(&mut self, addr: HeapCellValue, frontier: usize) -> Result<(), usize> {
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
                    let mut writer = self.target.reserve(2).unwrap();

                    writer.write_with(|section| {
                        section.push_cell(attr_var_as_cell!(threshold));
                        section.push_cell(heap_loc_as_cell!(threshold + 1));
                    });

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

        Ok(())
    }

    fn copy_var(&mut self, addr: HeapCellValue) -> Result<(), usize> {
        let index = addr.get_value() as usize;
        let rd = self.target.deref(addr);
        let ra = self.target.store(rd);

        read_heap_cell!(ra,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                if h >= self.old_h {
                    *self.value_at_scan() = ra;
                    self.scan += 1;
                    return Ok(());
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
                    return Ok(());
                }
            }
            _ => {}
        );

        if rd == ra {
            self.reinstantiate_var(ra, self.scan)?;
            self.scan += 1;
        } else {
            *self.value_at_scan() = ra;
        }

        Ok(())
    }

    fn copy_structure(&mut self, addr: usize) -> Result<(), usize> {
        read_heap_cell!(self.target[addr],
            (HeapCellValueTag::Atom, (_name, arity)) => {
                let threshold = self.target.threshold();

                *self.value_at_scan() = str_loc_as_cell!(threshold);

                self.target.copy_slice_to_end(addr .. addr + 1 + arity)?;

                let trail_item = mem::replace(
                    &mut self.target[addr],
                    str_loc_as_cell!(threshold),
                );

                self.trail.push((Ref::heap_cell(addr), trail_item));
/*
                self.target.push(atom_as_cell!(name, arity));

                for i in 0..arity {
                    let hcv = self.target[addr + 1 + i];
                    self.target.push(hcv);
                }
*/
                if !self.target.pstr_at(addr + 1 + arity) {
                    let index_cell = self.target[addr + 1 + arity];

                    if get_structure_index(index_cell).is_some() {
                        // copy the index pointer trailing this
                        // inlined or expanded goal.
                        let mut writer = self.target.reserve(1).unwrap();

                        writer.write_with(|section| {
                            section.push_cell(index_cell);
                        });
                    }
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
        Ok(())
    }

    fn copy_term_impl(&mut self, addr: HeapCellValue) -> Result<(), usize> {
        self.scan = self.target.threshold();
        let mut writer = self.target.reserve(1)?;

        writer.write_with(|section| {
            section.push_cell(addr);
        });

        while self.scan < self.target.threshold() {
            if self.target.pstr_at(self.scan) {
                self.scan = self.target.next_non_pstr_cell_index(self.scan);
                continue;
            }

            let addr = *self.value_at_scan();

            read_heap_cell!(addr,
                (HeapCellValueTag::Lis, h) => {
                    if h >= self.old_h {
                        self.scan += 1;
                        continue;
                    } else {
                        self.copy_list(h)
                    }
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var) => {
                    self.copy_var(addr)
                }
                (HeapCellValueTag::Str, h) => {
                    self.copy_structure(h)
                }
                (HeapCellValueTag::PStrLoc, pstr_loc) => {
                    self.copy_partial_string(pstr_loc)
                }
                _ => {
                    self.scan += 1;
                    continue;
                }
            )?;
        }

        Ok(())
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
    use crate::functor_macro::*;
    use crate::machine::mock_wam::*;

    #[test]
    fn copier_tests() {
        let mut wam = MockWAM::new();

        // clear the heap of resource error data etc
        wam.machine_st.heap.clear();

        let f_atom = atom!("f");
        let a_atom = atom!("a");
        let b_atom = atom!("b");

        let mut functor_writer = Heap::functor_writer(
            functor!(f_atom, [atom_as_cell(a_atom), atom_as_cell(b_atom)]),
        );

        functor_writer(&mut wam.machine_st.heap).unwrap();

        assert_eq!(wam.machine_st.heap[0], atom_as_cell!(f_atom, 2));
        assert_eq!(wam.machine_st.heap[1], atom_as_cell!(a_atom));
        assert_eq!(wam.machine_st.heap[2], atom_as_cell!(b_atom));

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, str_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
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

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("abc ");
            section.push_cell(pstr_loc_as_cell!(heap_index!(2)));

            section.push_pstr("def");
            section.push_cell(pstr_loc_as_cell!(0));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(2)));
        assert_eq!(
            wam.machine_st.heap.slice_to_str(heap_index!(2), "def".len()),
            "def"
        );
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(0));

        assert_eq!(wam.machine_st.heap[4], pstr_loc_as_cell!(heap_index!(5)));

        assert_eq!(
            wam.machine_st.heap.slice_to_str(heap_index!(5), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[6], pstr_loc_as_cell!(heap_index!(7)));
        assert_eq!(
            wam.machine_st.heap.slice_to_str(heap_index!(7), "def".len()),
            "def"
        );
        assert_eq!(wam.machine_st.heap[8], pstr_loc_as_cell!(heap_index!(5)));

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

        functor_writer(&mut wam.machine_st.heap).unwrap();

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, str_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
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
