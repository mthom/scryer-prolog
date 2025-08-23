use fxhash::FxBuildHasher;
use indexmap::IndexSet;

use crate::atom_table::*;
use crate::machine::get_structure_index;
use crate::machine::heap::*;
use crate::machine::stack::*;
use crate::types::*;

use scryer_modular_bitfield::specifiers::*;
use scryer_modular_bitfield::*;

use std::collections::BTreeMap;
use std::mem;
use std::ops::{IndexMut, Range};

#[derive(BitfieldSpecifier, Copy, Clone, Debug)]
#[bits = 6]
enum TrailRefTag {
    HeapCell = 0b001011,
    StackCell = 0b001101,
    AttrVar = 0b010001,
    PStrLoc = 0b001111,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
struct TrailRef {
    val: B56,
    #[allow(unused)]
    m: bool,
    #[allow(unused)]
    f: bool,
    tag: TrailRefTag,
}

impl TrailRef {
    #[inline(always)]
    fn heap_cell(h: usize) -> Self {
        TrailRef::new()
            .with_tag(TrailRefTag::HeapCell)
            .with_val(h as u64)
    }

    #[inline(always)]
    fn stack_cell(h: usize) -> Self {
        TrailRef::new()
            .with_tag(TrailRefTag::StackCell)
            .with_val(h as u64)
    }

    #[inline(always)]
    fn attr_var(h: usize) -> Self {
        TrailRef::new()
            .with_tag(TrailRefTag::AttrVar)
            .with_val(h as u64)
    }

    #[inline(always)]
    fn pstr_loc(h: usize) -> Self {
        TrailRef::new()
            .with_tag(TrailRefTag::PStrLoc)
            .with_val(h as u64)
    }
}

type Trail = Vec<(TrailRef, HeapCellValue)>;

#[derive(Debug, Clone, Copy)]
pub enum AttrVarPolicy {
    DeepCopy,
    StripAttributes,
}

pub trait CopierTarget: IndexMut<usize, Output = HeapCellValue> {
    fn store(&self, value: HeapCellValue) -> HeapCellValue;
    fn deref(&self, value: HeapCellValue) -> HeapCellValue;
    fn push_attr_var_queue(&mut self, attr_var_loc: usize);
    fn stack(&mut self) -> &mut Stack;
    fn threshold(&self) -> usize;
    // returns the tail location of the pstr on success
    fn as_slice_from<'a>(&'a self, from: usize) -> Box<dyn Iterator<Item = u8> + 'a>;
    fn copy_pstr_to_threshold(&mut self, pstr_loc: usize) -> Result<usize, usize>;
    fn reserve(&mut self, num_cells: usize) -> Result<HeapWriter<'_>, usize>;
    fn copy_slice_to_end(&mut self, bounds: Range<usize>) -> Result<(), usize>;
}

pub(crate) fn copy_term<T: CopierTarget>(
    target: T,
    addr: HeapCellValue,
    attr_var_policy: AttrVarPolicy,
) -> Result<usize, usize> {
    let mut copy_term_state = CopyTermState::new(target, attr_var_policy);
    let old_threshold = copy_term_state.target.threshold();

    copy_term_state.copy_term_impl(addr)?;
    copy_term_state.copy_attr_var_lists()?;
    copy_term_state.unwind_trail();

    let new_threshold = copy_term_state.target.threshold();
    copy_term_state.copy_pstrs()?;

    Ok(new_threshold - old_threshold)
}

#[derive(Debug)]
pub struct PStrData {
    pre_old_h_tail_loc: usize,
    post_old_h_tail_loc: usize,
    post_old_h_pstr_loc_locs: IndexSet<usize, FxBuildHasher>,
}

#[derive(Debug)]
struct CopyTermState<T: CopierTarget> {
    trail: Trail,
    scan: usize,
    old_h: usize,
    target: T,
    attr_var_policy: AttrVarPolicy,
    attr_var_list_locs: Vec<(usize, HeapCellValue)>,
    // keys of pstr_loc_locs are byte indices rounded down to the
    // nearest cell boundary
    pstr_loc_locs: BTreeMap<usize, PStrData>,
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
            pstr_loc_locs: BTreeMap::new(),
        }
    }

    #[inline]
    fn value_at_scan(&mut self) -> &mut HeapCellValue {
        &mut self.target[self.scan]
    }

    fn trail_list_cell(&mut self, addr: usize, threshold: usize) {
        let trail_item = mem::replace(&mut self.target[addr], list_loc_as_cell!(threshold));
        self.trail.push((TrailRef::heap_cell(addr), trail_item));
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
        self.target.copy_slice_to_end(addr..addr + 2)?;

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

    fn copy_partial_string(&mut self, pstr_loc: usize) -> Result<(), usize> {
        match self.pstr_loc_locs.range_mut(..=pstr_loc).next_back() {
            Some((
                _prev_pstr_loc,
                &mut PStrData {
                    pre_old_h_tail_loc,
                    ref mut post_old_h_pstr_loc_locs,
                    ..
                },
            )) if pre_old_h_tail_loc >= cell_index!(pstr_loc) => {
                post_old_h_pstr_loc_locs.insert(self.scan);
                self.scan += 1;
                return Ok(());
            }
            _ => {}
        }

        let offset = self
            .target
            .as_slice_from(pstr_loc)
            .take_while(|b| *b != 0u8)
            .count();

        let left_pstr_boundary = cell_index!(pstr_loc + offset);
        let flag = u64::from_be_bytes(self.target[left_pstr_boundary].into_bytes());
        let pstr_loc_idx = cell_index!(pstr_loc);

        if flag == 1 {
            if left_pstr_boundary != pstr_loc_idx {
                let mut pstr_data = self
                    .pstr_loc_locs
                    .remove(&heap_index!(left_pstr_boundary))
                    .unwrap();

                pstr_data.post_old_h_pstr_loc_locs.insert(self.scan);
                self.pstr_loc_locs
                    .insert(heap_index!(cell_index!(pstr_loc)), pstr_data);

                let old_cell = self.target[pstr_loc_idx];
                self.target[pstr_loc_idx] = HeapCellValue::from_bytes(u64::to_be_bytes(1));
                self.trail
                    .push((TrailRef::pstr_loc(pstr_loc_idx), old_cell));
            } else {
                let pstr_data = self
                    .pstr_loc_locs
                    .get_mut(&heap_index!(left_pstr_boundary))
                    .unwrap();
                pstr_data.post_old_h_pstr_loc_locs.insert(self.scan);
            }
        } else {
            let old_cell = self.target[pstr_loc_idx];
            self.target[pstr_loc_idx] = HeapCellValue::from_bytes(u64::to_be_bytes(1));
            self.trail
                .push((TrailRef::pstr_loc(pstr_loc_idx), old_cell));

            let old_tail_idx = if (pstr_loc + offset + 1) % Heap::heap_cell_alignment() == 0 {
                cell_index!(pstr_loc + offset) + 2
            } else {
                cell_index!(pstr_loc + offset) + 1
            };

            let tail_cell = self.target[old_tail_idx];

            let new_tail_idx = self.target.threshold();
            let mut writer = self.target.reserve(1)?;

            writer.write_with(|section| {
                section.push_cell(tail_cell);
            });

            let mut post_old_h_pstr_loc_locs = IndexSet::with_hasher(FxBuildHasher::default());
            post_old_h_pstr_loc_locs.insert(self.scan);

            let pstr_data = PStrData {
                pre_old_h_tail_loc: old_tail_idx,
                post_old_h_tail_loc: new_tail_idx,
                post_old_h_pstr_loc_locs,
            };

            self.pstr_loc_locs
                .insert(heap_index!(pstr_loc_idx), pstr_data);
        }

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

                self.trail.push((TrailRef::heap_cell(h), heap_loc_as_cell!(h)));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.target[frontier] = heap_loc_as_cell!(frontier);
                self.target.stack()[s] = heap_loc_as_cell!(frontier);

                self.trail.push((TrailRef::stack_cell(s), stack_loc_as_cell!(s)));
            }
            (HeapCellValueTag::AttrVar, h) => {
                let threshold = if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    self.target.threshold()
                } else {
                    frontier
                };

                self.target[frontier] = heap_loc_as_cell!(threshold);
                self.target[h] = heap_loc_as_cell!(threshold);

                self.trail.push((TrailRef::attr_var(h), attr_var_as_cell!(h)));

                if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    let mut writer = self.target.reserve(2)?;

                    writer.write_with(|section| {
                        section.push_cell(attr_var_as_cell!(threshold));
                        section.push_cell(heap_loc_as_cell!(threshold + 1));
                    });

                    let old_list_link = self.target[h + 1];
                    self.trail.push((TrailRef::heap_cell(h + 1), old_list_link));
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

                let index_cell = self.target[addr.saturating_sub(1)];

                let str_cell = if get_structure_index(index_cell).is_some() {
                    // copy the index pointer trailing this
                    // inlined or expanded goal.
                    let mut writer = self.target.reserve(1).unwrap();

                    writer.write_with(|section| {
                        section.push_cell(index_cell);
                    });

                    str_loc_as_cell!(threshold + 1)
                } else {
                    str_loc_as_cell!(threshold)
                };

                *self.value_at_scan() = str_cell;
                self.target.copy_slice_to_end(addr .. addr + 1 + arity)?;

                let trail_item = mem::replace(
                    &mut self.target[addr],
                    str_cell,
                );

                self.trail.push((TrailRef::heap_cell(addr), trail_item));
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

    fn copy_pstrs(&mut self) -> Result<(), usize> {
        while let Some((least_pstr_loc, pstr_data)) = self.pstr_loc_locs.pop_first() {
            let threshold = heap_index!(self.target.threshold());

            for pstr_loc_loc in pstr_data.post_old_h_pstr_loc_locs {
                let pstr_loc = self.target[pstr_loc_loc].get_value() as usize;
                self.target[pstr_loc_loc] =
                    pstr_loc_as_cell!(threshold + pstr_loc - least_pstr_loc);
            }

            self.target.copy_pstr_to_threshold(least_pstr_loc)?;

            let mut writer = self.target.reserve(1)?;

            writer.write_with(|section| {
                section.push_cell(heap_loc_as_cell!(pstr_data.post_old_h_tail_loc));
            });
        }

        Ok(())
    }

    fn unwind_trail(&mut self) {
        for (r, value) in self.trail.drain(..) {
            let index = r.val() as usize;

            match r.tag() {
                TrailRefTag::AttrVar | TrailRefTag::HeapCell => {
                    self.target[index] = value;
                    self.target[index].set_mark_bit(false);
                    self.target[index].set_forwarding_bit(false);
                }
                TrailRefTag::StackCell => self.target.stack()[index] = value,
                TrailRefTag::PStrLoc => self.target[index] = value,
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

        let mut functor_writer = Heap::functor_writer(functor!(
            f_atom,
            [atom_as_cell(a_atom), atom_as_cell(b_atom)]
        ));

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

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(wam.machine_st.heap[1], pstr_loc_as_cell!(heap_index!(2)));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(2), "def".len()),
            "def"
        );
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(0));

        assert_eq!(wam.machine_st.heap[4], pstr_loc_as_cell!(heap_index!(7)));
        assert_eq!(wam.machine_st.heap[5], pstr_loc_as_cell!(heap_index!(9)));
        assert_eq!(wam.machine_st.heap[6], pstr_loc_as_cell!(heap_index!(7)));

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(7), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[8], heap_loc_as_cell!(5));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(9), "def".len()),
            "def"
        );
        assert_eq!(wam.machine_st.heap[10], heap_loc_as_cell!(6));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("abc ");
            section.push_cell(pstr_loc_as_cell!(heap_index!(2) + 9));

            section.push_pstr("defdefdefdef");
            section.push_cell(pstr_loc_as_cell!(0));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(wam.machine_st.heap.slice_to_str(0, "abc ".len()), "abc ");
        assert_eq!(
            wam.machine_st.heap[1],
            pstr_loc_as_cell!(heap_index!(2) + 9)
        );
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(2), "defdefdefdef".len()),
            "defdefdefdef"
        );
        assert_eq!(wam.machine_st.heap[4], pstr_loc_as_cell!(0));

        assert_eq!(wam.machine_st.heap[5], pstr_loc_as_cell!(heap_index!(8)));
        assert_eq!(
            wam.machine_st.heap[6],
            pstr_loc_as_cell!(heap_index!(10) + 1)
        );
        assert_eq!(wam.machine_st.heap[7], pstr_loc_as_cell!(heap_index!(8)));

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(8), "abc ".len()),
            "abc "
        );
        assert_eq!(wam.machine_st.heap[9], heap_loc_as_cell!(6));
        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(10), "fdef".len()),
            "fdef"
        );
        assert_eq!(wam.machine_st.heap[11], heap_loc_as_cell!(7));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("012345678912345");
            section.push_cell(pstr_loc_as_cell!(heap_index!(0)));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(wam.machine_st.heap[3], pstr_loc_as_cell!(heap_index!(0)));

        assert_eq!(wam.machine_st.heap[4], pstr_loc_as_cell!(heap_index!(6)));

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(6), "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(wam.machine_st.heap[5], pstr_loc_as_cell!(heap_index!(6)));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("012345678912345");
            section.push_cell(pstr_loc_as_cell!(heap_index!(0) + 9));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(0), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(
            wam.machine_st.heap[3],
            pstr_loc_as_cell!(heap_index!(0) + 9)
        );

        assert_eq!(wam.machine_st.heap[4], pstr_loc_as_cell!(heap_index!(6)));
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(6) + 9)
        );

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(6), "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(wam.machine_st.heap[9], heap_loc_as_cell!(5));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("012345678912345");
            section.push_cell(pstr_loc_as_cell!(heap_index!(0) + 7));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(11), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(
            wam.machine_st.heap[3],
            pstr_loc_as_cell!(heap_index!(0) + 7)
        );

        assert_eq!(
            wam.machine_st.heap[4],
            pstr_loc_as_cell!(heap_index!(6) + 11)
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(6) + 7)
        );

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(6), "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(wam.machine_st.heap[9], heap_loc_as_cell!(5));

        wam.machine_st.heap.clear();

        let mut writer = wam.machine_st.heap.reserve(4).unwrap();

        writer.write_with(|section| {
            section.push_pstr("012345678912345");
            section.push_cell(pstr_loc_as_cell!(heap_index!(0) + 12));
        });

        {
            let wam = TermCopyingMockWAM { wam: &mut wam };
            copy_term(wam, pstr_loc_as_cell!(11), AttrVarPolicy::DeepCopy).unwrap();
        }

        assert_eq!(
            wam.machine_st.heap.slice_to_str(0, "012345678912345".len()),
            "012345678912345"
        );
        assert_eq!(
            wam.machine_st.heap[3],
            pstr_loc_as_cell!(heap_index!(0) + 12)
        );

        assert_eq!(
            wam.machine_st.heap[4],
            pstr_loc_as_cell!(heap_index!(6) + 3)
        );
        assert_eq!(
            wam.machine_st.heap[5],
            pstr_loc_as_cell!(heap_index!(6) + 4)
        );

        assert_eq!(
            wam.machine_st
                .heap
                .slice_to_str(heap_index!(6), "8912345".len()),
            "8912345"
        );
        assert_eq!(wam.machine_st.heap[8], heap_loc_as_cell!(5));

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
