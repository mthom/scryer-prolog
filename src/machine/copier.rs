use crate::atom_table::*;
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
}

#[derive(Debug)]
struct CopyTermState<T: CopierTarget> {
    trail: Trail,
    scan: usize,
    old_h: usize,
    target: T,
    attr_var_policy: AttrVarPolicy,
}

impl<T: CopierTarget> CopyTermState<T> {
    fn new(target: T, attr_var_policy: AttrVarPolicy) -> Self {
        CopyTermState {
            trail: Trail::new(),
            scan: 0,
            old_h: target.threshold(),
            target,
            attr_var_policy,
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
            self.trail_list_cell(addr + 1, threshold);
        } else {
            let car = self
                .target
                .store(self.target.deref(heap_loc_as_cell!(addr)));

            if !car.is_var() {
                self.trail_list_cell(addr, threshold);
            }
        }

        self.scan += 1;
    }

    fn copy_partial_string(&mut self, scan_tag: HeapCellValueTag, pstr_loc: usize) {
        read_heap_cell!(self.target[pstr_loc],
            (HeapCellValueTag::PStrLoc, h) => {
                if h >= self.old_h {
                    *self.value_at_scan() = match scan_tag {
                        HeapCellValueTag::PStrLoc => {
                            pstr_loc_as_cell!(h)
                        }
                        tag => {
                            debug_assert!(tag == HeapCellValueTag::PStrOffset);
                            pstr_offset_as_cell!(h)
                        }
                    };

                    self.scan += 1;
                    return;
                }
            }
            _ => {}
        );

        let threshold = self.target.threshold();

        *self.value_at_scan() = pstr_loc_as_cell!(threshold);
        self.scan += 1;

        self.target.push(self.target[pstr_loc]);

        let replacement = pstr_loc_as_cell!(threshold);
        let trail_item = mem::replace(&mut self.target[pstr_loc], replacement);

        self.trail.push((Ref::heap_cell(pstr_loc), trail_item));
        self.target.push(self.target[pstr_loc + 1]);
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
                    self.target
                        .push(attr_var_as_cell!(threshold));

                    let list_val = self.target[h + 1];
                    self.target.push(list_val);
                }
            }
            _ => {
                unreachable!()
            }
        );
    }

    fn copy_var(&mut self, addr: HeapCellValue) {
        let rd = self.target.deref(addr);
        let ra = self.target.store(rd);

        read_heap_cell!(ra,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                if h >= self.old_h {
                    *self.value_at_scan() = rd;
                    self.scan += 1;

                    return;
                }
            }
            _ => {}
        );

        if addr == ra {
            self.reinstantiate_var(addr, self.scan);
            self.scan += 1;
        } else {
            *self.value_at_scan() = ra;
            // self.copy_compound(rd, ra);
        }
    }

    /*
    fn copy_compound(&mut self, rd: HeapCellValue, ra: HeapCellValue) {
        let h = rd.get_value();
        let trail_item = self.target[h];
        let threshold = self.target.threshold();

        self.trail.push((Ref::heap_cell(h), trail_item));
        self.target[self.scan].set_value(threshold);

        read_heap_cell!(ra,
            (HeapCellValueTag::Atom, (_name, arity)) => {
                self.target.push(ra);

                for i in 0..arity {
                    self.target.push(self.target[h + 1 + i]);
                }

                self.target[h] = str_loc_as_cell!(self.scan + 1);
            }
            (HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset) => {
                self.target.push(ra);
                self.target.push(self.target[h + 1]);

                self.target[h] = pstr_loc_as_cell!(self.scan + 1);
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                self.target[h] = atom_as_cstr_cell!(cstr_atom);
            }
            (HeapCellValueTag::Str, s) => {
                self.copy_structure(s);
                return;
            }
            _ => {
                *self.value_at_scan() = rd;
                self.trail.pop();
                return;
            }
        );

        self.scan += 1;
    }
    */

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

        self.unwind_trail();
    }

    fn unwind_trail(&mut self) {
        for (r, value) in self.trail.drain(0..) {
            let index = r.get_value() as usize;

            match r.get_tag() {
                RefTag::AttrVar | RefTag::HeapCell => self.target[index] = value,
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

        wam.machine_st.heap
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

        let pstr_var_cell = put_partial_string(&mut wam.machine_st.heap, "abc ", &mut wam.machine_st.atom_tbl);
        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(pstr_loc_as_cell!(2));

        let pstr_second_var_cell = put_partial_string(&mut wam.machine_st.heap, "def", &mut wam.machine_st.atom_tbl);
        let pstr_second_cell = wam.machine_st.heap[pstr_second_var_cell.get_value() as usize];

        wam.machine_st.heap.pop();
        wam.machine_st.heap.push(pstr_loc_as_cell!(wam.machine_st.heap.len() + 1));

        wam.machine_st.heap.push(pstr_offset_as_cell!(0));
        wam.machine_st.heap.push(fixnum_as_cell!(Fixnum::build_with(0i64)));

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
        assert_eq!(wam.machine_st.heap[5], fixnum_as_cell!(Fixnum::build_with(0i64)));

        assert_eq!(wam.machine_st.heap[7], pstr_cell);
        assert_eq!(wam.machine_st.heap[8], pstr_loc_as_cell!(9));
        assert_eq!(wam.machine_st.heap[9], pstr_second_cell);
        assert_eq!(wam.machine_st.heap[10], pstr_loc_as_cell!(11));
        assert_eq!(wam.machine_st.heap[11], pstr_offset_as_cell!(7));
        assert_eq!(wam.machine_st.heap[12], fixnum_as_cell!(Fixnum::build_with(0i64)));

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
