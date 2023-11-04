use crate::heap_iter::*;
use crate::machine::*;
use crate::parser::ast::*;
use crate::temp_v;
use crate::types::*;

use indexmap::IndexSet;

use std::cmp::Ordering;
use std::vec::IntoIter;

pub(super) type Bindings = Vec<(usize, HeapCellValue)>;

#[derive(Debug)]
pub(super) struct AttrVarInitializer {
    pub(super) attr_var_queue: Vec<usize>,
    pub(super) bindings: Bindings,
    pub(super) p: usize,
    pub(super) cp: usize,
    // pub(super) instigating_p: usize,
    pub(super) verify_attrs_loc: usize,
}

impl AttrVarInitializer {
    pub(super) fn new(verify_attrs_loc: usize) -> Self {
        AttrVarInitializer {
            attr_var_queue: vec![],
            bindings: vec![],
            p: 0,
            cp: 0,
            verify_attrs_loc,
        }
    }

    #[inline]
    pub(super) fn reset(&mut self, len: usize) {
        self.attr_var_queue.truncate(len);
        self.bindings.clear();
    }
}

impl MachineState {
    pub(super) fn push_attr_var_binding(&mut self, h: usize, addr: HeapCellValue) {
        if self.attr_var_init.bindings.is_empty() {
            // save self.p and self.cp and ensure that the next
            // instruction is InstallVerifyAttrInterrupt.

            self.attr_var_init.p = self.p;
            self.attr_var_init.cp = self.cp;

            self.p = INSTALL_VERIFY_ATTR_INTERRUPT - 1;
            self.cp = INSTALL_VERIFY_ATTR_INTERRUPT;
        }

        debug_assert_eq!(self.heap[h].get_tag(), HeapCellValueTag::AttrVar);
        self.attr_var_init.bindings.push((h, addr));
    }

    fn populate_var_and_value_lists(&mut self) -> (HeapCellValue, HeapCellValue) {
        let iter = self
            .attr_var_init
            .bindings
            .iter()
            .map(|(ref h, _)| attr_var_as_cell!(*h));

        let var_list_addr = heap_loc_as_cell!(iter_to_heap_list(&mut self.heap, iter));
        let iter = self.attr_var_init.bindings.drain(0..).map(|(_, ref v)| *v);
        let value_list_addr = heap_loc_as_cell!(iter_to_heap_list(&mut self.heap, iter));

        (var_list_addr, value_list_addr)
    }

    fn verify_attributes(&mut self) {
        for (h, _) in &self.attr_var_init.bindings {
            self.heap[*h] = attr_var_as_cell!(*h);
        }

        let (var_list_addr, value_list_addr) = self.populate_var_and_value_lists();

        self[temp_v!(1)] = var_list_addr;
        self[temp_v!(2)] = value_list_addr;
    }

    pub(super) fn gather_attr_vars_created_since(&mut self, b: usize) -> IntoIter<HeapCellValue> {
        let mut attr_vars: Vec<_> = if b >= self.attr_var_init.attr_var_queue.len() {
            vec![]
        } else {
            self.attr_var_init.attr_var_queue[b..]
                .iter()
                .filter_map(|h| {
                    read_heap_cell!(self.store(self.deref(heap_loc_as_cell!(*h))),
                        (HeapCellValueTag::AttrVar, h) => {
                            Some(attr_var_as_cell!(h))
                        }
                        _ => {
                            None
                        }
                    )
                })
                .collect()
        };

        attr_vars.sort_unstable_by(|a1, a2| {
            compare_term_test!(self, *a1, *a2).unwrap_or(Ordering::Less)
        });

        attr_vars.dedup();
        attr_vars.into_iter()
    }

    pub(super) fn verify_attr_interrupt(&mut self, p: usize, arity: usize) {
        self.allocate(arity + 3);

        let e = self.e;
        let and_frame = self.stack.index_and_frame_mut(e);

        for i in 1..arity + 1 {
            and_frame[i] = self.registers[i];
        }

        and_frame[arity + 1] = fixnum_as_cell!(Fixnum::build_with(self.b0 as i64));
        and_frame[arity + 2] = fixnum_as_cell!(Fixnum::build_with(self.num_of_args as i64));
        and_frame[arity + 3] = fixnum_as_cell!(Fixnum::build_with(self.attr_var_init.cp as i64));

        self.verify_attributes();

        self.num_of_args = 3;
        self.b0 = self.b;
        self.p = p;
    }

    pub(super) fn attr_vars_of_term(&mut self, cell: HeapCellValue) -> Vec<HeapCellValue> {
        let mut seen_set = IndexSet::new();
        let mut seen_vars = vec![];

        let mut iter =
            stackful_preorder_iter::<NonListElider>(&mut self.heap, &mut self.stack, cell);

        while let Some(value) = iter.next() {
            read_heap_cell!(value,
                (HeapCellValueTag::AttrVar, h) => {
                    if seen_set.contains(&h) {
                        continue;
                    }

                    let value = unmark_cell_bits!(value);

                    if h != iter.focus().value() as usize {
                        let deref_value = heap_bound_store(iter.heap, heap_bound_deref(iter.heap, value));

                        if deref_value.is_compound(iter.heap) {
                            // a cyclic structure is bound to the attributed variable at h.
                            // it mustn't be included in seen_vars.
                            continue;
                        }
                    }

                    seen_vars.push(value);
                    seen_set.insert(h);

                    let mut l = h + 1;
                    // let mut list_elements = vec![];
                    // let iter_stack_len = iter.stack_len();

                    loop {
                        read_heap_cell!(iter.heap[l],
                            (HeapCellValueTag::Lis) => {
                                iter.push_stack(IterStackLoc::iterable_loc(l, HeapOrStackTag::Heap));
                                // l = elem + 1;
                                break;
                            }
                            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, h) => {
                                if h == l {
                                    break;
                                } else {
                                    l = h;
                                }
                            }
                            _ => {
                                break;
                            }
                        )
                    }

                    // iter.stack_slice_from(iter_stack_len ..).reverse();
                }
                _ => {
                }
            );
        }

        seen_vars
    }
}
