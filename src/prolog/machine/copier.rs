use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::stack::*;
use crate::prolog::machine::streams::*;

use std::mem;
use std::ops::IndexMut;

type Trail = Vec<(Ref, HeapCellValue)>;

#[derive(Clone, Copy)]
pub enum AttrVarPolicy {
    DeepCopy,
    StripAttributes
}

pub(crate)
trait CopierTarget: IndexMut<usize, Output = HeapCellValue> {
    fn deref(&self, val: Addr) -> Addr;
    fn push(&mut self, val: HeapCellValue);
    fn stack(&mut self) -> &mut Stack;
    fn store(&self, val: Addr) -> Addr;
    fn threshold(&self) -> usize;
}

pub(crate)
fn copy_term<T: CopierTarget>(target: T, addr: Addr, attr_var_policy: AttrVarPolicy) {
    let mut copy_term_state = CopyTermState::new(target, attr_var_policy);
    copy_term_state.copy_term_impl(addr);
}

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
            attr_var_policy
        }
    }

    #[inline]
    fn value_at_scan(&mut self) -> &mut HeapCellValue {
        let scan = self.scan;
        &mut self.target[scan]
    }

    fn copy_list(&mut self, addr: usize) {
        if let Addr::Lis(h) = self.target[addr + 1].as_addr(addr + 1) {
            if h >= self.old_h {
                *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(h));
                self.scan += 1;

                return;
            }
        }

        let threshold = self.target.threshold();

        *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(threshold));

        for i in 0 .. 2 {
            let hcv = self.target[addr + i].context_free_clone();
            self.target.push(hcv);
        }

        let cdr = self.target.store(self.target.deref(Addr::HeapCell(addr + 1)));

        if let Addr::Lis(_) = cdr {
            let tail_addr = self.target[addr + 1].as_addr(addr + 1);

            self.trail.push((
                Ref::HeapCell(addr + 1),
                HeapCellValue::Addr(tail_addr),
            ));

            self.target[addr + 1] = HeapCellValue::Addr(Addr::Lis(threshold));
        }

        self.scan += 1;
    }

    fn copy_partial_string(&mut self, addr: usize, n: usize) {
        if let &HeapCellValue::Addr(Addr::PStrLocation(h, _)) = &self.target[addr] {
            if h >= self.old_h {
                *self.value_at_scan() = HeapCellValue::Addr(Addr::PStrLocation(h, n));
                self.scan += 1;

                return;
            }
        }

        let threshold = self.target.threshold();

        *self.value_at_scan() =
            HeapCellValue::Addr(Addr::PStrLocation(threshold, 0));

        self.scan += 1;

        let (pstr, has_tail) =
            match &self.target[addr] {
                &HeapCellValue::PartialString(ref pstr, has_tail) => {
                    (pstr.clone_from_offset(n), has_tail)
                }
                _ => {
                    unreachable!()
                }
            };

        self.target.push(HeapCellValue::PartialString(pstr, has_tail));

        let replacement = HeapCellValue::Addr(Addr::PStrLocation(threshold, 0));

        let trail_item = mem::replace(
            &mut self.target[addr],
            replacement,
        );

        self.trail.push((
            Ref::HeapCell(addr),
            trail_item,
        ));

        if has_tail {
            let tail_addr = self.target[addr + 1].as_addr(addr + 1);
            self.target.push(HeapCellValue::Addr(tail_addr));
        }
    }

    fn reinstantiate_var(&mut self, addr: Addr, frontier: usize) {
        match addr {
            Addr::HeapCell(h) => {
                self.target[frontier] = HeapCellValue::Addr(Addr::HeapCell(frontier));
                self.target[h] = HeapCellValue::Addr(Addr::HeapCell(frontier));

                self.trail.push((
                    Ref::HeapCell(h),
                    HeapCellValue::Addr(Addr::HeapCell(h)),
                ));
            }
            Addr::StackCell(fr, sc) => {
                self.target[frontier] = HeapCellValue::Addr(Addr::HeapCell(frontier));
                self.target.stack().index_and_frame_mut(fr)[sc] = Addr::HeapCell(frontier);

                self.trail.push((
                    Ref::StackCell(fr, sc),
                    HeapCellValue::Addr(Addr::StackCell(fr, sc)),
                ));
            }
            Addr::AttrVar(h) => {
                let threshold = if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    self.target.threshold()
                } else {
                    frontier
                };

                self.target[frontier] = HeapCellValue::Addr(Addr::HeapCell(threshold));
                self.target[h] = HeapCellValue::Addr(Addr::HeapCell(frontier));

                self.trail.push((
                    Ref::AttrVar(h),
                    HeapCellValue::Addr(Addr::AttrVar(h)),
                ));

                if let AttrVarPolicy::DeepCopy = self.attr_var_policy {
                    self.target.push(HeapCellValue::Addr(Addr::AttrVar(threshold)));

                    let list_val = self.target[h + 1].context_free_clone();
                    self.target.push(list_val);
                }
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn copy_var(&mut self, addr: Addr) {
        let rd = self.target.store(self.target.deref(addr));

        match rd {
            Addr::AttrVar(h) | Addr::HeapCell(h) if h >= self.old_h => {
                *self.value_at_scan() = HeapCellValue::Addr(rd);
                self.scan += 1;
            }
            _ if addr == rd => {
                self.reinstantiate_var(addr, self.scan);
                self.scan += 1;
            }
            _ => {
                *self.value_at_scan() = HeapCellValue::Addr(rd);
            }
        }
    }

    fn copy_stream(&mut self, addr: usize) {
        let threshold = self.target.threshold();

        let trail_item = mem::replace(
            &mut self.target[addr],
            HeapCellValue::Addr(Addr::Stream(threshold)),
        );

        self.trail.push((
            Ref::HeapCell(addr),
            trail_item,
        ));

        self.target.push(HeapCellValue::Stream(Stream::null_stream()));

        self.scan += 1;
    }

    fn copy_structure(&mut self, addr: usize) {
        match self.target[addr].context_free_clone() {
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let threshold = self.target.threshold();

                *self.value_at_scan() = HeapCellValue::Addr(Addr::Str(threshold));

                let trail_item = mem::replace(
                    &mut self.target[addr],
                    HeapCellValue::Addr(Addr::Str(threshold)),
                );

                self.trail.push((
                    Ref::HeapCell(addr),
                    trail_item,
                ));

                self.target.push(HeapCellValue::NamedStr(arity, name, fixity));

                for i in 0..arity {
                    let hcv = self.target[addr + 1 + i].context_free_clone();
                    self.target.push(hcv);
                }
            }
            HeapCellValue::Addr(Addr::Str(addr)) => {
                *self.value_at_scan() = HeapCellValue::Addr(Addr::Str(addr))
            }
            _ => {
                unreachable!()
            }
        }

        self.scan += 1;
    }

    fn copy_term_impl(&mut self, addr: Addr) {
        self.scan = self.target.threshold();
        self.target.push(HeapCellValue::Addr(addr));

        while self.scan < self.target.threshold() {
            match self.value_at_scan() {
                &mut HeapCellValue::Addr(addr) => {
                    match addr {
                        Addr::Con(h) => {
                            let addr = self.target[h].as_addr(h);

                            if addr == Addr::Con(h) {
                                *self.value_at_scan() = self.target[h].context_free_clone();
                            } else {
                                *self.value_at_scan() = HeapCellValue::Addr(addr);
                            }
                        }
                        Addr::Lis(h) => {
                            self.copy_list(h);
                        }
                        addr @ Addr::AttrVar(_) |
                        addr @ Addr::HeapCell(_) |
                        addr @ Addr::StackCell(..) => {
                            self.copy_var(addr);
                        }
                        Addr::Str(addr) => {
                            self.copy_structure(addr);
                        }
                        Addr::PStrLocation(addr, n) => {
                            self.copy_partial_string(addr, n);
                        }
                        Addr::Stream(h) => {
                            self.copy_stream(h);
                        }
                        _ => {
                            self.scan += 1;
                        }
                    }
                }
                _ => {
                    self.scan += 1;
                }
            }
        }

        self.unwind_trail();
    }

    fn unwind_trail(&mut self) {
        for (r, value) in self.trail.drain(0..) {
            match r {
                Ref::AttrVar(h) | Ref::HeapCell(h) =>
                    self.target[h] = value,
                Ref::StackCell(fr, sc) =>
                    self.target.stack().index_and_frame_mut(fr)[sc] = value.as_addr(0),
            }
        }
    }
}
