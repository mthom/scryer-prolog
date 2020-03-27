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
    attr_var_policy: AttrVarPolicy
}

impl<T: CopierTarget> CopyTermState<T> {
    fn new(target: T, attr_var_policy: AttrVarPolicy) -> Self {
        CopyTermState {
            trail: vec![],
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

    fn copied_list(&mut self, addr: usize) -> bool {
        match &self.target[addr] {
            HeapCellValue::Addr(Addr::Lis(addr)) | HeapCellValue::Addr(Addr::HeapCell(addr)) => {
                if *addr >= self.old_h {
                    *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(*addr));
                    self.scan += 1;
                    return true;
                }
            }
            _ => {}
        };

        false
    }

    fn copy_list(&mut self, addr: usize) {
        if self.copied_list(addr) {
            return;
        }

        let threshold = self.target.threshold();

        *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(threshold));

        let ra = self.target[addr].as_addr(threshold);
        let rd = self.target.store(self.target.deref(ra));

        self.target.push(HeapCellValue::Addr(ra));

        let hcv = HeapCellValue::Addr(self.target[addr + 1].as_addr(addr + 1));

        self.target.push(hcv);

        match rd {
            Addr::AttrVar(h) | Addr::HeapCell(h)
                if h >= self.old_h => {
                    self.target[threshold] = HeapCellValue::Addr(rd)
                }
            var @ Addr::AttrVar(_)
          | var @ Addr::HeapCell(..)
          | var @ Addr::StackCell(..) => {
                if ra == rd {
                    self.reinstantiate_var(var, threshold);

                    if let AttrVarPolicy::StripAttributes = self.attr_var_policy {
                        self.trail.push((Ref::HeapCell(addr), HeapCellValue::Addr(ra)));
                        self.target[addr] = HeapCellValue::Addr(Addr::HeapCell(threshold));
                    }
                } else {
                    self.target[threshold] = HeapCellValue::Addr(ra);
                }
            }
            _ => {
                self.trail.push((
                    Ref::HeapCell(addr),
                    HeapCellValue::Addr(self.target[addr].as_addr(addr)),
                ));

                self.target[addr] = HeapCellValue::Addr(Addr::Lis(threshold))
            }
        };

        self.scan += 1;
    }

    fn copied_partial_string(&mut self, addr: usize) -> bool {
        if let &HeapCellValue::Addr(Addr::PStrLocation(h, n)) = &self.target[addr + 1] {
            if h >= self.old_h {
                *self.value_at_scan() = HeapCellValue::Addr(Addr::PStrLocation(h, n));
                self.scan += 1;
                return true;
            }
        }

        false
    }

    fn copy_partial_string(&mut self, addr: usize, n: usize) {
        let threshold = self.target.threshold();
        let tail_addr = self.target[addr + 1].as_addr(addr + 1);

        let trail_item = mem::replace(
            &mut self.target[addr + 1],
            HeapCellValue::Addr(Addr::PStrLocation(threshold, 0)),
        );

        self.trail.push((
            Ref::HeapCell(addr + 1),
            trail_item,
        ));

        let pstr =
            match &self.target[addr] {
                HeapCellValue::PartialString(ref pstr) => {
                    pstr.clone_from_offset(n)
                }
                _ => {
                    unreachable!()
                }
            };

        self.target.push(HeapCellValue::PartialString(pstr));
        self.target.push(HeapCellValue::Addr(tail_addr));
    }

    fn copy_partial_string_from(&mut self, addr: usize, n: usize) {
        if self.copied_partial_string(addr) {
            return;
        }

        let threshold = self.target.threshold();

        self.target[self.scan] =
            HeapCellValue::Addr(Addr::PStrLocation(threshold, 0));

        self.scan += 1;

        self.copy_partial_string(addr, n);
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
                self.target[h] = HeapCellValue::Addr(Addr::HeapCell(threshold));
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
            _ => unreachable!()
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

    fn copy_structure(&mut self, addr: usize) {
        match self.target[addr].context_free_clone() {
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let threshold = self.target.threshold();

                *self.value_at_scan() = HeapCellValue::Addr(Addr::Str(threshold));
                self.target[addr] = HeapCellValue::Addr(Addr::Str(threshold));

                self.trail.push((
                    Ref::HeapCell(addr),
                    HeapCellValue::NamedStr(arity, name.clone(), fixity.clone()),
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
            _ => {}
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
                            self.target.push(self.target[h].context_free_clone());
                            self.scan += 1;
                        }
                        Addr::Stream(_) => {
                            self.target.push(HeapCellValue::Stream(Stream::null_stream()));
                            self.scan += 1;
                        }
                        Addr::Lis(h) => {
                            self.copy_list(h);
                        }
                        addr @ Addr::AttrVar(_)
                      | addr @ Addr::HeapCell(_)
                      | addr @ Addr::StackCell(..) => {
                            self.copy_var(addr);
                        }
                        Addr::Str(addr) => {
                            self.copy_structure(addr);
                        }
                        Addr::PStrLocation(addr, n) => {
                            self.copy_partial_string_from(addr, n);
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
