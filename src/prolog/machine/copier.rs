use prolog::machine::and_stack::*;
use prolog::machine::machine_indices::*;

use std::ops::IndexMut;

type Trail = Vec<(Ref, HeapCellValue)>;

pub(crate) trait CopierTarget: IndexMut<usize, Output=HeapCellValue>
{
    fn threshold(&self) -> usize;
    fn push(&mut self, HeapCellValue);
    fn store(&self, Addr) -> Addr;
    fn deref(&self, Addr) -> Addr;
    fn stack(&mut self) -> &mut AndStack;
}

pub(crate)
fn copy_term<T: CopierTarget>(target: T, addr: Addr)
{
    let mut copy_term_state = CopyTermState::new(target);
    copy_term_state.copy_term_impl(addr);
}

struct CopyTermState<T: CopierTarget> {
    trail: Trail,
    scan: usize,
    old_h: usize,
    target: T
}

impl<T: CopierTarget> CopyTermState<T> {
    fn new(target: T) -> Self {
        CopyTermState {
            trail: vec![],
            scan:  0,
            old_h: target.threshold(),
            target
        }
    }

    #[inline]
    fn value_at_scan(&mut self) -> &mut HeapCellValue {
        let scan = self.scan;
        &mut self.target[scan]
    }

    fn reinstantiate_var(&mut self, addr: Addr, threshold: usize)
    {
        match addr {
            Addr::HeapCell(h) => {
                self.target[threshold] = HeapCellValue::Addr(Addr::HeapCell(threshold));
                self.target[h] = HeapCellValue::Addr(Addr::HeapCell(threshold));
                self.trail.push((Ref::HeapCell(h), HeapCellValue::Addr(Addr::HeapCell(h))));
            },
            Addr::StackCell(fr, sc) => {
                self.target[threshold] = HeapCellValue::Addr(Addr::HeapCell(threshold));
                self.target.stack()[fr][sc] = Addr::HeapCell(threshold);
                self.trail.push((Ref::StackCell(fr, sc), HeapCellValue::Addr(Addr::StackCell(fr, sc))));
            },
            Addr::AttrVar(h) => {
                self.target[threshold] = HeapCellValue::Addr(Addr::AttrVar(threshold));
                self.target[h] = HeapCellValue::Addr(Addr::AttrVar(threshold));
                self.trail.push((Ref::AttrVar(h), HeapCellValue::Addr(Addr::AttrVar(h))));
            },
            _ => {}
        }
    }

    fn copied_list(&mut self, addr: usize) -> bool {
        if let HeapCellValue::Addr(Addr::Lis(addr)) = self.target[addr].clone() {
            if addr >= self.old_h {
                *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(addr));
                self.scan += 1;
                return true;
            }
        }

        false
    }

    fn copy_list(&mut self, addr: usize) {
        if self.copied_list(addr) {
            return;
        }

        let threshold = self.target.threshold();
        *self.value_at_scan() = HeapCellValue::Addr(Addr::Lis(threshold));

        let hcv = self.target[addr].clone();
        self.target.push(hcv.clone());

        let ra = hcv.as_addr(threshold);
        let rd = self.target.store(self.target.deref(ra));

        match rd.clone() {
            Addr::AttrVar(h) | Addr::HeapCell(h) if h >= self.old_h =>
                self.target[threshold] = HeapCellValue::Addr(rd),
            ra @ Addr::AttrVar(_) | ra @ Addr::HeapCell(..) | ra @ Addr::StackCell(..) =>
                if ra == rd {
                    self.reinstantiate_var(ra, threshold);
                } else {
                    self.target[threshold] = HeapCellValue::Addr(ra);
                },
            _ => {
                self.trail.push((Ref::HeapCell(addr), self.target[addr].clone()));
                self.target[addr] = HeapCellValue::Addr(Addr::Lis(threshold))
            }
        };

        let hcv = self.target[addr + 1].clone();
        self.target.push(hcv);

        self.scan += 1;
    }

    fn copy_var(&mut self, addr: Addr) {
        let rd = self.target.store(self.target.deref(addr.clone()));

        match rd.clone() {
            Addr::AttrVar(h) | Addr::HeapCell(h) if h >= self.old_h => {
                *self.value_at_scan() = HeapCellValue::Addr(rd);
                self.scan += 1;
            },
            Addr::AttrVar(h) if addr == rd => {
                let threshold = self.target.threshold();
                self.target.push(HeapCellValue::Addr(Addr::AttrVar(threshold)));

                let list_val = self.target[h + 1].clone();
                self.target.push(list_val);

                self.reinstantiate_var(addr, threshold);
                *self.value_at_scan() = HeapCellValue::Addr(Addr::AttrVar(threshold));
            },
            _ if addr == rd => {
                let scan = self.scan;
                self.reinstantiate_var(addr, scan);
                self.scan += 1;
            },
            _ => *self.value_at_scan() = HeapCellValue::Addr(rd)
        }
    }

    fn copy_structure(&mut self, addr: usize) {
        match self.target[addr].clone() {
            HeapCellValue::NamedStr(arity, name, fixity) => {
                let threshold = self.target.threshold();

                *self.value_at_scan() = HeapCellValue::Addr(Addr::Str(threshold));
                self.target[addr] = HeapCellValue::Addr(Addr::Str(threshold));

                self.trail.push((Ref::HeapCell(addr),
                                 HeapCellValue::NamedStr(arity, name.clone(), fixity.clone())));

                self.target.push(HeapCellValue::NamedStr(arity, name, fixity));

                for i in 0 .. arity {
                    let hcv = self.target[addr + 1 + i].clone();
                    self.target.push(hcv);
                }
            },
            HeapCellValue::Addr(Addr::Str(addr)) =>
                *self.value_at_scan() = HeapCellValue::Addr(Addr::Str(addr)),
            _ => {}
        }

        self.scan += 1;
    }

    fn copy_term_impl(&mut self, addr: Addr) {
        self.scan = self.target.threshold();
        self.target.push(HeapCellValue::Addr(addr));

        while self.scan < self.target.threshold() {
            match self.value_at_scan().clone() {
                HeapCellValue::NamedStr(..) =>
                    self.scan += 1,
                HeapCellValue::Addr(addr) =>
                    match addr {
                        Addr::Lis(addr) =>
                            self.copy_list(addr),
                        addr @ Addr::AttrVar(_)
                      | addr @ Addr::HeapCell(_)
                      | addr @ Addr::StackCell(..) =>
                            self.copy_var(addr),
                        Addr::Str(addr) =>
                            self.copy_structure(addr),
                        Addr::Con(_) | Addr::DBRef(_) =>
                            self.scan += 1
                    }
            }
        }

        self.unwind_trail();
    }

    fn unwind_trail(&mut self) {
        for (r, value) in self.trail.drain(0 ..) {
            match r {
                Ref::AttrVar(h) | Ref::HeapCell(h) =>
                    self.target[h] = value,
                Ref::StackCell(fr, sc) =>
                    self.target.stack()[fr][sc] = value.as_addr(0)
            }
        }
    }
}
