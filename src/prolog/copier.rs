use prolog::and_stack::*;
use prolog::instructions::*;

use std::ops::IndexMut;

type Trail = Vec<(Ref, HeapCellValue)>;

pub(crate) struct RedirectInfo {
    trail: Trail
}

pub(crate) trait CopierTarget: IndexMut<usize, Output=HeapCellValue>
{
    fn source(&self) -> usize;
    fn threshold(&self) -> usize;
    fn push(&mut self, HeapCellValue);
    fn store(&self, Addr) -> Addr;
    fn deref(&self, Addr) -> Addr;
    fn stack(&mut self) -> &mut AndStack;

    fn unwind_trail(&mut self, redirect: RedirectInfo)
    {
        for (r, hcv) in redirect.trail {
            match r {
                Ref::AttrVar(hc) | Ref::HeapCell(hc) => self[hc] = hcv.clone(),
                Ref::StackCell(fr, sc) => self.stack()[fr][sc] = hcv.as_addr(0)
            }
        }
    }

    fn reinstantiate_var(&mut self, ra: Addr, scan: usize, trail: &mut Trail)
    {
        match ra {
            Addr::HeapCell(hc) => {
                self[scan] = HeapCellValue::Addr(Addr::HeapCell(scan));
                self[hc] = HeapCellValue::Addr(Addr::HeapCell(scan));
                trail.push((Ref::HeapCell(hc),
                            HeapCellValue::Addr(Addr::HeapCell(hc))));
            },
            Addr::StackCell(fr, sc) => {
                self[scan] = HeapCellValue::Addr(Addr::HeapCell(scan));
                self.stack()[fr][sc] = Addr::HeapCell(scan);
                trail.push((Ref::StackCell(fr, sc),
                            HeapCellValue::Addr(Addr::StackCell(fr, sc))));
            },
            Addr::AttrVar(hc) => {
                self[scan] = HeapCellValue::Addr(Addr::AttrVar(scan));
                self[hc] = HeapCellValue::Addr(Addr::AttrVar(scan));
                trail.push((Ref::AttrVar(hc),
                            HeapCellValue::Addr(Addr::AttrVar(hc))));
            },
            _ => {}
        }
    }

    // duplicate_term_impl(L1, L2) uses Cheney's algorithm to copy the term
    // at L1 to L2. trail is kept to restore the innards of L1 after
    // it's been copied to L2.
    fn duplicate_term_impl(&mut self, addr: Addr) -> RedirectInfo
    {
        let mut trail = Trail::new();
        let mut scan = self.source();
        let old_h = self.threshold();

        self.push(HeapCellValue::Addr(addr));

        while scan < self.threshold() {
            match self[scan].clone() {
                HeapCellValue::NamedStr(..) =>
                    scan += 1,
                HeapCellValue::Addr(a) =>
                    match a.clone() {
                        Addr::Lis(a) => {
                            if let HeapCellValue::Addr(Addr::Lis(b)) = self[a].clone() {
                                if b >= old_h {
                                    self[scan] = HeapCellValue::Addr(Addr::Lis(b));
                                    scan += 1;
                                    continue;
                                }
                            }

                            let threshold = self.threshold();
                            self[scan] = HeapCellValue::Addr(Addr::Lis(threshold));

                            let hcv = self[a].clone();
                            self.push(hcv.clone());

                            let ra = hcv.as_addr(threshold);
                            let rd = self.store(self.deref(ra));

                            match rd.clone() {
                                Addr::HeapCell(hc) if hc >= old_h => {
                                    self[threshold] = HeapCellValue::Addr(rd);
                                },
                                addr @ Addr::HeapCell(..) | addr @ Addr::StackCell(..) => {
                                    if rd == addr {
                                        self.reinstantiate_var(addr, threshold, &mut trail);
                                    } else {
                                        self[threshold] = HeapCellValue::Addr(addr);
                                    }
                                },
                                _ => {
                                    trail.push((Ref::HeapCell(a), self[a].clone()));
                                    self[a] = HeapCellValue::Addr(Addr::Lis(threshold))
                                }
                            };

                            let hcv = self[a+1].clone();
                            self.push(hcv);

                            scan += 1;
                        },
                        Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                            let ra = a;
                            let rd = self.store(self.deref(ra.clone()));

                            match rd.clone() {
                                Addr::AttrVar(h) | Addr::HeapCell(h) if h >= old_h => {
                                    self[scan] = HeapCellValue::Addr(rd);
                                    scan += 1;
                                },
                                _ if ra == rd => {
                                    self.reinstantiate_var(ra, scan, &mut trail);

                                    if let Addr::AttrVar(h) = rd {
                                        let value = self[h + 1].clone();
                                        self.push(value);
                                    }

                                    scan += 1;
                                },
                                _ => self[scan] = HeapCellValue::Addr(rd)
                            };
                        },
                        Addr::Str(s) => {
                            match self[s].clone() {
                                HeapCellValue::NamedStr(arity, name, fixity) => {
                                    let threshold = self.threshold();

                                    self[scan] = HeapCellValue::Addr(Addr::Str(threshold));
                                    self[s] = HeapCellValue::Addr(Addr::Str(threshold));

                                    trail.push((Ref::HeapCell(s),
                                                HeapCellValue::NamedStr(arity, name.clone(), fixity)));

                                    self.push(HeapCellValue::NamedStr(arity, name, fixity));

                                    for i in 0 .. arity {
                                        let hcv = self[s + 1 + i].clone();
                                        self.push(hcv);
                                    }
                                },
                                HeapCellValue::Addr(Addr::Str(o)) =>
                                    self[scan] = HeapCellValue::Addr(Addr::Str(o)),
                                _ => {}
                            };

                            scan += 1;
                        },
                        Addr::Con(_) => scan += 1
                    }
            }
        }

        RedirectInfo { trail }
    }

    fn duplicate_term(&mut self, addr: Addr)
    {
        let redirect = self.duplicate_term_impl(addr);
        self.unwind_trail(redirect);
    }
}
