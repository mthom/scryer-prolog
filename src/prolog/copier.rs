use prolog::and_stack::*;
use prolog::ast::*;

use std::collections::HashMap;
use std::ops::IndexMut;

pub type Trail = Vec<(Ref, HeapCellValue)>;

pub struct RedirectInfo {
    trail: Trail,
    list_redirect: HashMap<usize, usize>,
    offset: usize
}

// allows us to reconstruct a HeapVarDict by relating variables
// in an existing HeapVarDict to the ones created in fn duplicate_term.
// It is used to create meaningful error reports at the toplevel.
pub struct CellRedirect(pub HashMap<Addr, Addr>);

impl CellRedirect {
    pub fn new() -> Self {
        CellRedirect(HashMap::new())
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }
}

pub trait CopierTarget
{
    fn source(&self) -> usize;
    fn threshold(&self) -> usize;
    fn push(&mut self, HeapCellValue);
    fn store(&self, Addr) -> Addr;
    fn deref(&self, Addr) -> Addr;
    fn stack(&mut self) -> &mut AndStack;

    // unwind the trail *and* compute a cell redirection table.
    fn unwind_and_redirect(&mut self, redirect: RedirectInfo) -> CellRedirect
      where Self: IndexMut<usize, Output=HeapCellValue>
    {
        let mut cell_redirect: HashMap<Addr, Addr> = HashMap::new();

        for (r, hcv) in redirect.trail {
            let addr = Addr::from(r);

            match r {
                Ref::HeapCell(h) => {
                    cell_redirect.insert(addr, self[h].as_addr(h) - redirect.offset);
                    self[h] = hcv;
                },
                Ref::StackCell(fr, sc) => {
                    cell_redirect.insert(addr, self.stack()[fr][sc].clone() - redirect.offset);
                    self.stack()[fr][sc] = hcv.as_addr(0);
                }
            };
        }

        for (l, h) in redirect.list_redirect {
            cell_redirect.insert(Addr::Lis(l), Addr::Lis(h - redirect.offset));
        }

        CellRedirect(cell_redirect)
    }

    fn unwind_trail(&mut self, redirect: RedirectInfo)
      where Self: IndexMut<usize, Output=HeapCellValue>
    {
        for (r, hcv) in redirect.trail {
            match r {
                Ref::HeapCell(hc) => self[hc] = hcv.clone(),
                Ref::StackCell(fr, sc) => self.stack()[fr][sc] = hcv.as_addr(0)
            }
        }
    }

    // duplicate_term_impl(L1, L2) uses Cheney's algorithm to copy the term
    // at L1 to L2. trail is kept to restore the innards of L1 after
    // it's been copied to L2.
    fn duplicate_term_impl(&mut self, addr: Addr) -> RedirectInfo
      where Self: IndexMut<usize, Output=HeapCellValue>
    {
        let mut trail = Trail::new();
        let mut scan = self.source();
        let old_h = self.threshold();

        // Lists have a compressed representation as structures,
        // removing the need for NamedStr, so we use a redirection
        // table for copying lists.
        let mut list_redirect = HashMap::new();

        self.push(HeapCellValue::Addr(addr));

        while scan < self.threshold() {
            match self[scan].clone() {
                HeapCellValue::NamedStr(..) =>
                    scan += 1,
                HeapCellValue::Addr(a) =>
                    match a.clone() {
                        Addr::Lis(a) => {
                            if let Some(idx) = list_redirect.get(&a) {
                                self[scan] = HeapCellValue::Addr(Addr::Lis(*idx));
                                scan += 1;
                                continue;
                            }

                            list_redirect.insert(a, self.threshold());
                            self[scan] = HeapCellValue::Addr(Addr::Lis(self.threshold()));

                            let hcv = self[a].clone();
                            self.push(hcv);

                            let hcv = self[a+1].clone();
                            self.push(hcv);

                            scan += 1;
                        },
                        Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                            let ra = a;
                            let rd = self.store(self.deref(ra.clone()));

                            match rd.clone() {
                                Addr::HeapCell(hc) if hc >= old_h => {
                                    self[scan] = HeapCellValue::Addr(rd);
                                    scan += 1;
                                },
                                _ if ra == rd => {
                                    self[scan] = HeapCellValue::Addr(Addr::HeapCell(scan));

                                    if let Addr::HeapCell(hc) = ra.clone() {
                                        self[hc] = HeapCellValue::Addr(Addr::HeapCell(scan));
                                        trail.push((Ref::HeapCell(hc),
                                                    HeapCellValue::Addr(Addr::HeapCell(hc))));
                                    } else if let Addr::StackCell(fr, sc) = ra {
                                        self.stack()[fr][sc] = Addr::HeapCell(scan);
                                        trail.push((Ref::StackCell(fr, sc),
                                                    HeapCellValue::Addr(Addr::StackCell(fr, sc))));
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

        RedirectInfo { trail, list_redirect, offset: old_h }
    }

    fn duplicate_term_and_redirect(&mut self, addr: Addr) -> CellRedirect
      where Self: IndexMut<usize, Output=HeapCellValue>
    {
        let redirect = self.duplicate_term_impl(addr);
        self.unwind_and_redirect(redirect)
    }

    fn duplicate_term(&mut self, addr: Addr)
      where Self: IndexMut<usize, Output=HeapCellValue>
    {
        let redirect = self.duplicate_term_impl(addr);
        self.unwind_trail(redirect);
    }
}
