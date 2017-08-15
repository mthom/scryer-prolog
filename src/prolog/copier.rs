use prolog::and_stack::*;
use prolog::ast::*;

use std::ops::IndexMut;

pub trait CopierTarget
{
    fn source(&self) -> usize;
    fn threshold(&self) -> usize;
    fn push(&mut self, HeapCellValue);
    fn store(&self, Addr) -> Addr;
    fn deref(&self, Addr) -> Addr;
    fn stack(&mut self) -> &mut AndStack;

    // duplicate_term(L1, L2) uses Cheney's algorithm to copy the term at
    // L1 to L2. forwarding_terms is kept to restore the innards of L1
    // after it's been copied to L2.
    fn duplicate_term(&mut self, a: Addr) where Self: IndexMut<usize, Output=HeapCellValue>
    {
        let mut forward_trail: Vec<(Ref, HeapCellValue)>= Vec::new();
        let mut scan = self.source();
        let old_h = self.threshold();

        self.push(HeapCellValue::from(a));

        while scan < self.threshold() {
            match self[scan].clone() {
                HeapCellValue::Con(_) | HeapCellValue::NamedStr(_, _) =>
                    scan += 1,
                HeapCellValue::Lis(a) => {
                    self[scan] = HeapCellValue::Lis(self.threshold());

                    let hcv = self[a].clone();
                    self.push(hcv);

                    let hcv = self[a+1].clone();
                    self.push(hcv);

                    scan += 1;
                },
                HeapCellValue::Ref(r) => {
                    let ra = Addr::from(r);
                    let rd = self.store(self.deref(ra.clone()));

                    match rd {
                        Addr::HeapCell(hc) if hc >= old_h => {
                            self[scan] = HeapCellValue::Ref(Ref::HeapCell(hc));
                            scan += 1;
                        },
                        _ if ra == rd => {
                            self[scan] = HeapCellValue::Ref(Ref::HeapCell(scan));

                            match r {
                                Ref::HeapCell(hc) =>
                                    self[hc] = HeapCellValue::Ref(Ref::HeapCell(scan)),
                                Ref::StackCell(fr, sc) =>
                                    self.stack()[fr][sc] = Addr::HeapCell(scan)
                            };

                            forward_trail.push((r, HeapCellValue::Ref(r)));
                            scan += 1;
                        },
                        _ => self[scan] = HeapCellValue::from(rd)
                    }
                },
                HeapCellValue::Str(s) => {
                    match self[s].clone() {
                        HeapCellValue::NamedStr(arity, name) => {
                            let threshold = self.threshold();
                            
                            self[scan] = HeapCellValue::Str(threshold);
                            self[s] = HeapCellValue::Str(threshold);

                            forward_trail.push((Ref::HeapCell(s),
                                                HeapCellValue::NamedStr(arity, name.clone())));

                            self.push(HeapCellValue::NamedStr(arity, name));

                            for i in 0 .. arity {
                                let hcv = self[s + 1 + i].clone();
                                self.push(hcv);
                            }
                        },
                        HeapCellValue::Str(o) =>
                            self[scan] = HeapCellValue::Str(o),
                        _ => {}
                    };

                    scan += 1;
                }
            };
        }   
        
        for (r, hcv) in forward_trail {
            match r {
                Ref::HeapCell(hc) => self[hc] = hcv,
                Ref::StackCell(fr, sc) => self.stack()[fr][sc] = hcv.as_addr(0)
            }
        }
    }
}
    
