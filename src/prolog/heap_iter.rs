use prolog::ast::*;
use prolog::machine::machine_state::MachineState;

use std::vec::Vec;

pub struct HeapCellIterator<'a> {
    machine_st  : &'a MachineState,
    state_stack : Vec<Ref>
}

impl<'a> HeapCellIterator<'a> {
    pub fn new(machine_st: &'a MachineState, r: Ref) -> Self
    {
        let mut iter = HeapCellIterator {
            machine_st,
            state_stack: vec![]
        };

        iter.state_stack.push(r);
        iter
    }

    // called under the assumption that the location at r is about to
    // be visited, and so any follow up states need to be added to
    // state_stack. returns the dereferenced Addr from Ref.
    fn follow(&mut self, r: Ref) -> Addr
    {
        match r {
            Ref::HeapCell(hc)      => self.follow_heap(hc),
            Ref::StackCell(fr, sc) => self.follow_addr(Addr::StackCell(fr, sc))
        }
    }

    fn follow_heap(&mut self, h: usize) -> Addr
    {
        match &self.machine_st.heap[h] {
            &HeapCellValue::NamedStr(arity, _, _) => {
                for idx in (1 .. arity + 1).rev() {
                    self.state_stack.push(Ref::HeapCell(h + idx));
                }

                Addr::HeapCell(h)
            },
            &HeapCellValue::Addr(ref a) =>
                self.follow_addr(a.clone())
        }
    }

    fn follow_addr(&mut self, addr: Addr) -> Addr
    {
        let da = self.machine_st.store(self.machine_st.deref(addr));

        match &da {
            &Addr::Con(_) => da,
            &Addr::Lis(a) => {
                self.state_stack.push(Ref::HeapCell(a + 1));
                self.state_stack.push(Ref::HeapCell(a));

                da
            },
            &Addr::HeapCell(_) | &Addr::StackCell(_, _) =>
                da,
            &Addr::Str(s) => {
                self.follow_heap(s); // record terms of structure.
                Addr::HeapCell(s)
            }
        }        
    }
}

impl<'a> Iterator for HeapCellIterator<'a> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(r) = self.state_stack.pop() {
            match self.follow(r) {
                Addr::HeapCell(h) => Some(self.machine_st.heap[h].clone()),
                Addr::StackCell(fr, sc) => {
                    let heap_val = HeapCellValue::Addr(self.machine_st.and_stack[fr][sc].clone());
                    Some(heap_val)
                },
                da => Some(HeapCellValue::Addr(da))
            }
        } else {
            None
        }
    }
}
