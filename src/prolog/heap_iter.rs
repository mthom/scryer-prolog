use prolog::ast::*;
use prolog::machine::machine_state::MachineState;

use std::collections::HashSet;
use std::vec::Vec;

pub struct HeapCellPreOrderIterator<'a> {
    machine_st: &'a MachineState,
    state_stack: Vec<Addr>
}

impl<'a> HeapCellPreOrderIterator<'a> {
    pub fn new(machine_st: &'a MachineState, a: Addr) -> Self
    {
        HeapCellPreOrderIterator {
            machine_st, state_stack: vec![a]
        }
    }

    fn follow_heap(&mut self, h: usize) -> Addr
    {
        match &self.machine_st.heap[h] {
            &HeapCellValue::NamedStr(arity, _, _) => {
                for idx in (1 .. arity + 1).rev() {
                    self.state_stack.push(Addr::HeapCell(h + idx));
                }

                Addr::HeapCell(h)
            },
            &HeapCellValue::Addr(ref a) =>
                self.follow(a.clone())
        }
    }

    // called under the assumption that the location at r is about to
    // be visited, and so any follow up states need to be added to
    // state_stack. returns the dereferenced Addr from Ref.
    fn follow(&mut self, addr: Addr) -> Addr
    {
        let da = self.machine_st.store(self.machine_st.deref(addr));

        match &da {
            &Addr::Con(_) => da,
            &Addr::Lis(a) => {
                self.state_stack.push(Addr::HeapCell(a + 1));
                self.state_stack.push(Addr::HeapCell(a));

                da
            },
            &Addr::HeapCell(_) | &Addr::StackCell(_, _) =>
                da,
            &Addr::Str(s) =>
                self.follow_heap(s) // record terms of structure.
        }
    }
}

impl<'a> Iterator for HeapCellPreOrderIterator<'a> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(a) = self.state_stack.pop() {
            match self.follow(a) {
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

pub struct HeapCellPostOrderIterator<'a> {
    pre_iter:     HeapCellPreOrderIterator<'a>,
    parent_stack: Vec<(usize, HeapCellValue)> // number of children, parent node.
}

impl<'a> HeapCellPostOrderIterator<'a> {
    pub fn new(pre_iter: HeapCellPreOrderIterator<'a>) -> Self {
        HeapCellPostOrderIterator {
            pre_iter,
            parent_stack: vec![]
        }
    }
}

impl<'a> Iterator for HeapCellPostOrderIterator<'a> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((child_count, node)) = self.parent_stack.pop() {
                if child_count == 0 {
                    return Some(node);
                }

                self.parent_stack.push((child_count - 1, node));
            }

            if let Some(item) = self.pre_iter.next() {
                match item {
                    HeapCellValue::NamedStr(arity, name, fix) =>
                        self.parent_stack.push((arity, HeapCellValue::NamedStr(arity, name, fix))),
                    HeapCellValue::Addr(Addr::Lis(a)) =>
                        self.parent_stack.push((2, HeapCellValue::Addr(Addr::Lis(a)))),
                    child_node => {
                        return Some(child_node);
                    }
                }
            } else {
                return None;
            }
        }
    }
}

impl MachineState {
    pub fn post_order_iter<'a>(&'a self, a: Addr) -> HeapCellPostOrderIterator<'a> {
        HeapCellPostOrderIterator::new(HeapCellPreOrderIterator::new(self, a))
    }

    pub fn acyclic_pre_order_iter<'a>(&'a self, a: Addr) -> HeapCellAcyclicIterator<HeapCellPreOrderIterator<'a>>
    {
        HeapCellAcyclicIterator::new(HeapCellPreOrderIterator::new(self, a))
    }
}

pub trait MutStackHeapCellIterator {
    fn stack(&mut self) -> &mut Vec<Addr>;
}

impl<'a> MutStackHeapCellIterator for HeapCellPreOrderIterator<'a> {
    fn stack(&mut self) -> &mut Vec<Addr> {
        &mut self.state_stack
    }
}

pub struct HeapCellAcyclicIterator<HeapCellIter> {
    iter: HeapCellIter,
    seen: HashSet<Addr>
}

impl<HeapCellIter: MutStackHeapCellIterator> HeapCellAcyclicIterator<HeapCellIter>
{
    pub fn new(mut iter: HeapCellIter) -> Self {
        let mut seen = HashSet::new();

        if let Some(addr) = iter.stack().last() {
            seen.insert(addr.clone());
        }

        HeapCellAcyclicIterator { iter, seen }
    }
}

impl<HeapCellIter> Iterator for HeapCellAcyclicIterator<HeapCellIter>
    where HeapCellIter: Iterator<Item=HeapCellValue>
                      + MutStackHeapCellIterator
{
    type Item = HeapCellValue;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(hcv) = self.iter.next() {
            if let Some(addr) = self.iter.stack().pop() {
                if self.seen.contains(&addr) {
                    continue;
                } else {
                    self.iter.stack().push(addr.clone());
                    self.seen.insert(addr);
                }
            }

            return Some(hcv);
        }

        None
    }
}
