use prolog::ast::*;
use prolog::machine::machine_state::MachineState;

use std::collections::HashSet;
use std::vec::Vec;

pub struct HCPreOrderIterator<'a> {
    machine_st: &'a MachineState,
    state_stack: Vec<Addr>
}

impl<'a> HCPreOrderIterator<'a> {
    pub fn new(machine_st: &'a MachineState, a: Addr) -> Self
    {
        HCPreOrderIterator {
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

impl<'a> Iterator for HCPreOrderIterator<'a> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        self.state_stack.pop().map(|a| {
            match self.follow(a) {
                Addr::HeapCell(h) =>
                    self.machine_st.heap[h].clone(),
                Addr::StackCell(fr, sc) =>
                    HeapCellValue::Addr(self.machine_st.and_stack[fr][sc].clone()),
                da =>
                    HeapCellValue::Addr(da)
            }
        })
    }
}

pub struct HCPostOrderIterator<'a> {
    pre_iter:     HCPreOrderIterator<'a>,
    parent_stack: Vec<(usize, HeapCellValue)> // number of children, parent node.
}

impl<'a> HCPostOrderIterator<'a> {
    pub fn new(pre_iter: HCPreOrderIterator<'a>) -> Self {
        HCPostOrderIterator {
            pre_iter,
            parent_stack: vec![]
        }
    }
}

impl<'a> Iterator for HCPostOrderIterator<'a> {
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
    pub fn pre_order_iter<'a>(&'a self, a: Addr) -> HCPreOrderIterator<'a> {
        HCPreOrderIterator::new(self, a)
    }

    pub fn post_order_iter<'a>(&'a self, a: Addr) -> HCPostOrderIterator<'a> {
        HCPostOrderIterator::new(HCPreOrderIterator::new(self, a))
    }

    pub fn acyclic_pre_order_iter<'a>(&'a self, a: Addr)
                                      -> HCAcyclicIterator<HCPreOrderIterator<'a>>
    {
        HCAcyclicIterator::new(HCPreOrderIterator::new(self, a))
    }

    pub fn zipped_acyclic_pre_order_iter<'a>(&'a self, a1: Addr, a2: Addr)
                                             -> HCZippedAcyclicIterator<HCPreOrderIterator<'a>>
    {
        HCZippedAcyclicIterator::new(HCPreOrderIterator::new(self, a1),
                                     HCPreOrderIterator::new(self, a2))
    }
}

pub trait MutStackHCIterator {
    fn stack(&mut self) -> &mut Vec<Addr>;
}

impl<'a> MutStackHCIterator for HCPreOrderIterator<'a> {
    fn stack(&mut self) -> &mut Vec<Addr> {
        &mut self.state_stack
    }
}

pub struct HCAcyclicIterator<HCIter> {
    iter: HCIter,
    seen: HashSet<Addr>
}

impl<HCIter: MutStackHCIterator> HCAcyclicIterator<HCIter>
{
    pub fn new(iter: HCIter) -> Self {
        HCAcyclicIterator { iter, seen: HashSet::new() }
    }
}

impl<HCIter> Iterator for HCAcyclicIterator<HCIter>
where HCIter: Iterator<Item=HeapCellValue> + MutStackHCIterator
{
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(addr) = self.iter.stack().pop() {
            if !self.seen.contains(&addr) {
                self.iter.stack().push(addr.clone());
                self.seen.insert(addr);
                break;
            }
        }

        self.iter.next()
    }
}

pub struct HCZippedAcyclicIterator<HCIter> {
    i1: HCIter,
    i2: HCIter,
    seen: HashSet<(Addr, Addr)>
}

impl<HCIter: MutStackHCIterator> HCZippedAcyclicIterator<HCIter>
{
    pub fn new(i1: HCIter, i2: HCIter) -> Self {
        HCZippedAcyclicIterator { i1, i2, seen: HashSet::new() }
    }
}

impl<HCIter> Iterator for HCZippedAcyclicIterator<HCIter>
where HCIter: Iterator<Item=HeapCellValue> + MutStackHCIterator
{
    type Item = (HeapCellValue, HeapCellValue);

    fn next(&mut self) -> Option<Self::Item> {
        while let (Some(a1), Some(a2)) = (self.i1.stack().pop(), self.i2.stack().pop()) {
            if !self.seen.contains(&(a1.clone(), a2.clone())) {
                self.i1.stack().push(a1.clone());
                self.i2.stack().push(a2.clone());
                self.seen.insert((a1, a2));

                break;
            }
        }

        if let (Some(v1), Some(v2)) = (self.i1.next(), self.i2.next()) {
            Some((v1, v2))
        } else {
            None
        }
    }
}
