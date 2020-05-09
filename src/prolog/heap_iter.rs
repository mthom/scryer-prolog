use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;

use indexmap::IndexSet;

use std::cmp::Ordering;
use std::ops::Deref;
use std::vec::Vec;

#[derive(Debug)]
pub struct HCPreOrderIterator<'a> {
    pub machine_st: &'a MachineState,
    pub state_stack: Vec<Addr>,
}

impl<'a> HCPreOrderIterator<'a> {
    pub fn new(machine_st: &'a MachineState, a: Addr) -> Self {
        HCPreOrderIterator {
            machine_st,
            state_stack: vec![a],
        }
    }

    #[inline]
    pub fn machine_st(&self) -> &MachineState {
        &self.machine_st
    }

    fn follow_heap(&mut self, h: usize) -> Addr {
        match &self.machine_st.heap[h] {
            &HeapCellValue::NamedStr(arity, _, _) => {
                for idx in (1 .. arity + 1).rev() {
                    self.state_stack.push(Addr::HeapCell(h + idx));
                }

                Addr::Str(h)
            }
            &HeapCellValue::Addr(a) => {
                self.follow(a)
            }
            HeapCellValue::PartialString(..) => {
                self.follow(Addr::PStrLocation(h, 0))
            }
            HeapCellValue::Atom(..) | HeapCellValue::DBRef(_)
          | HeapCellValue::Integer(_) | HeapCellValue::Rational(_) => {
                Addr::Con(h)
            }
            HeapCellValue::Stream(_) => {
                Addr::Stream(h)
            }
            &HeapCellValue::TcpListener(_) => {
                Addr::TcpListener(h)
            }
        }
    }

    // called under the assumption that the location at r is about to
    // be visited, and so any follow up states need to be added to
    // state_stack. returns the dereferenced Addr from Ref.
    fn follow(&mut self, addr: Addr) -> Addr {
        let da = self.machine_st.store(self.machine_st.deref(addr));

        match da {
            Addr::Lis(a) => {
                self.state_stack.push(Addr::HeapCell(a + 1));
                self.state_stack.push(Addr::HeapCell(a));

                da
            }
            Addr::PStrLocation(h, n) => {
                if let &HeapCellValue::PartialString(ref pstr, has_tail) = &self.machine_st.heap[h] {
                    if let Some(c) = pstr.range_from(n ..).next() {
                        if !pstr.at_end(n + c.len_utf8()) {
                            self.state_stack.push(Addr::PStrLocation(h, n + c.len_utf8()));
                        } else if has_tail {
                            self.state_stack.push(Addr::HeapCell(h + 1));
                        } else {
                            self.state_stack.push(Addr::EmptyList);
                        }

                        self.state_stack.push(Addr::Char(c));
                    } else if has_tail {
                        return self.follow(Addr::HeapCell(h + 1));
                    }
                } else {
                    unreachable!()
                }

                Addr::PStrLocation(h, n)
            }
            Addr::Str(s) => {
                self.follow_heap(s) // record terms of structure.
            }
            Addr::Con(h) => {
                if let &HeapCellValue::PartialString(ref pstr, has_tail) = &self.machine_st.heap[h] {
                    if !self.machine_st.flags.double_quotes.is_atom() {
                        return if let Some(c) = pstr.range_from(0 ..).next() {
                            self.state_stack.push(Addr::PStrLocation(h, c.len_utf8()));
                            self.state_stack.push(Addr::Char(c));

                            Addr::PStrLocation(h, 0)
                        } else if has_tail {
                            self.follow(Addr::HeapCell(h + 1))
                        } else {
                            Addr::EmptyList
                        };
                    }
                }

                Addr::Con(h)
            }
            da => {
                da
            }
        }
    }
}

impl<'a> Iterator for HCPreOrderIterator<'a> {
    type Item = Addr;

    fn next(&mut self) -> Option<Self::Item> {
        self.state_stack.pop().map(|a| self.follow(a))
    }
}

pub trait MutStackHCIterator<'b> where Self: Iterator
{
    type MutStack;

    fn stack(&'b mut self) -> Self::MutStack;
}

#[derive(Debug)]
pub struct HCPostOrderIterator<'a> {
    base_iter: HCPreOrderIterator<'a>,
    parent_stack: Vec<(usize, Addr)>, // number of children, parent node.
}

impl<'a> Deref for HCPostOrderIterator<'a> {
    type Target = HCPreOrderIterator<'a>;

    fn deref(&self) -> &Self::Target {
        &self.base_iter
    }
}

impl<'a> HCPostOrderIterator<'a> {
    pub fn new(base_iter: HCPreOrderIterator<'a>) -> Self {
        HCPostOrderIterator {
            base_iter,
            parent_stack: vec![],
        }
    }
}

impl<'a> Iterator for HCPostOrderIterator<'a> {
    type Item = Addr;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((child_count, node)) = self.parent_stack.pop() {
                if child_count == 0 {
                    return Some(node);
                }

                self.parent_stack.push((child_count - 1, node));
            }

            if let Some(item) = self.base_iter.next() {
                match self.base_iter.machine_st.heap.index_addr(&item).as_ref() {
                    &HeapCellValue::NamedStr(arity, ..) => {
                        self.parent_stack.push((arity, item));
                    }
                    &HeapCellValue::Addr(Addr::Lis(a)) => {
                        self.parent_stack.push((2, Addr::Lis(a)));
                    }
                    &HeapCellValue::Addr(Addr::PStrLocation(h, n)) => {
                        match &self.machine_st.heap[h] {
                            &HeapCellValue::PartialString(ref pstr, _) => {
                                let c = pstr.range_from(n ..).next().unwrap();
                                let next_n = n + c.len_utf8();

                                if !pstr.at_end(next_n) {
                                    self.parent_stack.push((2, Addr::PStrLocation(h, next_n)));
                                }
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                    _ => {
                        return Some(item);
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

    pub fn acyclic_pre_order_iter<'a>(&'a self, a: Addr,) -> HCAcyclicIterator<'a> {
        HCAcyclicIterator::new(HCPreOrderIterator::new(self, a))
    }

    pub fn zipped_acyclic_pre_order_iter<'a>(
        &'a self,
        a1: Addr,
        a2: Addr,
    ) -> HCZippedAcyclicIterator<'a> {
        HCZippedAcyclicIterator::new(
            HCPreOrderIterator::new(self, a1),
            HCPreOrderIterator::new(self, a2),
        )
    }
}

impl<'b, 'a: 'b> MutStackHCIterator<'b> for HCPreOrderIterator<'a> {
    type MutStack = &'b mut Vec<Addr>;

    fn stack(&'b mut self) -> Self::MutStack {
        &mut self.state_stack
    }
}

#[derive(Debug)]
pub struct HCAcyclicIterator<'a> {
    iter: HCPreOrderIterator<'a>,
    seen: IndexSet<Addr>,
}

impl<'a> HCAcyclicIterator<'a> {
    pub fn new(iter: HCPreOrderIterator<'a>) -> Self {
        HCAcyclicIterator {
            iter,
            seen: IndexSet::new(),
        }
    }
}

impl<'a> Deref for HCAcyclicIterator<'a> {
    type Target = HCPreOrderIterator<'a>;

    fn deref(&self) -> &Self::Target {
        &self.iter
    }
}

impl<'b, 'a: 'b> MutStackHCIterator<'b> for HCAcyclicIterator<'a> {
    type MutStack = &'b mut Vec<Addr>;

    fn stack(&'b mut self) -> Self::MutStack {
        self.iter.stack()
    }
}

impl<'a> Iterator for HCAcyclicIterator<'a>
{
    type Item = Addr;

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

#[derive(Debug)]
pub struct HCZippedAcyclicIterator<'a> {
    i1: HCPreOrderIterator<'a>,
    i2: HCPreOrderIterator<'a>,
    seen: IndexSet<(Addr, Addr)>,
    pub first_to_expire: Ordering,
}

impl<'b, 'a: 'b> MutStackHCIterator<'b> for HCZippedAcyclicIterator<'a> {
    type MutStack = (&'b mut Vec<Addr>, &'b mut Vec<Addr>);

    fn stack(&'b mut self) -> Self::MutStack {
        (self.i1.stack(), self.i2.stack())
    }
}

impl<'a> HCZippedAcyclicIterator<'a> {
    pub fn new(i1: HCPreOrderIterator<'a>, i2: HCPreOrderIterator<'a>) -> Self {
        HCZippedAcyclicIterator {
            i1,
            i2,
            seen: IndexSet::new(),
            first_to_expire: Ordering::Equal,
        }
    }
}

impl<'a> Iterator for HCZippedAcyclicIterator<'a>
{
    type Item = (Addr, Addr);

    fn next(&mut self) -> Option<Self::Item> {
        while let (Some(a1), Some(a2)) = (self.i1.stack().pop(), self.i2.stack().pop()) {
            if !self.seen.contains(&(a1.clone(), a2.clone())) {
                self.i1.stack().push(a1.clone());
                self.i2.stack().push(a2.clone());

                self.seen.insert((a1, a2));

                break;
            }
        }

        match (self.i1.next(), self.i2.next()) {
            (Some(v1), Some(v2)) => Some((v1, v2)),
            (Some(_), None) => {
                self.first_to_expire = Ordering::Greater;
                None
            }
            (None, Some(_)) => {
                self.first_to_expire = Ordering::Less;
                None
            }
            _ => {
                None
            }
        }
    }
}
