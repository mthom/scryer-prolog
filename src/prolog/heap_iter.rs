use prolog_parser::ast::*;

use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;

use indexmap::IndexSet;

use std::cmp::Ordering;
use std::ops::Deref;
use std::vec::Vec;

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

    pub fn machine_st(&self) -> &MachineState {
        &self.machine_st
    }

    fn follow_heap(&mut self, h: usize) -> Addr {
        match &self.machine_st.heap[h] {
            HeapCellValue::NamedStr(arity, _, _) => {
                for idx in (1..arity + 1).rev() {
                    self.state_stack.push(Addr::HeapCell(h + idx));
                }

                Addr::Str(h)
            }
            HeapCellValue::Addr(ref a) => {
                self.follow(a.clone())
            }
            HeapCellValue::PartialString(_) => {
                self.follow(Addr::PStrLocation(h, 0))
            }
        }
    }

    // called under the assumption that the location at r is about to
    // be visited, and so any follow up states need to be added to
    // state_stack. returns the dereferenced Addr from Ref.
    fn follow(&mut self, addr: Addr) -> Addr {
        let da = self.machine_st.store(self.machine_st.deref(addr));

        match da {
            Addr::Con(Constant::String(n, s)) => {
                if !self.machine_st.machine_flags().double_quotes.is_atom() {
                    if s.len() > n {
                        if let Some(c) = s[n ..].chars().next() {
                            let o = c.len_utf8();

                            self.state_stack.push(Addr::Con(Constant::String(n+o, s.clone())));

                            if self.machine_st.machine_flags().double_quotes.is_codes() {
                                self.state_stack.push(Addr::Con(Constant::CharCode(c as u32)));
                            } else {
                                self.state_stack.push(Addr::Con(Constant::Char(c)));
                            }
                        }
                    } else {
                        return Addr::Con(Constant::EmptyList);
                    }
                }

                Addr::Con(Constant::String(n, s))
            }
            Addr::Con(_) | Addr::DBRef(_) | Addr::Stream(_) => {
                da
            }
            Addr::Lis(a) => {
                self.state_stack.push(Addr::HeapCell(a + 1));
                self.state_stack.push(Addr::HeapCell(a));

                da
            }
            Addr::PStrLocation(h, n) => {
                if let HeapCellValue::PartialString(ref pstr) = &self.machine_st.heap[h] {
                    let s = pstr.block_as_str();
                    
                    if let Some(c) = s[n ..].chars().next() {
                        if pstr.len() > n + c.len_utf8() {                        
                            self.state_stack.push(Addr::PStrLocation(h, n + c.len_utf8()));
                        } else {
                            self.state_stack.push(Addr::HeapCell(h + 1));
                        }

                        self.state_stack.push(Addr::Con(Constant::Char(c)));
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }

                Addr::PStrLocation(h, n)
            }
            Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                da
            }
            Addr::Str(s) => {
                self.follow_heap(s) // record terms of structure.
            }
        }
    }
}

impl<'a> Iterator for HCPreOrderIterator<'a> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        self.state_stack.pop().map(|a| match self.follow(a) {
            Addr::HeapCell(h) => {
                HeapCellValue::Addr(self.machine_st.heap[h].as_addr(h))
            }
            Addr::Str(s) => {
                match &self.machine_st.heap[s] {
                    val @ HeapCellValue::NamedStr(..) => {
                        val.clone()
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            Addr::StackCell(fr, sc) => {
                HeapCellValue::Addr(self.machine_st.stack.index_and_frame(fr)[sc].clone())
            }
            da => {
                HeapCellValue::Addr(da)
            }
        })
    }
}

pub trait MutStackHCIterator
where
    Self: Iterator<Item = HeapCellValue>,
{
    fn stack(&mut self) -> &mut Vec<Addr>;
}

pub struct HCPostOrderIterator<HCIter> {
    base_iter: HCIter,
    parent_stack: Vec<(usize, HeapCellValue)>, // number of children, parent node.
}

impl<HCIter> Deref for HCPostOrderIterator<HCIter> {
    type Target = HCIter;

    fn deref(&self) -> &Self::Target {
        &self.base_iter
    }
}

impl<HCIter: Iterator<Item = HeapCellValue>> HCPostOrderIterator<HCIter> {
    pub fn new(base_iter: HCIter) -> Self {
        HCPostOrderIterator {
            base_iter,
            parent_stack: vec![],
        }
    }
}

impl<HCIter: Iterator<Item = HeapCellValue>> Iterator for HCPostOrderIterator<HCIter> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((child_count, node)) = self.parent_stack.pop() {
                if child_count == 0 {
                    return Some(node);
                }

                self.parent_stack.push((child_count - 1, node));
            }

            if let Some(item) = self.base_iter.next() {
                match item {
                    HeapCellValue::NamedStr(arity, name, fix) => self
                        .parent_stack
                        .push((arity, HeapCellValue::NamedStr(arity, name, fix))),
                    HeapCellValue::Addr(Addr::Lis(a)) => self
                        .parent_stack
                        .push((2, HeapCellValue::Addr(Addr::Lis(a)))),
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

pub type HCProperPostOrderIterator<'a> = HCPostOrderIterator<HCPreOrderIterator<'a>>;

impl MachineState {
    pub fn pre_order_iter<'a>(&'a self, a: Addr) -> HCPreOrderIterator<'a> {
        HCPreOrderIterator::new(self, a)
    }

    pub fn post_order_iter<'a>(&'a self, a: Addr) -> HCProperPostOrderIterator<'a> {
        HCPostOrderIterator::new(HCPreOrderIterator::new(self, a))
    }

    pub fn acyclic_pre_order_iter<'a>(
        &'a self,
        a: Addr,
    ) -> HCAcyclicIterator<HCPreOrderIterator<'a>> {
        HCAcyclicIterator::new(HCPreOrderIterator::new(self, a))
    }

    pub fn zipped_acyclic_pre_order_iter<'a>(
        &'a self,
        a1: Addr,
        a2: Addr,
    ) -> HCZippedAcyclicIterator<HCPreOrderIterator<'a>> {
        HCZippedAcyclicIterator::new(
            HCPreOrderIterator::new(self, a1),
            HCPreOrderIterator::new(self, a2),
        )
    }
}

impl<'a> MutStackHCIterator for HCPreOrderIterator<'a> {
    fn stack(&mut self) -> &mut Vec<Addr> {
        &mut self.state_stack
    }
}

pub struct HCAcyclicIterator<HCIter> {
    iter: HCIter,
    seen: IndexSet<Addr>,
}

impl<HCIter: MutStackHCIterator> HCAcyclicIterator<HCIter> {
    pub fn new(iter: HCIter) -> Self {
        HCAcyclicIterator {
            iter,
            seen: IndexSet::new(),
        }
    }
}

impl<HCIter> Deref for HCAcyclicIterator<HCIter> {
    type Target = HCIter;

    fn deref(&self) -> &Self::Target {
        &self.iter
    }
}

impl<HCIter> Iterator for HCAcyclicIterator<HCIter>
where
    HCIter: Iterator<Item = HeapCellValue> + MutStackHCIterator,
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
    seen: IndexSet<(Addr, Addr)>,
    pub first_to_expire: Ordering,
}

impl<HCIter: MutStackHCIterator> HCZippedAcyclicIterator<HCIter> {
    pub fn new(i1: HCIter, i2: HCIter) -> Self {
        HCZippedAcyclicIterator {
            i1,
            i2,
            seen: IndexSet::new(),
            first_to_expire: Ordering::Equal,
        }
    }
}

impl<HCIter> Iterator for HCZippedAcyclicIterator<HCIter>
where
    HCIter: Iterator<Item = HeapCellValue> + MutStackHCIterator,
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
            _ => None,
        }
    }
}
