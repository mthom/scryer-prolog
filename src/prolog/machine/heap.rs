use prolog_parser::ast::*;

use prolog::machine::machine_indices::*;

use std::mem;
use std::ops::{Index, IndexMut};

pub struct Heap {
    heap: Vec<HeapCellValue>,
    pub h: usize,
}

impl Heap {
    pub fn with_capacity(cap: usize) -> Self {
        Heap { heap: Vec::with_capacity(cap),
               h: 0 }
    }

    #[inline]
    pub fn push(&mut self, val: HeapCellValue) {
        self.heap.push(val);
        self.h += 1;
    }

    #[inline]
    pub(crate) fn take(&mut self) -> Self {
        let h = self.h;
        self.h = 0;

        Heap {
            heap: mem::replace(&mut self.heap, vec![]),
            h
        }
    }

    #[inline]
    pub fn truncate(&mut self, h: usize) {
        self.h = h;
        self.heap.truncate(h);
    }

    #[inline]
    pub fn last(&self) -> Option<&HeapCellValue> {
        self.heap.last()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn append(&mut self, vals: Vec<HeapCellValue>) {
        let n = vals.len();

        self.heap.extend(vals.into_iter());
        self.h += n;
    }

    pub fn clear(&mut self) {
        self.heap.clear();
        self.h = 0;
    }

    pub fn to_list<Iter: Iterator<Item=Addr>>(&mut self, values: Iter) -> usize {
        let head_addr = self.h;

        for value in values {
            let h = self.h;

            self.push(HeapCellValue::Addr(Addr::Lis(h+1)));
            self.push(HeapCellValue::Addr(value));
        }

        self.push(HeapCellValue::Addr(Addr::Con(Constant::EmptyList)));
        head_addr
    }

    pub fn extend<Iter: Iterator<Item=HeapCellValue>>(&mut self, iter: Iter) {
        for hcv in iter {
            self.push(hcv);
        }
    }
}

impl Index<usize> for Heap {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index]
    }
}

impl IndexMut<usize> for Heap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.heap[index]
    }
}
