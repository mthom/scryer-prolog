use prolog_parser::ast::*;

use crate::prolog::machine::machine_indices::*;

use std::mem;
use std::ops::{Index, IndexMut};

pub struct Heap {
    heap: Vec<HeapCellValue>,
    pub h: usize,
}

impl Heap {
    pub fn with_capacity(cap: usize) -> Self {
        Heap {
            heap: Vec::with_capacity(cap),
            h: 0,
        }
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
            h,
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

    pub fn to_list<Iter: Iterator<Item = Addr>>(&mut self, values: Iter) -> usize {
        let head_addr = self.h;

        for value in values {
            let h = self.h;

            self.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
            self.push(HeapCellValue::Addr(value));
        }

        self.push(HeapCellValue::Addr(Addr::Con(Constant::EmptyList)));
        head_addr
    }

    pub fn extend<Iter: Iterator<Item = HeapCellValue>>(&mut self, iter: Iter) {
        for hcv in iter {
            self.push(hcv);
        }
    }

    pub fn to_local_code_ptr(&self, addr: &Addr) -> Option<LocalCodePtr> {
        let extract_integer = |s: usize| -> Option<usize> {
            match self.heap[s].as_addr(s) {
                Addr::Con(Constant::Integer(n)) => n.to_usize(),
                _ => None
            }
        };
        
        match addr {
            Addr::Str(s) => {
                match &self.heap[*s] {
                    HeapCellValue::NamedStr(arity, ref name, _) => {
                        match (name.as_str(), *arity) {
                            ("dir_entry", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::DirEntry)
                            }
                            ("in_situ_dir_entry", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::InSituDirEntry)
                            }
                            ("top_level", 2) => {
                                if let Some(chunk_num) = extract_integer(s+1) {
                                    if let Some(p) = extract_integer(s+2) {
                                        return Some(LocalCodePtr::TopLevel(chunk_num, p));
                                    }
                                }

                                None
                            }
                            ("user_goal_expansion", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::UserGoalExpansion)
                            }
                            ("user_term_expansion", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::UserTermExpansion)
                            }
                            _ => None
                        }
                    }
                    _ => unreachable!()
                }
            }
            _ => None
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
