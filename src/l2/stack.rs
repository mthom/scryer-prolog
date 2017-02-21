use l2::ast::*;

use std::ops::{Index, IndexMut};
use std::vec::Vec;

struct Frame {
    cp: CodePtr,
    perms: Vec<HeapCellValue>
}

impl Frame {
    fn new(cp: CodePtr, n: usize) -> Self {
        Frame {
            cp: cp,
            perms: vec![HeapCellValue::Ref(0); n]
        }
    }

    fn read_pv(&self, i: usize) -> &HeapCellValue {
        self.perms.index(i)
    }

    fn read_pv_mut(&mut self, i: usize) -> &mut HeapCellValue {
        self.perms.index_mut(i)
    }
}

pub struct Stack(Vec<Frame>);

impl Stack {
    pub fn new() -> Self {
        Stack(Vec::new())
    }
    
    pub fn push(&mut self, cp: CodePtr, n: usize) {
        self.0.push(Frame::new(cp, n));
    }

    pub fn get_cp(&self) -> CodePtr {
        self.0.last().unwrap().cp
    }
    
    pub fn pop(&mut self) {
        self.0.pop();
    }
}

impl Index<usize> for Stack {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.last().unwrap().read_pv(index - 1)
    }
}

impl IndexMut<usize> for Stack {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.last_mut().unwrap().read_pv_mut(index - 1)
    }
}
