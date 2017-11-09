use prolog::ast::*;

use std::ops::{Index, IndexMut};
use std::vec::Vec;

#[derive(Clone)]
pub struct Frame {
    pub global_index: usize,
    pub b0: usize,
    pub e: usize,
    pub cp: CodePtr,
    perms: Vec<Addr>
}

impl Frame {
    fn new(global_index: usize, fr: usize, e: usize, cp: CodePtr, n: usize) -> Self {
        Frame {
            global_index,
            b0: 0,
            e: e,
            cp: cp,
            perms: (1 .. n+1).map(|i| Addr::StackCell(fr, i)).collect()
        }
    }
}

pub struct AndStack(Vec<Frame>);

impl AndStack {
    pub fn new() -> Self {
        AndStack(Vec::new())
    }

    pub fn push(&mut self, global_index: usize, e: usize, cp: CodePtr, n: usize) {
        let len = self.0.len();
        self.0.push(Frame::new(global_index, len, e, cp, n));
    }

    #[allow(dead_code)]
    pub fn top(&self) -> Option<&Frame> {
        self.0.last()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn pop(&mut self) {
        self.0.pop();
    }
}

impl Index<usize> for AndStack {
    type Output = Frame;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl IndexMut<usize> for AndStack {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl Index<usize> for Frame {
    type Output = Addr;

    fn index(&self, index: usize) -> &Self::Output {
        self.perms.index(index - 1)
    }
}

impl IndexMut<usize> for Frame {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.perms.index_mut(index - 1)
    }
}
