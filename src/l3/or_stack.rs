use l3::ast::*;

use std::ops::{Index, IndexMut};
use std::vec::Vec;

pub struct Frame {
    pub global_index: usize,
    pub e: usize,
    pub cp: CodePtr,
    pub b: usize,
    pub bp: CodePtr,
    pub tr: usize,
    pub h: usize,
    args: Vec<Addr>
}

impl Frame {
    fn new(global_index: usize,
           e: usize,
           cp: CodePtr,
           b: usize,
           bp: CodePtr,
           tr: usize,
           h: usize,
           n: usize)
           -> Self
    {
        Frame {
            global_index: global_index,
            e: e,
            cp: cp,
            b: b,
            bp: bp,
            tr: tr,
            h: h,
            args: vec![Addr::HeapCell(0); n]
        }
    }

    pub fn num_args(&self) -> usize {
        self.args.len()
    }
}

pub struct OrStack(Vec<Frame>);

impl OrStack {
    pub fn new() -> Self {
        OrStack(Vec::new())
    }

    pub fn push(&mut self,
                global_index: usize,
                e: usize,
                cp: CodePtr,
                b: usize,
                bp: CodePtr,
                tr: usize,
                h: usize,
                n: usize)
    {
        self.0.push(Frame::new(global_index, e, cp, b, bp, tr, h, n));
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn top(&self) -> Option<&Frame> {
        self.0.last()
    }

    pub fn pop(&mut self) {
        self.0.pop();
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Index<usize> for OrStack {
    type Output = Frame;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl IndexMut<usize> for OrStack {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl Index<usize> for Frame {
    type Output = Addr;

    fn index(&self, index: usize) -> &Self::Output {
        self.args.index(index - 1)
    }
}

impl IndexMut<usize> for Frame {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.args.index_mut(index - 1)
    }
}
