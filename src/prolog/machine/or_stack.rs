use prolog::machine::machine_indices::*;

use std::mem;
use std::ops::{Index, IndexMut};
use std::vec::Vec;

pub struct Frame {
    pub global_index: usize,
    pub e: usize,
    pub cp: LocalCodePtr,
    pub attr_var_init_b: usize,
    pub b: usize,
    pub bp: CodePtr,
    pub tr: usize,
    pub pstr_tr: usize,
    pub h: usize,
    pub b0: usize,
    args: Vec<Addr>,
}

impl Frame {
    fn new(
        global_index: usize,
        e: usize,
        cp: LocalCodePtr,
        attr_var_init_b: usize,
        b: usize,
        bp: CodePtr,
        tr: usize,
        pstr_tr: usize,
        h: usize,
        b0: usize,
        n: usize,
    ) -> Self {
        Frame {
            global_index,
            e,
            cp,
            attr_var_init_b,
            b,
            bp,
            tr,
            pstr_tr,
            h,
            b0,
            args: vec![Addr::HeapCell(0); n],
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

    pub fn push(
        &mut self,
        global_index: usize,
        e: usize,
        cp: LocalCodePtr,
        attr_var_init_b: usize,
        b: usize,
        bp: CodePtr,
        tr: usize,
        pstr_tr: usize,
        h: usize,
        b0: usize,
        n: usize,
    ) {
        self.0.push(Frame::new(
            global_index,
            e,
            cp,
            attr_var_init_b,
            b,
            bp,
            tr,
            pstr_tr,
            h,
            b0,
            n,
        ));
    }

    #[inline]
    pub(crate) fn take(&mut self) -> Self {
        OrStack(mem::replace(&mut self.0, vec![]))
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

    // truncate expects a 1-indexed new_b, ie.
    // the value b of MachineState.
    pub fn truncate(&mut self, new_b: usize) {
        self.0.truncate(new_b);
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
