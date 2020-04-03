use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::raw_block::*;

use core::marker::PhantomData;

use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

struct StackTraits {}

impl RawBlockTraits for StackTraits {
    #[inline]
    fn init_size() -> usize {
        10 * 1024 * 1024
    }

    #[inline]
    fn align() -> usize {
        mem::align_of::<Addr>()
    }

    #[inline]
    fn base_offset(base: *const u8) -> *const u8 {
        unsafe {
            base.offset(Self::align() as isize)
        }
    }
}

const fn prelude_size<Prelude>() -> usize {
    let size = mem::size_of::<Prelude>();
    let align = mem::align_of::<Addr>();

    (size & !(align - 1)) + align
}

pub struct Stack {
    buf: RawBlock<StackTraits>,
    _marker: PhantomData<Addr>,
}

impl Drop for Stack {
    fn drop(&mut self) {
        self.drop_in_place();
        self.buf.deallocate();
    }
}

#[derive(Clone, Copy)]
pub struct FramePrelude {
    pub num_cells: usize,
}

pub struct AndFramePrelude {
    pub univ_prelude: FramePrelude,
    pub e: usize,
    pub cp: LocalCodePtr,
    pub interrupt_cp: LocalCodePtr,
}

pub struct AndFrame {
    pub prelude: AndFramePrelude,
}

impl AndFrame {
    pub fn size_of(num_cells: usize) -> usize {
        prelude_size::<AndFramePrelude>() + num_cells * mem::size_of::<Addr>()
    }
}

impl Index<usize> for AndFrame {
    type Output = Addr;

    fn index(&self, index: usize) -> &Self::Output {
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<Addr>();

        unsafe {
            let ptr = mem::transmute::<&AndFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset + index_offset;

            &*(ptr as *const Addr)
        }
    }
}

impl IndexMut<usize> for AndFrame {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<Addr>();

        unsafe {
            let ptr = mem::transmute::<&mut AndFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset + index_offset;

            &mut *(ptr as *mut Addr)
        }
    }
}

pub struct OrFramePrelude {
    pub univ_prelude: FramePrelude,
    pub e: usize,
    pub cp: LocalCodePtr,
    pub b: usize,
    pub bp: LocalCodePtr,
    pub tr: usize,
    pub pstr_tr: usize,
    pub h: usize,
    pub b0: usize,
    pub attr_var_init_queue_b: usize,
    pub attr_var_init_bindings_b: usize,
}

pub struct OrFrame {
    pub prelude: OrFramePrelude,
}

impl Index<usize> for OrFrame {
    type Output = Addr;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<Addr>();

        unsafe {
            let ptr = mem::transmute::<&OrFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset + index_offset;

            &*(ptr as *const Addr)
        }
    }
}

impl IndexMut<usize> for OrFrame {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<Addr>();

        unsafe {
            let ptr = mem::transmute::<&mut OrFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset + index_offset;

            &mut *(ptr as *mut Addr)
        }
    }
}

impl OrFrame {
    pub fn size_of(num_cells: usize) -> usize {
        prelude_size::<OrFramePrelude>() + num_cells * mem::size_of::<Addr>()
    }
}

impl Stack {
    pub fn new() -> Self {
        Stack { buf: RawBlock::new(), _marker: PhantomData }
    }

    pub fn allocate_and_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = AndFrame::size_of(num_cells);

        unsafe {
            let new_top = self.buf.new_block(frame_size);

            for idx in 0 .. num_cells {
                let offset = prelude_size::<AndFramePrelude>() + idx * mem::size_of::<Addr>();
                ptr::write((self.buf.top as usize + offset) as *mut Addr, Addr::StackCell(0,0));
            }

            let and_frame = &mut *(self.buf.top as *mut AndFrame);
            and_frame.prelude.univ_prelude.num_cells = num_cells;

            let e = self.buf.top as usize - self.buf.base as usize;
            self.buf.top = new_top;

            e
        }
    }

    pub fn allocate_or_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = OrFrame::size_of(num_cells);

        unsafe {
            let new_top = self.buf.new_block(frame_size);

            for idx in 0 .. num_cells {
                let offset = prelude_size::<OrFramePrelude>() + idx * mem::size_of::<Addr>();
                ptr::write((self.buf.top as usize + offset) as *mut Addr, Addr::StackCell(0,0));
            }

            let or_frame = &mut *(self.buf.top as *mut OrFrame);
            or_frame.prelude.univ_prelude.num_cells = num_cells;

            let b = self.buf.top as usize - self.buf.base as usize;
            self.buf.top = new_top;

            b
        }
    }

    #[inline]
    pub fn index_and_frame(&self, e: usize) -> &AndFrame {
        unsafe {
            let ptr = self.buf.base as usize + e;
            &*(ptr as *const AndFrame)
        }
    }

    #[inline]
    pub fn index_and_frame_mut(&mut self, e: usize) -> &mut AndFrame {
        unsafe {
            let ptr = self.buf.base as usize + e;
            &mut *(ptr as *mut AndFrame)
        }
    }

    #[inline]
    pub fn index_or_frame(&self, b: usize) -> &OrFrame {
        unsafe {
            let ptr = self.buf.base as usize + b;
            &*(ptr as *const OrFrame)
        }
    }

    #[inline]
    pub fn index_or_frame_mut(&mut self, b: usize) -> &mut OrFrame {
        unsafe {
            let ptr = self.buf.base as usize + b;
            &mut *(ptr as *mut OrFrame)
        }
    }

    pub fn take(&mut self) -> Self {
        Stack { buf: self.buf.take(), _marker: PhantomData }
    }

    #[inline]
    pub fn truncate(&mut self, b: usize) {
        if b == 0 {
            self.inner_truncate(mem::align_of::<Addr>());
        } else {
            self.inner_truncate(b);
        }
    }

    #[inline]
    fn inner_truncate(&mut self, b: usize) {
        let base = b + self.buf.base as usize;

        if base < self.buf.top as usize {
            self.buf.top = base as *const _;
        }
    }

    pub fn drop_in_place(&mut self) {
        self.truncate(mem::align_of::<Addr>());

        debug_assert!(if self.buf.top.is_null() {
            self.buf.top == self.buf.base
        } else {
            self.buf.top as usize == self.buf.base as usize + mem::align_of::<Addr>()
        });
    }
}
