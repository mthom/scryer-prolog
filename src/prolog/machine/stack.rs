use crate::prolog::machine::machine_indices::*;

use core::marker::PhantomData;

use std::alloc;
use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

const STACK_ALIGN: usize = mem::align_of::<Addr>();
const INIT_STACK_SIZE: usize = 10 * 1024 * 1024;

const fn prelude_size<Prelude>() -> usize {
    let size = mem::size_of::<Prelude>();
    let align = mem::align_of::<Addr>();

    (size & !(align - 1)) + align
}

pub struct Stack {
    size: usize,
    base: *const u8,
    top:  *const u8,
    _marker: PhantomData<Addr>,
}

impl Drop for Stack {
    fn drop(&mut self) {
        self.drop_in_place();
        self.deallocate();
    }
}

#[derive(Clone, Copy)]
pub struct FramePrelude {
    is_or_frame: u8,
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
    _marker: PhantomData<Addr>,
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

impl Drop for AndFrame {
    fn drop(&mut self) {
        let prelude_offset = prelude_size::<AndFramePrelude>();

        unsafe {
            let ptr = mem::transmute::<&mut AndFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset;

            for idx in 0 .. self.prelude.univ_prelude.num_cells {
                let index_offset = idx * mem::size_of::<Addr>();
                let ptr = (ptr + index_offset) as *mut Addr;

                ptr::drop_in_place(ptr);
            }
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
    _marker: PhantomData<Addr>
}

impl Index<usize> for OrFrame {
    type Output = Addr;

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

impl Drop for OrFrame {
    fn drop(&mut self) {
        let prelude_offset = prelude_size::<OrFramePrelude>();

        unsafe {
            let ptr = mem::transmute::<&mut OrFrame, *const u8>(self);
            let ptr = ptr as usize + prelude_offset;

            for idx in 0 .. self.prelude.univ_prelude.num_cells {
                let index_offset = idx * mem::size_of::<Addr>();
                let ptr = (ptr + index_offset) as *mut Addr;

                ptr::drop_in_place(ptr);
            }
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
        let mut stack = Stack { size: 0, base: ptr::null(), top: ptr::null(),
                                _marker: PhantomData };

        unsafe { stack.grow(); }
        stack
    }

    fn empty_stack() -> Self {
        Stack { size: 0, base: ptr::null(), top: ptr::null(),
                _marker: PhantomData }
    }

    #[inline]
    pub fn take(&mut self) -> Stack {
        mem::replace(self, Stack::empty_stack())
    }

    #[inline]
    fn free_space(&self) -> usize {
        debug_assert!(self.top >= self.base,
                      "self.top = {:?} < {:?} = self.base",
                      self.top, self.base);

        self.size - (self.top as usize - self.base as usize)
    }

    unsafe fn grow(&mut self) {
        if self.size == 0 {
            let layout = alloc::Layout::from_size_align_unchecked(INIT_STACK_SIZE, STACK_ALIGN);

            self.base = alloc::alloc(layout) as *const _;
            self.top = self.base as *const _;
            self.size = INIT_STACK_SIZE;

            self.top = self.top.offset(mem::align_of::<Addr>() as isize);
        } else {
            let layout = alloc::Layout::from_size_align_unchecked(self.size, STACK_ALIGN);
            let top_dist = self.top as usize - self.base as usize;

            self.base = alloc::realloc(self.base as *mut _, layout, self.size*2) as *const _;
            self.top = (self.base as usize + top_dist) as *const _;
            self.size *= 2;
        }
    }

    #[inline]
    unsafe fn new_frame_ptr(&mut self, frame_size: usize) -> *const u8 {
        loop {
            if self.free_space() >= frame_size {
                return (self.top as usize + frame_size) as *const _;
            } else {
                self.grow();
            }
        }
    }

    pub fn allocate_and_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = AndFrame::size_of(num_cells);

        unsafe {
            let new_top = self.new_frame_ptr(frame_size);

            for idx in 0 .. num_cells {
                let offset = prelude_size::<AndFramePrelude>() + idx * mem::size_of::<Addr>();
                ptr::write((self.top as usize + offset) as *mut Addr, Addr::StackCell(0,0));
            }

            let and_frame = &mut *(self.top as *mut AndFrame);

            and_frame.prelude.univ_prelude.is_or_frame = 0;
            and_frame.prelude.univ_prelude.num_cells = num_cells;

            let e = self.top as usize - self.base as usize;
            self.top = new_top;
            e
        }
    }

    pub fn allocate_or_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = OrFrame::size_of(num_cells);

        unsafe {
            let new_top = self.new_frame_ptr(frame_size);

            for idx in 0 .. num_cells {
                let offset = prelude_size::<OrFramePrelude>() + idx * mem::size_of::<Addr>();
                ptr::write((self.top as usize + offset) as *mut Addr, Addr::StackCell(0,0));
            }

            let or_frame = &mut *(self.top as *mut OrFrame);

            or_frame.prelude.univ_prelude.is_or_frame = 1;
            or_frame.prelude.univ_prelude.num_cells = num_cells;

            let b = self.top as usize - self.base as usize;
            self.top = new_top;
            b
        }
    }

    #[inline]
    pub fn index_and_frame(&self, e: usize) -> &AndFrame {
        unsafe {
            let ptr = self.base as usize + e;
            &*(ptr as *const AndFrame)
        }
    }

    #[inline]
    pub fn index_and_frame_mut(&mut self, e: usize) -> &mut AndFrame {
        unsafe {
            let ptr = self.base as usize + e;
            &mut *(ptr as *mut AndFrame)
        }
    }

    #[inline]
    pub fn index_or_frame(&self, b: usize) -> &OrFrame {
        unsafe {
            let ptr = self.base as usize + b;
            &*(ptr as *const OrFrame)
        }
    }

    #[inline]
    pub fn index_or_frame_mut(&mut self, b: usize) -> &mut OrFrame {
        unsafe {
            let ptr = self.base as usize + b;
            &mut *(ptr as *mut OrFrame)
        }
    }

    pub fn deallocate(&mut self) {
        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(self.size, STACK_ALIGN);
            alloc::dealloc(self.base as *mut u8, layout);

            self.top  = ptr::null();
            self.base = ptr::null();
            self.size = 0;
        }
    }

    pub fn truncate_to_frame(&mut self, b: usize) {
        if b == 0 {
            self.truncate(mem::align_of::<Addr>());
        } else {
            let univ_prelude = self.index_or_frame(b).prelude.univ_prelude;
            let size = OrFrame::size_of(univ_prelude.num_cells);

            self.truncate(b + size);
        }
    }

    fn truncate(&mut self, b: usize) {
        let mut b = b + self.base as usize;
        let base =  b;

        unsafe {
            while b as *const _ < self.top {
                let univ_prelude = ptr::read(b as *const FramePrelude);

                let offset = if univ_prelude.is_or_frame == 0 {
                    let frame_ptr = b as *mut AndFrame;
                    let frame = &mut *frame_ptr;
                    let size_of_frame = AndFrame::size_of(frame.prelude.univ_prelude.num_cells);

                    ptr::drop_in_place(frame_ptr);

                    b + size_of_frame
                } else {
                    debug_assert!(univ_prelude.is_or_frame == 1);

                    let frame_ptr = b as *mut OrFrame;
                    let frame = &mut *frame_ptr;
                    let size_of_frame = OrFrame::size_of(frame.prelude.univ_prelude.num_cells);

                    ptr::drop_in_place(frame_ptr);

                    b + size_of_frame
                };

                b = offset;
            }

            if base < self.top as usize {
                self.top = base as *const _;
            }
        }
    }

    pub fn drop_in_place(&mut self) {
        self.truncate(mem::align_of::<Addr>());

        debug_assert!(if self.top.is_null() {
            self.top == self.base
        } else {
            self.top as usize == self.base as usize + mem::align_of::<Addr>()
        });
    }
}
