use core::marker::PhantomData;

use std::alloc;
use std::ptr;

pub trait RawBlockTraits {
    fn init_size() -> usize;
    fn align() -> usize;
}

#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits> {
    pub base: *const u8,
    pub top: *const u8,
    pub ptr: *mut u8,
    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    #[inline]
    fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            top: ptr::null(),
            ptr: ptr::null_mut(),
            _marker: PhantomData,
        }
    }

    pub fn new() -> Self {
        let mut block = Self::empty_block();

        unsafe {
            block.grow();
        }

        block
    }

    unsafe fn init_at_size(&mut self, cap: usize) {
        let layout = alloc::Layout::from_size_align_unchecked(cap, T::align());

        self.base = alloc::alloc(layout) as *const _;
        self.top = (self.base as usize + cap) as *const _;
        self.ptr = self.base as *mut _;
    }

    pub unsafe fn grow(&mut self) {
        if self.base.is_null() {
            self.init_at_size(T::init_size());
        } else {
            let size = self.size();
            let layout = alloc::Layout::from_size_align_unchecked(size, T::align());

            self.base = alloc::realloc(self.base as *mut _, layout, size * 2) as *const _;
            self.top = (self.base as usize + size * 2) as *const _;
            self.ptr = (self.base as usize + size) as *mut _;
        }
    }

    /*
    #[inline]
    pub fn take(&mut self) -> Self {
        mem::replace(self, Self::empty_block())
    }
    */

    #[inline]
    pub fn size(&self) -> usize {
        self.top as usize - self.base as usize
    }

    #[inline(always)]
    fn free_space(&self) -> usize {
        debug_assert!(
            self.ptr as *const _ >= self.base,
            "self.ptr = {:?} < {:?} = self.base",
            self.ptr,
            self.base
        );

        self.top as usize - self.ptr as usize
    }

    pub unsafe fn alloc(&mut self, size: usize) -> *mut u8 {
        if self.free_space() >= size {
            let ptr = self.ptr;
            self.ptr = (self.ptr as usize + size) as *mut _;
            ptr
        } else {
            ptr::null_mut()
        }
    }

    pub fn deallocate(&mut self) {
        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(self.size(), T::align());
            alloc::dealloc(self.base as *mut _, layout);

            self.top = ptr::null();
            self.base = ptr::null();
            self.ptr = ptr::null_mut();
        }
    }
}
