use core::marker::PhantomData;

use std::alloc;
use std::mem;
use std::ptr;

pub(crate) trait RawBlockTraits {
    fn init_size() -> usize;
    fn align() -> usize;

    #[inline]
    fn base_offset(base: *const u8) -> *const u8 {
        base
    }
}

#[derive(Debug)]
pub(crate) struct RawBlock<T: RawBlockTraits> {
    pub(crate) size: usize,
    pub(crate) base: *const u8,
    pub(crate) top: *const u8,
    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    pub(crate) fn new() -> Self {
        let mut block = Self::uninitialized();

        unsafe {
            block.grow();
        }

        block
    }

    pub(crate) fn uninitialized() -> Self {
        Self {
            size: 0,
            base: ptr::null(),
            top: ptr::null(),
            _marker: PhantomData,
        }
    }

    unsafe fn init_at_size(&mut self, cap: usize) {
        let layout = alloc::Layout::from_size_align_unchecked(cap, T::align());

        self.base = alloc::alloc(layout) as *const _;
        self.size = cap;

        self.top = T::base_offset(self.base);
    }

    pub(super) unsafe fn grow(&mut self) {
        if self.size == 0 {
            self.init_at_size(T::init_size());
        } else {
            let layout = alloc::Layout::from_size_align_unchecked(T::init_size(), T::align());
            let top_dist = self.top as usize - self.base as usize;

            self.base = alloc::realloc(self.base as *mut _, layout, self.size * 2) as *const _;
            self.top = (self.base as usize + top_dist) as *const _;
            self.size *= 2;
        }
    }

    fn empty_block() -> Self {
        RawBlock {
            size: 0,
            base: ptr::null(),
            top: ptr::null(),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn take(&mut self) -> Self {
        mem::replace(self, Self::empty_block())
    }

    #[inline]
    fn free_space(&self) -> usize {
        debug_assert!(
            self.top >= self.base,
            "self.top = {:?} < {:?} = self.base",
            self.top,
            self.base
        );

        self.size - (self.top as usize - self.base as usize)
    }

    #[inline]
    pub(crate) unsafe fn new_block(&mut self, size: usize) -> *const u8 {
        loop {
            if self.free_space() >= size {
                return (self.top as usize + size) as *const _;
            } else {
                self.grow();
            }
        }
    }

    pub(crate) fn deallocate(&mut self) {
        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(self.size, T::align());

            alloc::dealloc(self.base as *mut u8, layout);

            self.top = ptr::null();
            self.base = ptr::null();
            self.size = 0;
        }
    }
}
