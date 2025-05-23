use core::marker::PhantomData;

use std::alloc;
use std::cell::UnsafeCell;
use std::ptr;

pub trait RawBlockTraits {
    fn init_size() -> usize;
    fn align() -> usize;
}

#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits> {
    pub base: *const u8,
    pub top: *const u8,
    pub ptr: UnsafeCell<*mut u8>,
    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    #[inline]
    fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            top: ptr::null(),
            ptr: UnsafeCell::new(ptr::null_mut()),
            _marker: PhantomData,
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        let mut block = Self::empty_block();

        unsafe {
            block.grow();
        }

        block
    }

    unsafe fn init_at_size(&mut self, cap: usize) {
        let layout = alloc::Layout::from_size_align_unchecked(cap, T::align());
        let new_base = alloc::alloc(layout).cast_const();
        if new_base.is_null() {
            panic!(
                "failed to allocate in init_at_size for {}",
                std::any::type_name::<Self>()
            );
        }
        self.base = new_base;
        self.top = self.base.add(cap);
        *self.ptr.get_mut() = self.base.cast_mut();
    }

    pub unsafe fn grow(&mut self) -> bool {
        if self.base.is_null() {
            self.init_at_size(T::init_size());
            true
        } else {
            let size = self.size();
            let layout = alloc::Layout::from_size_align_unchecked(size, T::align());

            let new_base = alloc::realloc(self.base.cast_mut(), layout, size * 2).cast_const();
            if new_base.is_null() {
                false
            } else {
                self.base = new_base;
                self.top = (self.base as usize + size * 2) as *const _;
                *self.ptr.get_mut() = (self.base as usize + size) as *mut _;
                true
            }
        }
    }

    pub unsafe fn grow_new(&self) -> Option<Self> {
        if self.base.is_null() {
            Some(Self::new())
        } else {
            let mut new_block = Self::empty_block();
            new_block.init_at_size(self.size() * 2);
            if new_block.base.is_null() {
                // allocation failed
                None
            } else {
                let allocated = (*self.ptr.get()) as usize - self.base as usize;
                self.base.copy_to(new_block.base.cast_mut(), allocated);
                *new_block.ptr.get_mut() = new_block.base.add(allocated).cast_mut();
                Some(new_block)
            }
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.top as usize - self.base as usize
    }

    #[inline(always)]
    unsafe fn free_space(&self) -> usize {
        debug_assert!(
            *self.ptr.get() as *const _ >= self.base,
            "self.ptr = {:?} < {:?} = self.base",
            *self.ptr.get(),
            self.base
        );

        self.top as usize - (*self.ptr.get()) as usize
    }

    pub unsafe fn alloc(&self, size: usize) -> *mut u8 {
        let aligned_size = size.next_multiple_of(size);
        if self.free_space() >= aligned_size {
            let ptr = *self.ptr.get();
            *self.ptr.get() = ptr.add(aligned_size) as *mut _;
            ptr
        } else {
            ptr::null_mut()
        }
    }
}

impl<T: RawBlockTraits> Drop for RawBlock<T> {
    fn drop(&mut self) {
        if !self.base.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.size(), T::align());
                alloc::dealloc(self.base as *mut _, layout);
            }

            self.top = ptr::null();
            self.base = ptr::null();
            *self.ptr.get_mut() = ptr::null_mut();
        }
    }
}
