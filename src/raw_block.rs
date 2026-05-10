use core::marker::PhantomData;

use std::alloc;
use std::cell::UnsafeCell;
use std::ptr;

use crate::machine::heap::AllocError;

pub trait RawBlockTraits {
    fn init_size() -> usize;
    fn align() -> usize;
}

/// A block of memory with fast, lock-free appends.
#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits> {
    base: *const u8,
    capacity: usize,

    ptr: UnsafeCell<*mut u8>,
    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    #[inline]
    pub fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            capacity: 0,
            ptr: UnsafeCell::new(ptr::null_mut()),
            _marker: PhantomData,
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Result<Self, AllocError> {
        let mut block = Self::empty_block();

        unsafe {
            block.grow()?;
        }

        Ok(block)
    }

    unsafe fn init_at_size(&mut self, cap: usize) -> Result<(), AllocError> {
        let layout = alloc::Layout::from_size_align_unchecked(cap, T::align());
        let new_base = alloc::alloc(layout).cast_const();
        if new_base.is_null() {
            return Err(AllocError);
        }
        self.base = new_base;
        self.capacity = cap;
        *self.ptr.get_mut() = self.base.cast_mut();
        Ok(())
    }

    /// ## Safety
    ///
    /// Invalidates all pointers previously obtained by [`RawBlock::get()`] or [`RawBlock::alloc()`].
    pub unsafe fn grow(&mut self) -> Result<(), AllocError> {
        if self.base.is_null() {
            self.init_at_size(T::init_size())
        } else {
            let size = self.capacity();
            let layout = alloc::Layout::from_size_align_unchecked(size, T::align());

            let new_base = alloc::realloc(self.base.cast_mut(), layout, size * 2).cast_const();
            if new_base.is_null() {
                Err(AllocError)
            } else {
                self.base = new_base;
                self.capacity = size * 2;
                *self.ptr.get_mut() = (self.base as usize + size) as *mut _;
                Ok(())
            }
        }
    }

    pub unsafe fn grow_new(&self) -> Result<Self, AllocError> {
        self.debug_check_invariants();
        if self.base.is_null() {
            Self::new()
        } else {
            let mut new_block = Self::empty_block();
            new_block.init_at_size(self.capacity() * 2)?;
            let allocated = self.used_bytes();
            self.base.copy_to(new_block.base.cast_mut(), allocated);
            *new_block.ptr.get_mut() = new_block.base.add(allocated).cast_mut();

            new_block.debug_check_invariants();

            Ok(new_block)
        }
    }

    #[inline(always)]
    fn debug_check_invariants(&self) {
        if cfg!(debug_assertions) {
            unsafe {
                assert!(
                    *self.ptr.get() as *const _ >= self.base,
                    "self.ptr = {:?} < {:?} = self.base",
                    *self.ptr.get(),
                    self.base
                );
            }

            assert!(self.used_bytes() <= self.capacity());
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    pub fn used_bytes(&self) -> usize {
        // TODO: safety: UnsafeCell.get()
        // TODO: safety: prove that ∀Γ: reachable, Γ |- (ptr, base): same alloc
        unsafe { (*self.ptr.get()).offset_from(self.base) as usize }
    }

    #[inline(always)]
    unsafe fn free_bytes(&self) -> usize {
        self.capacity() - self.used_bytes()
    }

    pub unsafe fn alloc(&self, size: usize) -> *mut u8 {
        self.debug_check_invariants();

        let aligned_size = size.next_multiple_of(T::align());
        if self.free_bytes() >= aligned_size {
            // TODO: make this an atomic add
            let ptr = *self.ptr.get();
            *self.ptr.get() = ptr.add(aligned_size) as *mut _;
            ptr
        } else {
            ptr::null_mut()
        }
    }

    /// Moves `ptr` back to `new_size`.
    ///
    /// Note that this method does *not* deallocate what was placed in the [`RawBlock`].
    /// Pointers to data past `new_size` remain valid until the next call to [`RawBlock::alloc()`].
    pub fn shift_back(&mut self, new_size: usize) {
        self.debug_check_invariants();

        assert!(
            new_size <= self.used_bytes(),
            "Shrink cannot grow: new_size = {:?} > allocated = {:?}",
            new_size,
            self.used_bytes()
        );

        // SAFETY:
        // - Asserted: new_size <= self.capacity
        // - Definition: self.base := alloc(self.capacity)
        let new_ptr = unsafe { self.base.add(new_size) };

        debug_assert!(new_ptr as usize <= (*self.ptr.get_mut()) as usize,);

        *self.ptr.get_mut() = new_ptr as *mut u8;

        self.debug_check_invariants();
    }

    /// Returns a pointer at a given `offset` within the block of memory.
    ///
    /// Panics if that range of bytes wasn't allocated yet with [`RawBlock::alloc()`].
    pub fn get(&self, offset: usize) -> *const u8 {
        assert!(offset < self.used_bytes());

        // SAFETY: Asserted.
        unsafe { self.get_unchecked(offset) }
    }

    /// Returns a pointer at a given `offset` within the block of memory.
    ///
    /// ## Safety
    ///
    /// Assumes that `offset < self.capacity()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, offset: usize) -> *const u8 {
        debug_assert!(
            offset < self.capacity(),
            "offset out of bounds: offset is {:?} but {:?} bytes are available",
            offset,
            self.used_bytes()
        );
        self.base.add(offset)
    }

    /// ## Safety
    ///
    /// `ptr` is a valid pointer be obtained from [`RawBlock::get()`] or [`RawBlock::alloc()`].
    #[inline]
    pub unsafe fn get_offset(&self, ptr: *const u8) -> usize {
        // SAFETY:
        // - Guaranteed by caller: `ptr` is still valid
        // - Guranteed by caller: `ptr` was obtained from `get()` or `alloc()`
        // - get() and alloc() return pointers in the same allocation as `self.base`
        // - All functions modifying `self.base` invalidate pointers in their contract
        // - Thus `ptr` and `self.base` originate from the same allocation
        unsafe { ptr.offset_from(self.base) as usize }
    }
}

impl<T: RawBlockTraits> Drop for RawBlock<T> {
    fn drop(&mut self) {
        if !self.base.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.capacity(), T::align());
                alloc::dealloc(self.base as *mut _, layout);
            }

            self.base = ptr::null();
            *self.ptr.get_mut() = ptr::null_mut();
        }
    }
}
