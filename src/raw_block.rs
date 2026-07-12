#![deny(unsafe_op_in_unsafe_fn)]

use core::marker::PhantomData;

use std::alloc;
use std::cell::Cell;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

trait PtrCellTrait: std::fmt::Debug {
    fn new(val: *mut u8) -> Self;

    fn get(&self) -> *mut u8;

    /// Modifies the wrapped value.
    fn set(&mut self, val: *mut u8);

    /// Performs an atomic compare-and-swap on the wrapped value.
    ///
    /// If the compare succeeded and `cb` returns `Some(new_ptr)`, stored `new_ptr` and returns `Ok(old_ptr).
    ///
    /// If `cb` returns `None`, returns `Err(old_ptr)`.
    ///
    /// May retry multiple times if the comparison fails.
    fn try_update(&self, cb: impl Fn(*mut u8) -> Option<*mut u8>) -> Result<*mut u8, *mut u8>;
}

impl PtrCellTrait for Cell<*mut u8> {
    fn new(val: *mut u8) -> Self {
        Cell::new(val)
    }

    #[inline(always)]
    fn get(&self) -> *mut u8 {
        Cell::get(self)
    }

    #[inline(always)]
    fn set(&mut self, val: *mut u8) {
        Cell::set(self, val)
    }

    #[inline(always)]
    fn try_update(&self, cb: impl Fn(*mut u8) -> Option<*mut u8>) -> Result<*mut u8, *mut u8> {
        let val = Cell::get(self);
        if let Some(new_val) = cb(val) {
            Cell::set(self, new_val);
            Ok(val)
        } else {
            Err(val)
        }
    }
}

impl PtrCellTrait for AtomicPtr<u8> {
    fn new(val: *mut u8) -> Self {
        AtomicPtr::new(val)
    }

    #[inline(always)]
    fn get(&self) -> *mut u8 {
        self.load(Ordering::Acquire)
    }

    #[inline(always)]
    fn set(&mut self, val: *mut u8) {
        *self.get_mut() = val;
    }

    #[inline]
    fn try_update(&self, cb: impl Fn(*mut u8) -> Option<*mut u8>) -> Result<*mut u8, *mut u8> {
        let mut prev = PtrCellTrait::get(self);

        while let Some(next) = cb(prev) {
            match self.compare_exchange_weak(prev, next, Ordering::Relaxed, Ordering::Acquire) {
                x @ Ok(_) => return x,
                Err(next_prev) => prev = next_prev,
            }
        }

        Err(prev)

        // TODO: replace with the following once 1.95 is the msrv:
        // AtomicPtr::try_update(self, Ordering::Relaxed, Ordering::Acquire, cb)
    }
}

/// Allows the choice of implementation for the mutable pointer in [`RawBlock`].
/// Can be one of:
/// - [`RawBlockSerial`] (using a [`Cell<*mut u8>`])
/// - [`RawBlockConcurrent`] (using a [`AtomicPtr<u8>`])
pub(crate) trait RawBlockConcurrency {
    #[allow(private_bounds)]
    type PtrCell: PtrCellTrait;
}

#[derive(Debug, Clone, Copy)]
pub struct RawBlockSerial();
#[derive(Debug, Clone, Copy)]
pub struct RawBlockConcurrent();

impl RawBlockConcurrency for RawBlockSerial {
    type PtrCell = Cell<*mut u8>;
}

impl RawBlockConcurrency for RawBlockConcurrent {
    type PtrCell = AtomicPtr<u8>;
}

use crate::machine::heap::AllocError;

pub trait RawBlockTraits {
    /// ## Safety
    ///
    /// Must be non-zero.
    fn init_size() -> usize;

    /// ## Safety
    ///
    /// Must be constant.
    ///
    /// Must respect the invariants of [`std::alloc::Layout::from_size_align()`], namely:
    /// - must not be zero
    /// - must be a power of two
    /// - must not overflow `usize`
    fn align() -> usize;
}

/// A block of memory with fast, lock-free appends.
///
/// ## Invariants
///
/// - `base.is_null()` iff `capacity == 0`
/// - if `!base.is_null()`, then `ptr.get()` is in the same allocation as `base`.
#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits, C: RawBlockConcurrency = RawBlockSerial> {
    base: *const u8,
    capacity: usize,

    ptr: C::PtrCell,
    _marker: PhantomData<T>,
    _c_marker: PhantomData<C>,
}

impl<T: RawBlockTraits, C: RawBlockConcurrency> RawBlock<T, C> {
    #[inline]
    pub fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            capacity: 0,
            ptr: C::PtrCell::new(ptr::null_mut()),
            _marker: PhantomData,
            _c_marker: PhantomData,
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

    /// ## Safety
    ///
    /// Assumes that the object has not been initialized before (ie. `self.base.is_null()`)
    /// and assumes that `cap > 0`.
    unsafe fn init_at_size(&mut self, cap: usize) -> Result<(), AllocError> {
        debug_assert!(cap > 0);
        debug_assert!(self.base.is_null());

        // SAFETY:
        // - Guaranteed by caller: `cap > 0`
        // - Guaranteed by caller: `T::align()` respects the invariants of `Layout::from_size_align`
        let new_base = unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(cap, T::align());
            alloc::alloc(layout).cast_const()
        };

        if new_base.is_null() {
            return Err(AllocError);
        }

        self.base = new_base;
        self.capacity = cap;
        self.ptr.set(self.base.cast_mut());
        Ok(())
    }

    /// ## Safety
    ///
    /// Invalidates all pointers previously obtained by [`RawBlock::get()`] or [`RawBlock::alloc()`].
    pub unsafe fn grow(&mut self) -> Result<(), AllocError> {
        self.debug_check_invariants();

        if self.base.is_null() {
            // SAFETY:
            // - Guaranteed by caller: `T::init_size() > 0`
            // - Asserted: `self.base.is_null()`
            unsafe { self.init_at_size(T::init_size()) }
        } else {
            let size = self.capacity();
            let used_bytes = self.used_bytes();
            // SAFETY:
            // - Guaranteed by caller: `T::align()` respects the invariants of `Layout::from_size_align`
            // - Asserted: `!self.base.is_null()`
            // - Invariant: `self.base.is_null()` iff `self.capacity() == 0`
            // - Thus `self.capacity() > 0`
            let new_base = unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(size, T::align());

                alloc::realloc(self.base.cast_mut(), layout, size * 2).cast_const()
            };

            if new_base.is_null() {
                Err(AllocError)
            } else {
                self.base = new_base;
                self.capacity = size * 2;
                // SAFETY:
                // - Invariant: `used_bytes < size`
                // - Definition: `new_base` has allocation size `2 * size`
                let new_ptr = unsafe { self.base.add(used_bytes).cast_mut() };
                self.ptr.set(new_ptr);

                self.debug_check_invariants();
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
            // SAFETY:
            // - Asserted: !self.base.is_null()
            // - Invariant: self.base.is_null() iff self.capacity == 0
            // - Thus self.capacity > 0
            // - Definition: `new_block` was not yet initialized
            unsafe {
                new_block.init_at_size(self.capacity() * 2)?;
            }

            let used_bytes = self.used_bytes();

            // SAFETY:
            // - Definition: `self.base` contains `self.allocated()` bytes
            // - Invariant: `self.used_bytes() < self.allocated()`
            unsafe {
                self.base.copy_to(new_block.base.cast_mut(), used_bytes);
                new_block.ptr.set(new_block.base.add(used_bytes).cast_mut());
            }

            new_block.debug_check_invariants();

            Ok(new_block)
        }
    }

    #[inline(always)]
    fn debug_check_invariants(&self) {
        if cfg!(debug_assertions) {
            assert!(
                self.ptr.get().cast_const() >= self.base,
                "self.ptr = {:?} < {:?} = self.base",
                self.ptr.get(),
                self.base
            );

            assert!(self.used_bytes() <= self.capacity());
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    pub fn used_bytes(&self) -> usize {
        // SAFETY:
        // - Invariant: `ptr` is in the same allocation as `base`
        unsafe { self.ptr.get().offset_from(self.base) as usize }
    }

    pub unsafe fn alloc(&self, size: usize) -> *mut u8 {
        self.debug_check_invariants();

        let aligned_size = size.next_multiple_of(T::align());

        match self.ptr.try_update(|ptr| {
            // SAFETY:
            // - Invariant: `ptr` is in the same allocation as `base`
            let free_bytes = unsafe { self.capacity() - ptr.offset_from(self.base) as usize };

            if free_bytes >= aligned_size {
                Some(unsafe { ptr.add(aligned_size) })
            } else {
                // Not enough space: don't allocate and return a null pointer
                None
            }
        }) {
            Ok(ptr) => ptr,
            Err(_) => ptr::null_mut(),
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

        debug_assert!(new_ptr as usize <= self.ptr.get() as usize,);

        self.ptr.set(new_ptr.cast_mut());

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

        // SAFETY: Guaranteed by caller.
        unsafe { self.base.add(offset) }
    }

    /// ## Safety
    ///
    /// `ptr` is a valid pointer be obtained from [`RawBlock::get()`] or [`RawBlock::alloc()`].
    #[inline]
    pub unsafe fn get_offset(&self, ptr: *const u8) -> usize {
        // SAFETY:
        // - Guaranteed by caller: `ptr` is still valid
        // - Guaranteed by caller: `ptr` was obtained from `get()` or `alloc()`
        // - get() and alloc() return pointers in the same allocation as `self.base`
        // - All functions modifying `self.base` invalidate pointers in their contract
        // - Thus `ptr` and `self.base` originate from the same allocation
        unsafe { ptr.offset_from(self.base) as usize }
    }
}

impl<T: RawBlockTraits, C: RawBlockConcurrency> Drop for RawBlock<T, C> {
    fn drop(&mut self) {
        if !self.base.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.capacity(), T::align());
                alloc::dealloc(self.base as *mut _, layout);
            }
        }
    }
}

impl<T: RawBlockTraits> From<RawBlock<T, RawBlockConcurrent>> for RawBlock<T, RawBlockSerial> {
    fn from(other: RawBlock<T, RawBlockConcurrent>) -> Self {
        Self {
            base: other.base,
            capacity: other.capacity,
            ptr: PtrCellTrait::new(other.ptr.get()),
            _marker: PhantomData,
            _c_marker: PhantomData,
        }
    }
}

impl<T: RawBlockTraits> From<RawBlock<T, RawBlockSerial>> for RawBlock<T, RawBlockConcurrent> {
    fn from(other: RawBlock<T, RawBlockSerial>) -> Self {
        Self {
            base: other.base,
            capacity: other.capacity,
            ptr: PtrCellTrait::new(other.ptr.get()),
            _marker: PhantomData,
            _c_marker: PhantomData,
        }
    }
}
