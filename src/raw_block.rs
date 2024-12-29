use core::marker::PhantomData;

use std::alloc;
use std::cell::UnsafeCell;
use std::ptr;

pub trait RawBlockTraits {
    /// Must be a multiple of `ALIGN`.
    fn init_size() -> usize;

    const ALIGN: usize;
}

/// A handle to an allocated region of bytes, which is used to store an array of
/// DSTs.
///
/// # Safety
/// - `base`, `top` and `ptr` are guaranteed to be aligned to [`T::ALIGN`](RawBlockTraits::ALIGN).
/// - `base` points to the start of the allocated region and `top` to the end of it.
/// - `top - base < isize::MAX`
/// - `ptr` points to the last unused byte of the allocated region (aligned to `T::ALIGN`).
#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits> {
    base: *const u8,
    top: *const u8,
    ptr: UnsafeCell<*mut u8>,
    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    #[inline]
    pub(crate) fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            top: ptr::null(),
            ptr: UnsafeCell::new(ptr::null_mut()),
            _marker: PhantomData,
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::with_capacity(T::init_size())
    }

    pub fn with_capacity(cap: usize) -> Self {
        let mut block = Self::empty_block();

        unsafe {
            block.init_at_size(cap);
        }

        block
    }

    /// Returns a pointer to the data at `offset` within the allocated region.
    ///
    /// The returned pointer is invalidated by operations like [`grow`](Self::grow).
    ///
    /// The caller is responsible for ensuring that the return value points to
    /// valid objects, and that no mutable access may happen on it.
    pub fn get(&self, offset: usize) -> Option<*const u8> {
        if offset < self.capacity() {
            Some(unsafe {
                // SAFETY: Asserted: `offset < self.capacity()`.
                self.get_unchecked(offset)
            })
        } else {
            None
        }
    }

    /// The unchecked variant of [`RawBlock::get`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `offset < self.capacity()`
    pub unsafe fn get_unchecked(&self, offset: usize) -> *const u8 {
        // SAFETY:
        // - Invariant: `self.base + self.size() == self.top` is the top bound of
        //   the allocated region.
        // - Assumed: `offset < self.capacity()`
        // Thus `self.base + offset` is within the allocated region.
        self.base.add(offset)
    }

    /// The mutable equivalent of [`RawBlock::get`].
    /// Returns a pointer to the data at `offset` within the allocated region.
    ///
    /// The returned pointer is invalidated by operations like [`grow`](Self::grow).
    ///
    /// The caller is responsible for ensuring that the return value points to
    /// valid objects, and that no other mutable or immutable access may happen on it.
    pub fn get_mut(&mut self, offset: usize) -> Option<*mut u8> {
        self.get(offset).map(|ptr| ptr.cast_mut())
    }

    /// The unchecked variant of [`RawBlock::get_mut`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `offset < self.capacity()`
    pub unsafe fn get_mut_unchecked(&mut self, offset: usize) -> *mut u8 {
        unsafe {
            // SAFETY: Assumed: `offset < self.capacity()`
            self.get_unchecked(offset).cast_mut()
        }
    }

    /// Returns true iff `ptr` is within the allocated region of memory.
    pub fn contains(&self, ptr: *const u8) -> bool {
        (self.base..self.top).contains(&ptr)
    }

    /// Returns the offset of the pointer `ptr` within the allocated region.
    ///
    /// If `ptr` is not within the allocated region, returns `None`.
    pub fn offset_of(&self, ptr: *const u8) -> Option<usize> {
        if self.contains(ptr) {
            unsafe {
                // SAFETY: Asserted: `ptr` is between `self.start` and `self.end`.
                Some(self.offset_of_unchecked(ptr))
            }
        } else {
            None
        }
    }

    /// Returns the offset of the pointer `ptr` within the allocated region.
    ///
    /// # Safety
    ///
    /// Requires that `ptr` is between `self.start` and `self.end`.
    pub unsafe fn offset_of_unchecked(&self, ptr: *const u8) -> usize {
        unsafe {
            // SAFETY:
            // - Assumed: `ptr` is between `self.start` and `self.end`.
            // - Invariant: `self.start` and `self.end` are within the same allocated region.
            // Thus `ptr` is within the same allocated region as `ptr`.
            ptr.offset_from(self.base) as usize
        }
    }

    unsafe fn init_at_size(&mut self, cap: usize) {
        let layout = alloc::Layout::from_size_align_unchecked(cap, T::ALIGN);
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
            debug_assert!(size % T::ALIGN == 0);

            let layout = alloc::Layout::from_size_align_unchecked(size, T::ALIGN);

            debug_assert!(size < isize::MAX as usize / 2);

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
    #[deprecated(note = "Use RawBlock::capacity() instead")]
    pub fn size(&self) -> usize {
        self.capacity()
    }

    pub fn capacity(&self) -> usize {
        self.top as usize - self.base as usize
    }

    /// SAFETY: Assumes that no mutable borrow of `self.ptr` exists at this time.
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

    #[inline(always)]
    pub unsafe fn len(&self) -> usize {
        unsafe {
            // SAFETY:
            // - Invariant: `self.ptr` is between `self.base` and `self.top`
            // - Invariant: `self.base` and `self.top` belong to the same allocation
            // - Assumed: no other mutable borrow are currently active for `self.ptr`
            (*self.ptr.get()).cast_const().offset_from(self.base) as usize
        }
    }

    /// The reverse operation of [`alloc()`](RawBlock::alloc):
    /// moves the pointer to the first unused byte back.
    ///
    /// Subsequent calls to `alloc()` will re-use those bytes,
    /// invalidating any previously-stored data. For this reason,
    /// this function is marked as unsafe.
    ///
    /// Does not resize the allocated region of memory.
    pub unsafe fn truncate(&mut self, new_len: usize) {
        let new_ptr = self.get_mut(new_len).unwrap();

        if new_ptr < *self.ptr.get_mut() {
            *self.ptr.get_mut() = new_ptr as *mut _;
        }
    }

    pub unsafe fn alloc(&self, size: usize) -> *mut u8 {
        let aligned_size = size.next_multiple_of(T::ALIGN);

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
                let layout = alloc::Layout::from_size_align_unchecked(self.size(), T::ALIGN);
                alloc::dealloc(self.base as *mut _, layout);
            }

            self.top = ptr::null();
            self.base = ptr::null();
            *self.ptr.get_mut() = ptr::null_mut();
        }
    }
}
