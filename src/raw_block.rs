use core::marker::PhantomData;

use std::alloc;
use std::cell::Cell;
use std::ptr;

pub trait RawBlockTraits {
    /// Must be a multiple of `ALIGN`.
    fn init_size() -> usize;

    const ALIGN: usize;
}

/// A handle to an allocated region of bytes, which is used to store an array of DSTs.
#[derive(Debug)]
pub struct RawBlock<T: RawBlockTraits> {
    /// # Safety
    ///
    /// Should be aligned to [`T::ALIGN`](RawBlockTraits::ALIGN).
    ///
    /// Should point to the start of the currently-allocated region.
    base: *const u8,

    /// # Safety
    ///
    /// Should be aligned to [`T::ALIGN`](RawBlockTraits::ALIGN).
    ///
    /// Should point to the end of the currently-allocated region.
    top: *const u8,

    /// # Safety
    ///
    /// `head <= self.capacity()`
    ///
    /// `head` must always be a multiple of [`T::ALIGN`](RawBlockTraits::ALIGN).
    head: Cell<usize>,

    _marker: PhantomData<T>,
}

impl<T: RawBlockTraits> RawBlock<T> {
    #[inline]
    pub(crate) fn empty_block() -> Self {
        RawBlock {
            base: ptr::null(),
            top: ptr::null(),
            head: Cell::new(0),
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
        if offset < self.len() {
            Some(unsafe {
                // SAFETY: Asserted: `offset < self.len()`.
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
    /// The caller must ensure that `offset < self.len()`
    pub unsafe fn get_unchecked(&self, offset: usize) -> *const u8 {
        // SAFETY:
        // - Invariant: `self.base + self.size() == self.top` is the top bound of
        //   the allocated region.
        // - Assumed: `offset < self.len()`
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
    #[allow(dead_code)]
    pub fn get_mut(&mut self, offset: usize) -> Option<*mut u8> {
        self.get(offset).map(|ptr| ptr.cast_mut())
    }

    /// The unchecked variant of [`RawBlock::get_mut`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `offset < self.len()`
    pub unsafe fn get_mut_unchecked(&mut self, offset: usize) -> *mut u8 {
        unsafe {
            // SAFETY: Assumed: `offset < self.len()`
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
        self.head.set(0);
    }

    pub unsafe fn grow(&mut self) -> bool {
        if self.base.is_null() {
            self.init_at_size(T::init_size());
            true
        } else {
            let capacity = self.capacity();
            debug_assert!(capacity % T::ALIGN == 0);

            let layout = alloc::Layout::from_size_align_unchecked(capacity, T::ALIGN);

            debug_assert!(capacity < isize::MAX as usize / 2);

            let new_base = alloc::realloc(self.base.cast_mut(), layout, capacity * 2).cast_const();
            if new_base.is_null() {
                false
            } else {
                self.base = new_base;
                self.top = self.base.add(capacity * 2);
                true
            }
        }
    }

    pub unsafe fn grow_new(&self) -> Option<Self> {
        if self.base.is_null() {
            Some(Self::new())
        } else {
            let mut new_block = Self::empty_block();
            new_block.init_at_size(self.capacity() * 2);
            if new_block.base.is_null() {
                // allocation failed
                None
            } else {
                let allocated = self.len();
                self.base.copy_to(new_block.base.cast_mut(), allocated);
                new_block.head.set(allocated);
                Some(new_block)
            }
        }
    }

    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.top as usize - self.base as usize
    }

    #[inline(always)]
    fn free_space(&self) -> usize {
        self.capacity() - self.len()
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.head.get()
    }

    /// The reverse operation of [`alloc()`](RawBlock::alloc):
    /// moves the pointer to the first unused byte back.
    ///
    /// Subsequent calls to `alloc()` will re-use those bytes,
    /// invalidating any previously-stored data. For this reason,
    /// this function is marked as unsafe.
    ///
    /// Does not resize the allocated region of memory.
    ///
    /// Panics if `new_len` is not a multiple of [`T::ALIGN`](RawBlockTraits::ALIGN).
    pub unsafe fn truncate(&mut self, new_len: usize) {
        assert_eq!(
            new_len % T::ALIGN,
            0,
            "RawBlock::truncate(new_len = {new_len}) requires new_len to be aligned to {}",
            T::ALIGN
        );

        let head = self.head.get_mut();
        if new_len < *head {
            *head = new_len;
        }
    }

    /// Allocates `size` bytes into the buffer, returning a mutable
    /// pointer to beginning of them. If there are not enough bytes available,
    /// returns [`ptr::null_mut()`].
    ///
    /// If non-null, the return value is guaranteed to point to
    /// at least `size` bytes of unused memory.
    ///
    /// The return value is aligned to [`T::ALIGN`](RawBlockTraits::ALIGN).
    pub unsafe fn alloc(&self, size: usize) -> *mut u8 {
        let aligned_size = size.next_multiple_of(T::ALIGN);

        if self.free_space() >= aligned_size {
            let head = self.head.get();
            self.head.set(head + aligned_size);
            unsafe { self.get_unchecked(head).cast_mut() }
        } else {
            ptr::null_mut()
        }
    }
}

impl<T: RawBlockTraits> Drop for RawBlock<T> {
    fn drop(&mut self) {
        if !self.base.is_null() {
            unsafe {
                let layout = alloc::Layout::from_size_align_unchecked(self.capacity(), T::ALIGN);
                alloc::dealloc(self.base as *mut _, layout);
            }

            self.top = ptr::null();
            self.base = ptr::null();
            self.head.set(0);
        }
    }
}
