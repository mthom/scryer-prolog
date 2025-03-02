use crate::atom_table::*;
use crate::forms::*;
use crate::functor_macro::*;
use crate::types::*;

use std::alloc;
use std::convert::TryFrom;
use std::ops::{Bound, Index, IndexMut, Range, RangeBounds};
use std::ptr;
use std::sync::Once;
use std::mem::size_of; // Not in prelude in 1.77

use super::MachineState;

const ALIGN: usize = Heap::heap_cell_alignment();

#[derive(Debug)]
pub struct Heap {
    inner: InnerHeap,
    resource_err_loc: usize,
}

impl Drop for Heap {
    fn drop(&mut self) {
        if !self.inner.ptr.is_null() {
            unsafe {
                let layout = alloc::Layout::array::<u8>(self.inner.byte_cap).unwrap();
                alloc::dealloc(self.inner.ptr, layout);
            }
        }
    }
}

// TODO: verify the soundness of the various accesses to `ptr`,
// or rely on a Vec-like library with fallible allocations.
#[derive(Debug)]
struct InnerHeap {
    ptr: *mut u8,

    /// # Safety
    ///
    /// Must be equal to zero when `ptr.is_null()`.
    byte_len: usize,

    /// # Safety
    ///
    /// Must be equal to zero when `ptr.is_null()`.
    byte_cap: usize,
}

impl InnerHeap {
    unsafe fn grow(&mut self) -> bool {
        let new_cap = if self.byte_cap == 0 {
            256 * 256 * 8
        } else {
            2 * self.byte_cap
        };

        let new_layout = alloc::Layout::array::<u8>(new_cap).unwrap();

        assert!(
            new_layout.size() <= isize::MAX as usize,
            "Allocation too large. We should probably GC (TODO)"
        );

        let new_ptr = if self.byte_cap == 0 {
            alloc::alloc(new_layout)
        } else {
            let old_layout = alloc::Layout::array::<u8>(self.byte_cap).unwrap();
            alloc::realloc(self.ptr, old_layout, new_layout.size())
        };

        if !new_ptr.is_null() {
            self.ptr = new_ptr;
            self.byte_cap = new_cap;

            true
        } else {
            false
        }
    }
}

unsafe impl Send for Heap {}
unsafe impl Sync for Heap {}

static RESOURCE_ERROR_OFFSET_INIT: Once = Once::new();

#[derive(Debug)]
pub struct HeapStringScan<'a> {
    pub string: &'a str,
    pub tail_idx: usize,
}

// return the string at ptr and the tail location relative to ptr.
unsafe fn scan_slice_to_str<'a>(heap_slice: &'a [u8]) -> HeapStringScan<'a> {
    let string_len = heap_slice.iter().position(|b| *b == 0u8).unwrap();
    let zero_byte_addr = heap_slice.as_ptr().add(string_len);
    let sentinel_len = pstr_sentinel_length(zero_byte_addr as usize);
    let tail_idx = cell_index!(
        (string_len + sentinel_len).next_multiple_of(ALIGN)
            + if sentinel_len <= 1 { heap_index!(1) } else { 0 }
    );

    let str_slice = &heap_slice[..string_len];

    HeapStringScan {
        string: std::str::from_utf8_unchecked(str_slice),
        tail_idx,
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PStrSegmentCmpResult {
    Mismatch {
        c1: char,
        c2: char,
    },
    FirstMatch {
        pstr_loc1: usize,
        pstr_loc2: usize,
        l1_offset: usize,
    },
    SecondMatch {
        pstr_loc1: usize,
        pstr_loc2: usize,
        l2_offset: usize,
    },
    BothMatch {
        pstr_loc1: usize,
        pstr_loc2: usize,
        null_offset: usize,
    },
}

impl PStrSegmentCmpResult {
    pub(crate) fn continue_pstr_compare(
        self,
        pdl: &mut Vec<HeapCellValue>,
    ) -> Option<std::cmp::Ordering> {
        match self {
            PStrSegmentCmpResult::FirstMatch {
                pstr_loc1,
                pstr_loc2,
                l1_offset,
            } => {
                let tail1 = Heap::pstr_tail_idx(pstr_loc1 + l1_offset);
                let rest_of_l2 = pstr_loc_as_cell!(pstr_loc2 + l1_offset);

                pdl.push(heap_loc_as_cell!(tail1));
                pdl.push(rest_of_l2);
            }
            PStrSegmentCmpResult::SecondMatch {
                pstr_loc1,
                pstr_loc2,
                l2_offset,
            } => {
                let tail2 = Heap::pstr_tail_idx(pstr_loc2 + l2_offset);
                let rest_of_l1 = pstr_loc_as_cell!(pstr_loc1 + l2_offset);

                pdl.push(rest_of_l1);
                pdl.push(heap_loc_as_cell!(tail2));
            }
            PStrSegmentCmpResult::BothMatch {
                pstr_loc1,
                pstr_loc2,
                null_offset,
            } => {
                // exhaustive match
                let tail1 = Heap::pstr_tail_idx(pstr_loc1 + null_offset);
                let tail2 = Heap::pstr_tail_idx(pstr_loc2 + null_offset);

                pdl.push(heap_loc_as_cell!(tail1));
                pdl.push(heap_loc_as_cell!(tail2));
            }
            PStrSegmentCmpResult::Mismatch { c1, c2 } => {
                return Some(c1.cmp(&c2));
            }
        }

        None
    }
}

#[derive(Debug)]
pub struct PStrWriteInfo {
    pstr_loc: usize,
}

#[derive(Debug)]
pub(crate) struct ReservedHeapSection {
    heap_ptr: *mut u8,
    heap_cell_len: usize,
}

impl ReservedHeapSection {
    #[inline]
    pub(crate) fn cell_len(&self) -> usize {
        self.heap_cell_len
    }

    pub(crate) fn push_cell(&mut self, cell: HeapCellValue) {
        unsafe {
            ptr::write(
                self.heap_ptr.add(heap_index!(self.heap_cell_len)) as *mut _,
                cell,
            );
        }
        // self.pstr_vec.push(false);
        self.heap_cell_len += 1;
    }

    fn push_pstr_segment(&mut self, src: &str) -> usize {
        if src.is_empty() {
            return 0;
        }

        let cells_written;
        let str_byte_len = src.len();

        unsafe {
            ptr::copy_nonoverlapping(
                src.as_ptr(),
                self.heap_ptr.add(heap_index!(self.heap_cell_len)),
                str_byte_len,
            );

            let zero_region_idx = heap_index!(self.heap_cell_len) + str_byte_len;

            let align_offset = pstr_sentinel_length(zero_region_idx);

            ptr::write_bytes(self.heap_ptr.add(zero_region_idx), 0u8, align_offset);

            cells_written = if align_offset == 1 {
                ptr::write_bytes(
                    self.heap_ptr.add(zero_region_idx + 1),
                    0u8,
                    size_of::<HeapCellValue>(),
                );

                // ensure there are at least two bytes in the boundary
                // buffer separating the string data from the tail
                // cell
                cell_index!(src.len() + align_offset + size_of::<HeapCellValue>())
            } else {
                cell_index!(src.len() + align_offset)
            };

            self.heap_cell_len += cells_written;
        }

        cells_written
    }

    pub(crate) fn push_pstr(&mut self, mut src: &str) -> Option<HeapCellValue> {
        let orig_h = self.cell_len();

        if src.is_empty() {
            return if orig_h == self.heap_cell_len {
                // src is empty and always was. nothing allocated
                // in this case, so nothing to point to in heap.
                None
            } else {
                self.push_cell(heap_loc_as_cell!(orig_h));
                Some(heap_loc_as_cell!(orig_h))
            };
        }

        loop {
            let null_char_idx = src.find('\u{0}').unwrap_or_else(|| src.len());
            let cells_written = self.push_pstr_segment(&src[0..null_char_idx]);
            let tail_idx = self.cell_len();

            if cells_written == 0 {
                return None;
            } else if null_char_idx + 1 < src.len() {
                self.push_cell(pstr_loc_as_cell!(heap_index!(tail_idx + 1)));
                src = &src[null_char_idx + 1..];
            } else {
                return Some(pstr_loc_as_cell!(heap_index!(orig_h)));
            }
        }
    }

    pub(crate) fn functor_writer(
        functor: Vec<FunctorElement>,
    ) -> impl FnMut(&mut ReservedHeapSection) {
        struct FunctorData<'a> {
            functor: &'a Vec<FunctorElement>,
            cell_offset: usize,
            cursor: usize,
        }

        move |section| {
            let mut functor_stack = vec![FunctorData {
                functor: &functor,
                cell_offset: section.heap_cell_len,
                cursor: 0,
            }];

            while let Some(FunctorData {
                functor,
                cell_offset,
                mut cursor,
            }) = functor_stack.pop()
            {
                while cursor < functor.len() {
                    match &functor[cursor] {
                        &FunctorElement::AbsoluteCell(cell) => {
                            section.push_cell(cell);
                        }
                        &FunctorElement::Cell(cell) => {
                            section.push_cell(cell + cell_offset);
                        }
                        &FunctorElement::String(_cell_len, ref string) => {
                            if section.push_pstr(&string).is_some() {
                                section.push_cell(empty_list_as_cell!());
                            }
                        }
                        FunctorElement::InnerFunctor(_inner_size, succ_functor) => {
                            if cursor + 1 < functor.len() {
                                functor_stack.push(FunctorData {
                                    functor: &functor,
                                    cell_offset,
                                    cursor: cursor + 1,
                                });
                            }

                            functor_stack.push(FunctorData {
                                functor: succ_functor,
                                cell_offset: section.heap_cell_len,
                                cursor: 0,
                            });

                            break;
                        }
                    }

                    cursor += 1;
                }
            }
        }
    }
}

impl Index<usize> for ReservedHeapSection {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, idx: usize) -> &Self::Output {
        debug_assert!(idx < self.heap_cell_len);
        unsafe { &*(self.heap_ptr as *const HeapCellValue).add(idx) }
    }
}

/// Computes the number of bytes required to pad a string of length `chunk_len`
/// with zeroes, such that `chunk_len + pstr_sentinel_length(chunk_len)` is a
/// multiple of `Heap::heap_cell_alignement()`.
fn pstr_sentinel_length(chunk_len: usize) -> usize {
    let res = chunk_len.next_multiple_of(ALIGN) - chunk_len;

    // No bytes available in last chunk
    if res == 0 {
        ALIGN
    } else {
        res
    }
}

#[must_use]
#[derive(Debug)]
pub struct HeapWriter<'a> {
    section: ReservedHeapSection,
    heap_byte_len: &'a mut usize,
}

impl<'a> HeapWriter<'a> {
    #[allow(dead_code)]
    pub(crate) fn write_with_error_handling<E>(
        &mut self,
        writer: impl FnOnce(&mut ReservedHeapSection) -> Result<(), E>,
    ) -> Result<usize, E> {
        let old_section_cell_len = self.section.heap_cell_len;
        writer(&mut self.section)?;
        *self.heap_byte_len = heap_index!(self.section.heap_cell_len);

        // return the number of bytes written
        Ok(heap_index!(
            self.section.heap_cell_len - old_section_cell_len
        ))
    }

    pub(crate) fn write_with(&mut self, writer: impl FnOnce(&mut ReservedHeapSection)) -> usize {
        let old_section_cell_len = self.section.heap_cell_len;
        writer(&mut self.section);
        *self.heap_byte_len = heap_index!(self.section.heap_cell_len);

        // return the number of bytes written
        heap_index!(self.section.heap_cell_len - old_section_cell_len)
    }

    #[inline]
    pub(crate) fn truncate(&mut self, cell_offset: usize) {
        self.section.heap_cell_len = cell_offset;
        // self.section.pstr_vec.truncate(cell_offset);
        *self.heap_byte_len = heap_index!(cell_offset);
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.section.heap_cell_len == 0
    }

    #[inline]
    pub(crate) fn cell_len(&self) -> usize {
        self.section.heap_cell_len
    }
}

impl<'a> Index<usize> for HeapWriter<'a> {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, idx: usize) -> &Self::Output {
        debug_assert!(heap_index!(idx) < *self.heap_byte_len);
        unsafe { &*(self.section.heap_ptr.add(heap_index!(idx)) as *const HeapCellValue) }
    }
}

impl<'a> IndexMut<usize> for HeapWriter<'a> {
    #[inline]
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        debug_assert!(heap_index!(idx) < *self.heap_byte_len);
        unsafe { &mut *(self.section.heap_ptr.add(heap_index!(idx)) as *mut HeapCellValue) }
    }
}

impl<'a> SizedHeap for HeapWriter<'a> {
    fn cell_len(&self) -> usize {
        self.section.cell_len()
    }

    fn scan_slice_to_str(&self, slice_loc: usize) -> HeapStringScan {
        let HeapStringScan { string, tail_idx } = unsafe {
            let slice = std::slice::from_raw_parts(
                self.section.heap_ptr.byte_add(slice_loc),
                heap_index!(self.section.heap_cell_len) - slice_loc,
            );

            scan_slice_to_str(slice)
        };

        HeapStringScan {
            string,
            tail_idx: cell_index!(slice_loc) + tail_idx,
        }
    }

    fn as_slice(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(
                self.section.heap_ptr,
                heap_index!(self.section.heap_cell_len),
            )
        }
    }
}

impl<'a> SizedHeapMut for HeapWriter<'a> {}

impl Heap {
    pub(crate) fn new() -> Self {
        Self {
            inner: InnerHeap {
                ptr: ptr::null_mut(),
                byte_len: 0,
                byte_cap: 0,
            },
            resource_err_loc: 0,
        }
    }

    // takes a heap index, returns a cell index
    #[inline]
    pub const fn pstr_tail_idx(pstr_zero_byte_loc: usize) -> usize {
        if (pstr_zero_byte_loc + 1) % Heap::heap_cell_alignment() == 0 {
            cell_index!(pstr_zero_byte_loc) + 2
        } else {
            cell_index!(pstr_zero_byte_loc) + 1
        }
    }

    #[inline(always)]
    unsafe fn grow(&mut self) -> bool {
        self.inner.grow()
    }

    #[inline]
    fn resource_error_offset(&self) -> usize {
        self.resource_err_loc
    }

    pub(crate) fn with_cell_capacity(cap: usize) -> Result<Self, usize> {
        let ptr = unsafe {
            let layout = alloc::Layout::array::<HeapCellValue>(cap).unwrap();
            alloc::alloc(layout)
        };

        if ptr.is_null() {
            panic!("could not allocate {} bytes for heap!", heap_index!(cap))
        } else {
            Ok(Self {
                inner: InnerHeap {
                    ptr,
                    byte_len: 0,
                    byte_cap: heap_index!(cap),
                },
                // pstr_vec: bitvec![],
                resource_err_loc: 0,
            })
        }
    }

    #[must_use]
    pub fn reserve(&mut self, num_cells: usize) -> Result<HeapWriter, usize> {
        let section;
        let len = heap_index!(num_cells);

        loop {
            unsafe {
                if self.free_space() >= len {
                    section = ReservedHeapSection {
                        heap_ptr: self.inner.ptr,
                        heap_cell_len: self.cell_len(),
                    };
                    break;
                } else if !self.grow() {
                    return Err(self.resource_error_offset());
                }
            }
        }

        Ok(HeapWriter {
            section,
            heap_byte_len: &mut self.inner.byte_len,
        })
    }

    pub(crate) fn last_cell(&mut self) -> Option<HeapCellValue> {
        if self.inner.byte_len == 0 {
            None
        } else {
            unsafe {
                Some(ptr::read(
                    self.inner.ptr.add(self.inner.byte_len - heap_index!(1))
                        as *const HeapCellValue,
                ))
            }
        }
    }

    pub(crate) fn append(&mut self, other_heap: &impl SizedHeap) -> Result<(), usize> {
        let other_len = heap_index!(other_heap.cell_len());

        loop {
            if self.free_space() >= other_len {
                let heap_slice = unsafe {
                    std::slice::from_raw_parts_mut(
                        self.inner.ptr.add(self.inner.byte_len),
                        other_len,
                    )
                };

                heap_slice.copy_from_slice(other_heap.as_slice());
                self.inner.byte_len += heap_index!(other_heap.cell_len());
                break;
            } else if unsafe { !self.grow() } {
                return Err(self.resource_error_offset());
            }
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.inner.byte_len == 0
    }

    pub(crate) fn index_of(&mut self, cell: HeapCellValue) -> Result<usize, usize> {
        Ok(if cell.is_var() {
            cell.get_value() as usize
        } else {
            let focus = self.cell_len();
            self.push_cell(cell)?;
            focus
        })
    }

    pub(crate) fn clear(&mut self) {
        unsafe {
            let layout = alloc::Layout::array::<u8>(self.inner.byte_cap).unwrap();
            alloc::dealloc(self.inner.ptr, layout);
        }

        self.inner.ptr = ptr::null_mut();
        self.inner.byte_len = 0;
        self.inner.byte_cap = 0;

        // self.pstr_vec.clear();
    }

    // pub(crate) fn append(&mut self, heap_slice: HeapView) -> Result<(), usize> {
    //     unsafe {
    //         loop {
    //             if self.free_space() >= heap_index!(heap_slice.slice_cell_len) {
    //                 ptr::copy_nonoverlapping(
    //                     heap_slice.slice,
    //                     self.inner.ptr.add(self.inner.byte_len),
    //                     heap_index!(heap_slice.slice_cell_len),
    //                 );

    //                 self.inner.byte_len += heap_index!(heap_slice.slice_cell_len);
    //                 // self.pstr_vec.extend(heap_slice.pstr_slice.iter());

    //                 break;
    //             } else if !self.grow() {
    //                 return Err(self.resource_error_offset());
    //             }
    //         }
    //     }

    //     Ok(())
    // }

    pub(crate) fn store_resource_error(&mut self) {
        RESOURCE_ERROR_OFFSET_INIT.call_once(move || {
            let stub = functor!(atom!("resource_error"), [atom_as_cell((atom!("memory")))]);
            self.resource_err_loc = cell_index!(self.inner.byte_len);

            let mut writer = Heap::functor_writer(stub);
            writer(self).unwrap();
        });
    }

    pub(crate) fn compare_pstr_segments(
        &self,
        pstr_loc1: usize,
        pstr_loc2: usize,
    ) -> PStrSegmentCmpResult {
        unsafe {
            let slice1 = std::slice::from_raw_parts(
                self.inner.ptr.add(pstr_loc1),
                self.inner.byte_len - pstr_loc1,
            );

            let slice2 = std::slice::from_raw_parts(
                self.inner.ptr.add(pstr_loc2),
                self.inner.byte_len - pstr_loc2,
            );

            let str1 = std::str::from_utf8_unchecked(&slice1);
            let str2 = std::str::from_utf8_unchecked(&slice2);

            debug_assert!(!str1.is_empty());
            debug_assert!(!str2.is_empty());

            for ((idx, c1), c2) in str1.char_indices().zip(str2.chars()) {
                if c1 == '\u{0}' && c2 == '\u{0}' {
                    return PStrSegmentCmpResult::BothMatch {
                        pstr_loc1,
                        pstr_loc2,
                        null_offset: idx,
                    };
                } else if c1 == '\u{0}' {
                    return PStrSegmentCmpResult::FirstMatch {
                        pstr_loc1,
                        pstr_loc2,
                        l1_offset: idx,
                    };
                } else if c2 == '\u{0}' {
                    return PStrSegmentCmpResult::SecondMatch {
                        pstr_loc1,
                        pstr_loc2,
                        l2_offset: idx,
                    };
                } else if c1 != c2 {
                    return PStrSegmentCmpResult::Mismatch { c1, c2 };
                }
            }

            unreachable!() // PStrSegmentCmpResult::Match(std::cmp::min(str1.len(), str2.len()))
        }
    }

    #[inline]
    pub(crate) fn slice_to_str(&self, slice_loc: usize, slice_len: usize) -> &str {
        unsafe {
            let slice = std::slice::from_raw_parts(self.inner.ptr.add(slice_loc), slice_len);
            std::str::from_utf8_unchecked(&slice)
        }
    }

    #[inline]
    pub(crate) fn byte_len(&self) -> usize {
        self.inner.byte_len
    }

    #[inline]
    pub(crate) fn cell_len(&self) -> usize {
        cell_index!(self.inner.byte_len)
    }

    // free space in bytes.
    #[inline]
    fn free_space(&self) -> usize {
        self.inner.byte_cap - self.inner.byte_len
    }

    pub(crate) fn char_iter<'a>(&'a self, pstr_loc: usize) -> PStrSegmentIter<'a> {
        PStrSegmentIter::from(self, pstr_loc)
    }

    // either succeed & return nothing or fail & return an offset into
    // the heap to a pre-allocated resource error
    pub(crate) fn push_cell(&mut self, cell: HeapCellValue) -> Result<(), usize> {
        unsafe {
            if self.inner.byte_len == self.inner.byte_cap {
                if !self.grow() {
                    return Err(self.resource_error_offset());
                }
            }

            // SAFETY:
            // - Postcondition: from `self.grow()`, `self.inner.byte_len + size_of::<HeapCellValue>()`
            //   is strictly less than `self.inner.byte_cap`.
            // - Asserted: `self.cell_len() * size_of::<HeapCellvalue>() <= self.inner.byte_cap`.
            // - Invariant: from `InnerHeap`, `self.inner.byte_cap < isize::MAX`.
            let cell_ptr = (self.inner.ptr as *mut HeapCellValue).add(self.cell_len());
            cell_ptr.write(cell);
            // self.pstr_vec.push(false);
            self.inner.byte_len += heap_index!(1);
        }

        Ok(())
    }

    /*
    pub(crate) fn pop_cell(&mut self) -> Option<HeapCellValue> {
        unsafe {
            if self.inner.byte_len > 0 {
                let cell_ptr = (self.inner.ptr as *const HeapCellValue)
                    .add(self.cell_len())
                    .sub(1);
                let cell = ptr::read(cell_ptr);

                self.inner.byte_len -= heap_index!(1);
                self.pstr_vec.pop();

                Some(cell)
            } else {
                None
            }
        }
    }
    */

    fn slice_range<R: RangeBounds<usize>>(&self, range: R) -> Range<usize> {
        let start = match range.start_bound() {
            Bound::Included(lower_bound) => *lower_bound,
            Bound::Excluded(lower_bound) => *lower_bound + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(upper_bound) => *upper_bound + 1,
            Bound::Excluded(0) => 0,
            Bound::Excluded(upper_bound) => *upper_bound,
            Bound::Unbounded => self.cell_len(),
        };

        Range { start, end }
    }

    /*
    pub(crate) fn splice<R: RangeBounds<usize>>(
        &self,
        range: R,
    ) -> HeapView {
        let range = self.slice_range(range);

        HeapView {
            slice: unsafe { self.inner.ptr.add(heap_index!(range.start)) },
            cell_offset: range.start,
            slice_cell_len: range.end - range.start,
            // pstr_slice: &self.pstr_vec.as_bitslice()[range],
        }
    }

    pub(crate) fn splice_mut<R: RangeBounds<usize>>(
        &self,
        range: R,
    ) -> HeapViewMut {
        let range = self.slice_range(range);

        HeapViewMut {
            slice: unsafe { self.inner.ptr.add(heap_index!(range.start)) },
            cell_offset: range.start,
            slice_cell_len: range.end - range.start,
            // pstr_slice: &self.pstr_vec.as_bitslice()[range],
        }
    }
    */

    pub fn allocate_pstr(&mut self, src: &str) -> Result<Option<PStrWriteInfo>, usize> {
        let size_in_heap = Self::compute_pstr_size(src);
        let pstr_loc = heap_index!(self.cell_len());

        Ok(if size_in_heap > 0 {
            let mut writer = self.reserve(size_in_heap)?;

            writer.write_with(|section| {
                section.push_pstr(src);
            });

            Some(PStrWriteInfo { pstr_loc })
        } else {
            None
        })
    }

    pub const fn heap_cell_alignment() -> usize {
        // yes, size_of, not align_of. the alignment of HeapCellValue
        // is 1 byte. In the heap, though, its alignment must be its
        // size.
        size_of::<HeapCellValue>()
    }

    #[inline]
    pub(crate) fn char_at(&self, byte_idx: usize) -> char {
        let s = unsafe {
            let char_ptr = self.inner.ptr.add(byte_idx);
            let slice = std::slice::from_raw_parts(char_ptr, size_of::<char>());
            std::str::from_utf8_unchecked(&slice)
        };

        s.chars().next().unwrap()
    }

    pub(crate) fn last_str_char_and_tail(&self, loc: usize) -> (char, HeapCellValue) {
        unsafe {
            let char_ptr = self.inner.ptr.add(loc);
            let slice = std::slice::from_raw_parts(char_ptr, self.inner.byte_len - loc);

            let s = std::str::from_utf8_unchecked(&slice);
            let mut chars_iter = s.chars();
            let c = chars_iter.next().unwrap();
            let succ_len = loc + c.len_utf8();

            if chars_iter.next() == Some('\u{0}') {
                (c, heap_loc_as_cell!(Self::pstr_tail_idx(succ_len)))
            } else {
                (c, pstr_loc_as_cell!(succ_len))
            }
        }
    }

    // copies only the string, not its tail. returns the cell index of
    // the tail location
    pub(crate) fn copy_pstr_within(&mut self, pstr_loc: usize) -> Result<usize, usize> {
        let HeapStringScan { string, tail_idx } = self.scan_slice_to_str(pstr_loc);
        let s_len = string.len();

        let align_offset = pstr_sentinel_length(s_len);
        let copy_size = s_len + align_offset;

        unsafe {
            loop {
                if self.free_space() >= copy_size {
                    let slice =
                        std::slice::from_raw_parts_mut(self.inner.ptr, self.inner.byte_len + s_len);

                    slice.copy_within(pstr_loc..pstr_loc + s_len, self.inner.byte_len);

                    ptr::write_bytes(
                        self.inner.ptr.add(self.inner.byte_len + s_len),
                        0u8,
                        align_offset,
                    );

                    if align_offset == 1 {
                        ptr::write_bytes(
                            self.inner.ptr.add(self.inner.byte_len + copy_size),
                            0u8,
                            size_of::<HeapCellValue>(),
                        );

                        self.inner.byte_len += copy_size + heap_index!(1);
                    } else {
                        self.inner.byte_len += copy_size;
                    }

                    break;
                } else if !self.grow() {
                    return Err(self.resource_error_offset());
                }
            }
        }

        Ok(tail_idx)
    }

    // src is a cell-indexed range.
    pub(crate) fn copy_slice_to_end<R: RangeBounds<usize>>(&mut self, src: R) -> Result<(), usize> {
        let range = self.slice_range(src);
        let len = range.end - range.start;

        unsafe {
            loop {
                if self.free_space() >= len {
                    ptr::copy_nonoverlapping(
                        self.inner.ptr.add(heap_index!(range.start)),
                        self.inner.ptr.add(self.inner.byte_len),
                        heap_index!(len),
                    );

                    // self.pstr_vec.resize(self.cell_len() + len, false);
                    self.inner.byte_len += heap_index!(len);

                    break;
                } else if !self.grow() {
                    return Err(self.resource_error_offset());
                }
            }
        }

        Ok(())
    }

    /// Returns the number of bytes needed to store `src` as a `PStr`.
    /// Assumes the string will be allocated on a ALIGN-byte boundary.
    pub(crate) fn compute_pstr_size(src: &str) -> usize {
        if src.is_empty() {
            return 0;
        }

        let mut byte_size = 0;
        let mut null_idx = 0;

        loop {
            let src_bytes = src.as_bytes();

            while null_idx < src_bytes.len() {
                if src_bytes[null_idx] == 0u8 {
                    break;
                }

                null_idx += 1;
            }

            byte_size += null_idx + pstr_sentinel_length(null_idx);

            // each partial string must be buffered from its tail cell
            // by at least two null bytes so one of them may be used
            // to mark partial strings e.g. during iteration

            if (null_idx + 1) % ALIGN == 0 {
                byte_size += 2 * size_of::<HeapCellValue>();
            } else {
                byte_size += size_of::<HeapCellValue>();
            }

            if null_idx + 1 >= src.len() {
                break;
            } else {
                null_idx += 1;
            }
        }

        byte_size
    }

    pub(crate) const fn compute_functor_byte_size(functor: &[FunctorElement]) -> usize {
        let mut byte_size = 0;
        let mut idx = 0;

        while idx < functor.len() {
            match &functor[idx] {
                &FunctorElement::InnerFunctor(inner_cell_size, ref _inner_functor) => {
                    byte_size += inner_cell_size as usize * size_of::<HeapCellValue>();
                }
                FunctorElement::AbsoluteCell(_cell) | FunctorElement::Cell(_cell) => {
                    byte_size += size_of::<HeapCellValue>();
                }
                &FunctorElement::String(cell_len, _) => {
                    byte_size += cell_len as usize * size_of::<HeapCellValue>();
                }
            }

            idx += 1;
        }

        byte_size
    }

    pub(crate) fn functor_writer(
        functor: Vec<FunctorElement>,
    ) -> impl FnMut(&mut Heap) -> Result<HeapCellValue, usize> {
        let size = Heap::compute_functor_byte_size(&functor);
        let mut functor_writer = ReservedHeapSection::functor_writer(functor);

        move |heap| {
            let mut writer = heap.reserve(size)?;
            let heap_byte_len = *writer.heap_byte_len;
            let bytes_written = writer.write_with(&mut functor_writer);

            Ok(if cell_index!(bytes_written) > 1 {
                str_loc_as_cell!(cell_index!(heap_byte_len))
            } else {
                heap_loc_as_cell!(cell_index!(heap_byte_len))
            })
        }
    }

    #[inline]
    pub(crate) fn truncate(&mut self, cell_offset: usize) {
        self.inner.byte_len = heap_index!(cell_offset);
        // self.pstr_vec.truncate(cell_offset);
    }
}

pub(crate) struct PStrSegmentIter<'a> {
    string_buf: &'a str,
}

impl<'a> PStrSegmentIter<'a> {
    fn from(heap: &'a Heap, pstr_loc: usize) -> Self {
        debug_assert!(pstr_loc <= heap.inner.byte_len);

        let string_buf = unsafe {
            let char_ptr = heap.inner.ptr.add(pstr_loc);
            let slice = std::slice::from_raw_parts(char_ptr, heap.inner.byte_len - pstr_loc);
            std::str::from_utf8_unchecked(&slice)
        };

        PStrSegmentIter { string_buf }
    }
}

impl<'a> Iterator for PStrSegmentIter<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.string_buf.chars().next().and_then(|c| {
            if c == '\u{0}' {
                None
            } else {
                self.string_buf = &self.string_buf[c.len_utf8()..];
                Some(c)
            }
        })
    }
}

impl MachineState {
    pub(crate) fn allocate_pstr(&mut self, src: &str) -> Result<HeapCellValue, usize> {
        match self.heap.allocate_pstr(src)? {
            None => Ok(empty_list_as_cell!()),
            Some(PStrWriteInfo { pstr_loc, .. }) => Ok(pstr_loc_as_cell!(pstr_loc)),
        }
    }

    // note that allocate_cstr does emit a tail cell to the string
    // (completing it with the empty list), allocate_pstr does not, in
    // any incarnation.
    pub(crate) fn allocate_cstr(&mut self, src: &str) -> Result<HeapCellValue, usize> {
        match self.heap.allocate_pstr(src)? {
            None => Ok(empty_list_as_cell!()),
            Some(PStrWriteInfo { pstr_loc, .. }) => {
                self.heap.push_cell(empty_list_as_cell!())?;
                Ok(pstr_loc_as_cell!(pstr_loc))
            }
        }
    }
}

pub trait SizedHeap: Index<usize, Output = HeapCellValue> {
    // return the size of the instance in cells
    fn cell_len(&self) -> usize;

    // return a pointer to the heap string and the cell index of its tail
    fn scan_slice_to_str<'a>(&'a self, slice_loc: usize) -> HeapStringScan<'a>;

    fn as_slice(&self) -> &[u8];

    // return true iff a partial string is stored at cell_offset.
    // fn pstr_at(&self, cell_offset: usize) -> bool;
}

pub trait SizedHeapMut: IndexMut<usize, Output = HeapCellValue> + SizedHeap {}

impl Index<usize> for Heap {
    type Output = HeapCellValue;

    fn index(&self, idx: usize) -> &Self::Output {
        unsafe { &*(self.inner.ptr as *const HeapCellValue).add(idx) }
    }
}

impl IndexMut<usize> for Heap {
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        unsafe { &mut *(self.inner.ptr as *mut HeapCellValue).add(idx) }
    }
}

impl SizedHeap for Heap {
    fn cell_len(&self) -> usize {
        self.cell_len()
    }

    fn scan_slice_to_str<'a>(&'a self, slice_loc: usize) -> HeapStringScan<'a> {
        let HeapStringScan { string, tail_idx } = unsafe {
            let slice = std::slice::from_raw_parts(
                self.inner.ptr.add(slice_loc),
                self.inner.byte_len - slice_loc,
            );

            scan_slice_to_str(slice)
        };

        HeapStringScan {
            string,
            tail_idx: cell_index!(slice_loc) + tail_idx,
        }
    }

    fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.inner.ptr, self.inner.byte_len) }
    }
}

impl SizedHeapMut for Heap {}

// sometimes we need to dereference variables that are found only in
// the heap without access to the full WAM (e.g., while detecting
// cycles in terms), and which therefore may only point other cells in
// the heap (thanks to the design of the WAM).
pub fn heap_bound_deref(heap: &impl SizedHeap, mut value: HeapCellValue) -> HeapCellValue {
    loop {
        let new_value = read_heap_cell!(value,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                heap[h]
            }
            _ => {
                value
            }
        );

        if new_value != value && new_value.is_var() {
            value = new_value;
            continue;
        }

        return value;
    }
}

pub fn heap_bound_store(heap: &impl SizedHeap, value: HeapCellValue) -> HeapCellValue {
    read_heap_cell!(value,
        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
            heap[h]
        }
        _ => {
            value
        }
    )
}

#[allow(dead_code)]
pub fn print_heap_terms(heap: &Heap, h: usize) {
    for idx in 0..heap.cell_len() {
        let term = heap[idx];
        println!("{} : {:?}", h + idx, term);
    }
}

pub fn sized_iter_to_heap_list<SrcT: Into<HeapCellValue>>(
    heap: &mut Heap,
    size: usize,
    values: impl Iterator<Item = SrcT>,
) -> Result<HeapCellValue, usize> {
    if size > 0 {
        let h = heap.cell_len();
        let mut writer = heap.reserve(1 + 2 * size)?;

        writer.write_with(|section| {
            for (idx, value) in values.enumerate() {
                section.push_cell(list_loc_as_cell!(h + 1 + 2 * idx));
                section.push_cell(value.into());
            }

            section.push_cell(empty_list_as_cell!());
        });

        Ok(heap_loc_as_cell!(h))
    } else {
        Ok(empty_list_as_cell!())
    }
}

pub(crate) fn to_local_code_ptr(heap: &Heap, addr: HeapCellValue) -> Option<usize> {
    let extract_integer = |s: usize| -> Option<usize> {
        match Number::try_from(heap[s]) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                Some(value)
            }
            _ => None,
        }
    };

    read_heap_cell!(addr,
        (HeapCellValueTag::Str, s) => {
            let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

            if name == atom!("dir_entry") && arity == 1 {
                extract_integer(s+1)
            } else {
                panic!(
                    "to_local_code_ptr crashed with p.i. {}/{}",
                    name.as_str(),
                    arity,
                );
            }
        }
        _ => {
            None
        }
    )
}
