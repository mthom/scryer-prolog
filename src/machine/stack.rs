use core::marker::PhantomData;

use crate::raw_block::*;
use crate::types::*;

use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

/// TODO: remove this in favor of [`Ord::max`] once const fns
/// can be added in traits (https://github.com/rust-lang/rust/issues/67792)
const fn usize_max(lhs: usize, rhs: usize) -> usize {
    if lhs > rhs {
        lhs
    } else {
        rhs
    }
}

impl RawBlockTraits for Stack {
    #[inline]
    fn init_size() -> usize {
        10 * 1024 * 1024
    }

    const ALIGN: usize = usize_max(
        usize_max(mem::align_of::<OrFrame>(), mem::align_of::<AndFrame>()),
        mem::align_of::<HeapCellValue>(),
    );
}

#[inline(always)]
pub const fn prelude_size<Prelude>() -> usize {
    mem::size_of::<Prelude>()
}

#[derive(Debug)]
pub struct Stack {
    buf: RawBlock<Stack>,
    _marker: PhantomData<HeapCellValue>,
}

#[derive(Debug)]
pub(crate) struct AndFramePrelude {
    pub(crate) num_cells: usize,
    pub(crate) e: usize,
    pub(crate) cp: usize,
}

#[derive(Debug)]
pub(crate) struct AndFrame {
    pub(crate) prelude: AndFramePrelude,
}

impl AndFrame {
    pub(crate) fn size_of(num_cells: usize) -> usize {
        prelude_size::<AndFramePrelude>() + num_cells * mem::size_of::<HeapCellValue>()
    }
}

impl Index<usize> for AndFrame {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(
            index > 0 && index <= self.prelude.num_cells,
            "Invalid index within AndFrame: {index} not in 1..={}",
            self.prelude.num_cells
        );
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *const crate::machine::stack::AndFrame as *const u8;
            let ptr = ptr as usize + prelude_offset + index_offset;

            &*(ptr as *const HeapCellValue)
        }
    }
}

impl IndexMut<usize> for AndFrame {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(
            index > 0 && index <= self.prelude.num_cells,
            "Invalid index within AndFrame: {index} not in 1..={}",
            self.prelude.num_cells
        );
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *mut crate::machine::stack::AndFrame as *const u8;
            let ptr = ptr as usize + prelude_offset + index_offset;

            &mut *(ptr as *mut HeapCellValue)
        }
    }
}

impl Index<usize> for Stack {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            // TODO: implement some mechanism to verify soundness
            let ptr = self.buf.get(index).unwrap();
            &*(ptr as *const HeapCellValue)
        }
    }
}

impl IndexMut<usize> for Stack {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let ptr = self.buf.get_mut_unchecked(index);
            &mut *(ptr as *mut HeapCellValue)
        }
    }
}

#[derive(Debug)]
pub(crate) struct OrFramePrelude {
    pub(crate) num_cells: usize,
    pub(crate) e: usize,
    pub(crate) cp: usize,
    pub(crate) b: usize,
    pub(crate) bp: usize,
    pub(crate) boip: u32,
    pub(crate) biip: u32,
    pub(crate) tr: usize,
    pub(crate) h: usize,
    pub(crate) b0: usize,
    pub(crate) attr_var_queue_len: usize,
}

#[derive(Debug)]
pub(crate) struct OrFrame {
    pub(crate) prelude: OrFramePrelude,
}

impl Index<usize> for OrFrame {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        assert!(
            index < self.prelude.num_cells,
            "Invalid index within OrFrame: {index} not in 0..{}",
            self.prelude.num_cells
        );
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *const crate::machine::stack::OrFrame as *const u8;
            let ptr = ptr as usize + prelude_offset + index_offset;

            &*(ptr as *const HeapCellValue)
        }
    }
}

impl IndexMut<usize> for OrFrame {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(
            index < self.prelude.num_cells,
            "Invalid index within OrFrame: {index} not in 0..{}",
            self.prelude.num_cells
        );
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *mut crate::machine::stack::OrFrame as *const u8;
            let ptr = ptr as usize + prelude_offset + index_offset;

            &mut *(ptr as *mut HeapCellValue)
        }
    }
}

impl OrFrame {
    pub(crate) fn size_of(num_cells: usize) -> usize {
        prelude_size::<OrFramePrelude>() + num_cells * mem::size_of::<HeapCellValue>()
    }
}

impl Stack {
    pub(crate) fn new() -> Self {
        Stack {
            buf: RawBlock::new(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn uninitialized() -> Self {
        Stack {
            buf: RawBlock::empty_block(),
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    unsafe fn alloc(&mut self, frame_size: usize) -> *mut u8 {
        loop {
            let ptr = self.buf.alloc(frame_size);

            if ptr.is_null() {
                if !self.buf.grow() {
                    panic!("growing the stack failed")
                }
            } else {
                return ptr;
            }
        }
    }

    pub(crate) fn allocate_and_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = AndFrame::size_of(num_cells);

        // TODO: prove safety of this block and prove that it upholds the invariants of `Stack`.
        unsafe {
            let e = self.buf.len();
            let new_ptr = self.alloc(frame_size);
            let mut offset = prelude_size::<AndFramePrelude>();

            for idx in 0..num_cells {
                ptr::write(
                    new_ptr.add(offset) as *mut HeapCellValue,
                    stack_loc_as_cell!(AndFrame, e, idx + 1),
                );

                offset += mem::size_of::<HeapCellValue>();
            }

            let and_frame = self.index_and_frame_mut(e);
            and_frame.prelude.num_cells = num_cells;

            e
        }
    }

    pub(crate) fn top(&self) -> usize {
        self.buf.len()
    }

    pub(crate) fn allocate_or_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = OrFrame::size_of(num_cells);

        // TODO: prove safety of this block and prove that it upholds the invariants of `Stack`.
        unsafe {
            let b = self.buf.len();
            let new_ptr = self.alloc(frame_size);
            let mut offset = prelude_size::<OrFramePrelude>();

            for idx in 0..num_cells {
                ptr::write(
                    new_ptr.add(offset).cast::<HeapCellValue>(),
                    stack_loc_as_cell!(OrFrame, b, idx),
                );

                offset += mem::size_of::<HeapCellValue>();
            }

            let or_frame = self.index_or_frame_mut(b);
            or_frame.prelude.num_cells = num_cells;

            b
        }
    }

    #[inline(always)]
    pub(crate) fn index_and_frame(&self, e: usize) -> &AndFrame {
        unsafe {
            let ptr = self.buf.get(e).unwrap();
            // TODO: ensure safety of this cast
            &*(ptr as *const AndFrame)
        }
    }

    #[inline(always)]
    pub(crate) fn index_and_frame_mut(&mut self, e: usize) -> &mut AndFrame {
        unsafe {
            // This is doing alignment wrong
            let ptr = self.buf.get(e).unwrap();
            // TODO: ensure safety of this cast
            &mut *(ptr as *mut AndFrame)
        }
    }

    #[inline(always)]
    pub(crate) fn index_or_frame(&self, b: usize) -> &OrFrame {
        unsafe {
            let ptr = self.buf.get(b).unwrap();
            // TODO: ensure safety of this cast
            &*(ptr as *const OrFrame)
        }
    }

    /// Reads an [`OrFrame`] placed immediately after [`self.top()`](Self::top).
    ///
    /// # Safety
    ///
    /// The stack must contain a valid [`OrFrame`] at offset [`self.top()`](Self::top).
    ///
    /// No other allocations must have been done since the last call to [`truncate()`](Self::truncate).
    #[inline(always)]
    pub(crate) unsafe fn read_dangling_or_frame(&self) -> &OrFrame {
        unsafe {
            // SAFETY:
            // - Assumed: the stack contains a valid `OrFrame` at this offset
            // - Assumed: no other allocations have been done since the last call to `self.truncate()`
            // - Postcondition: from `self.buf.truncate`, the pointer `ptr` is not yet invalidated.
            let ptr = self.buf.get_unchecked(self.top());
            &*(ptr as *const OrFrame)
        }
    }

    #[inline(always)]
    pub(crate) fn index_or_frame_mut(&mut self, b: usize) -> &mut OrFrame {
        unsafe {
            let ptr = self.buf.get_mut_unchecked(b);
            // TODO: ensure safety of this cast
            &mut *(ptr as *mut OrFrame)
        }
    }

    /// Panics if `byte_offset` is not aligned to [`Stack::ALIGN`].
    ///
    /// Frames beyond `byte_offset` become invalidated after a call to this function.
    #[inline(always)]
    pub(crate) fn truncate(&mut self, byte_offset: usize) {
        unsafe {
            // TODO: implement a way to mitigate indexing to invalidated frames,
            // and/or mark this function as unsafe.
            //
            // I think that one could also create a safer abstraction for the
            // "store offset, do work, truncate to offset" kind of tasks.
            self.buf.truncate(byte_offset);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::machine::mock_wam::*;

    #[test]
    fn stack_tests() {
        let mut wam = MockWAM::new();

        let e = wam.machine_st.stack.allocate_and_frame(10); // create an AND frame!
        let and_frame = wam.machine_st.stack.index_and_frame_mut(e);

        assert_eq!(
            e,
            0 // 10 * mem::size_of::<HeapCellValue>() + prelude_size::<AndFrame>()
        );

        assert_eq!(and_frame.prelude.num_cells, 10);

        for idx in 0..10 {
            assert_eq!(and_frame[idx + 1], stack_loc_as_cell!(AndFrame, e, idx + 1));
        }

        and_frame[5] = empty_list_as_cell!();

        assert_eq!(and_frame[5], empty_list_as_cell!());

        let b = wam.machine_st.stack.allocate_or_frame(5);

        let or_frame = wam.machine_st.stack.index_or_frame_mut(b);

        for idx in 0..5 {
            assert_eq!(or_frame[idx], stack_loc_as_cell!(OrFrame, b, idx));
        }

        let next_e = wam.machine_st.stack.allocate_and_frame(9); // create an AND frame!
        let and_frame = wam.machine_st.stack.index_and_frame_mut(next_e);

        for idx in 0..9 {
            assert_eq!(
                and_frame[idx + 1],
                stack_loc_as_cell!(AndFrame, next_e, idx + 1)
            );
        }

        let and_frame = wam.machine_st.stack.index_and_frame(e);
        assert_eq!(and_frame[5], empty_list_as_cell!());

        assert_eq!(
            wam.machine_st.stack[stack_loc!(AndFrame, e, 5)],
            empty_list_as_cell!()
        );
    }
}
