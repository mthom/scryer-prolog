use core::marker::PhantomData;

use crate::raw_block::*;
use crate::types::*;

use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

impl RawBlockTraits for Stack {
    #[inline]
    fn init_size() -> usize {
        10 * 1024 * 1024
    }

    #[inline]
    fn align() -> usize {
        mem::align_of::<OrFrame>()
            .max(mem::align_of::<AndFrame>())
            .max(mem::align_of::<HeapCellValue>())
    }
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
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *const crate::machine::stack::AndFrame as *const u8;

            // This address falls outside the provenance for self, therefore we have to get it
            // from exposed provenance.
            &*std::ptr::with_exposed_provenance(ptr.addr() + prelude_offset + index_offset)
        }
    }
}

impl IndexMut<usize> for AndFrame {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let prelude_offset = prelude_size::<AndFramePrelude>();
        let index_offset = (index - 1) * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *mut crate::machine::stack::AndFrame as *mut u8;

            // This address falls outside the provenance for self, therefore we have to get it
            // from exposed provenance.
            &mut *std::ptr::with_exposed_provenance_mut(ptr.addr() + prelude_offset + index_offset)
        }
    }
}

impl Index<usize> for Stack {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { &*self.buf.base.add(index).cast() }
    }
}

impl IndexMut<usize> for Stack {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { &mut *self.buf.base.add(index).cast_mut().cast() }
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
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *const crate::machine::stack::OrFrame as *const u8;

            // This address falls outside the provenance for self, therefore we have to get it
            // from exposed provenance.
            &*std::ptr::with_exposed_provenance(ptr.addr() + prelude_offset + index_offset)
        }
    }
}

impl IndexMut<usize> for OrFrame {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let prelude_offset = prelude_size::<OrFramePrelude>();
        let index_offset = index * mem::size_of::<HeapCellValue>();

        unsafe {
            let ptr = self as *mut crate::machine::stack::OrFrame as *mut u8;

            // This address falls outside the provenance for self, therefore we have to get it
            // from exposed provenance.
            &mut *std::ptr::with_exposed_provenance_mut(ptr.addr() + prelude_offset + index_offset)
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

        unsafe {
            let e = (*self.buf.ptr.get_mut()).addr() - self.buf.base.addr();
            let new_ptr = self.alloc(frame_size);
            let mut offset = prelude_size::<AndFramePrelude>();

            for idx in 0..num_cells {
                let cell_ptr = new_ptr.add(offset) as *mut HeapCellValue;
                ptr::write(cell_ptr, stack_loc_as_cell!(AndFrame, e, idx + 1));

                // Because in the Index and IndexMut inplementations we need to get this from
                // exposed provenance, we need to expose the provenance here, even though we don't
                // actually use the value for anything. This is a reminder that `expose_provenance`
                // isn't just a cast from a pointer to an integer but has actual side effects.
                cell_ptr.expose_provenance();

                offset += mem::size_of::<HeapCellValue>();
            }

            let and_frame = self.index_and_frame_mut(e);
            and_frame.prelude.num_cells = num_cells;

            e
        }
    }

    pub(crate) fn top(&self) -> usize {
        unsafe { (*self.buf.ptr.get()).addr() - self.buf.base.addr() }
    }

    pub(crate) fn allocate_or_frame(&mut self, num_cells: usize) -> usize {
        let frame_size = OrFrame::size_of(num_cells);

        unsafe {
            let b = (*self.buf.ptr.get_mut()).addr() - self.buf.base.addr();
            let new_ptr = self.alloc(frame_size);
            let mut offset = prelude_size::<OrFramePrelude>();

            for idx in 0..num_cells {
                let cell_ptr = new_ptr.byte_add(offset) as *mut HeapCellValue;
                ptr::write(cell_ptr, stack_loc_as_cell!(OrFrame, b, idx));

                // Because in the Index and IndexMut inplementations we need to get this from
                // exposed provenance, we need to expose the provenance here, even though we don't
                // actually use the value for anything. This is a reminder that `expose_provenance`
                // isn't just a cast from a pointer to an integer but has actual side effects.
                cell_ptr.expose_provenance();

                offset += mem::size_of::<HeapCellValue>();
            }

            let or_frame = self.index_or_frame_mut(b);
            or_frame.prelude.num_cells = num_cells;

            b
        }
    }

    #[inline(always)]
    pub(crate) fn index_and_frame(&self, e: usize) -> &AndFrame {
        unsafe { &*self.buf.base.add(e).cast() }
    }

    #[inline(always)]
    pub(crate) fn index_and_frame_mut(&mut self, e: usize) -> &mut AndFrame {
        unsafe {
            // This is doing alignment wrong
            let ptr = self.buf.base.add(e);
            &mut *(ptr as *mut AndFrame)
        }
    }

    #[inline(always)]
    pub(crate) fn index_or_frame(&self, b: usize) -> &OrFrame {
        unsafe { &*self.buf.base.add(b).cast() }
    }

    #[inline(always)]
    pub(crate) fn index_or_frame_mut(&mut self, b: usize) -> &mut OrFrame {
        unsafe { &mut *self.buf.base.add(b).cast_mut().cast() }
    }

    #[inline(always)]
    pub(crate) fn truncate(&mut self, b: usize) {
        let base = unsafe { self.buf.base.add(b) };

        if base < (*self.buf.ptr.get_mut()) {
            *self.buf.ptr.get_mut() = base.cast_mut();
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
