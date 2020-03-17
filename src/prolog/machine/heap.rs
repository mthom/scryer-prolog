use core::marker::PhantomData;

use crate::prolog_parser::ast::*;

use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::partial_string::*;
use crate::prolog::machine::raw_block::*;

use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

pub(crate) struct StandardHeapTraits {}

impl RawBlockTraits for StandardHeapTraits {
    #[inline]
    fn init_size() -> usize {
        256 * mem::size_of::<HeapCellValue>()
    }

    #[inline]
    fn align() -> usize {
        mem::align_of::<HeapCellValue>()
    }
}

pub(crate) struct HeapTemplate<T: RawBlockTraits> {
    buf: RawBlock<T>,
    _marker: PhantomData<HeapCellValue>,
}

pub(crate) type Heap = HeapTemplate<StandardHeapTraits>;

impl<T: RawBlockTraits> Drop for HeapTemplate<T> {
    fn drop(&mut self) {
        self.clear();
        self.buf.deallocate();
    }
}

pub(crate)
struct HeapIntoIterator<T: RawBlockTraits> {
    offset: usize,
    buf: RawBlock<T>,
}

impl<T: RawBlockTraits> Drop for HeapIntoIterator<T> {
    fn drop(&mut self) {
        let mut heap =
            HeapTemplate { buf: self.buf.take(), _marker: PhantomData };

        heap.truncate(self.offset / mem::size_of::<HeapCellValue>());
        heap.buf.deallocate();
    }
}

impl<T: RawBlockTraits> Iterator for HeapIntoIterator<T> {
    type Item = HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = self.buf.base as usize + self.offset;
        self.offset += mem::size_of::<HeapCellValue>();

        if ptr < self.buf.top as usize {
            unsafe {
                Some(ptr::read(ptr as *const HeapCellValue))
            }
        } else {
            None
        }
    }
}

pub(crate)
struct HeapIterator<'a, T: RawBlockTraits> {
    offset: usize,
    buf: &'a RawBlock<T>,
}

impl<'a, T: RawBlockTraits> HeapIterator<'a, T> {
    pub(crate)
    fn new(buf: &'a RawBlock<T>, offset: usize) -> Self {
        HeapIterator { buf, offset }
    }
}

impl<'a, T: RawBlockTraits> Iterator for HeapIterator<'a, T> {
    type Item = &'a HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = self.buf.base as usize + self.offset;
        self.offset += mem::size_of::<HeapCellValue>();

        if ptr < self.buf.top as usize {
            unsafe {
                Some(&*(ptr as *const _))
            }
        } else {
            None
        }
    }
}

pub(crate)
struct HeapIteratorMut<'a, T: RawBlockTraits> {
    offset: usize,
    buf: &'a mut RawBlock<T>,
}

impl<'a, T: RawBlockTraits> HeapIteratorMut<'a, T> {
    pub(crate)
    fn new(buf: &'a mut RawBlock<T>, offset: usize) -> Self {
        HeapIteratorMut { buf, offset }
    }
}

impl<'a, T: RawBlockTraits> Iterator for HeapIteratorMut<'a, T> {
    type Item = &'a mut HeapCellValue;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = self.buf.base as usize + self.offset;
        self.offset += mem::size_of::<HeapCellValue>();

        if ptr < self.buf.top as usize {
            unsafe {
                Some(&mut *(ptr as *mut _))
            }
        } else {
            None
        }
    }
}

impl<T: RawBlockTraits> HeapTemplate<T> {
    #[inline]
    pub(crate)
    fn new() -> Self {
        HeapTemplate { buf: RawBlock::new(), _marker: PhantomData }
    }

    #[inline]
    pub(crate)
    fn push(&mut self, val: HeapCellValue) {
        unsafe {
            let new_top = self.buf.new_block(mem::size_of::<HeapCellValue>());
            ptr::write(self.buf.top as *mut _, val);
            self.buf.top = new_top;
        }
    }

    #[inline]
    pub(crate)
    fn allocate_pstr(&mut self, mut src: &str) -> Option<Addr> {
        let orig_h = self.h();

        loop {
            if src == "" {
                return if orig_h == self.h() {
                    None
                } else {
                    let tail_h = self.h() - 1;
                    self[tail_h] = HeapCellValue::Addr(Addr::HeapCell(tail_h));

                    Some(Addr::PStrLocation(orig_h, 0))
                };
            }

            let h = self.h();

            let (pstr, rest_src) =
                match PartialString::new(src) {
                    Some(tuple) => {
                        tuple
                    }
                    None => {
                        if src.len() > '\u{0}'.len_utf8() {
                            src = &src['\u{0}'.len_utf8() ..];
                            continue;
                        } else if orig_h == h {
                            return None;
                        } else {
                            self[h - 1] = HeapCellValue::Addr(Addr::HeapCell(h - 1));
                            return Some(Addr::PStrLocation(orig_h, 0));
                        }
                    }
                };

            self.push(HeapCellValue::PartialString(pstr));

            if rest_src != "" {
                self.push(HeapCellValue::Addr(Addr::PStrLocation(h + 2, 0)));
                src = rest_src;
            } else {
                self.push(HeapCellValue::Addr(Addr::HeapCell(h + 1)));
                return Some(Addr::PStrLocation(orig_h, 0));
            }
        }
    }

    #[inline]
    pub(crate)
    fn take(&mut self) -> Self {
        HeapTemplate {
            buf: self.buf.take(),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub(crate)
    fn truncate(&mut self, h: usize) {
        let new_top = h * mem::size_of::<HeapCellValue>() + self.buf.base as usize;
        let mut h = new_top;

        unsafe {
            while h as *const _ < self.buf.top {
                let val = h as *mut HeapCellValue;
                ptr::drop_in_place(val);
                h += mem::size_of::<HeapCellValue>();
            }
        }

        self.buf.top = new_top as *const _;
    }

    #[inline]
    pub(crate)
    fn h(&self) -> usize {
        (self.buf.top as usize - self.buf.base as usize) / mem::size_of::<HeapCellValue>()
    }

    pub(crate)
    fn append(&mut self, vals: Vec<HeapCellValue>) {
        for val in vals {
            self.push(val);
        }
    }

    pub(crate)
    fn clear(&mut self) {
        if !self.buf.base.is_null() {
            self.truncate(0);
            self.buf.top = self.buf.base;
        }
    }

    pub(crate)
    fn to_list<Iter: Iterator<Item = Addr>>(&mut self, values: Iter) -> usize {
        let head_addr = self.h();

        for value in values {
            let h = self.h();

            self.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
            self.push(HeapCellValue::Addr(value));
        }

        self.push(HeapCellValue::Addr(Addr::Con(Constant::EmptyList)));

        head_addr
    }

    /* Create an iterator starting from the passed offset. */
    pub(crate)
    fn iter_from<'a>(&'a self, offset: usize) -> HeapIterator<'a, T> {
        HeapIterator::new(&self.buf, offset * mem::size_of::<HeapCellValue>())
    }

    pub(crate)
    fn iter_mut_from<'a>(&'a mut self, offset: usize) -> HeapIteratorMut<'a, T> {
        HeapIteratorMut::new(&mut self.buf, offset * mem::size_of::<HeapCellValue>())
    }

    pub(crate)
    fn into_iter(mut self) -> HeapIntoIterator<T> {
        HeapIntoIterator { buf: self.buf.take(), offset: 0 }
    }

    pub(crate)
    fn extend<Iter: Iterator<Item = HeapCellValue>>(&mut self, iter: Iter) {
        for hcv in iter {
            self.push(hcv);
        }
    }

    pub(crate)
    fn to_local_code_ptr(&self, addr: &Addr) -> Option<LocalCodePtr> {
        let extract_integer = |s: usize| -> Option<usize> {
            match self[s].as_addr(s) {
                Addr::Con(Constant::Integer(n)) => n.to_usize(),
                _ => None
            }
        };

        match addr {
            Addr::Str(s) => {
                match &self[*s] {
                    HeapCellValue::NamedStr(arity, ref name, _) => {
                        match (name.as_str(), *arity) {
                            ("dir_entry", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::DirEntry)
                            }
                            ("in_situ_dir_entry", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::InSituDirEntry)
                            }
                            ("top_level", 2) => {
                                if let Some(chunk_num) = extract_integer(s+1) {
                                    if let Some(p) = extract_integer(s+2) {
                                        return Some(LocalCodePtr::TopLevel(chunk_num, p));
                                    }
                                }

                                None
                            }
                            ("user_goal_expansion", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::UserGoalExpansion)
                            }
                            ("user_term_expansion", 1) => {
                                extract_integer(s+1).map(LocalCodePtr::UserTermExpansion)
                            }
                            _ => None
                        }
                    }
                    _ => unreachable!()
                }
            }
            _ => None
        }
    }
}

impl<T: RawBlockTraits> Index<usize> for HeapTemplate<T> {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let ptr = self.buf.base as usize + index * mem::size_of::<HeapCellValue>();
            &*(ptr as *const HeapCellValue)
        }
    }
}

impl<T: RawBlockTraits> IndexMut<usize> for HeapTemplate<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let ptr = self.buf.base as usize + index * mem::size_of::<HeapCellValue>();
            &mut *(ptr as *mut HeapCellValue)
        }
    }
}
