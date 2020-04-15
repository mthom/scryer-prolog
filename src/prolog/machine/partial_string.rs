use core::marker::PhantomData;

use std::alloc;
use std::mem;
use std::ptr;
use std::ops::RangeFrom;
use std::slice;
use std::str;

pub struct PartialString {
    buf: *const u8,
    len: usize,
    _marker: PhantomData<[u8]>,
}

impl Drop for PartialString {
    fn drop(&mut self) {
        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(self.len, mem::align_of::<u8>());
            alloc::dealloc(self.buf as *mut u8, layout);

            self.buf = ptr::null();
            self.len = 0;
        }
    }
}

impl Clone for PartialString {
    #[inline]
    fn clone(&self) -> Self {
        self.clone_from_offset(0)
    }
}

fn scan_for_terminator<Iter: Iterator<Item = char>>(iter: Iter) -> usize {
    let mut terminator_idx = 0;

    for c in iter {
        if c == '\u{0}' {
            break;
        }

        terminator_idx += c.len_utf8();
    }

    terminator_idx
}

pub struct PStrIter {
    buf: *const u8,
    len: usize,
}

impl PStrIter {
    #[inline]
    fn from(buf: *const u8, len: usize, idx: usize) -> Self {
        PStrIter {
            buf: (buf as usize + idx) as *const _,
            len: len - idx,
        }
    }
}

impl Iterator for PStrIter {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let slice = slice::from_raw_parts(self.buf, self.len);
            let s = str::from_utf8(slice).unwrap();

            if let Some(c) = s.chars().next() {
                self.buf = self.buf.offset(c.len_utf8() as isize);
                self.len -= c.len_utf8();

                Some(c)
            } else {
                None
            }
        }
    }
}

impl PartialString {
    #[inline]
    pub(super)
    fn new(src: &str) -> Option<(Self, &str)> {
        let pstr = PartialString {
            buf: ptr::null_mut(),
            len: 0,
            _marker: PhantomData,
        };

        unsafe {
            pstr.append_chars(src)
        }
    }

    #[inline]
    pub(super)
    fn empty() -> Self {
        let mut pstr = PartialString {
            buf: ptr::null(),
            len: 0,
            _marker: PhantomData,
        };

        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(
                '\u{0}'.len_utf8(),
                mem::align_of::<u8>(),
            );

            pstr.buf = alloc::alloc(layout) as *const _;
            pstr.len = '\u{0}'.len_utf8();

            pstr.write_terminator_at(0);
        }

        pstr
    }

    unsafe fn append_chars(mut self, src: &str) -> Option<(Self, &str)> {
        let terminator_idx = scan_for_terminator(src.chars());

        if terminator_idx == 0 {
            return None;
        }

        let layout = alloc::Layout::from_size_align_unchecked(
            terminator_idx + '\u{0}'.len_utf8(),
            mem::align_of::<u8>(),
        );

        self.buf = alloc::alloc(layout) as *const _;
        self.len = terminator_idx + '\u{0}'.len_utf8();

        ptr::copy(
            src.as_ptr(),
            self.buf as *mut _,
            terminator_idx,
        );

        self.write_terminator_at(terminator_idx);

        Some(if terminator_idx != src.len() {
            (self, &src[terminator_idx + '\u{0}'.len_utf8() ..])
        } else {
            (self, "")
        })
    }

    pub(super)
    fn clone_from_offset(&self, n: usize) -> Self {
        let len =
            if self.len - '\u{0}'.len_utf8() > n {
                self.len - n - '\u{0}'.len_utf8()
            } else {
                0
            };

        let mut pstr = PartialString {
            buf: ptr::null_mut(),
            len: len + '\u{0}'.len_utf8(),
            _marker: PhantomData,
        };

        unsafe {
            let layout = alloc::Layout::from_size_align_unchecked(
                len + '\u{0}'.len_utf8(),
                mem::align_of::<u8>(),
            );

            pstr.buf = alloc::alloc(layout);

            if len > 0 {
                ptr::copy(
                    (self.buf as usize + n) as *const u8,
                    pstr.buf as *mut _,
                    len,
                );
            }

            pstr.write_terminator_at(len);
        }

        pstr
    }

    #[inline]
    pub(super)
    fn write_terminator_at(&mut self, index: usize) {
        unsafe {
            ptr::write(
                (self.buf as usize + index) as *mut u8,
                0u8,
            );
        }
    }

    #[inline]
    pub fn range_from(&self, index: RangeFrom<usize>) -> PStrIter {
        PStrIter::from(self.buf, self.len - '\u{0}'.len_utf8(), index.start)
    }

    #[inline]
    pub fn at_end(&self, end_n: usize) -> bool {
        unsafe {
            ptr::read((self.buf as usize + end_n) as *const u8) == 0u8
        }
    }

    #[inline]
    pub fn as_str_from(&self, n: usize) -> &str {
        unsafe {
            let slice = slice::from_raw_parts(
                self.buf,
                self.len - '\u{0}'.len_utf8(),
            );

            let s = str::from_utf8(slice).unwrap();

            &s[n ..]
        }
    }
}
