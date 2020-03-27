use std::alloc;
use std::mem;
use std::ptr;
use std::ops::{Range, RangeFrom};
use std::str;

pub struct PartialString {
    buf: *const u8,
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
}

impl PStrIter {
    #[inline]
    fn from(buf: *const u8, idx: usize) -> Self {
        PStrIter {
            buf: (buf as usize + idx) as *const _
        }
    }
}

impl Iterator for PStrIter {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let b = ptr::read(self.buf);

            if b == 0u8 {
                return None;
            }

            let c = ptr::read(self.buf as *const char);
            self.buf = self.buf.offset(c.len_utf8() as isize);

            Some(c)
        }
    }
}

pub struct PStrIterBounded {
    buf: *const u8,
    end: *const u8,
}

impl PStrIterBounded {
    #[inline]
    fn from(buf: *const u8, start: usize, end: usize) -> Self {
        PStrIterBounded {
            buf: (buf as usize + start) as *const _,
            end: (buf as usize + end) as *const _,
        }
    }
}

impl Iterator for PStrIterBounded {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.buf >= self.end {
                return None;
            }

            let b = ptr::read(self.buf);

            if b == 0u8 {
                return None;
            }

            let c = ptr::read(self.buf as *const char);
            self.buf = self.buf.offset(c.len_utf8() as isize);

            Some(c)
        }
    }
}

impl PartialString {
    #[inline]
    pub(super)
    fn new(src: &str) -> Option<(Self, &str)> {
        let pstr = PartialString {
            buf: ptr::null_mut(),
        };

        unsafe {
            pstr.append_chars(src)
        }
    }

    #[inline]
    pub(super)
    fn empty() -> Self {
        PartialString {
            buf: "\u{0}".as_bytes()[0] as *const _,
        }
    }

    unsafe fn append_chars(mut self, src: &str) -> Option<(Self, &str)> {
        let terminator_idx = scan_for_terminator(src.chars());

        if terminator_idx == 0 {
            return None;
        }

        let layout = alloc::Layout::from_size_align_unchecked(
            src.len() + '\u{0}'.len_utf8(),
            mem::align_of::<u8>(),
        );

        self.buf = alloc::alloc(layout) as *const _;

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

    #[inline]
    pub(crate)
    fn iter(&self) -> PStrIter {
        PStrIter {
            buf: self.buf,
        }
    }

    pub(super)
    fn clone_from_offset(&self, n: usize) -> Self {
        let mut pstr = PartialString {
            buf: ptr::null_mut(),
        };

        unsafe {
            let len = scan_for_terminator(self.range_from(0 ..));
            let len = if len > n { len - n } else { 0 };

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
    pub fn range(&self, index: Range<usize>) -> PStrIterBounded {
        PStrIterBounded::from(self.buf, index.start, index.end)
    }

    #[inline]
    pub fn range_from(&self, index: RangeFrom<usize>) -> PStrIter {
        PStrIter::from(self.buf, index.start)
    }

    #[inline]
    pub fn at_end(&self, end_n: usize) -> bool {
        unsafe {
            ptr::read((self.buf as usize + end_n) as *const u8) == 0u8
        }
    }
}
