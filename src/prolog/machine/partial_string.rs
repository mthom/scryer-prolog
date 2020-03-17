use crate::prolog::machine::raw_block::*;

use std::mem;
use std::ptr;
use std::slice;
use std::str;

pub(crate) struct PartialStringTraits {}

impl RawBlockTraits for PartialStringTraits {
    #[inline]
    fn init_size() -> usize {
        0
    }

    #[inline]
    fn align() -> usize {
        mem::align_of::<char>()
    }
}

pub struct PartialString {
    pub(super) buf: RawBlock<PartialStringTraits>,
}

impl Clone for PartialString {
    #[inline]
    fn clone(&self) -> Self {
        self.clone_from_offset(0)
    }
}

impl PartialEq for PartialString {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }
}

fn scan_for_terminator(src: &str) -> usize {
    let mut terminator_idx = 0;

    for c in src.chars() {
        if c == '\u{0}' {
            break;
        }

        terminator_idx += c.len_utf8();
    }

    terminator_idx
}

impl PartialString {
    pub(super)
    fn new(src: &str) -> Option<(Self, &str)> {
        let pstr = PartialString {
            buf: RawBlock::with_capacity(src.len() + '\u{0}'.len_utf8()),
        };

        unsafe {
            pstr.append_chars(src)
        }
    }

    unsafe fn append_chars(mut self, src: &str) -> Option<(Self, &str)> {
        let terminator_idx = scan_for_terminator(src);

        if terminator_idx == 0 {
            return None;
        }

        let new_top = self.buf.new_block(terminator_idx + '\u{0}'.len_utf8());

        ptr::copy(
            src.as_ptr(),
            self.buf.top as *mut _,
            terminator_idx,
        );

        self.buf.top = (new_top as usize - '\u{0}'.len_utf8()) as *const _;
        self.write_terminator_at(terminator_idx);

        Some(if terminator_idx != src.len() {
            (self, &src[terminator_idx + '\u{0}'.len_utf8() ..])
        } else {
            (self, "")
        })
    }

    pub(super)
    fn clone_from_offset(&self, n: usize) -> Self {
        let mut pstr = PartialString {
            buf: RawBlock::with_capacity(self.len() + '\u{0}'.len_utf8()),
        };

        unsafe {
            let len = if self.len() > n { self.len() - n } else { 0 };
            let new_top = pstr.buf.new_block(len + '\u{0}'.len_utf8());

            if len > 0 {
                ptr::copy(
                    (self.buf.base as usize + n) as *mut u8,
                    pstr.buf.base as *mut _,
                    len,
                );
            }

            pstr.write_terminator_at(len);
            pstr.buf.top = (new_top as usize - '\u{0}'.len_utf8()) as *const _;
        }

        pstr
    }

    #[inline]
    pub(super)
    fn write_terminator_at(&mut self, index: usize) {
        unsafe {
            ptr::write(
                (self.buf.base as usize + index) as *mut u8,
                0u8,
            );
        }
    }

    #[inline]
    pub(crate)
    fn block_as_str(&self) -> &str {
        unsafe {
            let slice = slice::from_raw_parts(self.buf.base, self.len());
            str::from_utf8(slice).unwrap()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.buf.top as usize - self.buf.base as usize
    }
}
