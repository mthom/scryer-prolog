use crate::machine::machine_indices::*;
use crate::machine::*;

use core::marker::PhantomData;

use std::alloc;
use std::cmp::Ordering;
use std::mem;
use std::ops::RangeFrom;
use std::ptr;
use std::slice;
use std::str;

use indexmap::IndexSet;

#[derive(Debug)]
pub(crate) struct PartialString {
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
        if c == '\u{0}' && terminator_idx != 0 {
            return terminator_idx;
        }

        terminator_idx += c.len_utf8();
    }

    terminator_idx
}

#[derive(Debug)]
pub(crate) struct PStrIter {
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
    pub(super) fn new(src: &str) -> Option<(Self, &str)> {
        let pstr = PartialString {
            buf: ptr::null_mut(),
            len: 0,
            _marker: PhantomData,
        };

        unsafe { pstr.append_chars(src) }
    }

    unsafe fn append_chars(mut self, src: &str) -> Option<(Self, &str)> {
        let terminator_idx = scan_for_terminator(src.chars());

        let layout = alloc::Layout::from_size_align_unchecked(
            terminator_idx + '\u{0}'.len_utf8(),
            mem::align_of::<u8>(),
        );

        self.buf = alloc::alloc(layout) as *const _;
        self.len = terminator_idx + '\u{0}'.len_utf8();

        ptr::copy(src.as_ptr(), self.buf as *mut _, terminator_idx);

        self.write_terminator_at(terminator_idx);

        Some(if terminator_idx != src.as_bytes().len() {
            (self, &src[terminator_idx..])
        } else {
            (self, "")
        })
    }

    pub(super) fn clone_from_offset(&self, n: usize) -> Self {
        let len = if self.len - '\u{0}'.len_utf8() > n {
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
    pub(super) fn write_terminator_at(&mut self, index: usize) {
        unsafe {
            ptr::write((self.buf as usize + index) as *mut u8, 0u8);
        }
    }

    #[inline]
    pub(crate) fn range_from(&self, index: RangeFrom<usize>) -> PStrIter {
        if self.len >= '\u{0}'.len_utf8() {
            PStrIter::from(self.buf, self.len - '\u{0}'.len_utf8(), index.start)
        } else {
            PStrIter::from(self.buf, 0, 0)
        }
    }

    #[inline]
    pub(crate) fn at_end(&self, end_n: usize) -> bool {
        end_n + 1 == self.len
    }

    #[inline]
    pub(crate) fn as_str_from(&self, n: usize) -> &str {
        unsafe {
            let slice = slice::from_raw_parts(self.buf, self.len - '\u{0}'.len_utf8());

            let s = str::from_utf8(slice).unwrap();

            &s[n..]
        }
    }
}

#[derive(Debug)]
pub(crate) struct HeapPStrIter<'a> {
    focus: Addr,
    machine_st: &'a MachineState,
    seen: IndexSet<Addr>,
}

impl<'a> HeapPStrIter<'a> {
    #[inline]
    pub(super) fn new(machine_st: &'a MachineState, focus: Addr) -> Self {
        HeapPStrIter {
            focus,
            machine_st,
            seen: IndexSet::new(),
        }
    }

    #[inline]
    pub(crate) fn focus(&self) -> Addr {
        self.machine_st.store(self.machine_st.deref(self.focus))
    }

    #[inline]
    pub(crate) fn to_string(&mut self) -> String {
        let mut buf = String::new();

        while let Some(iteratee) = self.next() {
            match iteratee {
                PStrIteratee::Char(c) => {
                    buf.push(c);
                }
                PStrIteratee::PStrSegment(h, n) => match &self.machine_st.heap[h] {
                    HeapCellValue::PartialString(ref pstr, _) => {
                        buf += pstr.as_str_from(n);
                    }
                    _ => {
                        unreachable!()
                    }
                },
            }
        }

        buf
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PStrIteratee {
    Char(char),
    PStrSegment(usize, usize),
}

impl<'a> Iterator for HeapPStrIter<'a> {
    type Item = PStrIteratee;

    fn next(&mut self) -> Option<Self::Item> {
        let addr = self.machine_st.store(self.machine_st.deref(self.focus));

        if !self.seen.contains(&addr) {
            self.seen.insert(addr);
        } else {
            return None;
        }

        match addr {
            Addr::PStrLocation(h, n) => {
                if let &HeapCellValue::PartialString(_, has_tail) = &self.machine_st.heap[h] {
                    self.focus = if has_tail {
                        Addr::HeapCell(h + 1)
                    } else {
                        Addr::EmptyList
                    };

                    return Some(PStrIteratee::PStrSegment(h, n));
                } else {
                    unreachable!()
                }
            }
            Addr::Lis(l) => {
                let addr = self
                    .machine_st
                    .store(self.machine_st.deref(Addr::HeapCell(l)));

                let opt_c = match addr {
                    Addr::Con(h) if self.machine_st.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.machine_st.heap[h] {
                            if atom.is_char() {
                                atom.as_str().chars().next()
                            } else {
                                None
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => Some(c),
                    _ => None,
                };

                if let Some(c) = opt_c {
                    self.focus = Addr::HeapCell(l + 1);
                    return Some(PStrIteratee::Char(c));
                } else {
                    return None;
                }
            }
            Addr::EmptyList => {
                self.focus = Addr::EmptyList;
                return None;
            }
            _ => {
                return None;
            }
        }
    }
}

#[inline]
pub(super) fn compare_pstr_prefixes<'a>(
    i1: &mut HeapPStrIter<'a>,
    i2: &mut HeapPStrIter<'a>,
) -> Option<Ordering> {
    let mut r1 = i1.next();
    let mut r2 = i2.next();

    loop {
        if let Some(r1i) = r1 {
            if let Some(r2i) = r2 {
                match (r1i, r2i) {
                    (PStrIteratee::Char(c1), PStrIteratee::Char(c2)) => {
                        if c1 != c2 {
                            return c1.partial_cmp(&c2);
                        }
                    }
                    (PStrIteratee::Char(c1), PStrIteratee::PStrSegment(h, n)) => {
                        if let &HeapCellValue::PartialString(ref pstr, _) = &i2.machine_st.heap[h] {
                            if let Some(c2) = pstr.as_str_from(n).chars().next() {
                                if c1 != c2 {
                                    return c1.partial_cmp(&c2);
                                } else {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h, n + c2.len_utf8()));

                                    continue;
                                }
                            } else {
                                r2 = i2.next();
                                continue;
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (PStrIteratee::PStrSegment(h, n), PStrIteratee::Char(c2)) => {
                        if let &HeapCellValue::PartialString(ref pstr, _) = &i1.machine_st.heap[h] {
                            if let Some(c1) = pstr.as_str_from(n).chars().next() {
                                if c1 != c2 {
                                    return c2.partial_cmp(&c1);
                                } else {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h, n + c1.len_utf8()));

                                    continue;
                                }
                            } else {
                                r1 = i1.next();
                                continue;
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (PStrIteratee::PStrSegment(h1, n1), PStrIteratee::PStrSegment(h2, n2)) => {
                        match (&i1.machine_st.heap[h1], &i2.machine_st.heap[h2]) {
                            (
                                &HeapCellValue::PartialString(ref pstr1, _),
                                &HeapCellValue::PartialString(ref pstr2, _),
                            ) => {
                                let str1 = pstr1.as_str_from(n1);
                                let str2 = pstr2.as_str_from(n2);

                                if str1.starts_with(str2) {
                                    r1 = Some(PStrIteratee::PStrSegment(h1, n1 + str2.len()));
                                    r2 = i2.next();

                                    continue;
                                } else if str2.starts_with(str1) {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h2, n2 + str1.len()));

                                    continue;
                                } else {
                                    return str1.partial_cmp(str2);
                                }
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                }

                r1 = i1.next();
                r2 = i2.next();

                continue;
            }
        }

        let ordering = if r1.is_none() {
            mem::swap(&mut r1, &mut r2);
            Ordering::Less
        } else {
            Ordering::Greater
        };

        let machine_st = i1.machine_st;

        let check_focuses = || match (i1.focus(), i2.focus()) {
            (Addr::EmptyList, Addr::EmptyList) => Some(Ordering::Equal),
            (Addr::EmptyList, _) => Some(Ordering::Less),
            (_, Addr::EmptyList) => Some(Ordering::Greater),
            _ => None,
        };

        return match r1 {
            Some(PStrIteratee::PStrSegment(h, n)) => {
                if let &HeapCellValue::PartialString(ref pstr, _) = &machine_st.heap[h] {
                    if pstr.as_str_from(n).chars().next().is_some() {
                        Some(ordering)
                    } else {
                        check_focuses()
                    }
                } else {
                    unreachable!()
                }
            }
            Some(PStrIteratee::Char(_)) => Some(ordering),
            None => check_focuses(),
        };
    }
}

#[inline]
pub(super) fn compare_pstr_to_string<'a>(
    heap_pstr_iter: &mut HeapPStrIter<'a>,
    s: &String,
) -> Option<usize> {
    let mut s_offset = 0;

    while let Some(iteratee) = heap_pstr_iter.next() {
        match iteratee {
            PStrIteratee::Char(c1) => {
                if let Some(c2) = s[s_offset..].chars().next() {
                    if c1 != c2 {
                        return None;
                    } else {
                        s_offset += c1.len_utf8();
                    }
                } else {
                    return Some(s_offset);
                }
            }
            PStrIteratee::PStrSegment(h, n) => match heap_pstr_iter.machine_st.heap[h] {
                HeapCellValue::PartialString(ref pstr, _) => {
                    let t = pstr.as_str_from(n);

                    if s[s_offset..].starts_with(t) {
                        s_offset += t.len();
                    } else if t.starts_with(&s[s_offset..]) {
                        heap_pstr_iter.focus = Addr::PStrLocation(h, n + s[s_offset..].len());

                        s_offset += s[s_offset..].len();
                        return Some(s_offset);
                    } else {
                        return None;
                    }
                }
                _ => {
                    unreachable!()
                }
            },
        }

        if s[s_offset..].is_empty() {
            return Some(s_offset);
        }
    }

    Some(s_offset)
}
