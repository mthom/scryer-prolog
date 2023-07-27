use crate::parser::ast::MAX_ARITY;
use crate::raw_block::*;
use crate::types::*;

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ptr;
use std::slice;
use std::str;

use indexmap::IndexSet;

use modular_bitfield::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Atom {
    pub index: usize,
}

const_assert!(mem::size_of::<Atom>() == 8);

include!(concat!(env!("OUT_DIR"), "/static_atoms.rs"));

impl<'a> From<&'a Atom> for Atom {
    #[inline]
    fn from(atom: &'a Atom) -> Self {
        *atom
    }
}

impl From<bool> for Atom {
    #[inline]
    fn from(value: bool) -> Self {
        if value { atom!("true") } else { atom!("false") }
    }
}

#[cfg(test)]
use std::cell::RefCell;

const ATOM_TABLE_INIT_SIZE: usize = 1 << 16;
const ATOM_TABLE_ALIGN: usize = 8;

#[cfg(test)]
thread_local! {
    static ATOM_TABLE_BUF_BASE: RefCell<*const u8> = RefCell::new(ptr::null_mut());
}

#[cfg(not(test))]
static mut ATOM_TABLE_BUF_BASE: *const u8 = ptr::null_mut();

#[cfg(test)]
fn set_atom_tbl_buf_base(ptr: *const u8) {
    ATOM_TABLE_BUF_BASE.with(|atom_table_buf_base| {
        let mut borrow = atom_table_buf_base.borrow_mut();
        assert!(
            borrow.is_null() || ptr.is_null(),
            "Overwriting atom table base pointer!"
        );
        *borrow = ptr;
    });
}

#[cfg(test)]
pub(crate) fn get_atom_tbl_buf_base() -> *const u8 {
    ATOM_TABLE_BUF_BASE.with(|atom_table_buf_base| *atom_table_buf_base.borrow())
}

#[cfg(not(test))]
fn set_atom_tbl_buf_base(ptr: *const u8) {
    unsafe {
        // FIXME: to prevent a toctou race-condition an atomic compare_exchange or a global lock should be used
        assert!(
            ATOM_TABLE_BUF_BASE.is_null() || ptr.is_null(),
            "Overwriting atom table base pointer!"
        );
        ATOM_TABLE_BUF_BASE = ptr;
    }
}

#[cfg(not(test))]
pub(crate) fn get_atom_tbl_buf_base() -> *const u8 {
    unsafe { ATOM_TABLE_BUF_BASE }
}

#[test]
#[should_panic(expected = "Overwriting atom table base pointer!")]
fn atomtable_is_not_concurrency_safe() {
    let table_a = AtomTable::new();
    let table_b = AtomTable::new();
}

impl RawBlockTraits for AtomTable {
    #[inline]
    fn init_size() -> usize {
        ATOM_TABLE_INIT_SIZE
    }

    #[inline]
    fn align() -> usize {
        ATOM_TABLE_ALIGN
    }
}

#[bitfield]
#[derive(Copy, Clone, Debug)]
struct AtomHeader {
    #[allow(unused)] m: bool,
    len: B50,
    #[allow(unused)] padding: B13,
}

impl AtomHeader {
    fn build_with(len: u64) -> Self {
        AtomHeader::new().with_len(len).with_m(false)
    }
}

impl Borrow<str> for Atom {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Hash for Atom {
    #[inline]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.as_str().hash(hasher)
        // hasher.write_usize(self.index)
    }
}

#[macro_export]
macro_rules! is_char {
    ($s:expr) => {
        !$s.is_empty() && $s.chars().nth(1).is_none()
    };
}

impl Atom {
    #[inline]
    pub fn buf(self) -> *const u8 {
        let ptr = self.as_ptr();

        if ptr.is_null() {
            return ptr::null();
        }

        (ptr as usize + mem::size_of::<AtomHeader>()) as *const u8
    }

    #[inline(always)]
    pub fn is_static(self) -> bool {
        self.index < STRINGS.len() << 3
    }

    #[inline(always)]
    pub fn as_ptr(self) -> *const u8 {
        if self.is_static() {
            ptr::null()
        } else {
            (get_atom_tbl_buf_base() as usize + self.index - (STRINGS.len() << 3)) as *const u8
        }
    }

    #[inline(always)]
    pub fn from(index: usize) -> Self {
        Self { index }
    }

    #[inline(always)]
    pub fn len(self) -> usize {
        if self.is_static() {
            STRINGS[self.index >> 3].len()
        } else {
            unsafe { ptr::read(self.as_ptr() as *const AtomHeader).len() as _ }
        }
    }

    #[inline(always)]
    pub fn flat_index(self) -> u64 {
        (self.index >> 3) as u64
    }

    pub fn as_char(self) -> Option<char> {
        let s = self.as_str();
        let mut it = s.chars();

        let c1 = it.next();
        let c2 = it.next();

        if c2.is_none() { c1 } else { None }
    }

    #[inline]
    pub fn chars(&self) -> str::Chars {
        self.as_str().chars()
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        unsafe {
            let ptr = self.as_ptr();

            if ptr.is_null() {
                return STRINGS[self.index >> 3];
            }

            let header = ptr::read::<AtomHeader>(ptr as *const _);
            let len = header.len() as usize;
            let buf = (ptr as usize + mem::size_of::<AtomHeader>()) as *mut u8;

            str::from_utf8_unchecked(slice::from_raw_parts(buf, len))
        }
    }

    pub fn defrock_brackets(&self, atom_tbl: &mut AtomTable) -> Self {
        let s = self.as_str();

        let s = if s.starts_with('(') && s.ends_with(')') {
            &s['('.len_utf8()..s.len() - ')'.len_utf8()]
        } else {
            return *self;
        };

        atom_tbl.build_with(s)
    }
}

unsafe fn write_to_ptr(string: &str, ptr: *mut u8) {
    ptr::write(ptr as *mut _, AtomHeader::build_with(string.len() as u64));
    let str_ptr = (ptr as usize + mem::size_of::<AtomHeader>()) as *mut u8;
    ptr::copy_nonoverlapping(string.as_ptr(), str_ptr as *mut u8, string.len());
}

impl PartialOrd for Atom {
    #[inline]
    fn partial_cmp(&self, other: &Atom) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Atom {
    #[inline]
    fn cmp(&self, other: &Atom) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

#[derive(Debug)]
pub struct AtomTable {
    block: RawBlock<AtomTable>,
    pub table: IndexSet<Atom>,
}

impl Drop for AtomTable {
    fn drop(&mut self) {
        set_atom_tbl_buf_base(ptr::null());
        self.block.deallocate();
    }
}

impl AtomTable {
    #[inline]
    pub fn new() -> Self {
        let table = Self {
            block: RawBlock::new(),
            table: IndexSet::new(),
        };

        set_atom_tbl_buf_base(table.block.base);
        table
    }

    #[inline]
    pub fn buf(&self) -> *const u8 {
        self.block.base as *const u8
    }

    #[inline]
    pub fn top(&self) -> *const u8 {
        self.block.top
    }

    #[inline(always)]
    fn lookup_str(&self, string: &str) -> Option<Atom> {
        STATIC_ATOMS_MAP.get(string).or_else(|| self.table.get(string)).cloned()
    }

    pub fn build_with(&mut self, string: &str) -> Atom {
        if let Some(atom) = self.lookup_str(string) {
            return atom;
        }

        unsafe {
            let size = mem::size_of::<AtomHeader>() + string.len();
            let align_offset = 8 * mem::align_of::<AtomHeader>();
            let size = (size & !(align_offset - 1)) + align_offset;

            let len_ptr = {
                let mut ptr;

                loop {
                    ptr = self.block.alloc(size);

                    if ptr.is_null() {
                        self.block.grow();
                        set_atom_tbl_buf_base(self.block.base);
                    } else {
                        break;
                    }
                }

                ptr
            };

            let ptr_base = self.block.base as usize;

            write_to_ptr(string, len_ptr);

            let atom = Atom {
                index: (STRINGS.len() << 3) + len_ptr as usize - ptr_base,
            };

            self.table.insert(atom);

            atom
        }
    }
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug)]
pub struct AtomCell {
    name: B46,
    arity: B10,
    #[allow(unused)] f: bool,
    #[allow(unused)] m: bool,
    #[allow(unused)] tag: B6,
}

impl AtomCell {
    #[inline]
    pub fn build_with(name: u64, arity: u16, tag: HeapCellValueTag) -> Self {
        if arity > 0 {
            debug_assert!(arity as usize <= MAX_ARITY);

            AtomCell::new()
                .with_name(name)
                .with_arity(arity)
                .with_f(false)
                .with_tag(tag as u8)
        } else {
            AtomCell::new()
                .with_name(name)
                .with_f(false)
                .with_tag(tag as u8)
        }
    }

    #[inline]
    pub fn get_index(self) -> usize {
        self.name() as usize
    }

    #[inline]
    pub fn get_name(self) -> Atom {
        Atom::from(self.get_index() << 3)
    }

    #[inline]
    pub fn get_arity(self) -> usize {
        self.arity() as usize
    }

    #[inline]
    pub fn get_name_and_arity(self) -> (Atom, usize) {
        (Atom::from(self.get_index() << 3), self.get_arity())
    }
}
