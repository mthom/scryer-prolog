use crate::parser::ast::MAX_ARITY;
use crate::raw_block::*;
use crate::types::*;

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::Deref;
use std::ptr;
use std::slice;
use std::str;
use std::sync::Arc;
use std::sync::Weak;

use indexmap::IndexSet;

use modular_bitfield::prelude::*;
use tokio::runtime::Handle;
use tokio::sync::OwnedRwLockReadGuard;
use tokio::sync::RwLock;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Atom {
    pub index: u64,
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
        if value {
            atom!("true")
        } else {
            atom!("false")
        }
    }
}

impl indexmap::Equivalent<Atom> for str {
    fn equivalent(&self, atom: &Atom) -> bool {
        &*atom.as_str() == self
    }
}

const ATOM_TABLE_INIT_SIZE: usize = 1 << 16;
const ATOM_TABLE_ALIGN: usize = 8;

pub fn global_atom_table() -> &'static RwLock<Weak<RwLock<AtomTable>>> {
    #[cfg(feature = "rust_beta_channel")]
    {
        // const Weak::new will be stabilized in 1.73 which is currently in beta,
        // till then we need a OnceLock for initialization
        static GLOBAL_ATOM_TABLE: RwLock<Weak<RwLock<AtomTable>>> = RwLock::new(Weak::new());
        &GLOBAL_ATOM_TABLE
    }
    #[cfg(not(feature = "rust_beta_channel"))]
    {
        use std::sync::OnceLock;
        static GLOBAL_ATOM_TABLE: OnceLock<RwLock<Weak<RwLock<AtomTable>>>> = OnceLock::new();
        GLOBAL_ATOM_TABLE.get_or_init(|| RwLock::new(Weak::new()))
    }
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
    #[allow(unused)]
    m: bool,
    len: B50,
    #[allow(unused)]
    padding: B13,
}

impl AtomHeader {
    fn build_with(len: u64) -> Self {
        AtomHeader::new().with_len(len).with_m(false)
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

pub enum AtomString<'a> {
    Static(&'a str),
    Dynamic(OwnedRwLockReadGuard<AtomTable, str>),
}

impl AtomString<'_> {
    pub fn map<F>(self, f: F) -> Self
    where
        for<'a> F: FnOnce(&'a str) -> &'a str,
    {
        match self {
            Self::Static(reference) => Self::Static(f(reference)),
            Self::Dynamic(guard) => Self::Dynamic(OwnedRwLockReadGuard::map(guard, f)),
        }
    }
}

impl std::fmt::Debug for AtomString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.deref(), f)
    }
}

impl std::fmt::Display for AtomString<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self.deref(), f)
    }
}

impl std::ops::Deref for AtomString<'_> {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Static(reference) => reference,
            Self::Dynamic(guard) => guard.deref(),
        }
    }
}

impl rustyline::completion::Candidate for AtomString<'_> {
    fn display(&self) -> &str {
        self.deref()
    }

    fn replacement(&self) -> &str {
        self.deref()
    }
}

impl Atom {
    #[inline]
    pub fn buf(self) -> Option<OwnedRwLockReadGuard<AtomTable, u8>> {
        if let Some(guard) = self.as_ptr() {
            Some(OwnedRwLockReadGuard::map(guard, |ptr| unsafe {
                (ptr as *const u8)
                    .offset(mem::size_of::<AtomHeader>() as isize)
                    .as_ref()
                    .unwrap()
            }))
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn is_static(self) -> bool {
        (self.index as usize) < STRINGS.len() << 3
    }

    #[inline(always)]
    pub fn as_ptr(self) -> Option<OwnedRwLockReadGuard<AtomTable, u8>> {
        if self.is_static() {
            None
        } else {
            let atom_table = global_atom_table()
                .blocking_read()
                .upgrade()
                .expect("We should only have an Atom while there is an AtomTable");

            #[cfg(not(test))]
            let guard = Handle::current().block_on(atom_table.read_owned());

            #[cfg(test)]
            let guard = {
                if let Ok(handle) = Handle::try_current() {
                    handle.block_on(atom_table.read_owned())
                } else {
                    tokio::runtime::Runtime::new()
                        .unwrap()
                        .block_on(atom_table.read_owned())
                }
            };

            Some(OwnedRwLockReadGuard::map(guard, |atom_table| unsafe {
                atom_table
                    .buf()
                    .offset(((self.index as usize) - (STRINGS.len() << 3)) as isize)
                    .as_ref()
                    .unwrap()
            }))
        }
    }

    #[inline(always)]
    pub fn from(index: u64) -> Self {
        Self { index }
    }

    #[inline(always)]
    pub fn len(self) -> usize {
        if self.is_static() {
            STRINGS[(self.index >> 3) as usize].len()
        } else {
            unsafe {
                ptr::read(self.as_ptr().unwrap().deref() as *const u8 as *const AtomHeader).len()
                    as _
            }
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

        if c2.is_none() {
            c1
        } else {
            None
        }
    }

    #[inline]
    pub fn as_str(&self) -> AtomString<'static> {
        if let Some(ptr_guard) = self.as_ptr() {
            AtomString::Dynamic(OwnedRwLockReadGuard::map(ptr_guard, |ptr| {
                let header =
                    unsafe { ptr::read::<AtomHeader>(ptr as *const u8 as *const AtomHeader) };
                let len = header.len() as usize;
                let buf =
                    (unsafe { (ptr as *const u8).offset(mem::size_of::<AtomHeader>() as isize) })
                        as *mut u8;

                unsafe { str::from_utf8_unchecked(slice::from_raw_parts(buf, len)) }
            }))
        } else {
            return AtomString::Static(STRINGS[(self.index >> 3) as usize]);
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
        self.as_str().cmp(&*other.as_str())
    }
}

#[derive(Debug)]
pub struct AtomTable {
    block: RawBlock<AtomTable>,
    pub table: IndexSet<Atom>,
}

impl Drop for AtomTable {
    fn drop(&mut self) {
        self.block.deallocate();
    }
}

impl AtomTable {
    #[inline]
    pub fn new() -> Arc<RwLock<Self>> {
        let upgraded = global_atom_table().blocking_read().upgrade();
        // don't inline upgraded, temporary will be dropped too late in case of None
        if let Some(atom_table) = upgraded {
            atom_table
        } else {
            let mut guard = global_atom_table().blocking_write();
            // try to upgrade again in case we lost the race on the write lock
            if let Some(atom_table) = guard.upgrade() {
                atom_table
            } else {
                let atom_table = Arc::new(RwLock::new(Self {
                    block: RawBlock::new(),
                    table: IndexSet::new(),
                }));
                *guard = Arc::downgrade(&atom_table);
                atom_table
            }
        }
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
        STATIC_ATOMS_MAP
            .get(string)
            .or_else(|| self.table.get(string))
            .cloned()
    }

    pub fn build_with(&mut self, string: &str) -> Atom {
        if let Some(atom) = self.lookup_str(string) {
            return atom;
        }

        unsafe {
            let size = mem::size_of::<AtomHeader>() + string.len();
            let align_offset = 8 * mem::align_of::<AtomHeader>();
            let size = (size & !(align_offset - 1)) + align_offset;

            let len_ptr = loop {
                let ptr = self.block.alloc(size);

                if ptr.is_null() {
                    self.block.grow();
                } else {
                    break ptr;
                }
            };

            let ptr_base = self.block.base as usize;

            write_to_ptr(string, len_ptr);

            let atom = Atom {
                index: ((STRINGS.len() << 3) + len_ptr as usize - ptr_base) as u64,
            };

            self.table.insert(atom);

            atom
        }
    }
}

unsafe impl Send for AtomTable {}
unsafe impl Sync for AtomTable {}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug)]
pub struct AtomCell {
    name: B46,
    arity: B10,
    #[allow(unused)]
    f: bool,
    #[allow(unused)]
    m: bool,
    #[allow(unused)]
    tag: B6,
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
        Atom::from((self.get_index() as u64) << 3)
    }

    #[inline]
    pub fn get_arity(self) -> usize {
        self.arity() as usize
    }

    #[inline]
    pub fn get_name_and_arity(self) -> (Atom, usize) {
        (Atom::from((self.get_index() as u64) << 3), self.get_arity())
    }
}
