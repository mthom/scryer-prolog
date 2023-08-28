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

impl indexmap::Equivalent<Atom> for LookupKey<'_, '_> {
    fn equivalent(&self, key: &Atom) -> bool {
        &*key.as_str_with_table(self.0) == self.1
    }
}

const ATOM_TABLE_INIT_SIZE: usize = 1 << 16;
const ATOM_TABLE_ALIGN: usize = 8;

fn global_atom_table() -> &'static RwLock<Weak<RwLock<AtomTable>>> {
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

fn owned_atom_table_read_guard() -> Option<OwnedRwLockReadGuard<AtomTable>> {
    let atom_table = global_atom_table().blocking_read().upgrade()?;

    let guard = {
        // some test don't start a Runtime
        if let Ok(handle) = Handle::try_current() {
            handle.block_on(atom_table.read_owned())
        } else {
            tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(atom_table.read_owned())
        }
    };
    Some(guard)
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
    pub fn as_ptr_with_table<'at>(&self, atom_table: &'at AtomTable) -> Option<&'at u8> {
        if self.is_static() {
            None
        } else {
            unsafe {
                atom_table
                    .buf()
                    .offset(((self.index as usize) - (STRINGS.len() << 3)) as isize)
                    .as_ref()
            }
        }
    }

    #[inline(always)]
    pub fn as_ptr(self) -> Option<OwnedRwLockReadGuard<AtomTable, u8>> {
        if self.is_static() {
            None
        } else {
            let guard = owned_atom_table_read_guard()
                .expect("We should only have an Atom while there is an AtomTable");
            OwnedRwLockReadGuard::try_map(guard, |atom_table| self.as_ptr_with_table(atom_table))
                .ok()
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
            let ptr = self.as_ptr().unwrap();
            let ptr = ptr.deref() as *const u8 as *const AtomHeader;
            unsafe { ptr::read(ptr) }.len() as _
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

    #[inline(always)]
    pub fn as_str_with_table<'at>(&self, atom_table: &'at AtomTable) -> &'at str {
        if let Some(ptr) = self.as_ptr_with_table(atom_table) {
            let header = unsafe { ptr::read::<AtomHeader>(ptr as *const u8 as *const AtomHeader) };
            let len = header.len() as usize;
            let buf = (unsafe { (ptr as *const u8).offset(mem::size_of::<AtomHeader>() as isize) })
                as *mut u8;

            unsafe { str::from_utf8_unchecked(slice::from_raw_parts(buf, len)) }
        } else {
            &STRINGS[(self.index >> 3) as usize]
        }
    }

    #[track_caller]
    #[inline]
    pub fn as_str(&self) -> AtomString<'static> {
        if self.is_static() {
            AtomString::Static(STRINGS[(self.index >> 3) as usize])
        } else {
            let guard = owned_atom_table_read_guard()
                .expect("We should only have an Atom while there is an AtomTable");
            AtomString::Dynamic(OwnedRwLockReadGuard::map(guard, |atom_table| {
                self.as_str_with_table(atom_table)
            }))
        }
    }

    pub fn defrock_brackets(&self, atom_tbl: &Arc<RwLock<AtomTable>>) -> Self {
        let s = self.as_str();

        let sub_str = if s.starts_with('(') && s.ends_with(')') {
            &s['('.len_utf8()..s.len() - ')'.len_utf8()]
        } else {
            return *self;
        };

        let val = sub_str.to_string();
        drop(s); // wee need to drop s as it holds a read lock on the AtomTable and build_with may need to acquire a write lock
        AtomTable::build_with(&atom_tbl, &val)
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
    pub table: RwLock<IndexSet<Atom>>,
}

impl Drop for AtomTable {
    fn drop(&mut self) {
        self.block.deallocate();
    }
}

struct LookupKey<'table, 'key>(&'table AtomTable, &'key str);

impl Hash for LookupKey<'_, '_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}

impl AtomTable {
    #[inline]
    pub fn new() -> Arc<RwLock<Self>> {
        let upgraded = global_atom_table().blocking_read().upgrade();
        // don't inline upgraded, otherwise temporary will be dropped too late in case of None
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
                    table: RwLock::new(IndexSet::new()),
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
    fn lookup_str(self: &AtomTable, string: &str) -> Option<Atom> {
        STATIC_ATOMS_MAP.get(string).cloned().or_else(|| {
            self.table
                .blocking_read()
                .get(&LookupKey(self, string))
                .cloned()
        })
    }

    pub fn build_with(atom_table: &RwLock<AtomTable>, string: &str) -> Atom {
        let mut atom_table = loop {
            if let Ok(guard) = atom_table.try_write() {
                break guard;
            }
        };

        if let Some(atom) = atom_table.lookup_str(string) {
            return atom;
        }

        unsafe {
            let size = mem::size_of::<AtomHeader>() + string.len();
            let align_offset = 8 * mem::align_of::<AtomHeader>();
            let size = (size & !(align_offset - 1)) + align_offset;

            let len_ptr = loop {
                let ptr = atom_table.block.alloc(size);

                if ptr.is_null() {
                    atom_table.block.grow();
                } else {
                    break ptr;
                }
            };

            let ptr_base = atom_table.block.base as usize;

            write_to_ptr(string, len_ptr);

            let atom = Atom {
                index: ((STRINGS.len() << 3) + len_ptr as usize - ptr_base) as u64,
            };

            // we need to downgrade to a read so that Atom::hash can read from the AtomTable,
            // so that it can calculate the hash for inserting the atom
            // we can't just drop the guard as otherwise another thread could race us with another atom insertion
            let atom_table = atom_table.downgrade();

            // NOTE: there is no race between downgrade and blocking write as table is only accessed writable in this function
            // and only after the write lock is acquired as we have the guard and just convert it from a write to a read guard no writer can race us
            atom_table.table.blocking_write().insert(atom);

            drop(atom_table); // we need to keep the guard around till after the insert

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
