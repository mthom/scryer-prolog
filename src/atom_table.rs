use crate::parser::ast::MAX_ARITY;
use crate::raw_block::*;
use crate::rcu::{Rcu, RcuRef};
use crate::types::*;

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::Deref;
use std::ptr;
use std::slice;
use std::str;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::RwLock;
use std::sync::Weak;

use indexmap::IndexSet;

use modular_bitfield::prelude::*;

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
    fn equivalent(&self, key: &Atom) -> bool {
        &*key.as_str() == self
    }
}

const ATOM_TABLE_INIT_SIZE: usize = 1 << 16;
const ATOM_TABLE_ALIGN: usize = 8;

#[inline(always)]
fn global_atom_table() -> &'static RwLock<Weak<AtomTable>> {
    #[cfg(feature = "rust_beta_channel")]
    {
        // const Weak::new will be stabilized in 1.73 which is currently in beta,
        // till then we need a OnceLock for initialization
        static GLOBAL_ATOM_TABLE: RwLock<Weak<AtomTable>> = RwLock::const_new(Weak::new());
        &GLOBAL_ATOM_TABLE
    }
    #[cfg(not(feature = "rust_beta_channel"))]
    {
        use std::sync::OnceLock;
        static GLOBAL_ATOM_TABLE: OnceLock<RwLock<Weak<AtomTable>>> = OnceLock::new();
        GLOBAL_ATOM_TABLE.get_or_init(|| RwLock::new(Weak::new()))
    }
}

#[inline(always)]
fn arc_atom_table() -> Option<Arc<AtomTable>> {
    global_atom_table().read().unwrap().upgrade()
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
    Dynamic(AtomTableRef<str>),
}

impl AtomString<'_> {
    pub fn map<F>(self, f: F) -> Self
    where
        for<'a> F: FnOnce(&'a str) -> &'a str,
    {
        match self {
            Self::Static(reference) => Self::Static(f(reference)),
            Self::Dynamic(guard) => Self::Dynamic(AtomTableRef::map(guard, f)),
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

#[cfg(feature = "repl")]
impl rustyline::completion::Candidate for AtomString<'_> {
    fn display(&self) -> &str {
        self.deref()
    }

    fn replacement(&self) -> &str {
        self.deref()
    }
}

impl Atom {
    #[inline(always)]
    pub fn is_static(self) -> bool {
        (self.index as usize) < STRINGS.len() << 3
    }

    #[inline(always)]
    pub fn as_ptr(self) -> Option<AtomTableRef<u8>> {
        if self.is_static() {
            None
        } else {
            let atom_table =
                arc_atom_table().expect("We should only have an Atom while there is an AtomTable");
            unsafe {
                AtomTableRef::try_map(atom_table.buf(), |buf| {
                    (buf as *const u8)
                        .offset(((self.index as usize) - (STRINGS.len() << 3)) as isize)
                        .as_ref()
                })
            }
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

    #[inline]
    pub fn as_str(&self) -> AtomString<'static> {
        if self.is_static() {
            AtomString::Static(STRINGS[(self.index >> 3) as usize])
        } else {
            if let Some(ptr) = self.as_ptr() {
                AtomString::Dynamic(AtomTableRef::map(ptr, |ptr| {
                    let header =
                        unsafe { ptr::read::<AtomHeader>(ptr as *const u8 as *const AtomHeader) };
                    let len = header.len() as usize;
                    let buf =
                        unsafe { (ptr as *const u8).offset(mem::size_of::<AtomHeader>() as isize) };

                    unsafe { str::from_utf8_unchecked(slice::from_raw_parts(buf, len)) }
                }))
            } else {
                AtomString::Static(&STRINGS[(self.index >> 3) as usize])
            }
        }
    }

    pub fn defrock_brackets(&self, atom_tbl: &AtomTable) -> Self {
        let s = self.as_str();

        let sub_str = if s.starts_with('(') && s.ends_with(')') {
            &s['('.len_utf8()..s.len() - ')'.len_utf8()]
        } else {
            return *self;
        };

        AtomTable::build_with(&atom_tbl, &sub_str)
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
pub struct InnerAtomTable {
    block: RawBlock<AtomTable>,
    pub table: Rcu<IndexSet<Atom>>,
}

#[derive(Debug)]
pub struct AtomTable {
    inner: Rcu<InnerAtomTable>,
    // this lock is taking during resizing
    update: Mutex<()>,
}

pub type AtomTableRef<M> = RcuRef<InnerAtomTable, M>;

impl InnerAtomTable {
    #[inline(always)]
    fn lookup_str(self: &InnerAtomTable, string: &str) -> Option<Atom> {
        STATIC_ATOMS_MAP
            .get(string)
            .cloned()
            .or_else(|| self.table.active_epoch().get(string).cloned())
    }
}

impl AtomTable {
    #[inline]
    pub fn new() -> Arc<Self> {
        let upgraded = global_atom_table().read().unwrap().upgrade();
        // don't inline upgraded, otherwise temporary will be dropped too late in case of None
        if let Some(atom_table) = upgraded {
            atom_table
        } else {
            let mut guard = global_atom_table().write().unwrap();
            // try to upgrade again in case we lost the race on the write lock
            if let Some(atom_table) = guard.upgrade() {
                atom_table
            } else {
                let atom_table = Arc::new(Self {
                    inner: Rcu::new(InnerAtomTable {
                        block: RawBlock::new(),
                        table: Rcu::new(IndexSet::new()),
                    }),
                    update: Mutex::new(()),
                });
                *guard = Arc::downgrade(&atom_table);
                atom_table
            }
        }
    }

    #[inline]
    pub fn buf(&self) -> AtomTableRef<u8> {
        AtomTableRef::<InnerAtomTable>::map(self.inner.active_epoch(), |inner| {
            unsafe { inner.block.base.as_ref() }.unwrap()
        })
    }

    pub fn active_table(&self) -> RcuRef<IndexSet<Atom>, IndexSet<Atom>> {
        self.inner.active_epoch().table.active_epoch()
    }

    pub fn build_with(atom_table: &AtomTable, string: &str) -> Atom {
        loop {
            let mut block_epoch = atom_table.inner.active_epoch();
            let mut table_epoch = block_epoch.table.active_epoch();

            if let Some(atom) = block_epoch.lookup_str(string) {
                return atom;
            }

            // take a lock to prevent concurrent updates
            let update_guard = atom_table.update.lock().unwrap();

            let is_same_allocation =
                RcuRef::same_epoch(&block_epoch, &atom_table.inner.active_epoch());
            let is_same_atom_list =
                RcuRef::same_epoch(&table_epoch, &block_epoch.table.active_epoch());

            if !(is_same_allocation && is_same_atom_list) {
                // some other thread raced us between our lookup and
                // us aquring the update lock,
                // try again
                continue;
            }

            let size = mem::size_of::<AtomHeader>() + string.len();
            let align_offset = 8 * mem::align_of::<AtomHeader>();
            let size = (size & !(align_offset - 1)) + align_offset;

            unsafe {
                let len_ptr = loop {
                    let ptr = block_epoch.block.alloc(size);

                    if ptr.is_null() {
                        // garbage collection would go here
                        let new_block = block_epoch.block.grow_new().unwrap();
                        let new_table = Rcu::new(table_epoch.clone());
                        let new_alloc = InnerAtomTable {
                            block: new_block,
                            table: new_table,
                        };
                        atom_table.inner.replace(new_alloc);
                        block_epoch = atom_table.inner.active_epoch();
                        table_epoch = block_epoch.table.active_epoch();
                    } else {
                        break ptr;
                    }
                };

                let ptr_base = block_epoch.block.base as usize;

                write_to_ptr(string, len_ptr);

                let atom = Atom {
                    index: ((STRINGS.len() << 3) + len_ptr as usize - ptr_base) as u64,
                };

                let mut table = table_epoch.clone();
                table.insert(atom);
                block_epoch.table.replace(table);

                // expicit drop to ensure we don't accidentally drop it early
                drop(update_guard);

                return atom;
            }
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
