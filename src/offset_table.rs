use std::cell::UnsafeCell;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::RwLock;
use std::sync::Weak;
use std::sync::{Arc, Mutex};
use std::{fmt, mem, ptr};

use arcu::atomic::Arcu;
use arcu::epoch_counters::GlobalEpochCounterPool;
use arcu::rcu_ref::RcuRef;
use arcu::Rcu;

use crate::machine::machine_indices::IndexPtr;
use crate::raw_block::RawBlock;
use crate::raw_block::RawBlockTraits;

use ordered_float::OrderedFloat;

const F64_TABLE_INIT_SIZE: usize = 1 << 16;
const F64_TABLE_ALIGN: usize = 8;

const CODE_INDEX_TABLE_INIT_SIZE: usize = 1 << 16;
const CODE_INDEX_TABLE_ALIGN: usize = 8;

#[derive(Debug)]
pub struct OffsetTableImpl<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    block: Arcu<RawBlock<OffsetTableImpl<T>>, GlobalEpochCounterPool>,
    update: Mutex<()>,
}

pub type F64Table = OffsetTableImpl<OrderedFloat<f64>>;
pub type CodeIndexTable = OffsetTableImpl<IndexPtr>;

impl RawBlockTraits for F64Table {
    #[inline]
    fn init_size() -> usize {
        F64_TABLE_INIT_SIZE
    }

    #[inline]
    fn align() -> usize {
        F64_TABLE_ALIGN
    }
}

impl RawBlockTraits for CodeIndexTable {
    #[inline]
    fn init_size() -> usize {
        CODE_INDEX_TABLE_INIT_SIZE
    }

    #[inline]
    fn align() -> usize {
        CODE_INDEX_TABLE_ALIGN
    }
}

pub trait OffsetTable: RawBlockTraits {
    type Offset: Copy + From<usize> + Into<usize>;
    type Stored;

    fn global_table() -> &'static RwLock<Weak<Self>>;
}

impl OffsetTable for F64Table {
    type Offset = F64Offset;
    type Stored = OrderedFloat<f64>;

    #[inline(always)]
    fn global_table() -> &'static RwLock<Weak<Self>> {
        static GLOBAL_ATOM_TABLE: RwLock<Weak<F64Table>> = RwLock::new(Weak::new());
        &GLOBAL_ATOM_TABLE
    }
}

impl OffsetTable for CodeIndexTable {
    type Offset = CodeIndexOffset;
    type Stored = IndexPtr;

    #[inline(always)]
    fn global_table() -> &'static RwLock<Weak<CodeIndexTable>> {
        static GLOBAL_CODE_INDEX_TABLE: RwLock<Weak<CodeIndexTable>> = RwLock::new(Weak::new());
        &GLOBAL_CODE_INDEX_TABLE
    }
}

impl<T: 'static> OffsetTableImpl<T>
where
    OffsetTableImpl<T>: OffsetTable<Stored = T>,
{
    #[inline]
    pub fn new() -> Arc<Self> {
        let upgraded = Self::global_table().read().unwrap().upgrade();
        // don't inline upgraded, otherwise temporary will be dropped too late in case of None
        if let Some(atom_table) = upgraded {
            atom_table
        } else {
            let mut guard = Self::global_table().write().unwrap();
            // try to upgrade again in case we lost the race on the write lock
            if let Some(atom_table) = guard.upgrade() {
                atom_table
            } else {
                let table = Arc::new(Self {
                    block: Arcu::new(RawBlock::new(), GlobalEpochCounterPool),
                    update: Mutex::new(()),
                });
                *guard = Arc::downgrade(&table);
                table
            }
        }
    }

    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn build_with(
        &self,
        value: <OffsetTableImpl<T> as OffsetTable>::Stored,
    ) -> <OffsetTableImpl<T> as OffsetTable>::Offset {
        let update_guard = self.update.lock();

        // we don't have an index table for lookups as AtomTable does so
        // just get the epoch after we take the upgrade lock
        let mut block_epoch = self.block.read();

        let mut ptr;

        loop {
            ptr = block_epoch.alloc(mem::size_of::<T>());

            if ptr.is_null() {
                let new_block = block_epoch.grow_new().unwrap();
                self.block.replace(new_block);
                block_epoch = self.block.read();
            } else {
                break;
            }
        }

        ptr::write(ptr as *mut T, value);

        let value =
            <OffsetTableImpl<T> as OffsetTable>::Offset::from(ptr.addr() - block_epoch.base.addr());

        // AtomTable would have to update the index table at this point
        // explicit drop to ensure we don't accidentally drop it early
        drop(update_guard);

        value
    }

    pub fn lookup(offset: <Self as OffsetTable>::Offset) -> RcuRef<RawBlock<Self>, UnsafeCell<T>> {
        let table = Self::global_table()
            .read()
            .unwrap()
            .upgrade()
            .expect("We should only be looking up entries when there is a table");

        RcuRef::try_map(table.block.read(), |raw_block| unsafe {
            raw_block
                .base
                .add(offset.into())
                .cast_mut()
                .cast::<UnsafeCell<T>>()
                .as_ref()
        })
        .expect("The offset should result in a non-null pointer")
    }
}

#[derive(Debug)]
pub struct TablePtr<T>(RcuRef<RawBlock<OffsetTableImpl<T>>, UnsafeCell<T>>)
where
    OffsetTableImpl<T>: RawBlockTraits;

pub type CodeIndexPtr = TablePtr<IndexPtr>;
pub type F64Ptr = TablePtr<OrderedFloat<f64>>;

impl<T> Clone for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    fn clone(&self) -> Self {
        Self(RcuRef::clone(&self.0))
    }
}

impl<T: PartialEq> PartialEq for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    fn eq(&self, other: &TablePtr<T>) -> bool {
        RcuRef::ptr_eq(&self.0, &other.0) || self.deref() == other.deref()
    }
}

impl<T: Eq> Eq for TablePtr<T> where OffsetTableImpl<T>: RawBlockTraits {}

impl<T: PartialOrd + Ord> PartialOrd for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord> Ord for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash> Hash for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self as &T).hash(hasher)
    }
}

impl<T: fmt::Display> fmt::Display for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self as &T)
    }
}

impl<T> Deref for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.get().as_ref().unwrap() }
    }
}

impl<T> DerefMut for TablePtr<T>
where
    OffsetTableImpl<T>: RawBlockTraits,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.0.get().as_mut().unwrap() }
    }
}

impl<T: 'static> TablePtr<T>
where
    OffsetTableImpl<T>: OffsetTable<Stored = T>,
{
    #[inline(always)]
    pub fn from_offset(offset: <OffsetTableImpl<T> as OffsetTable>::Offset) -> Self {
        Self(OffsetTableImpl::<T>::lookup(offset))
    }

    #[inline(always)]
    pub fn as_offset(&self) -> <OffsetTableImpl<T> as OffsetTable>::Offset {
        <OffsetTableImpl<T> as OffsetTable>::Offset::from(
            self.0.get().addr() - RcuRef::get_root(&self.0).base.addr(),
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub struct F64Offset(usize);

impl From<usize> for F64Offset {
    #[inline(always)]
    fn from(offset: usize) -> Self {
        Self(offset)
    }
}

impl Into<usize> for F64Offset {
    #[inline(always)]
    fn into(self: Self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CodeIndexOffset(usize);

impl From<usize> for CodeIndexOffset {
    #[inline(always)]
    fn from(offset: usize) -> Self {
        Self(offset)
    }
}

impl Into<usize> for CodeIndexOffset {
    #[inline(always)]
    fn into(self: Self) -> usize {
        self.0
    }
}

impl CodeIndexOffset {
    #[inline(always)]
    pub fn from_ptr(ptr: CodeIndexPtr) -> Self {
        ptr.as_offset()
    }

    #[inline(always)]
    pub fn as_ptr(self) -> CodeIndexPtr {
        CodeIndexPtr::from_offset(self)
    }

    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.0 as u64
    }
}

impl PartialEq for CodeIndexOffset {
    #[inline(always)]
    fn eq(&self, other: &CodeIndexOffset) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl Eq for CodeIndexOffset {}

impl PartialOrd for CodeIndexOffset {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CodeIndexOffset {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl Hash for CodeIndexOffset {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.as_ptr().hash(hasher)
    }
}

impl fmt::Display for CodeIndexOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CodeIndexOffset({})", self.0)
    }
}

impl CodeIndexPtr {
    #[inline]
    pub fn set(&self, val: IndexPtr) {
        unsafe { *self.0.get() = val };
    }

    #[inline]
    pub fn replace(&self, val: IndexPtr) -> IndexPtr {
        unsafe { self.0.get().replace(val) }
    }
}

impl F64Offset {
    #[inline(always)]
    pub fn from_ptr(ptr: F64Ptr) -> Self {
        ptr.as_offset()
    }

    #[inline(always)]
    pub fn as_ptr(self) -> F64Ptr {
        F64Ptr::from_offset(self)
    }

    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.0 as u64
    }
}

impl PartialEq for F64Offset {
    #[inline(always)]
    fn eq(&self, other: &F64Offset) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl Eq for F64Offset {}

impl PartialOrd for F64Offset {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for F64Offset {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl Hash for F64Offset {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.as_ptr().hash(hasher)
    }
}

impl fmt::Display for F64Offset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "F64Offset({})", self.0)
    }
}
