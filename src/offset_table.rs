use std::cell::UnsafeCell;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock, RwLockReadGuard};
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

impl RawBlockTraits for OrderedFloat<f64> {
    #[inline]
    fn init_size() -> usize {
        F64_TABLE_INIT_SIZE
    }

    #[inline]
    fn align() -> usize {
        F64_TABLE_ALIGN
    }
}

impl RawBlockTraits for IndexPtr {
    #[inline]
    fn init_size() -> usize {
        CODE_INDEX_TABLE_INIT_SIZE
    }

    #[inline]
    fn align() -> usize {
        CODE_INDEX_TABLE_ALIGN
    }
}

#[derive(Debug)]
pub struct OffsetTableImpl<T: RawBlockTraits>(InnerOffsetTableImpl<T>);

impl<T: RawBlockTraits> From<Arc<ConcurrentOffsetTable<T>>> for OffsetTableImpl<T> {
    #[inline]
    fn from(value: Arc<ConcurrentOffsetTable<T>>) -> Self {
        OffsetTableImpl(InnerOffsetTableImpl::Concurrent(value))
    }
}

impl<T: RawBlockTraits> OffsetTableImpl<T> {
    #[inline(always)]
    pub fn new() -> Self {
        Self(InnerOffsetTableImpl::Serial(SerialOffsetTable::new()))
    }

    #[must_use = "the returned concurrent table must be absorbed into the owned OffsetTable"]
    pub fn single_to_concurrent(&mut self) -> Arc<ConcurrentOffsetTable<T>> {
        match &mut self.0 {
            InnerOffsetTableImpl::Serial(serial_tbl) => {
                let empty_serial_tbl = SerialOffsetTable {
                    block: RawBlock::empty_block(),
                };

                let serial_tbl = mem::replace(serial_tbl, empty_serial_tbl);
                let block = Arcu::new(serial_tbl.block, GlobalEpochCounterPool);

                let growth_lock = RwLock::new(());
                let concurrent_tbl = Arc::new(ConcurrentOffsetTable { block, growth_lock });

                self.0 = InnerOffsetTableImpl::Concurrent(concurrent_tbl.clone());

                concurrent_tbl
            }
            InnerOffsetTableImpl::Concurrent(concurrent_tbl) => concurrent_tbl.clone(),
        }
    }

    #[must_use = "the transition to a single-threaded offset table may fail if the concurrent table is held from multiple places"]
    pub fn concurrent_to_single(&mut self) -> Result<(), ()> {
        match &mut self.0 {
            InnerOffsetTableImpl::Serial(_serial_tbl) => Ok(()),
            InnerOffsetTableImpl::Concurrent(concurrent_tbl) => {
                let lock_guard = concurrent_tbl.growth_lock.write().unwrap();
                let raw_block = concurrent_tbl.block.replace(RawBlock::empty_block());

                match Arc::try_unwrap(raw_block) {
                    Ok(block) => {
                        drop(lock_guard);
                        self.0 = InnerOffsetTableImpl::Serial(SerialOffsetTable { block });
                        Ok(())
                    }
                    Err(_) => Err(()),
                }
            }
        }
    }
}

impl<T: RawBlockTraits> Default for OffsetTableImpl<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
struct SerialOffsetTable<T: RawBlockTraits> {
    block: RawBlock<T>,
}

#[derive(Debug)]
pub struct ConcurrentOffsetTable<T: RawBlockTraits> {
    block: Arcu<RawBlock<T>, GlobalEpochCounterPool>,
    growth_lock: RwLock<()>,
}

#[derive(Debug)]
enum InnerOffsetTableImpl<T: RawBlockTraits> {
    Serial(SerialOffsetTable<T>),
    #[allow(dead_code)]
    Concurrent(Arc<ConcurrentOffsetTable<T>>),
}

impl<T: RawBlockTraits> InnerOffsetTableImpl<T> {
    #[inline(always)]
    fn build_with(&mut self, value: T) -> usize {
        match self {
            Self::Concurrent(concurrent_tbl) => unsafe { concurrent_tbl.build_with(value) },
            Self::Serial(serial_tbl) => unsafe { serial_tbl.build_with(value) },
        }
    }

    #[inline(always)]
    fn lookup<'a>(&'a self, offset: usize) -> TablePtr<'a, T> {
        match self {
            Self::Concurrent(concurrent_tbl) => TablePtr({
                let (rcu_ref, guard_lock) = concurrent_tbl.lookup(offset);
                InnerTablePtr::Concurrent {
                    rcu_ref,
                    guard_lock,
                }
            }),
            Self::Serial(serial_tbl) => unsafe {
                TablePtr(InnerTablePtr::Serial(serial_tbl.lookup(offset)))
            },
        }
    }

    #[inline(always)]
    fn lookup_mut<'a>(&'a mut self, offset: usize) -> TablePtrMut<'a, T> {
        match self {
            InnerOffsetTableImpl::Concurrent(concurrent_tbl) => TablePtrMut({
                let (rcu_ref, guard_lock) = concurrent_tbl.lookup_mut(offset);
                InnerTablePtrMut::Concurrent {
                    rcu_ref,
                    guard_lock,
                }
            }),
            InnerOffsetTableImpl::Serial(serial_tbl) => {
                TablePtrMut(InnerTablePtrMut::Serial(unsafe {
                    serial_tbl.lookup_mut(offset)
                }))
            }
        }
    }
}

pub trait OffsetTable<T: RawBlockTraits> {
    type Offset: Copy + Into<usize>;

    fn build_with(&mut self, value: T) -> Self::Offset;
    fn lookup<'a>(&'a self, offset: Self::Offset) -> TablePtr<'a, T>;
    fn lookup_mut<'a>(&'a mut self, offset: Self::Offset) -> TablePtrMut<'a, T>;
}

impl OffsetTable<OrderedFloat<f64>> for OffsetTableImpl<OrderedFloat<f64>> {
    type Offset = F64Offset;

    fn build_with(&mut self, value: OrderedFloat<f64>) -> F64Offset {
        F64Offset(self.0.build_with(value))
    }

    fn lookup<'a>(&'a self, offset: F64Offset) -> TablePtr<'a, OrderedFloat<f64>> {
        self.0.lookup(offset.into())
    }

    fn lookup_mut<'a>(&'a mut self, offset: F64Offset) -> TablePtrMut<'a, OrderedFloat<f64>> {
        self.0.lookup_mut(offset.into())
    }
}

impl OffsetTable<IndexPtr> for OffsetTableImpl<IndexPtr> {
    type Offset = CodeIndexOffset;

    fn build_with(&mut self, value: IndexPtr) -> CodeIndexOffset {
        CodeIndexOffset(self.0.build_with(value))
    }

    fn lookup<'a>(&'a self, offset: CodeIndexOffset) -> TablePtr<'a, IndexPtr> {
        self.0.lookup(offset.into())
    }

    fn lookup_mut<'a>(&'a mut self, offset: CodeIndexOffset) -> TablePtrMut<'a, IndexPtr> {
        self.0.lookup_mut(offset.into())
    }
}

impl<T: RawBlockTraits> SerialOffsetTable<T> {
    #[inline]
    fn new() -> Self {
        Self {
            block: RawBlock::new(),
        }
    }

    unsafe fn build_with(&mut self, value: T) -> usize {
        let mut ptr;

        loop {
            ptr = self.block.alloc(size_of::<T>());

            if ptr.is_null() {
                let new_block = self.block.grow_new().unwrap();
                self.block = new_block;
            } else {
                break;
            }
        }

        ptr::write(ptr as *mut T, value);
        ptr.addr() - self.block.base.addr()
    }

    #[inline]
    unsafe fn lookup(&self, offset: usize) -> &T {
        &*self.block.base.add(offset).cast::<T>()
    }

    #[inline]
    unsafe fn lookup_mut(&mut self, offset: usize) -> &mut T {
        &mut *self.block.base.add(offset).cast::<T>().cast_mut()
    }
}

impl<T: RawBlockTraits> ConcurrentOffsetTable<T> {
    #[allow(clippy::missing_safety_doc)]
    unsafe fn build_with(&self, value: T) -> usize {
        let update_guard = self.growth_lock.write().unwrap();

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

        let value = ptr.addr() - block_epoch.base.addr();

        // AtomTable would have to update the index table at this point
        // explicit drop to ensure we don't accidentally drop it early
        drop(update_guard);

        value
    }

    #[inline]
    fn lookup<'a>(&'a self, offset: usize) -> (RcuRef<RawBlock<T>, T>, RwLockReadGuard<'a, ()>) {
        let growth_lock_guard = self.growth_lock.read().unwrap();

        let rcu_ref = RcuRef::try_map(self.block.read(), |raw_block| unsafe {
            raw_block.base.add(offset).cast::<T>().as_ref()
        })
        .expect("The offset should result in a non-null pointer");

        (rcu_ref, growth_lock_guard)
    }

    #[inline]
    fn lookup_mut<'a>(
        &'a self,
        offset: usize,
    ) -> (RcuRef<RawBlock<T>, UnsafeCell<T>>, RwLockReadGuard<'a, ()>) {
        let growth_lock_guard = self.growth_lock.read().unwrap();

        let rcu_ref = RcuRef::try_map(self.block.read(), |raw_block| unsafe {
            raw_block
                .base
                .add(offset)
                .cast_mut()
                .cast::<UnsafeCell<T>>()
                .as_ref()
        })
        .expect("The offset should result in a non-null pointer");

        (rcu_ref, growth_lock_guard)
    }
}

pub type F64Table = OffsetTableImpl<OrderedFloat<f64>>;
pub type CodeIndexTable = OffsetTableImpl<IndexPtr>;

#[derive(Clone, Copy, Debug)]
pub struct F64Offset(usize);

impl From<usize> for F64Offset {
    #[inline(always)]
    fn from(offset: usize) -> Self {
        Self(offset)
    }
}

impl From<F64Offset> for usize {
    fn from(val: F64Offset) -> Self {
        val.0
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

impl From<CodeIndexOffset> for usize {
    #[inline(always)]
    fn from(val: CodeIndexOffset) -> Self {
        val.0
    }
}

impl CodeIndexOffset {
    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.0 as u64
    }
}

#[derive(Debug)]
pub struct TablePtr<'a, T: RawBlockTraits>(InnerTablePtr<'a, T>);

#[derive(Debug)]
enum InnerTablePtr<'a, T: RawBlockTraits> {
    Concurrent {
        rcu_ref: RcuRef<RawBlock<T>, T>,
        #[allow(dead_code)]
        guard_lock: RwLockReadGuard<'a, ()>,
    },
    Serial(&'a T),
}

impl<T: PartialEq + RawBlockTraits> PartialEq for TablePtr<'_, T> {
    fn eq(&self, other: &TablePtr<'_, T>) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: Eq + RawBlockTraits> Eq for TablePtr<'_, T> {}

impl<T: PartialOrd + Ord + RawBlockTraits> PartialOrd for TablePtr<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord + RawBlockTraits> Ord for TablePtr<'_, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash + RawBlockTraits> Hash for TablePtr<'_, T> {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self as &T).hash(hasher)
    }
}

impl<T: fmt::Display + RawBlockTraits> fmt::Display for TablePtr<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self as &T)
    }
}

impl<T: RawBlockTraits> Deref for TablePtr<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        match &self.0 {
            InnerTablePtr::Concurrent { rcu_ref, .. } => rcu_ref,
            InnerTablePtr::Serial(ref_mut) => ref_mut,
        }
    }
}

impl fmt::Display for CodeIndexOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CodeIndexOffset({})", self.0)
    }
}

impl F64Offset {
    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.0 as u64
    }
}

impl fmt::Display for F64Offset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "F64Offset({})", self.0)
    }
}

#[derive(Debug)]
pub struct TablePtrMut<'a, T: RawBlockTraits>(InnerTablePtrMut<'a, T>);

#[derive(Debug)]
enum InnerTablePtrMut<'a, T: RawBlockTraits> {
    Concurrent {
        rcu_ref: RcuRef<RawBlock<T>, UnsafeCell<T>>,
        #[allow(dead_code)]
        guard_lock: RwLockReadGuard<'a, ()>,
    },
    Serial(&'a mut T),
}

impl<T: PartialEq + RawBlockTraits> PartialEq for TablePtrMut<'_, T> {
    fn eq(&self, other: &TablePtrMut<'_, T>) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: Eq + RawBlockTraits> Eq for TablePtrMut<'_, T> {}

impl<T: PartialOrd + Ord + RawBlockTraits> PartialOrd for TablePtrMut<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord + RawBlockTraits> Ord for TablePtrMut<'_, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash + RawBlockTraits> Hash for TablePtrMut<'_, T> {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self as &T).hash(hasher)
    }
}

impl<T: fmt::Display + RawBlockTraits> fmt::Display for TablePtrMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self as &T)
    }
}

impl<T: RawBlockTraits> Deref for TablePtrMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        match &self.0 {
            InnerTablePtrMut::Concurrent { rcu_ref, .. } => unsafe {
                rcu_ref.get().as_ref().unwrap()
            },
            InnerTablePtrMut::Serial(ref_mut) => ref_mut,
        }
    }
}

impl<T: RawBlockTraits> DerefMut for TablePtrMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        match &mut self.0 {
            InnerTablePtrMut::Concurrent { rcu_ref, .. } => unsafe {
                &mut *rcu_ref.get().as_mut().unwrap()
            },
            InnerTablePtrMut::Serial(ref_mut) => ref_mut,
        }
    }
}

impl TablePtrMut<'_, IndexPtr> {
    #[inline]
    pub fn set(&mut self, val: IndexPtr) {
        match &mut self.0 {
            InnerTablePtrMut::Concurrent { rcu_ref, .. } => unsafe {
                *rcu_ref.get() = val;
            },
            InnerTablePtrMut::Serial(ref_mut) => {
                **ref_mut = val;
            }
        }
    }

    #[inline]
    pub fn replace(&mut self, val: IndexPtr) -> IndexPtr {
        match &mut self.0 {
            InnerTablePtrMut::Concurrent { rcu_ref, .. } => unsafe { rcu_ref.get().replace(val) },
            InnerTablePtrMut::Serial(ref_mut) => mem::replace(*ref_mut, val),
        }
    }
}
