use std::cell::UnsafeCell;
use std::sync::Arc;
use std::{fmt, mem, ptr};

use arcu::atomic::Arcu;
use arcu::epoch_counters::GlobalEpochCounterPool;
use arcu::rcu_ref::RcuRef;
use arcu::Rcu;
use parking_lot::RwLock;

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

impl<T: fmt::Debug + RawBlockTraits> OffsetTableImpl<T> {
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
                let num_tbl_entries = serial_tbl.block.size() / size_of::<T>();
                let block = Arcu::new(serial_tbl.block, GlobalEpochCounterPool);

                let offset_locks: Vec<RwLock<()>> =
                    (0..num_tbl_entries).map(|_| RwLock::new(())).collect();

                let concurrent_tbl = Arc::new(ConcurrentOffsetTable {
                    block,
                    growth_lock: RwLock::new(()),
                    offset_locks: RwLock::new(offset_locks),
                });

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
                let table_arc = std::mem::replace(
                    concurrent_tbl,
                    Arc::new(ConcurrentOffsetTable {
                        block: Arcu::new(RawBlock::empty_block(), GlobalEpochCounterPool),
                        growth_lock: RwLock::new(()),
                        offset_locks: RwLock::new(vec![]),
                    }),
                );

                match Arc::try_unwrap(table_arc) {
                    Ok(table) => {
                        // this was the only instance of the concurrent table, as such
                        // at this point no build_with/with_entry{_mut} call can be in-progress/made

                        // this shouldn't be able to fail
                        let raw_block =
                            Arc::try_unwrap(table.block.replace(RawBlock::empty_block())).unwrap();
                        self.0 =
                            InnerOffsetTableImpl::Serial(SerialOffsetTable { block: raw_block });
                        Ok(())
                    }
                    Err(table_arc) => {
                        // restore the concurrent_tbl
                        *concurrent_tbl = table_arc;
                        Err(())
                    }
                }
            }
        }
    }

    #[inline]
    pub fn get_entry(&self, offset: <Self as OffsetTable<T>>::Offset) -> T
    where
        Self: OffsetTable<T>,
        T: Copy,
    {
        self.with_entry(offset, |value| *value)
    }
}

impl<T: fmt::Debug + RawBlockTraits> Default for OffsetTableImpl<T> {
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
    offset_locks: RwLock<Vec<RwLock<()>>>,
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
            Self::Concurrent(concurrent_tbl) => concurrent_tbl.build_with(value),
            Self::Serial(serial_tbl) => unsafe { serial_tbl.build_with(value) },
        }
    }

    #[inline(always)]
    fn with_entry<R, F: FnOnce(&T) -> R>(&self, offset: usize, f: F) -> R {
        match self {
            Self::Concurrent(concurrent_tbl) => concurrent_tbl.with_entry(offset, f),
            Self::Serial(serial_tbl) => f(unsafe { serial_tbl.lookup(offset) }),
        }
    }

    #[inline(always)]
    fn with_entry_mut<R, F: FnOnce(&mut T) -> R>(&mut self, offset: usize, f: F) -> R {
        match self {
            Self::Concurrent(concurrent_tbl) => concurrent_tbl.with_entry_mut(offset, f),
            Self::Serial(serial_tbl) => f(unsafe { serial_tbl.lookup_mut(offset) }),
        }
    }
}

pub trait OffsetTable<T: RawBlockTraits> {
    type Offset: Copy + Into<usize>;

    fn build_with(&mut self, value: T) -> Self::Offset;

    fn with_entry<R, F: FnOnce(&T) -> R>(&self, offset: Self::Offset, f: F) -> R;
    fn with_entry_mut<R, F: FnOnce(&mut T) -> R>(&mut self, offset: Self::Offset, f: F) -> R;
}

impl OffsetTable<OrderedFloat<f64>> for OffsetTableImpl<OrderedFloat<f64>> {
    type Offset = F64Offset;

    fn build_with(&mut self, value: OrderedFloat<f64>) -> F64Offset {
        F64Offset(self.0.build_with(value))
    }

    #[inline]
    fn with_entry<R, F: FnOnce(&OrderedFloat<f64>) -> R>(&self, offset: F64Offset, f: F) -> R {
        self.0.with_entry(offset.into(), f)
    }

    #[inline]
    fn with_entry_mut<R, F: FnOnce(&mut OrderedFloat<f64>) -> R>(
        &mut self,
        offset: F64Offset,
        f: F,
    ) -> R {
        self.0.with_entry_mut(offset.into(), f)
    }
}

impl OffsetTable<IndexPtr> for OffsetTableImpl<IndexPtr> {
    type Offset = CodeIndexOffset;

    fn build_with(&mut self, value: IndexPtr) -> CodeIndexOffset {
        CodeIndexOffset(self.0.build_with(value))
    }

    #[inline]
    fn with_entry<R, F: FnOnce(&IndexPtr) -> R>(&self, offset: CodeIndexOffset, f: F) -> R {
        self.0.with_entry(offset.into(), f)
    }

    #[inline]
    fn with_entry_mut<R, F: FnOnce(&mut IndexPtr) -> R>(
        &mut self,
        offset: CodeIndexOffset,
        f: F,
    ) -> R {
        self.0.with_entry_mut(offset.into(), f)
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
    fn build_with(&self, value: T) -> usize {
        let growth_lock = self.growth_lock.write();

        // we don't have an index table for lookups as AtomTable does so
        // just get the epoch after we take the upgrade lock
        let mut block_epoch = self.block.read();
        let mut ptr;

        loop {
            ptr = unsafe { block_epoch.alloc(mem::size_of::<T>()) };

            if ptr.is_null() {
                let new_block = unsafe { block_epoch.grow_new().unwrap() };
                self.block.replace(new_block);
                block_epoch = self.block.read();
            } else {
                break;
            }
        }

        let new_tbl_sz = block_epoch.size() / size_of::<T>();
        let mut offset_locks = self.offset_locks.write();

        offset_locks.resize_with(new_tbl_sz, || RwLock::new(()));

        unsafe {
            ptr::write(ptr as *mut T, value);
        }

        let value = ptr.addr() - block_epoch.base.addr();

        // AtomTable would have to update the index table at this point
        // explicit drop to ensure we don't accidentally drop it early
        drop(offset_locks);
        drop(growth_lock);

        value
    }

    fn with_entry<R, F: FnOnce(&T) -> R>(&self, offset: usize, f: F) -> R {
        let outer_offset_lock = self.offset_locks.read();
        let inner_offset_lock = outer_offset_lock[offset / size_of::<T>()].read();

        let rcu_ref = RcuRef::try_map(self.block.read(), |raw_block| unsafe {
            raw_block.base.add(offset).cast::<T>().as_ref()
        })
        .expect("offset valid");

        let result = f(&*rcu_ref);

        drop(inner_offset_lock);
        drop(outer_offset_lock);

        result
    }

    fn with_entry_mut<R, F: FnOnce(&mut T) -> R>(&self, offset: usize, f: F) -> R {
        let growth_lock = self.growth_lock.read();
        let outer_offset_lock = self.offset_locks.read();
        let inner_offset_lock = outer_offset_lock[offset / size_of::<T>()].write();

        let rcu_ref = RcuRef::try_map(self.block.read(), |raw_block| unsafe {
            raw_block
                .base
                .add(offset)
                .cast_mut()
                .cast::<UnsafeCell<T>>()
                .as_ref()
        })
        .expect("offset valid");

        let result = f(unsafe { &mut *rcu_ref.get().as_mut().unwrap() });

        drop(inner_offset_lock);
        drop(outer_offset_lock);
        drop(growth_lock);

        result
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
