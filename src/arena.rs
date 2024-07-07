#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

#[cfg(feature = "http")]
use crate::http::{HttpListener, HttpResponse};
use crate::machine::loader::LiveLoadState;
use crate::machine::machine_indices::*;
use crate::machine::streams::*;
use crate::raw_block::*;
use crate::read::*;
use crate::types::UntypedArenaPtr;

use crate::parser::dashu::{Integer, Rational};
use arcu::atomic::Arcu;
use arcu::epoch_counters::GlobalEpochCounterPool;
use arcu::rcu_ref::RcuRef;
use arcu::Rcu;
use ordered_float::OrderedFloat;

use std::cell::UnsafeCell;
use std::fmt;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::mem;
use std::mem::ManuallyDrop;
use std::net::TcpListener;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::ptr::addr_of_mut;
use std::ptr::NonNull;
use std::sync::RwLock;

#[macro_export]
macro_rules! arena_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        $crate::arena::AllocateInArena::arena_allocate(result, $arena)
    }};
}

#[macro_export]
macro_rules! float_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        unsafe { $arena.f64_tbl.build_with(result).as_ptr() }
    }};
}

pub fn header_offset_from_payload<T: ?Sized + ArenaAllocated>() -> usize
where
    T::Payload: Sized,
{
    let payload_offset = mem::offset_of!(TypedAllocSlab<T>, payload);
    let slab_offset = mem::offset_of!(TypedAllocSlab<T>, slab);
    let header_offset = slab_offset + mem::offset_of!(AllocSlab, header);

    debug_assert!(payload_offset > header_offset);
    payload_offset - header_offset
}

use std::sync::Arc;
use std::sync::Mutex;
use std::sync::Weak;

const F64_TABLE_INIT_SIZE: usize = 1 << 16;
const F64_TABLE_ALIGN: usize = 8;

#[inline(always)]
fn global_f64table() -> &'static RwLock<Weak<F64Table>> {
    static GLOBAL_ATOM_TABLE: RwLock<Weak<F64Table>> = RwLock::new(Weak::new());
    &GLOBAL_ATOM_TABLE
}

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

#[derive(Debug)]
pub struct F64Table {
    block: Arcu<RawBlock<F64Table>, GlobalEpochCounterPool>,
    update: Mutex<()>,
}

#[inline(always)]
pub fn lookup_float(
    offset: F64Offset,
) -> RcuRef<RawBlock<F64Table>, UnsafeCell<OrderedFloat<f64>>> {
    let f64table = global_f64table()
        .read()
        .unwrap()
        .upgrade()
        .expect("We should only be looking up floats while there is a float table");

    RcuRef::try_map(f64table.block.read(), |raw_block| unsafe {
        raw_block
            .base
            .add(offset.0)
            .cast_mut()
            .cast::<UnsafeCell<OrderedFloat<f64>>>()
            .as_ref()
    })
    .expect("The offset should result in a non-null pointer")
}

impl F64Table {
    #[inline]
    pub fn new() -> Arc<Self> {
        let upgraded = global_f64table().read().unwrap().upgrade();
        // don't inline upgraded, otherwise temporary will be dropped too late in case of None
        if let Some(atom_table) = upgraded {
            atom_table
        } else {
            let mut guard = global_f64table().write().unwrap();
            // try to upgrade again in case we lost the race on the write lock
            if let Some(atom_table) = guard.upgrade() {
                atom_table
            } else {
                let atom_table = Arc::new(Self {
                    block: Arcu::new(RawBlock::new(), GlobalEpochCounterPool),
                    update: Mutex::new(()),
                });
                *guard = Arc::downgrade(&atom_table);
                atom_table
            }
        }
    }

    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn build_with(&self, value: f64) -> F64Offset {
        let update_guard = self.update.lock();

        // we don't have an index table for lookups as AtomTable does so
        // just get the epoch after we take the upgrade lock
        let mut block_epoch = self.block.read();

        let mut ptr;

        loop {
            ptr = block_epoch.alloc(mem::size_of::<f64>());

            if ptr.is_null() {
                let new_block = block_epoch.grow_new().unwrap();
                self.block.replace(new_block);
                block_epoch = self.block.read();
            } else {
                break;
            }
        }

        ptr::write(ptr as *mut OrderedFloat<f64>, OrderedFloat(value));

        let float = F64Offset(ptr as usize - block_epoch.base as usize);

        // atometable would have to update the index table at this point

        // expicit drop to ensure we don't accidentally drop it early
        drop(update_guard);

        float
    }
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq)]
#[bits = 7]
pub enum ArenaHeaderTag {
    Integer = 0b10,
    Rational = 0b11,
    LiveLoadState = 0b0001000,
    InactiveLoadState = 0b1011000,
    InputFileStream = 0b10000,
    OutputFileStream = 0b10100,
    NamedTcpStream = 0b011100,
    NamedTlsStream = 0b100000,
    HttpReadStream = 0b100001,
    HttpWriteStream = 0b100010,
    ReadlineStream = 0b110000,
    StaticStringStream = 0b110100,
    ByteStream = 0b111000,
    StandardOutputStream = 0b1100,
    StandardErrorStream = 0b11000,
    NullStream = 0b111100,
    TcpListener = 0b1000000,
    HttpListener = 0b1000001,
    HttpResponse = 0b1000010,
    Dropped = 0b1000100,
    IndexPtrDynamicUndefined = 0b1000101,
    IndexPtrDynamicIndex = 0b1000110,
    IndexPtrIndex = 0b1000111,
    IndexPtrUndefined = 0b1001000,
}

#[bitfield]
#[derive(Copy, Clone, Debug)]
pub struct ArenaHeader {
    #[allow(dead_code)]
    size: B56,
    m: bool,
    tag: ArenaHeaderTag,
}

const_assert!(mem::size_of::<ArenaHeader>() == 8);

impl ArenaHeader {
    #[inline]
    pub fn build_with(size: u64, tag: ArenaHeaderTag) -> Self {
        ArenaHeader::new()
            .with_size(size)
            .with_tag(tag)
            .with_m(false)
    }

    #[inline]
    pub fn get_tag(self) -> ArenaHeaderTag {
        self.tag()
    }
}

#[derive(Debug)]
pub struct TypedArenaPtr<T: ?Sized + ArenaAllocated>(ptr::NonNull<T::Payload>);

impl<T: ?Sized + ArenaAllocated> PartialOrd for TypedArenaPtr<T>
where
    T::Payload: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + ArenaAllocated> PartialEq for TypedArenaPtr<T>
where
    T::Payload: PartialEq,
{
    fn eq(&self, other: &TypedArenaPtr<T>) -> bool {
        std::ptr::addr_eq(self.0.as_ptr(), other.0.as_ptr()) || **self == **other
    }
}

impl<T: ?Sized + ArenaAllocated> Eq for TypedArenaPtr<T> where T::Payload: Eq {}

impl<T: ?Sized + ArenaAllocated> Ord for TypedArenaPtr<T>
where
    T::Payload: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + ArenaAllocated> Hash for TypedArenaPtr<T>
where
    T::Payload: Hash,
{
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self as &T::Payload).hash(hasher)
    }
}

impl<T: ?Sized + ArenaAllocated> Clone for TypedArenaPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + ArenaAllocated> Copy for TypedArenaPtr<T> {}

impl<T: ?Sized + ArenaAllocated> Deref for TypedArenaPtr<T> {
    type Target = T::Payload;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T: ?Sized + ArenaAllocated> DerefMut for TypedArenaPtr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<T: ArenaAllocated> fmt::Display for TypedArenaPtr<T>
where
    T::Payload: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", (self as &T::Payload))
    }
}

impl<T: ?Sized + ArenaAllocated> TypedArenaPtr<T> {
    /// # Safety
    /// - the pointers referee type is correct, safe code depends on the correctness of the type argument
    /// - the pointer is allocated in the arena
    #[inline]
    pub const unsafe fn new(data: *mut T::Payload) -> Self {
        unsafe { TypedArenaPtr(ptr::NonNull::new_unchecked(data)) }
    }

    #[inline]
    pub fn as_ptr(&self) -> *mut T::Payload {
        self.0.as_ptr()
    }
}

impl<T: ?Sized + ArenaAllocated> TypedArenaPtr<T>
where
    T::Payload: Sized,
{
    #[inline]
    pub fn header_ptr(&self) -> *const ArenaHeader {
        unsafe { self.as_ptr().byte_sub(T::header_offset_from_payload()) as *const _ }
    }

    #[inline]
    fn header_ptr_mut(&mut self) -> *mut ArenaHeader {
        unsafe { self.as_ptr().byte_sub(T::header_offset_from_payload()) as *mut _ }
    }

    #[inline]
    pub fn get_mark_bit(&self) -> bool {
        unsafe { (*self.header_ptr()).m() }
    }

    #[inline]
    pub fn set_tag(&mut self, tag: ArenaHeaderTag) {
        unsafe {
            (*self.header_ptr_mut()).set_tag(tag);
        }
    }

    #[inline]
    pub fn get_tag(&self) -> ArenaHeaderTag {
        unsafe { (*self.header_ptr()).get_tag() }
    }

    #[inline]
    pub fn mark(&mut self) {
        unsafe {
            (*self.header_ptr_mut()).set_m(true);
        }
    }

    #[inline]
    pub fn unmark(&mut self) {
        unsafe {
            (*self.header_ptr_mut()).set_m(false);
        }
    }
}

pub trait AllocateInArena<AllocFor>
where
    AllocFor: ArenaAllocated,
{
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<AllocFor>;
}

impl<P, T: ArenaAllocated<Payload = P>> AllocateInArena<T> for P {
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<T> {
        T::alloc(arena, self)
    }
}

/* apparently this overlaps the planket impl above somehow
impl<P, T: ArenaAllocated<Payload = ManuallyDrop<P>>> AllocateInArena<T> for P {
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<T> {
        T::alloc(arena, ManuallyDrop::new(self))
    }
}
*/

pub trait ArenaAllocated {
    type Payload: ?Sized;

    fn tag() -> ArenaHeaderTag;

    fn header_offset_from_payload() -> usize
    where
        Self::Payload: Sized,
    {
        header_offset_from_payload::<Self>()
    }

    /// #  Safety
    /// - the caller must guarantee that the pointee type of UntypedArenaPtr is Self
    unsafe fn typed_ptr(ptr: UntypedArenaPtr) -> TypedArenaPtr<Self>
    where
        Self::Payload: Sized,
    {
        // safety:
        // - allocated in an arena as from an UntypedArenaPtr
        // - caller guarantees the type is correct
        unsafe { TypedArenaPtr::new(ptr.payload_offset().cast_mut().cast::<Self::Payload>()) }
    }

    #[allow(clippy::missing_safety_doc)]
    fn alloc(arena: &mut Arena, value: Self::Payload) -> TypedArenaPtr<Self>
    where
        Self::Payload: Sized,
    {
        let size = mem::size_of::<TypedAllocSlab<Self>>();
        let slab = Box::new(TypedAllocSlab {
            slab: AllocSlab {
                next: arena.base.take(),
                #[cfg(target_pointer_width = "32")]
                _padding: 0,
                header: HeaderOrIdxPtr {
                    header: ArenaHeader::build_with(size as u64, Self::tag()),
                },
            },
            payload: value,
        });

        let raw_box = Box::into_raw(slab);
        // safety: Box::into_raw retuns a pointer to a valid allocation
        let allocated_ptr = unsafe { TypedAllocSlab::to_typed_arena_ptr(raw_box) };

        arena.base = Some(NonNull::new(raw_box.cast::<AllocSlab>()).unwrap());

        allocated_ptr
    }

    /// # Safety
    /// - ptr points to an allocated slab of the correct kind
    unsafe fn dealloc(ptr: NonNull<TypedAllocSlab<Self>>) {
        drop(unsafe { Box::from_raw(ptr.as_ptr()) });
    }
}

#[derive(Debug)]
pub struct F64Ptr(RcuRef<RawBlock<F64Table>, UnsafeCell<OrderedFloat<f64>>>);

impl Clone for F64Ptr {
    fn clone(&self) -> Self {
        Self(RcuRef::clone(&self.0))
    }
}

impl PartialEq for F64Ptr {
    fn eq(&self, other: &F64Ptr) -> bool {
        RcuRef::ptr_eq(&self.0, &other.0) || self.deref() == other.deref()
    }
}

impl Eq for F64Ptr {}

impl PartialOrd for F64Ptr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for F64Ptr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl Hash for F64Ptr {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self as &OrderedFloat<f64>).hash(hasher)
    }
}

impl fmt::Display for F64Ptr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self as &OrderedFloat<f64>)
    }
}

impl Deref for F64Ptr {
    type Target = OrderedFloat<f64>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.get().as_ref().unwrap() }
    }
}

impl DerefMut for F64Ptr {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.0.get().as_mut().unwrap() }
    }
}

impl F64Ptr {
    #[inline(always)]
    pub fn from_offset(offset: F64Offset) -> Self {
        Self(lookup_float(offset))
    }

    #[inline(always)]
    pub fn as_offset(&self) -> F64Offset {
        F64Offset(self.0.get() as usize - RcuRef::get_root(&self.0).base as usize)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct F64Offset(usize);

impl F64Offset {
    #[inline(always)]
    pub fn new(offset: usize) -> Self {
        Self(offset)
    }

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

impl ArenaAllocated for Integer {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Integer
    }
}

impl ArenaAllocated for Rational {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Rational
    }
}

impl ArenaAllocated for LiveLoadState {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::LiveLoadState
    }
}

impl ArenaAllocated for TcpListener {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::TcpListener
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpListener {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpListener
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpResponse {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpResponse
    }
}

impl ArenaAllocated for IndexPtr {
    type Payload = Self;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::IndexPtrUndefined
    }

    #[inline]
    fn header_offset_from_payload() -> usize {
        0
    }

    /// #  Safety
    /// - the caller must guarantee that the pointee type of UntypedArenaPtr is T
    unsafe fn typed_ptr(ptr: UntypedArenaPtr) -> TypedArenaPtr<Self> {
        unsafe { TypedArenaPtr::new(ptr.get_ptr().cast_mut().cast::<IndexPtr>()) }
    }

    #[inline]
    fn alloc(arena: &mut Arena, value: Self) -> TypedArenaPtr<Self> {
        let slab = Box::new(AllocSlab {
            next: arena.base.take(),
            #[cfg(target_pointer_width = "32")]
            _padding: 0,
            header: HeaderOrIdxPtr { idx_ptr: value },
        });

        let raw_box = Box::into_raw(slab);
        let allocated_ptr =
            unsafe { TypedArenaPtr::new(ptr::addr_of_mut!((*raw_box).header.idx_ptr)) };
        arena.base = Some(NonNull::new(raw_box).unwrap());
        allocated_ptr
    }

    /// # Safety
    /// - ptr points to an allocated slab of the correct kind
    unsafe fn dealloc(ptr: NonNull<TypedAllocSlab<Self>>) {
        drop(unsafe { Box::from_raw(ptr.as_ptr().cast::<AllocSlab>()) });
    }
}

#[repr(C)]
union HeaderOrIdxPtr {
    header: ArenaHeader,
    idx_ptr: IndexPtr,
}

const _: () = {
    if std::mem::size_of::<ArenaHeader>() != std::mem::size_of::<IndexPtr>() {
        panic!("Size of ArenaHeader != IndexPtr")
    }
};

impl Debug for HeaderOrIdxPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { &self.header }.fmt(f)
    }
}

impl Clone for HeaderOrIdxPtr {
    fn clone(&self) -> Self {
        // safety:
        // - we created the pointer from a valid reference
        // - both ArenaHeader and IndexPtr are plain old datatypes, i.e. no managed resources that need to be cloned
        unsafe { std::ptr::read(self) }
    }
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct AllocSlab {
    next: Option<NonNull<AllocSlab>>,
    #[cfg(target_pointer_width = "32")]
    _padding: u32,
    header: HeaderOrIdxPtr,
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct TypedAllocSlab<T: ?Sized + ArenaAllocated> {
    slab: AllocSlab,
    payload: T::Payload,
}

impl<T: ?Sized + ArenaAllocated> TypedAllocSlab<T> {
    /// # Safety
    /// - ptr points to a valid allocation of Self
    #[inline]
    pub unsafe fn to_typed_arena_ptr(ptr: *mut Self) -> TypedArenaPtr<T> {
        // safety:
        // - this is the arena allocation of corresponding type
        unsafe { TypedArenaPtr::new(addr_of_mut!((*ptr).payload)) }
    }
}

#[derive(Debug)]
pub struct Arena {
    base: Option<NonNull<AllocSlab>>,
    pub f64_tbl: Arc<F64Table>,
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

#[allow(clippy::new_without_default)]
impl Arena {
    #[inline]
    pub fn new() -> Self {
        Arena {
            base: None,
            f64_tbl: F64Table::new(),
        }
    }
}

unsafe fn drop_slab_in_place(value: NonNull<AllocSlab>) {
    macro_rules! drop_typed_slab_in_place {
        ($payload: ty, $value: expr) => {
            <$payload as ArenaAllocated>::dealloc($value.cast::<TypedAllocSlab<$payload>>())
        };
    }

    match (unsafe { value.as_ref() }).header.header.tag() {
        ArenaHeaderTag::Integer => {
            drop_typed_slab_in_place!(Integer, value);
        }
        ArenaHeaderTag::Rational => {
            drop_typed_slab_in_place!(Rational, value);
        }
        ArenaHeaderTag::InputFileStream => {
            drop_typed_slab_in_place!(InputFileStream, value);
        }
        ArenaHeaderTag::OutputFileStream => {
            drop_typed_slab_in_place!(OutputFileStream, value);
        }
        ArenaHeaderTag::NamedTcpStream => {
            drop_typed_slab_in_place!(NamedTcpStream, value);
        }
        ArenaHeaderTag::NamedTlsStream => {
            #[cfg(feature = "tls")]
            drop_typed_slab_in_place!(NamedTlsStream, value);
        }
        ArenaHeaderTag::HttpReadStream => {
            #[cfg(feature = "http")]
            drop_typed_slab_in_place!(HttpReadStream, value);
        }
        ArenaHeaderTag::HttpWriteStream => {
            #[cfg(feature = "http")]
            drop_typed_slab_in_place!(HttpWriteStream, value);
        }
        ArenaHeaderTag::ReadlineStream => {
            drop_typed_slab_in_place!(ReadlineStream, value);
        }
        ArenaHeaderTag::StaticStringStream => {
            drop_typed_slab_in_place!(StaticStringStream, value);
        }
        ArenaHeaderTag::ByteStream => {
            drop_typed_slab_in_place!(ByteStream, value);
        }
        ArenaHeaderTag::LiveLoadState | ArenaHeaderTag::InactiveLoadState => {
            drop_typed_slab_in_place!(LiveLoadState, value);
        }
        ArenaHeaderTag::Dropped => {}
        ArenaHeaderTag::TcpListener => {
            drop_typed_slab_in_place!(TcpListener, value);
        }
        ArenaHeaderTag::HttpListener => {
            #[cfg(feature = "http")]
            drop_typed_slab_in_place!(HttpListener, value);
        }
        ArenaHeaderTag::HttpResponse => {
            #[cfg(feature = "http")]
            drop_typed_slab_in_place!(HttpResponse, value);
        }
        ArenaHeaderTag::StandardOutputStream => {
            drop_typed_slab_in_place!(StandardOutputStream, value);
        }
        ArenaHeaderTag::StandardErrorStream => {
            drop_typed_slab_in_place!(StandardErrorStream, value);
        }
        ArenaHeaderTag::IndexPtrUndefined
        | ArenaHeaderTag::IndexPtrDynamicUndefined
        | ArenaHeaderTag::IndexPtrDynamicIndex
        | ArenaHeaderTag::IndexPtrIndex => {
            drop_typed_slab_in_place!(IndexPtr, value);
        }
        ArenaHeaderTag::NullStream => {
            unreachable!("NullStream is never arena allocated!");
        }
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut ptr = self.base.take();

        while let Some(slab) = ptr {
            unsafe {
                ptr = slab.as_ref().next;
                drop_slab_in_place(slab);
            }
        }
    }
}

const_assert!(mem::size_of::<AllocSlab>() == 16);
const_assert!(mem::size_of::<OrderedFloat<f64>>() == 8);

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use crate::machine::mock_wam::*;
    use crate::machine::partial_string::*;

    use crate::parser::dashu::{Integer, Rational};
    use ordered_float::OrderedFloat;

    #[test]
    fn float_ptr_cast() {
        let wam = MockWAM::new();

        let f = 0f64;
        let fp = float_alloc!(f, wam.machine_st.arena);
        let mut cell = HeapCellValue::from(fp.clone());

        assert_eq!(cell.get_tag(), HeapCellValueTag::F64);
        assert!(!cell.get_mark_bit());
        assert_eq!(fp.deref(), &OrderedFloat(f));

        cell.set_mark_bit(true);

        assert!(cell.get_mark_bit());

        read_heap_cell!(cell,
            (HeapCellValueTag::F64, ptr) => {
                assert_eq!(OrderedFloat(*ptr), OrderedFloat(f))
            }
            _ => { unreachable!() }
        );
    }

    #[test]
    fn heap_cell_value_const_cast() {
        let mut wam = MockWAM::new();
        #[cfg(target_pointer_width = "32")]
        let const_value = HeapCellValue::from(ConsPtr::build_with(
            0x0000_0431 as *const _,
            ConsPtrMaskTag::Cons,
        ));
        #[cfg(target_pointer_width = "64")]
        let const_value = HeapCellValue::from(ConsPtr::build_with(
            0x0000_5555_ff00_0431 as *const _,
            ConsPtrMaskTag::Cons,
        ));

        match const_value.to_untyped_arena_ptr() {
            Some(arena_ptr) => {
                assert_eq!(
                    arena_ptr.into_bytes(),
                    const_value.to_untyped_arena_ptr_bytes()
                );
            }
            None => {
                unreachable!();
            }
        }

        let stream = Stream::from_static_string("test", &mut wam.machine_st.arena);
        let stream_cell =
            HeapCellValue::from(ConsPtr::build_with(stream.as_ptr(), ConsPtrMaskTag::Cons));

        match stream_cell.to_untyped_arena_ptr() {
            Some(arena_ptr) => {
                assert_eq!(
                    arena_ptr.into_bytes(),
                    stream_cell.to_untyped_arena_ptr_bytes()
                );
            }
            None => {
                unreachable!();
            }
        }
    }

    #[test]
    fn heap_put_literal_tests() {
        let mut wam = MockWAM::new();

        // integer

        let big_int: Integer = 2 * Integer::from(1u64 << 63);
        let big_int_ptr: TypedArenaPtr<Integer> = arena_alloc!(big_int, &mut wam.machine_st.arena);

        assert!(!big_int_ptr.as_ptr().is_null());

        let cell = HeapCellValue::from(Literal::Integer(big_int_ptr));
        assert_eq!(cell.get_tag(), HeapCellValueTag::Cons);

        let untyped_arena_ptr = match cell.to_untyped_arena_ptr() {
            Some(ptr) => ptr,
            None => {
                unreachable!()
            }
        };

        match_untyped_arena_ptr!(untyped_arena_ptr,
           (ArenaHeaderTag::Integer, n) => {
               assert_eq!(&*n, &(2 * Integer::from(1u64 << 63)))
           }
           _ => unreachable!()
        );

        read_heap_cell!(cell,
           (HeapCellValueTag::Cons, cons_ptr) => {
               match_untyped_arena_ptr!(cons_ptr,
                  (ArenaHeaderTag::Integer, n) => {
                      assert_eq!(&*n, &(2 * Integer::from(1u64 << 63)))
                  }
                  _ => { unreachable!() }
               )
           }
           _ => { unreachable!() }
        );

        // rational

        let big_rat = Rational::from(2) * Rational::from(1u64 << 63);
        let big_rat_ptr: TypedArenaPtr<Rational> = arena_alloc!(big_rat, &mut wam.machine_st.arena);

        assert!(!big_rat_ptr.as_ptr().is_null());

        let rat_cell = typed_arena_ptr_as_cell!(big_rat_ptr);
        assert_eq!(cell.get_tag(), HeapCellValueTag::Cons);

        match rat_cell.to_untyped_arena_ptr() {
            Some(untyped_arena_ptr) => {
                assert_eq!(
                    Some(big_rat_ptr.header_ptr()),
                    Some(untyped_arena_ptr.into()),
                );
            }
            None => {
                unreachable!();
            }
        }

        // assert_eq!(wam.machine_st.heap[1usize].get_tag(), HeapCellValueTag::Cons);

        read_heap_cell!(rat_cell,
          (HeapCellValueTag::Cons, cons_ptr) => {
              match_untyped_arena_ptr!(cons_ptr,
                 (ArenaHeaderTag::Rational, n) => {
                     assert_eq!(&*n, &(Rational::from(2) * Rational::from(1u64 << 63)));
                 }
                 _ => unreachable!()
              )
          }
          _ => { unreachable!() }
        );

        // atom

        let f_atom = atom!("f");
        let g_atom = atom!("g");

        assert_eq!(&*f_atom.as_str(), "f");
        assert_eq!(&*g_atom.as_str(), "g");

        let f_atom_cell = atom_as_cell!(f_atom);
        let g_atom_cell = atom_as_cell!(g_atom);

        assert_eq!(f_atom_cell.get_tag(), HeapCellValueTag::Atom);

        match f_atom_cell.to_atom() {
            Some(atom) => {
                assert_eq!(f_atom, atom);
                assert_eq!(&*atom.as_str(), "f");
            }
            None => {
                unreachable!();
            }
        }

        read_heap_cell!(f_atom_cell,
            (HeapCellValueTag::Atom, (atom, arity)) => {
                assert_eq!(f_atom, atom);
                assert_eq!(arity, 0);
                assert_eq!(&*atom.as_str(), "f");
            }
            _ => { unreachable!() }
        );

        read_heap_cell!(g_atom_cell,
            (HeapCellValueTag::Atom, (atom, arity)) => {
                assert_eq!(g_atom, atom);
                assert_eq!(arity, 0);
                assert_eq!(&*atom.as_str(), "g");
            }
            _ => { unreachable!() }
        );

        // complete string

        let pstr_var_cell =
            put_partial_string(&mut wam.machine_st.heap, "ronan", &wam.machine_st.atom_tbl);
        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        assert_eq!(pstr_cell.get_tag(), HeapCellValueTag::PStr);

        match pstr_cell.to_pstr() {
            Some(pstr) => {
                assert_eq!(&*pstr.as_str_from(0), "ronan");
            }
            None => {
                unreachable!();
            }
        }

        read_heap_cell!(pstr_cell,
            (HeapCellValueTag::PStr, pstr_atom) => {
                let pstr = PartialString::from(pstr_atom);
                assert_eq!(&*pstr.as_str_from(0), "ronan");
            }
            _ => { unreachable!() }
        );

        // fixnum

        let fixnum_cell = fixnum_as_cell!(Fixnum::build_with(3));

        assert_eq!(fixnum_cell.get_tag(), HeapCellValueTag::Fixnum);

        match fixnum_cell.to_fixnum() {
            Some(n) => assert_eq!(n.get_num(), 3),
            None => unreachable!(),
        }

        read_heap_cell!(fixnum_cell,
            (HeapCellValueTag::Fixnum, n) => {
                assert_eq!(n.get_num(), 3);
            }
            _ => { unreachable!() }
        );

        let fixnum_b_cell = fixnum_as_cell!(Fixnum::build_with(1 << 54));

        assert_eq!(fixnum_b_cell.get_tag(), HeapCellValueTag::Fixnum);

        match fixnum_b_cell.to_fixnum() {
            Some(n) => assert_eq!(n.get_num(), 1 << 54),
            None => unreachable!(),
        }

        if Fixnum::build_with_checked(1 << 56).is_ok() {
            unreachable!()
        }

        if Fixnum::build_with_checked(i64::MAX).is_ok() {
            unreachable!()
        }

        if Fixnum::build_with_checked(i64::MIN).is_ok() {
            unreachable!()
        }

        match Fixnum::build_with_checked(-1) {
            Ok(n) => assert_eq!(n.get_num(), -1),
            _ => unreachable!(),
        }

        match Fixnum::build_with_checked((1 << 55) - 1) {
            Ok(n) => assert_eq!(n.get_num(), (1 << 55) - 1),
            _ => unreachable!(),
        }

        match Fixnum::build_with_checked(-(1 << 55)) {
            Ok(n) => assert_eq!(n.get_num(), -(1 << 55)),
            _ => unreachable!(),
        }

        if Fixnum::build_with_checked(-(1 << 55) - 1).is_ok() {
            unreachable!()
        }

        match Fixnum::build_with_checked(-1) {
            Ok(n) => assert_eq!(-n, Fixnum::build_with(1)),
            _ => unreachable!(),
        }

        // float

        let float = std::f64::consts::PI;
        let float_ptr = float_alloc!(float, wam.machine_st.arena);
        let cell = HeapCellValue::from(float_ptr);

        assert_eq!(cell.get_tag(), HeapCellValueTag::F64);

        // char

        let c = 'c';
        let char_cell = char_as_cell!(c);

        read_heap_cell!(char_cell,
            (HeapCellValueTag::Char, c) => {
                assert_eq!(c, 'c');
            }
            _ => { unreachable!() }
        );

        let c = 'Ћ';
        let cyrillic_char_cell = char_as_cell!(c);

        read_heap_cell!(cyrillic_char_cell,
            (HeapCellValueTag::Char, c) => {
                assert_eq!(c, 'Ћ');
            }
            _ => { unreachable!() }
        );

        // empty list

        let cell = empty_list_as_cell!();

        read_heap_cell!(cell,
            (HeapCellValueTag::Atom, (el, _arity)) => {
                assert_eq!(el.flat_index(), empty_list_as_cell!().get_value());
                assert_eq!(&*el.as_str(), "[]");
            }
            _ => { unreachable!() }
        );
    }
}
