#[cfg(feature = "http")]
use crate::http::{HttpListener, HttpResponse};
use crate::machine::loader::LiveLoadState;
use crate::machine::machine_indices::*;
use crate::machine::streams::*;
use crate::raw_block::*;
use crate::rcu::Rcu;
use crate::rcu::RcuRef;
use crate::read::*;

use crate::parser::dashu::{Integer, Rational};
use ordered_float::OrderedFloat;

use std::alloc;
use std::cell::UnsafeCell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::net::TcpListener;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::sync::RwLock;

#[macro_export]
macro_rules! arena_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        #[allow(unused_unsafe)]
        unsafe {
            ArenaAllocated::alloc($arena, result)
        }
    }};
}

#[macro_export]
macro_rules! float_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        #[allow(unused_unsafe)]
        unsafe {
            $arena.f64_tbl.build_with(result).as_ptr()
        }
    }};
}

use std::sync::Arc;
use std::sync::Mutex;
use std::sync::Weak;

const F64_TABLE_INIT_SIZE: usize = 1 << 16;
const F64_TABLE_ALIGN: usize = 8;

#[inline(always)]
fn global_f64table() -> &'static RwLock<Weak<F64Table>> {
    #[cfg(feature = "rust_beta_channel")]
    {
        // const Weak::new will be stabilized in 1.73 which is currently in beta,
        // till then we need a OnceLock for initialization
        static GLOBAL_ATOM_TABLE: RwLock<Weak<F64Table>> = RwLock::const_new(Weak::new());
        &GLOBAL_ATOM_TABLE
    }
    #[cfg(not(feature = "rust_beta_channel"))]
    {
        use std::sync::OnceLock;
        static GLOBAL_ATOM_TABLE: OnceLock<RwLock<Weak<F64Table>>> = OnceLock::new();
        GLOBAL_ATOM_TABLE.get_or_init(|| RwLock::new(Weak::new()))
    }
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
    block: Rcu<RawBlock<F64Table>>,
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

    RcuRef::try_map(f64table.block.active_epoch(), |raw_block| unsafe {
        raw_block
            .base
            .offset(offset.0 as isize)
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
                    block: Rcu::new(RawBlock::new()),
                    update: Mutex::new(()),
                });
                *guard = Arc::downgrade(&atom_table);
                atom_table
            }
        }
    }

    pub unsafe fn build_with(&self, value: f64) -> F64Offset {
        let update_guard = self.update.lock();

        // we don't have an index table for lookups as AtomTable does so
        // just get the epoch after we take the upgrade lock
        let mut block_epoch = self.block.active_epoch();

        let mut ptr;

        loop {
            ptr = block_epoch.alloc(mem::size_of::<f64>());

            if ptr.is_null() {
                let new_block = block_epoch.grow_new().unwrap();
                self.block.replace(new_block);
                block_epoch = self.block.active_epoch();
            } else {
                break;
            }
        }

        ptr::write(ptr as *mut OrderedFloat<f64>, OrderedFloat(value));

        let float = F64Offset {
            0: ptr as usize - block_epoch.base as usize,
        };

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
pub struct TypedArenaPtr<T: ?Sized>(ptr::NonNull<T>);

impl<T: ?Sized + PartialOrd> PartialOrd for TypedArenaPtr<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for TypedArenaPtr<T> {
    fn eq(&self, other: &TypedArenaPtr<T>) -> bool {
        self.0 == other.0 || &**self == &**other
    }
}

impl<T: ?Sized + PartialEq> Eq for TypedArenaPtr<T> {}

impl<T: ?Sized + Ord> Ord for TypedArenaPtr<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Hash> Hash for TypedArenaPtr<T> {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (&*self as &T).hash(hasher)
    }
}

impl<T: ?Sized> Clone for TypedArenaPtr<T> {
    fn clone(&self) -> Self {
        TypedArenaPtr(self.0)
    }
}

impl<T: ?Sized> Copy for TypedArenaPtr<T> {}

impl<T: ?Sized> Deref for TypedArenaPtr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for TypedArenaPtr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<T: fmt::Display> fmt::Display for TypedArenaPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", **self)
    }
}

impl<T: ?Sized + ArenaAllocated> TypedArenaPtr<T> {
    // data must be allocated in the arena already.
    #[inline]
    pub const fn new(data: *mut T) -> Self {
        let result = unsafe { TypedArenaPtr(ptr::NonNull::new_unchecked(data)) };
        result
    }

    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

    #[inline]
    pub fn header_ptr(&self) -> *const ArenaHeader {
        let mut ptr = self.as_ptr() as *const u8 as usize;
        ptr -= T::header_offset_from_payload(); // mem::size_of::<*const ArenaHeader>();
        ptr as *const ArenaHeader
    }

    #[inline]
    fn header_ptr_mut(&mut self) -> *mut ArenaHeader {
        let mut ptr = self.as_ptr() as *const u8 as usize;
        ptr -= T::header_offset_from_payload(); // mem::size_of::<*const ArenaHeader>();
        ptr as *mut ArenaHeader
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

pub trait ArenaAllocated: Sized {
    type PtrToAllocated;

    fn tag() -> ArenaHeaderTag;
    fn size(&self) -> usize;
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated;

    fn header_offset_from_payload() -> usize {
        mem::size_of::<ArenaHeader>()
    }

    unsafe fn alloc(arena: &mut Arena, value: Self) -> Self::PtrToAllocated {
        let size = value.size() + mem::size_of::<AllocSlab>();

        #[cfg(target_pointer_width = "32")]
        let align = mem::align_of::<AllocSlab>() * 2;

        #[cfg(target_pointer_width = "64")]
        let align = mem::align_of::<AllocSlab>();
        let layout = alloc::Layout::from_size_align_unchecked(size, align);

        let slab = alloc::alloc(layout) as *mut AllocSlab;

        (*slab).next = arena.base;
        (*slab).header = ArenaHeader::build_with(value.size() as u64, Self::tag());

        let offset = (*slab).payload_offset();
        let result = value.copy_to_arena(offset as *mut Self);

        arena.base = slab;

        result
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
        (**self).partial_cmp(&**other)
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
        (&*self as &OrderedFloat<f64>).hash(hasher)
    }
}

impl fmt::Display for F64Ptr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", *self)
    }
}

impl Deref for F64Ptr {
    type Target = OrderedFloat<f64>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0.get().as_ref().unwrap() }
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
        self.as_ptr().partial_cmp(&other.as_ptr())
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
    type PtrToAllocated = TypedArenaPtr<Integer>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Integer
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

impl ArenaAllocated for Rational {
    type PtrToAllocated = TypedArenaPtr<Rational>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Rational
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

impl ArenaAllocated for LiveLoadState {
    type PtrToAllocated = TypedArenaPtr<LiveLoadState>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::LiveLoadState
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

impl ArenaAllocated for TcpListener {
    type PtrToAllocated = TypedArenaPtr<TcpListener>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::TcpListener
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpListener {
    type PtrToAllocated = TypedArenaPtr<HttpListener>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpListener
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpResponse {
    type PtrToAllocated = TypedArenaPtr<HttpResponse>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpResponse
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }
}

impl ArenaAllocated for IndexPtr {
    type PtrToAllocated = TypedArenaPtr<IndexPtr>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::IndexPtrUndefined
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            TypedArenaPtr::new(dst as *mut Self)
        }
    }

    #[inline]
    fn header_offset_from_payload() -> usize {
        0
    }

    unsafe fn alloc(arena: &mut Arena, value: Self) -> Self::PtrToAllocated {
        let size = mem::size_of::<AllocSlab>();

        let align = mem::align_of::<AllocSlab>();
        let layout = alloc::Layout::from_size_align_unchecked(size, align);

        let slab = alloc::alloc(layout) as *mut AllocSlab;

        (*slab).next = arena.base;

        let result = value.copy_to_arena(mem::transmute::<_, *mut IndexPtr>(&(*slab).header));
        arena.base = slab;

        result
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct AllocSlab {
    next: *mut AllocSlab,
    #[cfg(target_pointer_width = "32")]
    _padding: u32,
    header: ArenaHeader,
}

#[derive(Debug)]
pub struct Arena {
    base: *mut AllocSlab,
    pub f64_tbl: Arc<F64Table>,
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
    #[inline]
    pub fn new() -> Self {
        Arena {
            base: ptr::null_mut(),
            f64_tbl: F64Table::new(),
        }
    }
}

unsafe fn drop_slab_in_place(value: &mut AllocSlab) {
    use crate::parser::char_reader::CharReader;

    match value.header.tag() {
        ArenaHeaderTag::Integer => {
            ptr::drop_in_place(value.payload_offset::<Integer>());
        }
        ArenaHeaderTag::Rational => {
            ptr::drop_in_place(value.payload_offset::<Rational>());
        }
        ArenaHeaderTag::InputFileStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<InputFileStream>>>());
        }
        ArenaHeaderTag::OutputFileStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<OutputFileStream>>());
        }
        ArenaHeaderTag::NamedTcpStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<NamedTcpStream>>>());
        }
        ArenaHeaderTag::NamedTlsStream => {
            #[cfg(feature = "tls")]
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<NamedTlsStream>>>());
        }
        ArenaHeaderTag::HttpReadStream => {
            #[cfg(feature = "http")]
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<HttpReadStream>>>());
        }
        ArenaHeaderTag::HttpWriteStream => {
            #[cfg(feature = "http")]
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<HttpWriteStream>>>());
        }
        ArenaHeaderTag::ReadlineStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<ReadlineStream>>());
        }
        ArenaHeaderTag::StaticStringStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<StaticStringStream>>());
        }
        ArenaHeaderTag::ByteStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<CharReader<ByteStream>>>());
        }
        ArenaHeaderTag::LiveLoadState | ArenaHeaderTag::InactiveLoadState => {
            ptr::drop_in_place(value.payload_offset::<LiveLoadState>());
        }
        ArenaHeaderTag::Dropped => {}
        ArenaHeaderTag::TcpListener => {
            ptr::drop_in_place(value.payload_offset::<TcpListener>());
        }
        ArenaHeaderTag::HttpListener => {
            #[cfg(feature = "http")]
            ptr::drop_in_place(value.payload_offset::<HttpListener>());
        }
        ArenaHeaderTag::HttpResponse => {
            #[cfg(feature = "http")]
            ptr::drop_in_place(value.payload_offset::<HttpResponse>());
        }
        ArenaHeaderTag::StandardOutputStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<StandardOutputStream>>());
        }
        ArenaHeaderTag::StandardErrorStream => {
            ptr::drop_in_place(value.payload_offset::<StreamLayout<StandardErrorStream>>());
        }
        ArenaHeaderTag::NullStream
        | ArenaHeaderTag::IndexPtrUndefined
        | ArenaHeaderTag::IndexPtrDynamicUndefined
        | ArenaHeaderTag::IndexPtrDynamicIndex
        | ArenaHeaderTag::IndexPtrIndex => {}
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut ptr = self.base;

        while !ptr.is_null() {
            unsafe {
                let ptr_r = &*ptr;

                let layout = alloc::Layout::from_size_align_unchecked(
                    ptr_r.slab_size(),
                    mem::align_of::<AllocSlab>(),
                );

                drop_slab_in_place(&mut *ptr);

                let next_ptr = ptr_r.next;
                alloc::dealloc(ptr as *mut u8, layout);
                ptr = next_ptr;
            }
        }

        self.base = ptr::null_mut();
    }
}

const_assert!(mem::size_of::<AllocSlab>() == 16);

impl AllocSlab {
    #[inline]
    fn slab_size(&self) -> usize {
        self.header.size() as usize + mem::size_of::<AllocSlab>()
    }

    fn payload_offset<T>(&self) -> *mut T {
        let mut ptr = (self as *const AllocSlab) as usize;
        ptr += mem::size_of::<AllocSlab>();
        ptr as *mut T
    }
}

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
        assert_eq!(cell.get_mark_bit(), false);
        assert_eq!(fp.deref(), &OrderedFloat(f));

        cell.set_mark_bit(true);

        assert_eq!(cell.get_mark_bit(), true);

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
                assert!(false);
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
                assert!(false);
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
                assert!(false);
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
                assert!(false); // we fail.
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
                assert!(false);
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
                assert!(false);
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
            None => assert!(false),
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
            None => assert!(false),
        }

        match Fixnum::build_with_checked(1 << 56) {
            Ok(_) => assert!(false),
            _ => assert!(true),
        }

        match Fixnum::build_with_checked(i64::MAX) {
            Ok(_) => assert!(false),
            _ => assert!(true),
        }

        match Fixnum::build_with_checked(i64::MIN) {
            Ok(_) => assert!(false),
            _ => assert!(true),
        }

        match Fixnum::build_with_checked(-1) {
            Ok(n) => assert_eq!(n.get_num(), -1),
            _ => assert!(false),
        }

        match Fixnum::build_with_checked((1 << 55) - 1) {
            Ok(n) => assert_eq!(n.get_num(), (1 << 55) - 1),
            _ => assert!(false),
        }

        match Fixnum::build_with_checked(-(1 << 55)) {
            Ok(n) => assert_eq!(n.get_num(), -(1 << 55)),
            _ => assert!(false),
        }

        match Fixnum::build_with_checked(-(1 << 55) - 1) {
            Ok(_n) => assert!(false),
            _ => assert!(true),
        }

        match Fixnum::build_with_checked(-1) {
            Ok(n) => assert_eq!(-n, Fixnum::build_with(1)),
            _ => assert!(false),
        }

        // float

        let float = 3.1415926f64;
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
