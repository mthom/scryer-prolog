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

pub fn header_offset_from_payload<Payload: Sized>() -> usize {
    let payload_offset = mem::offset_of!(TypedAllocSlab<Payload>, payload);
    let slab_offset = mem::offset_of!(TypedAllocSlab<Payload>, slab);
    let header_offset = slab_offset + mem::offset_of!(AllocSlab, header);

    debug_assert!(payload_offset > header_offset);
    payload_offset - header_offset
}

pub fn ptr_to_allocated<Payload: ArenaAllocated>(slab: &mut AllocSlab) -> TypedArenaPtr<Payload> {
    let typed_slab: &mut TypedAllocSlab<Payload> = unsafe { mem::transmute(slab) };
    typed_slab.to_typed_arena_ptr()
}

#[macro_export]
macro_rules! gen_ptr_to_allocated {
    ($payload: ty) => {
        fn ptr_to_allocated(slab: &mut AllocSlab) -> TypedArenaPtr<$payload> {
            ptr_to_allocated::<$payload>(slab)
        }
    };
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
                    block: Rcu::new(RawBlock::new()),
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
pub struct TypedArenaPtr<T: ?Sized>(ptr::NonNull<T>);

impl<T: ?Sized + PartialOrd> PartialOrd for TypedArenaPtr<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for TypedArenaPtr<T> {
    fn eq(&self, other: &TypedArenaPtr<T>) -> bool {
        self.0 == other.0 || **self == **other
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
        (self as &T).hash(hasher)
    }
}

impl<T: ?Sized> Clone for TypedArenaPtr<T> {
    fn clone(&self) -> Self {
        *self
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
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[inline]
    pub const fn new(data: *mut T) -> Self {
        unsafe { TypedArenaPtr(ptr::NonNull::new_unchecked(data)) }
    }

    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

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

pub trait ArenaAllocated: Sized {
    type PtrToAllocated;

    fn tag() -> ArenaHeaderTag;
    fn ptr_to_allocated(slab: &mut AllocSlab) -> Self::PtrToAllocated;

    fn header_offset_from_payload() -> usize {
        header_offset_from_payload::<Self>()
    }

    #[allow(clippy::missing_safety_doc)]
    fn alloc(arena: &mut Arena, value: Self) -> Self::PtrToAllocated {
        let size = mem::size_of::<TypedAllocSlab<Self>>();
        let slab = Box::new(TypedAllocSlab {
            slab: AllocSlab {
                next: arena.base.take(),
                #[cfg(target_pointer_width = "32")]
                _padding: 0,
                header: ArenaHeader::build_with(size as u64, Self::tag()),
            },
            payload: value,
        });

        let mut untyped_slab = unsafe { Box::from_raw(Box::into_raw(slab) as *mut AllocSlab) };
        let allocated_ptr = Self::ptr_to_allocated(untyped_slab.as_mut());

        arena.base = Some(untyped_slab);

        allocated_ptr
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
    type PtrToAllocated = TypedArenaPtr<Integer>;

    gen_ptr_to_allocated!(Integer);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Integer
    }
}

impl ArenaAllocated for Rational {
    type PtrToAllocated = TypedArenaPtr<Rational>;

    gen_ptr_to_allocated!(Rational);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::Rational
    }
}

impl ArenaAllocated for LiveLoadState {
    type PtrToAllocated = TypedArenaPtr<LiveLoadState>;

    gen_ptr_to_allocated!(LiveLoadState);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::LiveLoadState
    }
}

impl ArenaAllocated for TcpListener {
    type PtrToAllocated = TypedArenaPtr<TcpListener>;

    gen_ptr_to_allocated!(TcpListener);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::TcpListener
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpListener {
    type PtrToAllocated = TypedArenaPtr<HttpListener>;

    gen_ptr_to_allocated!(HttpListener);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpListener
    }
}

#[cfg(feature = "http")]
impl ArenaAllocated for HttpResponse {
    type PtrToAllocated = TypedArenaPtr<HttpResponse>;

    gen_ptr_to_allocated!(HttpResponse);

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::HttpResponse
    }
}

impl ArenaAllocated for IndexPtr {
    type PtrToAllocated = TypedArenaPtr<IndexPtr>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::IndexPtrUndefined
    }

    #[inline]
    fn ptr_to_allocated(slab: &mut AllocSlab) -> Self::PtrToAllocated {
        TypedArenaPtr::new(ptr::addr_of_mut!(slab.header) as *mut _)
    }

    #[inline]
    fn header_offset_from_payload() -> usize {
        0
    }

    #[inline]
    fn alloc(arena: &mut Arena, value: Self) -> Self::PtrToAllocated {
        let mut slab = Box::new(AllocSlab {
            next: arena.base.take(),
            #[cfg(target_pointer_width = "32")]
            _padding: 0,
            header: unsafe { mem::transmute(value) },
        });

        let allocated_ptr =
            TypedArenaPtr::new(unsafe { mem::transmute(ptr::addr_of_mut!(slab.header)) });
        arena.base = Some(slab);
        allocated_ptr
    }
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct AllocSlab {
    next: Option<Box<AllocSlab>>,
    #[cfg(target_pointer_width = "32")]
    _padding: u32,
    header: ArenaHeader,
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct TypedAllocSlab<Payload> {
    slab: AllocSlab,
    payload: Payload,
}

impl<Payload: ArenaAllocated> TypedAllocSlab<Payload> {
    #[inline]
    pub fn to_typed_arena_ptr(&mut self) -> TypedArenaPtr<Payload> {
        TypedArenaPtr::new(&mut self.payload as *mut _)
    }
}

#[derive(Debug)]
pub struct Arena {
    base: Option<Box<AllocSlab>>,
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

unsafe fn drop_slab_in_place(value: &mut AllocSlab) {
    macro_rules! drop_typed_slab_in_place {
        ($payload: ty, $value: expr) => {
            let slab: &mut TypedAllocSlab<$payload> = mem::transmute($value);
            ptr::drop_in_place(&mut slab.payload);
        };
    }

    match value.header.tag() {
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
        ArenaHeaderTag::NullStream
        | ArenaHeaderTag::IndexPtrUndefined
        | ArenaHeaderTag::IndexPtrDynamicUndefined
        | ArenaHeaderTag::IndexPtrDynamicIndex
        | ArenaHeaderTag::IndexPtrIndex => {}
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut ptr = self.base.take();

        while let Some(mut slab) = ptr {
            unsafe {
                drop_slab_in_place(&mut slab);
                ptr = slab.next;
            }
        }

        self.base = None;
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
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    #[cfg_attr(miri, ignore = "blocked on arena.rs UB")]
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
