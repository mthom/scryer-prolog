#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

#[cfg(feature = "http")]
use crate::http::{HttpListener, HttpResponse};
use crate::machine::loader::LiveLoadState;
use crate::machine::streams::*;
use crate::offset_table::*;
use crate::read::*;
use crate::types::UntypedArenaPtr;

use crate::parser::dashu::{Integer, Rational};
use ordered_float::OrderedFloat;

use std::fmt;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::io::PipeReader;
use std::io::PipeWriter;
use std::mem;
use std::mem::ManuallyDrop;
use std::net::TcpListener;
use std::ops::{Deref, DerefMut};
use std::process::Child;
use std::ptr;
use std::ptr::addr_of_mut;
use std::ptr::NonNull;

macro_rules! arena_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        $crate::arena::AllocateInArena::arena_allocate(result, $arena)
    }};
}

macro_rules! float_alloc {
    ($e:expr, $arena:expr) => {{
        $arena.f64_tbl.build_with(OrderedFloat($e))
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
    CallbackStream = 0b111001,
    InputChannelStream = 0b111010,
    StandardOutputStream = 0b1100,
    StandardErrorStream = 0b11000,
    NullStream = 0b111100,
    TcpListener = 0b1000000,
    HttpListener = 0b1000001,
    HttpResponse = 0b1000010,
    PipeWriter = 0b1000011,
    Dropped = 0b1000100,
    PipeReader = 0b1001001,
    ChildProcess = 0b1001010,
}

#[bitfield]
#[repr(align(8))]
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
    #[inline]
    pub fn as_ptr(&self) -> *mut T::Payload {
        self.0.as_ptr()
    }
}

impl<P, T: ?Sized + ArenaAllocated<Payload = ManuallyDrop<P>>> TypedArenaPtr<T> {
    pub fn drop_payload(&mut self) {
        if self.get_tag() != ArenaHeaderTag::Dropped {
            self.set_tag(ArenaHeaderTag::Dropped);
            unsafe { ManuallyDrop::drop(&mut *self.as_ptr()) }
        }
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

/* this isn't allowed due to https://github.com/rust-lang/rust/issues/20400 I think,
   though P == ManuallyDrop<P> might also be a problem event though that shouldn't be possible
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
    /// - the pointer must be non-null
    unsafe fn typed_ptr(ptr: UntypedArenaPtr) -> TypedArenaPtr<Self>
    where
        Self::Payload: Sized,
    {
        TypedArenaPtr(NonNull::new_unchecked(
            ptr.payload_offset().cast_mut().cast::<Self::Payload>(),
        ))
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
                header: ArenaHeader::build_with(size as u64, Self::tag()),
            },
            payload: value,
        });

        let (allocated_ptr, untyped_slab) = slab.to_untyped();

        arena.base = Some(untyped_slab);

        allocated_ptr
    }

    /// # Safety
    /// - ptr points to an allocated slab of the correct kind
    unsafe fn dealloc(ptr: NonNull<TypedAllocSlab<Self>>) {
        drop(unsafe { Box::from_raw(ptr.as_ptr()) });
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

impl AllocateInArena<LiveLoadState> for LiveLoadState {
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<LiveLoadState> {
        LiveLoadState::alloc(arena, ManuallyDrop::new(self))
    }
}

impl ArenaAllocated for LiveLoadState {
    type Payload = ManuallyDrop<Self>;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::LiveLoadState
    }

    unsafe fn dealloc(ptr: NonNull<TypedAllocSlab<Self>>) {
        let mut slab = unsafe { Box::from_raw(ptr.as_ptr()) };

        match slab.tag() {
            ArenaHeaderTag::LiveLoadState | ArenaHeaderTag::InactiveLoadState => {
                unsafe { ManuallyDrop::drop(&mut slab.payload) };
            }
            ArenaHeaderTag::Dropped => {}
            _ => {
                unreachable!()
            }
        }
        drop(slab);
    }
}

impl AllocateInArena<TcpListener> for TcpListener {
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<TcpListener> {
        TcpListener::alloc(arena, ManuallyDrop::new(self))
    }
}

impl ArenaAllocated for TcpListener {
    type Payload = ManuallyDrop<Self>;
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

impl ArenaAllocated for Child {
    type Payload = ManuallyDrop<Self>;
    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::ChildProcess
    }
}
impl AllocateInArena<Child> for Child {
    fn arena_allocate(self, arena: &mut Arena) -> TypedArenaPtr<Child> {
        Child::alloc(arena, ManuallyDrop::new(self))
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct AllocSlab {
    next: Option<UntypedArenaSlab>,
    header: ArenaHeader,
}

const _: () = {
    if std::mem::align_of::<AllocSlab>() < std::mem::align_of::<*const ()>() {
        panic!("alignment of AllocSlab is too low");
    }

    if std::mem::offset_of!(AllocSlab, header) % std::mem::align_of::<*const ()>() != 0 {
        panic!("alignment of header not a multiple of pointers alignment");
    }
};

#[repr(C)]
#[derive(Debug)]
pub struct TypedAllocSlab<T: ?Sized + ArenaAllocated> {
    slab: AllocSlab,
    payload: T::Payload,
}

impl<T: ?Sized + ArenaAllocated> TypedAllocSlab<T> {
    pub fn tag(&self) -> ArenaHeaderTag {
        self.slab.header.tag()
    }

    pub fn payload(&mut self) -> &mut T::Payload {
        &mut self.payload
    }

    #[inline]
    pub fn to_untyped(self: Box<Self>) -> (TypedArenaPtr<T>, UntypedArenaSlab) {
        let raw_box = Box::into_raw(self);

        // safety: the pointer from Box::into_raw fullfills addr_of_mut's saftey requirements
        let payload_ptr = unsafe { addr_of_mut!((*raw_box).payload) };

        (
            TypedArenaPtr(unsafe {
                // safety: the pointer points into a valid allocation so it is non null
                ptr::NonNull::new_unchecked(payload_ptr)
            }),
            UntypedArenaSlab {
                // safety: pointer from Box::into_raw is never null
                slab: unsafe { NonNull::new_unchecked(raw_box.cast::<AllocSlab>()) },
                tag: T::tag(),
            },
        )
    }
}

#[derive(Debug)]
pub struct UntypedArenaSlab {
    slab: NonNull<AllocSlab>,
    tag: ArenaHeaderTag,
}

impl Drop for UntypedArenaSlab {
    fn drop(&mut self) {
        unsafe { drop_slab_in_place(self.slab, self.tag) };
    }
}

#[derive(Debug)]
pub struct Arena {
    base: Option<UntypedArenaSlab>,
    pub f64_tbl: F64Table,
    pub code_index_tbl: CodeIndexTable,
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
            code_index_tbl: CodeIndexTable::new(),
        }
    }
}

unsafe fn drop_slab_in_place(value: NonNull<AllocSlab>, tag: ArenaHeaderTag) {
    macro_rules! drop_typed_slab_in_place {
        ($payload: ty, $value: expr) => {
            <$payload as ArenaAllocated>::dealloc($value.cast::<TypedAllocSlab<$payload>>())
        };
    }

    match tag {
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
        ArenaHeaderTag::CallbackStream => {
            drop_typed_slab_in_place!(CallbackStream, value);
        }
        ArenaHeaderTag::InputChannelStream => {
            drop_typed_slab_in_place!(InputChannelStream, value);
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
        ArenaHeaderTag::PipeReader => {
            drop_typed_slab_in_place!(PipeReader, value);
        }
        ArenaHeaderTag::PipeWriter => {
            drop_typed_slab_in_place!(PipeWriter, value);
        }
        ArenaHeaderTag::ChildProcess => {
            drop_typed_slab_in_place!(Child, value);
        }
        ArenaHeaderTag::NullStream => {
            unreachable!("NullStream is never arena allocated!");
        }
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        // we un-nest UntypedArenaSlab to prevent stackoverflow due to the recursive drop

        let mut ptr = self.base.take();

        while let Some(mut slab) = ptr {
            ptr = unsafe { slab.slab.as_mut() }.next.take();
            drop(slab);
        }
    }
}

const_assert!(mem::size_of::<AllocSlab>() <= 24);
const_assert!(mem::size_of::<OrderedFloat<f64>>() == 8);

#[cfg(test)]
mod tests {
    use crate::arena::*;
    use crate::atom_table::*;
    use crate::machine::mock_wam::*;
    use crate::types::*;

    use crate::parser::dashu::{Integer, Rational};
    use ordered_float::OrderedFloat;

    #[test]
    fn float_ptr_cast() {
        let mut wam = MockWAM::new();

        let f = 0f64;
        let fp = float_alloc!(f, wam.machine_st.arena);
        let mut cell = HeapCellValue::from(fp);

        assert_eq!(cell.get_tag(), HeapCellValueTag::F64Offset);
        assert!(!cell.get_mark_bit());
        assert_eq!(wam.machine_st.arena.f64_tbl.get_entry(fp), OrderedFloat(f));

        cell.set_mark_bit(true);

        assert!(cell.get_mark_bit());

        read_heap_cell!(cell,
            (HeapCellValueTag::F64Offset, offset) => {
                let fp = wam.machine_st.arena.f64_tbl.get_entry(offset);
                assert_eq!(fp, OrderedFloat(0f64))
            }
            _ => { unreachable!() }
        );
    }

    #[test]
    fn heap_cell_value_const_cast() {
        let mut wam = MockWAM::new();
        #[cfg(target_pointer_width = "32")]
        let const_value = HeapCellValue::from(ConsPtr::build_with(
            std::ptr::without_provenance(0x0000_0431),
            ConsPtrMaskTag::Cons,
        ));
        #[cfg(target_pointer_width = "64")]
        let const_value = HeapCellValue::from(ConsPtr::build_with(
            std::ptr::without_provenance(0x0000_5555_ff00_0431),
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

        let cell = HeapCellValue::from(big_int_ptr);
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

        let fixnum_b_cell = fixnum_as_cell!(
            Fixnum::build_with_checked(1i64 << 54).expect("1 << 54 fits in Fixnum")
        );

        assert_eq!(fixnum_b_cell.get_tag(), HeapCellValueTag::Fixnum);

        match fixnum_b_cell.to_fixnum() {
            Some(n) => assert_eq!(n.get_num(), 1 << 54),
            None => unreachable!(),
        }

        Fixnum::build_with_checked(1i64 << 56).expect_err("1 << 56 is too large for fixnum");

        Fixnum::build_with_checked(i64::MAX).expect_err("i64::MAX is too large for Fixnum");
        Fixnum::build_with_checked(i64::MIN).expect_err("i64::MIN is too small for Fixnum");
        assert_eq!(
            Fixnum::build_with_checked(-1i64)
                .expect("-1 fits in fixnum")
                .get_num(),
            -1
        );

        Fixnum::build_with_checked((1i64 << 55) - 1)
            .expect("(1 << 55) - 1 is the largest value that fits in Fixnum");

        Fixnum::build_with_checked(-(1i64 << 55))
            .expect("-(1 << 55) is the smallest value that fits in fixnum");
        Fixnum::build_with_checked(-(1i64 << 55) - 1)
            .expect_err("-(1<<55) - 1 is too small for Fixnum");

        assert_eq!(
            -Fixnum::build_with_checked(-1i64).expect("-1 fits in Fixnum"),
            Fixnum::build_with(1)
        );

        // float

        let float = std::f64::consts::PI;
        let float_ptr = float_alloc!(float, wam.machine_st.arena);
        let cell = HeapCellValue::from(float_ptr);

        assert_eq!(cell.get_tag(), HeapCellValueTag::F64Offset);

        // char

        let c = 'c';
        let char_cell = char_as_cell!(c);

        read_heap_cell!(char_cell,
            (HeapCellValueTag::Atom, (c, _arity)) => {
                assert_eq!(&*c.as_str(), "c");
            }
            _ => { unreachable!() }
        );

        let c = 'Ћ';
        let cyrillic_char_cell = char_as_cell!(c);

        read_heap_cell!(cyrillic_char_cell,
            (HeapCellValueTag::Atom, (c, _arity)) => {
                assert_eq!(&*c.as_str(), "Ћ");
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
