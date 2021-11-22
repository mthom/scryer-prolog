use crate::machine::loader::LiveLoadState;
use crate::machine::machine_indices::*;
use crate::machine::streams::*;
use crate::read::*;

use modular_bitfield::prelude::*;
use ordered_float::OrderedFloat;
use rug::{Integer, Rational};

use std::alloc;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::net::TcpListener;
use std::ops::{Deref, DerefMut};
use std::ptr;

#[macro_export]
macro_rules! arena_alloc {
    ($e:expr, $arena:expr) => {{
        let result = $e;
        #[allow(unused_unsafe)]
        unsafe { $arena.alloc(result) }
    }};
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq)]
#[bits = 7]
pub enum ArenaHeaderTag {
    F64 = 0b01,
    Integer = 0b10,
    Rational = 0b11,
    OssifiedOpDir = 0b0000100,
    LiveLoadState = 0b0001000,
    InactiveLoadState = 0b1011000,
    InputFileStream = 0b10000,
    OutputFileStream = 0b10100,
    NamedTcpStream = 0b011100,
    NamedTlsStream = 0b100000,
    ReadlineStream = 0b110000,
    StaticStringStream = 0b110100,
    ByteStream = 0b111000,
    StandardOutputStream = 0b1100,
    StandardErrorStream = 0b11000,
    NullStream = 0b111100,
    TcpListener = 0b1000000,
    Dropped = 0b1000100,
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

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct TypedArenaPtr<T: ?Sized>(ptr::NonNull<T>);

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

impl<T: ?Sized> TypedArenaPtr<T> {
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
        let mut ptr = self.as_ptr() as *const u8 as usize;
        ptr -= mem::size_of::<*const ArenaHeader>();
        ptr as *const ArenaHeader
    }

    #[inline]
    fn header_ptr_mut(&mut self) -> *mut ArenaHeader {
        let mut ptr = self.as_ptr() as *const u8 as usize;
        ptr -= mem::size_of::<*const ArenaHeader>();
        ptr as *mut ArenaHeader
    }

    #[inline]
    pub fn get_mark_bit(&self) -> bool {
        unsafe { (*self.header_ptr()).m() }
    }

    #[inline]
    pub fn set_tag(&mut self, tag: ArenaHeaderTag) {
        unsafe { (*self.header_ptr_mut()).set_tag(tag); }
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

pub trait ArenaAllocated {
    type PtrToAllocated;

    fn tag() -> ArenaHeaderTag;
    fn size(&self) -> usize;
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated
    where
        Self: Sized;
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct F64Ptr(pub TypedArenaPtr<OrderedFloat<f64>>);

impl fmt::Display for F64Ptr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", *self)
    }
}

impl Deref for F64Ptr {
    type Target = TypedArenaPtr<OrderedFloat<f64>>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for F64Ptr {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl ArenaAllocated for OrderedFloat<f64> {
    type PtrToAllocated = F64Ptr;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::F64
    }

    #[inline]
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }

    #[inline]
    fn copy_to_arena(self, dst: *mut Self) -> Self::PtrToAllocated {
        unsafe {
            ptr::write(dst, self);
            F64Ptr(TypedArenaPtr::new(dst as *mut Self))
        }
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

impl ArenaAllocated for OssifiedOpDir {
    type PtrToAllocated = TypedArenaPtr<OssifiedOpDir>;

    #[inline]
    fn tag() -> ArenaHeaderTag {
        ArenaHeaderTag::OssifiedOpDir
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

#[derive(Clone, Copy, Debug)]
struct AllocSlab {
    next: *mut AllocSlab,
    header: ArenaHeader,
}

#[derive(Debug)]
pub struct Arena(*mut AllocSlab);

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
    #[inline]
    pub fn new() -> Self {
        Arena(ptr::null_mut())
    }

    pub unsafe fn alloc<T: ArenaAllocated>(&mut self, value: T) -> T::PtrToAllocated {
        let size = value.size() + mem::size_of::<AllocSlab>();

        let align = mem::align_of::<AllocSlab>();
        let layout = alloc::Layout::from_size_align_unchecked(size, align);

        let slab = alloc::alloc(layout) as *mut AllocSlab;

        (*slab).next = self.0;
        (*slab).header = ArenaHeader::build_with(value.size() as u64, T::tag());

        let offset = (*slab).payload_offset();
        let result = value.copy_to_arena(offset as *mut T);

        self.0 = slab;

        result
    }
}

unsafe fn drop_slab_in_place(value: &mut AllocSlab) {
    match value.header.tag() {
        ArenaHeaderTag::Integer => {
            ptr::drop_in_place(value.payload_offset() as *mut Integer);
        }
        ArenaHeaderTag::Rational => {
            ptr::drop_in_place(value.payload_offset() as *mut Rational);
        }
        ArenaHeaderTag::InputFileStream => {
            ptr::drop_in_place(value.payload_offset() as *mut InputFileStream);
        }
        ArenaHeaderTag::OutputFileStream => {
            ptr::drop_in_place(value.payload_offset() as *mut OutputFileStream);
        }
        ArenaHeaderTag::NamedTcpStream => {
            ptr::drop_in_place(value.payload_offset() as *mut NamedTcpStream);
        }
        ArenaHeaderTag::NamedTlsStream => {
            ptr::drop_in_place(value.payload_offset() as *mut NamedTlsStream);
        }
        // ArenaHeaderTag::PausedPrologStream => {
        //     // idea: PausedPrologStream with only the buffer of unread characters.
        //     // no stream to be wrapped, no nuttin'.
        //     ptr::drop_in_place(value.payload_offset() as *mut PausedPrologStream);
        // }
        ArenaHeaderTag::ReadlineStream => {
            ptr::drop_in_place(value.payload_offset() as *mut ReadlineStream);
        }
        ArenaHeaderTag::StaticStringStream => {
            ptr::drop_in_place(value.payload_offset() as *mut StaticStringStream);
        }
        ArenaHeaderTag::ByteStream => {
            ptr::drop_in_place(value.payload_offset() as *mut ByteStream);
        }
        ArenaHeaderTag::OssifiedOpDir => {
            ptr::drop_in_place(
                mem::transmute::<_, *mut OssifiedOpDir>(value.payload_offset())
            );
        }
        ArenaHeaderTag::LiveLoadState | ArenaHeaderTag::InactiveLoadState => {
            ptr::drop_in_place(
                mem::transmute::<_, *mut LiveLoadState>(value.payload_offset())
            );
        }
        ArenaHeaderTag::Dropped => {
        }
        ArenaHeaderTag::TcpListener => {
            ptr::drop_in_place(value.payload_offset() as *mut TcpListener);
        }
        ArenaHeaderTag::F64 | ArenaHeaderTag::StandardOutputStream |
        ArenaHeaderTag::StandardErrorStream | ArenaHeaderTag::NullStream => {
        }
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut ptr = self.0;

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

        self.0 = ptr::null_mut();
    }
}

const_assert!(mem::size_of::<AllocSlab>() == 16);

impl AllocSlab {
    #[inline]
    fn slab_size(&self) -> usize {
        self.header.size() as usize + mem::size_of::<AllocSlab>()
    }

    fn payload_offset(&self) -> *const u8 {
        let mut ptr = (self as *const AllocSlab) as usize;
        ptr += mem::size_of::<AllocSlab>();
        ptr as *const u8
    }
}

const_assert!(mem::size_of::<OrderedFloat<f64>>() == 8);

#[cfg(test)]
mod tests {
    use crate::machine::mock_wam::*;
    use crate::machine::partial_string::*;

    use ordered_float::OrderedFloat;
    use rug::{Integer, Rational};

    #[test]
    fn float_ptr_cast() {
        let mut wam = MockWAM::new();

        let f = OrderedFloat(0f64);
        let mut fp = arena_alloc!(f, &mut wam.machine_st.arena);
        let cell = HeapCellValue::from(fp);

        assert_eq!(cell.get_tag(), HeapCellValueTag::F64);
        assert_eq!(fp.get_mark_bit(), false);
        assert_eq!(**fp, f);

        fp.mark();

        assert_eq!(fp.get_mark_bit(), true);

        read_heap_cell!(cell,
            (HeapCellValueTag::F64, ptr) => {
                assert_eq!(**ptr, f)
            }
            _ => { unreachable!() }
        );
    }

    #[test]
    fn heap_cell_value_const_cast() {
        let mut wam = MockWAM::new();
        let const_value = HeapCellValue::from(ConsPtr::build_with(
            0x0000_5555_ff00_0431 as *const _,
            ConsPtrMaskTag::Cons,
        ));

        match const_value.to_untyped_arena_ptr() {
            Some(arena_ptr) => {
                assert_eq!(arena_ptr.into_bytes(), const_value.into_bytes());
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
                assert_eq!(arena_ptr.into_bytes(), stream_cell.into_bytes());
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

        let big_int = 2 * Integer::from(1u64 << 63);
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

        let big_rat = 2 * Rational::from(1u64 << 63);
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
                     assert_eq!(&*n, &(2 * Rational::from(1u64 << 63)));
                 }
                 _ => unreachable!()
              )
          }
          _ => { unreachable!() }
        );

        // atom

        let f_atom = atom!("f");
        let g_atom = atom!("g");

        assert_eq!(f_atom.as_str(), "f");
        assert_eq!(g_atom.as_str(), "g");

        let f_atom_cell = atom_as_cell!(f_atom);
        let g_atom_cell = atom_as_cell!(g_atom);

        assert_eq!(f_atom_cell.get_tag(), HeapCellValueTag::Atom);

        match f_atom_cell.to_atom() {
            Some(atom) => {
                assert_eq!(f_atom, atom);
                assert_eq!(atom.as_str(), "f");
            }
            None => {
                assert!(false);
            }
        }

        read_heap_cell!(f_atom_cell,
            (HeapCellValueTag::Atom, (atom, arity)) => {
                assert_eq!(f_atom, atom);
                assert_eq!(arity, 0);
                assert_eq!(atom.as_str(), "f");
            }
            _ => { unreachable!() }
        );

        read_heap_cell!(g_atom_cell,
            (HeapCellValueTag::Atom, (atom, arity)) => {
                assert_eq!(g_atom, atom);
                assert_eq!(arity, 0);
                assert_eq!(atom.as_str(), "g");
            }
            _ => { unreachable!() }
        );

        // complete string

        let pstr_var_cell = put_partial_string(&mut wam.machine_st.heap, "ronan", &mut wam.machine_st.atom_tbl);
        let pstr_cell = wam.machine_st.heap[pstr_var_cell.get_value() as usize];

        assert_eq!(pstr_cell.get_tag(), HeapCellValueTag::PStr);

        match pstr_cell.to_pstr() {
            Some(pstr) => {
                assert_eq!(pstr.as_str_from(0), "ronan");
            }
            None => {
                assert!(false);
            }
        }

        read_heap_cell!(pstr_cell,
            (HeapCellValueTag::PStr, pstr_atom) => {
                let pstr = PartialString::from(pstr_atom);
                assert_eq!(pstr.as_str_from(0), "ronan");
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

        let fixnum_b_cell = fixnum_as_cell!(Fixnum::build_with(1 << 55));

        assert_eq!(fixnum_b_cell.get_tag(), HeapCellValueTag::Fixnum);

        match fixnum_b_cell.to_fixnum() {
            Some(n) => assert_eq!(n.get_num(), 1 << 55),
            None => assert!(false),
        }

        match Fixnum::build_with_checked(1 << 57) {
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

        match Fixnum::build_with_checked((1 << 56) - 1) {
            Ok(n) => assert_eq!(n.get_num(), (1 << 56) - 1),
            _ => assert!(false),
        }

        match Fixnum::build_with_checked(-(1 << 56)) {
            Ok(n) => assert_eq!(n.get_num(), -(1 << 56)),
            _ => assert!(false),
        }

        match Fixnum::build_with_checked(-(1 << 56) - 1) {
            Ok(_n) => assert!(false),
            _ => assert!(true),
        }

        match Fixnum::build_with_checked(-1) {
            Ok(n) => assert_eq!(-n, Fixnum::build_with(1)),
            _ => assert!(false),
        }

        // float

        let float = OrderedFloat(3.1415926f64);
        let float_ptr = arena_alloc!(float, &mut wam.machine_st.arena);

        assert!(!float_ptr.as_ptr().is_null());

        let float_cell = typed_arena_ptr_as_cell!(float_ptr);
        assert_eq!(cell.get_tag(), HeapCellValueTag::Cons);

        match float_cell.to_untyped_arena_ptr() {
            Some(untyped_arena_ptr) => {
                assert_eq!(Some(float_ptr.header_ptr()), Some(untyped_arena_ptr.into()),);
            }
            None => {
                assert!(false); // we fail.
            }
        }

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
                assert_eq!(el.flat_index() as usize, empty_list_as_cell!().get_value());
                assert_eq!(el.as_str(), "[]");
            }
            _ => { unreachable!() }
        );
    }
}
