#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::heap::*;
use crate::machine::machine_indices::*;
use crate::machine::streams::*;
use crate::offset_table::*;
use crate::parser::ast::Fixnum;
use crate::parser::ast::Literal;

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use std::ops::{Add, Sub, SubAssign};

use dashu::{Integer, Rational};

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
#[bits = 6]
pub enum HeapCellValueTag {
    Str = 0b000001,
    Lis = 0b000101,
    Var = 0b001011,
    StackVar = 0b001101,
    AttrVar = 0b010001,
    PStrLoc = 0b010011,
    // constants.
    Cons = 0b0,
    F64Offset = 0b010101,
    Fixnum = 0b011001,
    CodeIndexOffset = 0b011011,
    Atom = 0b011111,
    CutPoint = 0b011101,
    // trail elements.
    TrailedHeapVar = 0b100001,
    TrailedStackVar = 0b100011,
    TrailedAttrVar = 0b100101,
    TrailedAttrVarListLink = 0b101001,
    TrailedAttachedValue = 0b101011,
    TrailedBlackboardEntry = 0b101101,
    TrailedBlackboardOffset = 0b110001,
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
#[bits = 6]
pub enum HeapCellValueView {
    Str = 0b000001,
    Lis = 0b000101,
    Var = 0b001011,
    StackVar = 0b001101,
    AttrVar = 0b010001,
    PStrLoc = 0b010011,
    // constants.
    Cons = 0b0,
    F64Offset = 0b010101,
    Fixnum = 0b011001,
    CodeIndexOffset = 0b011011,
    Atom = 0b011111,
    CutPoint = 0b011101,
    // trail elements.
    TrailedHeapVar = 0b100001,
    TrailedStackVar = 0b100011,
    TrailedAttrVar = 0b100101,
    TrailedAttrVarListLink = 0b101001,
    TrailedAttachedValue = 0b101011,
    TrailedBlackboardEntry = 0b101101,
    TrailedBlackboardOffset = 0b110001,
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 1]
pub enum ConsPtrMaskTag {
    Cons = 0b0,
    Atom = 0b1,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug)]
pub struct ConsPtr {
    ptr: B61,
    f: bool,
    m: bool,
    tag: ConsPtrMaskTag,
}

impl ConsPtr {
    #[inline(always)]
    pub fn build_with(ptr: *const ArenaHeader, tag: ConsPtrMaskTag) -> Self {
        ConsPtr::new()
            .with_ptr(ptr.expose_provenance() as u64)
            .with_f(false)
            .with_m(false)
            .with_tag(tag)
    }

    #[inline(always)]
    pub fn as_ptr(self) -> *mut u8 {
        let addr: u64 = self.ptr();
        std::ptr::with_exposed_provenance_mut(addr as usize)
    }

    #[inline(always)]
    pub fn get_tag(self) -> ConsPtrMaskTag {
        self.tag()
    }
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug)]
#[bits = 6]
pub(crate) enum RefTag {
    HeapCell = 0b001011,
    StackCell = 0b001101,
    AttrVar = 0b010001,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Ref {
    val: B56,
    #[allow(unused)]
    f: bool,
    #[allow(unused)]
    m: bool,
    tag: RefTag,
}

impl Ord for Ref {
    fn cmp(&self, rhs: &Ref) -> Ordering {
        match self.get_tag() {
            RefTag::HeapCell | RefTag::AttrVar => match rhs.get_tag() {
                RefTag::StackCell => Ordering::Less,
                _ => self.get_value().cmp(&rhs.get_value()),
            },
            RefTag::StackCell => match rhs.get_tag() {
                RefTag::StackCell => self.get_value().cmp(&rhs.get_value()),
                _ => Ordering::Greater,
            },
        }
    }
}

impl PartialOrd for Ref {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl Ref {
    #[inline(always)]
    pub(crate) fn build_with(tag: RefTag, value: u64) -> Self {
        Ref::new().with_tag(tag).with_val(value)
    }

    #[inline(always)]
    pub(crate) fn get_tag(self) -> RefTag {
        self.tag()
    }

    #[inline(always)]
    pub(crate) fn get_value(self) -> u64 {
        self.val()
    }

    #[inline(always)]
    pub(crate) fn as_heap_cell_value(self) -> HeapCellValue {
        HeapCellValue::from_bytes(self.into_bytes())
    }

    #[inline(always)]
    pub(crate) fn heap_cell(h: usize) -> Self {
        Ref::build_with(RefTag::HeapCell, h as u64)
    }

    #[inline(always)]
    pub(crate) fn stack_cell(h: usize) -> Self {
        Ref::build_with(RefTag::StackCell, h as u64)
    }

    #[inline(always)]
    pub(crate) fn attr_var(h: usize) -> Self {
        Ref::build_with(RefTag::AttrVar, h as u64)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TrailRef {
    Ref(Ref),
    AttrVarListLink(usize, usize),
    BlackboardEntry(Atom),
    BlackboardOffset(Atom, HeapCellValue), // key atom, key value
}

#[allow(clippy::enum_variant_names)] // allow the common "Trailed" prefix
#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 6]
pub(crate) enum TrailEntryTag {
    TrailedHeapVar = 0b101111,
    TrailedStackVar = 0b101011,
    TrailedAttrVar = 0b100001,
    TrailedAttrVarListLink = 0b100011,
    TrailedAttachedValue = 0b100101,
    TrailedBlackboardEntry = 0b100111,
    TrailedBlackboardOffset = 0b110011,
}

#[bitfield]
#[derive(Copy, Clone, Debug)]
#[repr(u64)]
pub(crate) struct TrailEntry {
    val: B56,
    #[allow(unused)]
    f: bool,
    #[allow(unused)]
    m: bool,
    #[allow(unused)]
    tag: TrailEntryTag,
}

impl TrailEntry {
    #[inline(always)]
    pub(crate) fn build_with(tag: TrailEntryTag, value: u64) -> Self {
        TrailEntry::new()
            .with_tag(tag)
            .with_m(false)
            .with_f(false)
            .with_val(value)
    }

    #[inline(always)]
    pub(crate) fn get_tag(self) -> TrailEntryTag {
        match self.tag_or_err() {
            Ok(tag) => tag,
            Err(_) => TrailEntryTag::TrailedAttachedValue,
        }
    }

    #[inline]
    pub(crate) fn get_value(self) -> u64 {
        self.val()
    }
}

#[repr(u64)]
#[bitfield]
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub struct HeapCellValue {
    val: B56,
    f: bool,
    m: bool,
    #[allow(dead_code)]
    tag: HeapCellValueTag,
}

impl fmt::Debug for HeapCellValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self.get_tag() {
            HeapCellValueTag::F64Offset => f
                .debug_struct("HeapCellValue")
                .field("tag", &HeapCellValueTag::F64Offset)
                .field("offset", &self.get_value())
                .field("m", &self.m())
                .field("f", &self.f())
                .finish(),
            HeapCellValueTag::Cons => {
                let cons_ptr = ConsPtr::from_bytes(self.into_bytes());

                f.debug_struct("HeapCellValue")
                    .field("tag", &HeapCellValueTag::Cons)
                    .field("ptr", &cons_ptr.ptr())
                    .field("m", &cons_ptr.m())
                    .field("f", &cons_ptr.f())
                    .finish()
            }
            HeapCellValueTag::Atom => {
                let (name, arity) = cell_as_atom_cell!(self).get_name_and_arity();

                f.debug_struct("HeapCellValue")
                    .field("tag", &HeapCellValueTag::Atom)
                    .field("name", &name.as_str())
                    .field("arity", &arity)
                    .field("m", &self.m())
                    .field("f", &self.f())
                    .finish()
            }
            tag => f
                .debug_struct("HeapCellValue")
                .field("tag", &tag)
                .field("value", &self.get_value())
                .field("m", &self.get_mark_bit())
                .field("f", &self.get_forwarding_bit())
                .finish(),
        }
    }
}

impl From<Literal> for HeapCellValue {
    #[inline]
    fn from(literal: Literal) -> Self {
        match literal {
            Literal::Atom(name) => atom_as_cell!(name),
            Literal::CodeIndexOffset(idx) => HeapCellValue::from(idx),
            Literal::Fixnum(n) => fixnum_as_cell!(n),
            Literal::Integer(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::Rational(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::F64(offset, _n) => HeapCellValue::from(offset),
        }
    }
}

impl TryFrom<(HeapCellValue, &'_ F64Table)> for Literal {
    type Error = ();

    fn try_from((value, f64_tbl): (HeapCellValue, &F64Table)) -> Result<Literal, ()> {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    Ok(Literal::Atom(name))
                } else {
                    Err(())
                }
            }
            (HeapCellValueTag::Fixnum, n) => {
                Ok(Literal::Fixnum(n))
            }
            (HeapCellValueTag::F64Offset, offset) => {
                Ok(Literal::F64(offset, f64_tbl.get_entry(offset)))
            }
            (HeapCellValueTag::CodeIndexOffset, idx) => {
                Ok(Literal::CodeIndexOffset(idx))
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::Integer, n) => {
                         Ok(Literal::Integer(n))
                     }
                     (ArenaHeaderTag::Rational, n) => {
                         Ok(Literal::Rational(n))
                     }
                     _ => {
                         Err(())
                     }
                )
            }
            _ => {
                Err(())
            }
        )
    }
}

impl<T: ArenaAllocated> From<TypedArenaPtr<T>> for HeapCellValue
where
    T::Payload: Sized,
{
    #[inline]
    fn from(arena_ptr: TypedArenaPtr<T>) -> HeapCellValue {
        HeapCellValue::from(arena_ptr.header_ptr().expose_provenance() as u64)
    }
}

impl From<F64Offset> for HeapCellValue {
    #[inline]
    fn from(f64_offset: F64Offset) -> HeapCellValue {
        HeapCellValue::build_with(HeapCellValueTag::F64Offset, f64_offset.to_u64())
    }
}

impl From<CodeIndexOffset> for HeapCellValue {
    #[inline]
    fn from(code_index_offset: CodeIndexOffset) -> HeapCellValue {
        HeapCellValue::build_with(
            HeapCellValueTag::CodeIndexOffset,
            code_index_offset.to_u64(),
        )
    }
}

impl From<ConsPtr> for HeapCellValue {
    #[inline(always)]
    fn from(cons_ptr: ConsPtr) -> HeapCellValue {
        HeapCellValue::from_bytes(
            ConsPtr::from(cons_ptr.as_ptr().expose_provenance() as u64)
                .with_tag(ConsPtrMaskTag::Cons)
                .with_m(false)
                .into_bytes(),
        )
    }
}

impl From<(Number, &mut Arena)> for HeapCellValue {
    #[inline(always)]
    fn from((n, arena): (Number, &mut Arena)) -> HeapCellValue {
        use ordered_float::OrderedFloat;

        match n {
            Number::Float(OrderedFloat(n)) => HeapCellValue::from(float_alloc!(n, arena)),
            Number::Integer(n) => HeapCellValue::from(n),
            Number::Rational(n) => HeapCellValue::from(n),
            Number::Fixnum(n) => fixnum_as_cell!(n),
        }
    }
}

impl HeapCellValue {
    #[inline(always)]
    pub fn build_with(tag: HeapCellValueTag, value: u64) -> Self {
        HeapCellValue::new()
            .with_tag(tag)
            .with_val(value)
            .with_m(false)
            .with_f(false)
    }

    #[inline]
    pub fn is_string_terminator(mut self, heap: &impl SizedHeap) -> bool {
        loop {
            return read_heap_cell!(self,
                (HeapCellValueTag::Atom, (name, arity)) => {
                    name == atom!("[]") && arity == 0
                }
                (HeapCellValueTag::PStrLoc, h) => {
                    let HeapStringScan { tail_idx, .. } = heap.scan_slice_to_str(h);
                    self = heap[tail_idx];
                    continue;
                }
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                    let cell = heap_bound_store(heap, heap_bound_deref(heap, heap[h]));

                    if cell.is_var() {
                        return false;
                    }

                    self = cell;
                    continue;
                }
                _ => {
                    false
                }
            );
        }
    }

    #[inline]
    pub fn is_ref(self) -> bool {
        matches!(
            self.get_tag(),
            HeapCellValueTag::Str
                | HeapCellValueTag::Lis
                | HeapCellValueTag::Var
                | HeapCellValueTag::StackVar
                | HeapCellValueTag::AttrVar
                | HeapCellValueTag::PStrLoc
        )
    }

    #[inline]
    pub fn as_char(self) -> Option<char> {
        read_heap_cell!(self,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity > 0 {
                    return None;
                }

                name.as_char()
            }
            _ => {
                None
            }
        )
    }

    #[inline]
    pub fn is_constant(self) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Cons
            | HeapCellValueTag::F64Offset
            | HeapCellValueTag::Fixnum
            | HeapCellValueTag::CutPoint => true,
            HeapCellValueTag::Atom => cell_as_atom_cell!(self).get_arity() == 0,
            _ => false,
        }
    }

    #[inline(always)]
    pub fn is_stack_var(self) -> bool {
        self.get_tag() == HeapCellValueTag::StackVar
    }

    #[inline]
    pub fn is_compound(self, heap: &Heap) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Str => {
                cell_as_atom_cell!(heap[self.get_value() as usize]).get_arity() > 0
            }
            HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc => true,
            HeapCellValueTag::Atom => cell_as_atom_cell!(self).get_arity() > 0,
            _ => false,
        }
    }

    #[inline]
    pub fn is_var(self) -> bool {
        read_heap_cell!(self,
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                true
            }
            _ => {
                false
            }
        )
    }

    #[inline]
    pub(crate) fn as_var(self) -> Option<Ref> {
        read_heap_cell!(self,
            (HeapCellValueTag::Var, h) => {
                Some(Ref::heap_cell(h))
            }
            (HeapCellValueTag::AttrVar, h) => {
                Some(Ref::attr_var(h))
            }
            (HeapCellValueTag::StackVar, s) => {
                Some(Ref::stack_cell(s))
            }
            _ => {
                None
            }
        )
    }

    #[inline]
    pub fn get_value(self) -> u64 {
        self.val()
    }

    #[inline]
    pub fn set_value(&mut self, val: u64) {
        self.set_val(val);
    }

    #[inline]
    pub fn get_tag(self) -> HeapCellValueTag {
        match self.tag_or_err() {
            Ok(tag) => tag,
            Err(_) => match ConsPtr::from_bytes(self.into_bytes()).tag() {
                ConsPtrMaskTag::Atom => HeapCellValueTag::Atom,
                ConsPtrMaskTag::Cons => HeapCellValueTag::Cons,
            },
        }
    }

    #[inline]
    pub fn to_atom(self) -> Option<Atom> {
        match self.get_tag() {
            HeapCellValueTag::Atom => Some(AtomCell::from_bytes(self.into_bytes()).get_name()),
            _ => None,
        }
    }

    #[inline]
    pub fn to_fixnum(self) -> Option<Fixnum> {
        match self.get_tag() {
            HeapCellValueTag::Fixnum => Some(Fixnum::from_bytes(self.into_bytes())),
            _ => None,
        }
    }

    // FIXME: someone that knows this better should check if this can be split into `to_fixnum_unchecked` and `to_cut_point_unchecked` assuming thats always unambigusly knowable
    #[inline]
    pub unsafe fn to_fixnum_or_cut_point_unchecked(self) -> Fixnum {
        debug_assert!(matches!(
            self.get_tag(),
            HeapCellValueTag::Fixnum | HeapCellValueTag::CutPoint
        ));
        Fixnum::from_bytes(self.into_bytes())
    }

    #[inline]
    pub fn from_ptr_addr(ptr_bytes: usize) -> Self {
        HeapCellValue::from_bytes((ptr_bytes as u64).to_ne_bytes())
    }

    pub fn to_ptr_addr(self) -> usize {
        u64::from_ne_bytes(self.into_bytes()) as usize
    }

    #[inline]
    pub fn to_untyped_arena_ptr_bytes(self) -> [u8; 8] {
        self.into_bytes()
    }

    #[inline]
    pub fn to_untyped_arena_ptr(self) -> Option<UntypedArenaPtr> {
        match self.get_tag() {
            HeapCellValueTag::Cons => Some(UntypedArenaPtr::from_bytes(
                self.to_untyped_arena_ptr_bytes(),
            )),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn get_forwarding_bit(self) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Cons => ConsPtr::from_bytes(self.into_bytes()).f(),
            _ => self.f(),
        }
    }

    #[inline(always)]
    pub fn set_forwarding_bit(&mut self, f: bool) {
        match self.get_tag() {
            HeapCellValueTag::Cons => {
                let value = ConsPtr::from_bytes(self.into_bytes()).with_f(f);
                *self = HeapCellValue::from_bytes(value.into_bytes());
            }
            _ => self.set_f(f),
        }
    }

    #[inline(always)]
    pub fn get_mark_bit(self) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Cons => ConsPtr::from_bytes(self.into_bytes()).m(),
            _ => self.m(),
        }
    }

    #[inline(always)]
    pub fn set_mark_bit(&mut self, m: bool) {
        match self.get_tag() {
            HeapCellValueTag::Cons => {
                let value = ConsPtr::from_bytes(self.into_bytes()).with_m(m);
                *self = HeapCellValue::from_bytes(value.into_bytes());
            }
            _ => self.set_m(m),
        }
    }

    pub fn order_category(self, heap: &Heap) -> Option<TermOrderCategory> {
        read_heap_cell!(self,
            (HeapCellValueTag::Cons, c) => {
                match_untyped_arena_ptr!(c,
                   (ArenaHeaderTag::Integer, _n) => {
                       Some(TermOrderCategory::Integer)
                   }
                   (ArenaHeaderTag::Rational, _n) => {
                       Some(TermOrderCategory::Integer)
                   }
                   _ => {
                       None
                   }
                )
            }
            (HeapCellValueTag::F64Offset) => {
                Some(TermOrderCategory::FloatingPoint)
            }
            (HeapCellValueTag::Fixnum | HeapCellValueTag::CutPoint) => {
                Some(TermOrderCategory::Integer)
            }
            (HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar) => {
                Some(TermOrderCategory::Variable)
            }
            (HeapCellValueTag::Atom, (_name, arity)) => {
                Some(if arity > 0 {
                    TermOrderCategory::Compound
                } else {
                    TermOrderCategory::Atom
                })
            }
            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                Some(TermOrderCategory::Compound)
            }
            (HeapCellValueTag::Str, s) => {
                let arity = cell_as_atom_cell!(heap[s]).get_arity();

                if arity == 0 {
                    Some(TermOrderCategory::Atom)
                } else {
                    Some(TermOrderCategory::Compound)
                }
            }
            _ => {
                None
            }
        )
    }

    #[inline(always)]
    pub fn is_protected(self, e: usize) -> bool {
        read_heap_cell!(self,
            (HeapCellValueTag::StackVar, s) => {
                s < e
            }
            _ => {
                true
            }
        )
    }
}

const_assert!(size_of::<HeapCellValue>() == 8);

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct UntypedArenaPtr {
    #[allow(unused)]
    ptr: B61,
    m: bool,
    #[allow(unused)]
    padding: B2,
}

impl UntypedArenaPtr {
    #[inline(always)]
    pub fn build_with(ptr: usize) -> Self {
        debug_assert!(ptr != 0);
        UntypedArenaPtr::new().with_ptr(ptr as u64)
    }
}

const_assert!(mem::size_of::<UntypedArenaPtr>() == 8);

impl From<*const ArenaHeader> for UntypedArenaPtr {
    #[inline]
    fn from(ptr: *const ArenaHeader) -> UntypedArenaPtr {
        UntypedArenaPtr::build_with(ptr.expose_provenance())
    }
}

impl From<*const IndexPtr> for UntypedArenaPtr {
    #[inline]
    fn from(ptr: *const IndexPtr) -> UntypedArenaPtr {
        UntypedArenaPtr::build_with(ptr.expose_provenance())
    }
}

impl From<UntypedArenaPtr> for *const ArenaHeader {
    #[inline]
    fn from(ptr: UntypedArenaPtr) -> *const ArenaHeader {
        ptr.get_ptr().cast::<ArenaHeader>()
    }
}

impl UntypedArenaPtr {
    #[inline]
    pub fn set_mark_bit(&mut self, m: bool) {
        self.set_m(m);
    }

    #[inline]
    pub fn get_ptr(self) -> *const u8 {
        let addr: u64 = self.ptr();
        std::ptr::with_exposed_provenance(addr as usize)
    }

    #[inline]
    pub fn get_tag(self) -> ArenaHeaderTag {
        unsafe {
            debug_assert!(!self.get_ptr().is_null());
            let header = *self.get_ptr().cast::<ArenaHeader>();
            header.get_tag()
        }
    }

    #[inline]
    pub fn payload_offset(self) -> *const u8 {
        unsafe { self.get_ptr().add(size_of::<ArenaHeader>()) }
    }

    /// # Safety
    /// - this UntypedArenaPtr actuall pointee type is T
    /// - the pointer must be non-null
    #[inline]
    pub unsafe fn as_typed_ptr<T: ?Sized + ArenaAllocated>(self) -> TypedArenaPtr<T>
    where
        T::Payload: Sized,
    {
        T::typed_ptr(self)
    }

    #[inline]
    pub fn get_mark_bit(self) -> bool {
        self.m()
    }
}

impl Add<usize> for HeapCellValue {
    type Output = HeapCellValue;

    fn add(self, rhs: usize) -> Self::Output {
        match self.get_tag() {
            tag @ HeapCellValueTag::Str
            | tag @ HeapCellValueTag::Lis
            | tag @ HeapCellValueTag::Var
            | tag @ HeapCellValueTag::AttrVar => {
                HeapCellValue::build_with(tag, (self.get_value() as usize + rhs) as u64)
            }
            tag @ HeapCellValueTag::PStrLoc => {
                let value = (self.get_value() as usize + heap_index!(rhs)) as u64;
                HeapCellValue::build_with(tag, value)
            }
            _ => self,
        }
    }
}

impl Sub<usize> for HeapCellValue {
    type Output = HeapCellValue;

    fn sub(self, rhs: usize) -> Self::Output {
        match self.get_tag() {
            tag @ HeapCellValueTag::Str
            | tag @ HeapCellValueTag::Lis
            | tag @ HeapCellValueTag::Var
            | tag @ HeapCellValueTag::AttrVar => {
                HeapCellValue::build_with(tag, (self.get_value() as usize - rhs) as u64)
            }
            tag @ HeapCellValueTag::PStrLoc => {
                let value = self.get_value() as usize - heap_index!(rhs);
                HeapCellValue::build_with(tag, value as u64)
            }
            _ => self,
        }
    }
}

impl SubAssign<usize> for HeapCellValue {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Sub<i64> for HeapCellValue {
    type Output = HeapCellValue;

    fn sub(self, rhs: i64) -> Self::Output {
        if rhs < 0 {
            match self.get_tag() {
                tag @ HeapCellValueTag::Str
                | tag @ HeapCellValueTag::Lis
                | tag @ HeapCellValueTag::Var
                | tag @ HeapCellValueTag::AttrVar => {
                    HeapCellValue::build_with(tag, self.get_value() + rhs.unsigned_abs())
                }
                tag @ HeapCellValueTag::PStrLoc => {
                    let value =
                        self.get_value() as usize + heap_index!(rhs.unsigned_abs() as usize);
                    HeapCellValue::build_with(tag, value as u64)
                }
                _ => self,
            }
        } else {
            self.sub(rhs as usize)
        }
    }
}
