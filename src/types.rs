use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::machine_indices::*;
use crate::machine::partial_string::PartialString;
use crate::parser::ast::Fixnum;

use modular_bitfield::prelude::*;

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use std::ops::{Add, Sub, SubAssign};

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 6]
pub enum HeapCellValueTag {
    // non-constants / tags with adjoining forwarding bits.
    Cons = 0b00,
    F64 = 0b01,
    Str = 0b000010,
    Lis = 0b000011,
    Var = 0b000110,
    StackVar = 0b000111,
    AttrVar = 0b010011,
    PStrLoc = 0b111111,
    PStrOffset = 0b001110,
    // constants.
    Fixnum = 0b010010,
    Char = 0b011011,
    Atom = 0b001010,
    PStr = 0b001011,
    CStr = 0b010110, // a complete string.
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 6]
pub enum HeapCellValueView {
    // non-constants / tags with adjoining forwarding bits.
    Cons = 0b00,
    F64 = 0b01,
    Str = 0b000010,
    Lis = 0b000011,
    Var = 0b000110,
    StackVar = 0b000111,
    AttrVar = 0b010011,
    PStrLoc = 0b111111,
    PStrOffset = 0b001110,
    // constants.
    Fixnum = 0b010010,
    Char = 0b011011,
    Atom = 0b001010,
    PStr = 0b001011,
    CStr = 0b010110,
    // trail elements.
    TrailedHeapVar = 0b011110,
    TrailedStackVar = 0b011111,
    TrailedAttrVarHeapLink = 0b101110,
    TrailedAttrVarListLink = 0b100010,
    TrailedAttachedValue = 0b101010,
    TrailedBlackboardEntry = 0b100110,
    TrailedBlackboardOffset = 0b100111,
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 2]
pub enum ConsPtrMaskTag {
    Cons = 0b00,
    F64 = 0b01,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug)]
pub struct ConsPtr {
    ptr: B61,
    m: bool,
    tag: ConsPtrMaskTag,
}

impl ConsPtr {
    #[inline(always)]
    pub fn build_with(ptr: *const ArenaHeader, tag: ConsPtrMaskTag) -> Self {
        ConsPtr::new()
            .with_ptr(ptr as *const u8 as u64)
            .with_m(false)
            .with_tag(tag)
    }

    #[inline]
    pub fn as_ptr(self) -> *mut u8 {
        self.ptr() as *mut _
    }
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug)]
#[bits = 6]
pub(crate) enum RefTag {
    HeapCell = 0b0110,
    StackCell = 0b111,
    AttrVar = 0b10011,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Ref {
    val: B56,
    #[allow(unused)] m: bool,
    #[allow(unused)] f: bool,
    tag: RefTag,
}

impl Ord for Ref {
    fn cmp(&self, rhs: &Ref) -> Ordering {
        match self.get_tag() {
            RefTag::HeapCell | RefTag::AttrVar => {
                match rhs.get_tag() {
                    RefTag::StackCell => Ordering::Less,
                    _ => self.get_value().cmp(&rhs.get_value()),
                }
            }
            RefTag::StackCell => {
                match rhs.get_tag() {
                    RefTag::StackCell =>
                        self.get_value().cmp(&rhs.get_value()),
                    _ =>
                        Ordering::Greater,
                }
            }
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
    AttrVarHeapLink(usize),
    AttrVarListLink(usize, usize),
    BlackboardEntry(Atom),
    BlackboardOffset(Atom, HeapCellValue), // key atom, key value
}

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[bits = 6]
pub(crate) enum TrailEntryTag {
    TrailedHeapVar = 0b011110,
    TrailedStackVar = 0b011111,
    TrailedAttrVar = 0b101110,
    TrailedAttrVarHeapLink = 0b100010,
    TrailedAttrVarListLink = 0b100011,
    TrailedAttachedValue = 0b101010,
    TrailedBlackboardEntry = 0b100110,
    TrailedBlackboardOffset = 0b100111,
}

#[bitfield]
#[derive(Copy, Clone, Debug)]
#[repr(u64)]
pub(crate) struct TrailEntry {
    val: B56,
    #[allow(unused)] f: bool,
    #[allow(unused)] m: bool,
    #[allow(unused)] tag: TrailEntryTag,
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
    tag: HeapCellValueTag,
}

impl fmt::Debug for HeapCellValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self.get_tag() {
            tag @ (HeapCellValueTag::Cons | HeapCellValueTag::F64) => {
                let cons_ptr = ConsPtr::from_bytes(self.into_bytes());

                f.debug_struct("HeapCellValue")
                    .field("tag", &tag)
                    .field("ptr", &cons_ptr.ptr())
                    .field("m", &cons_ptr.m())
                    .finish()
            }
            HeapCellValueTag::Atom => {
                let (name, arity) = cell_as_atom_cell!(self)
                     .get_name_and_arity();

                f.debug_struct("HeapCellValue")
                    .field("tag", &HeapCellValueTag::Atom)
                    .field("name", &name.as_str())
                    .field("arity", &arity)
                    .field("m", &self.m())
                    .field("f", &self.f())
                    .finish()
            }
            HeapCellValueTag::PStr => {
                let (name, _) = cell_as_atom_cell!(self)
                     .get_name_and_arity();

                f.debug_struct("HeapCellValue")
                    .field("tag", &HeapCellValueTag::PStr)
                    .field("contents", &name.as_str())
                    .field("m", &self.m())
                    .field("f", &self.f())
                    .finish()
            }
            tag => {
                f.debug_struct("HeapCellValue")
                    .field("tag", &tag)
                    .field("value", &self.get_value())
                    .field("m", &self.get_mark_bit())
                    .field("f", &self.get_forwarding_bit())
                    .finish()
            }
        }
    }
}

impl<T> From<TypedArenaPtr<T>> for HeapCellValue {
    #[inline]
    fn from(arena_ptr: TypedArenaPtr<T>) -> HeapCellValue {
        HeapCellValue::from(arena_ptr.header_ptr() as u64)
    }
}

impl From<F64Ptr> for HeapCellValue {
    #[inline]
    fn from(f64_ptr: F64Ptr) -> HeapCellValue {
        HeapCellValue::from_bytes(
            ConsPtr::from(f64_ptr.as_ptr() as u64)
                .with_tag(ConsPtrMaskTag::F64)
                .with_m(false)
                .into_bytes(),
        )
    }
}

impl From<ConsPtr> for HeapCellValue {
    #[inline(always)]
    fn from(cons_ptr: ConsPtr) -> HeapCellValue {
        HeapCellValue::from_bytes(
            ConsPtr::from(cons_ptr.as_ptr() as u64)
                .with_tag(ConsPtrMaskTag::Cons)
                .with_m(false)
                .into_bytes(),
        )
    }
}

impl<'a> From<(Number, &mut Arena)> for HeapCellValue {
    #[inline(always)]
    fn from((n, arena): (Number, &mut Arena)) -> HeapCellValue {
        match n {
            Number::Float(n) => HeapCellValue::from(arena_alloc!(n, arena)),
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
    pub fn is_string_terminator(mut self, heap: &[HeapCellValue]) -> bool {
        loop {
            return read_heap_cell!(self,
                (HeapCellValueTag::Atom, (name, arity)) => {
                    name == atom!("[]") && arity == 0
                }
                (HeapCellValueTag::CStr) => {
                    true
                }
                (HeapCellValueTag::PStrLoc, h) => {
                    self = heap[h];
                    continue;
                }
                (HeapCellValueTag::PStrOffset, pstr_offset) => {
                    heap[pstr_offset].get_tag() == HeapCellValueTag::CStr
                }
                _ => {
                    false
                }
            );
        }
    }

    #[inline(always)]
    pub fn is_forwarded(self) -> bool {
        self.get_forwarding_bit().unwrap_or(false)
    }

    #[inline]
    pub fn is_ref(self) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Str | HeapCellValueTag::Lis | HeapCellValueTag::Var |
            HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar | HeapCellValueTag::PStrLoc |
            HeapCellValueTag::PStrOffset => true,
            _ => false,
        }
    }

    #[inline]
    pub fn as_char(self) -> Option<char> {
        read_heap_cell!(self,
            (HeapCellValueTag::Char, c) => {
                Some(c)
            }
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
            HeapCellValueTag::Cons | HeapCellValueTag::F64 | HeapCellValueTag::Fixnum |
            HeapCellValueTag::Char | HeapCellValueTag::CStr => {
                true
            }
            HeapCellValueTag::Atom => {
                cell_as_atom_cell!(self).get_arity() == 0
            }
            _ => {
                false
            }
        }
    }

    #[inline(always)]
    pub fn is_stack_var(self) -> bool {
        self.get_tag() == HeapCellValueTag::StackVar
    }

    #[inline]
    pub fn is_compound(self) -> bool {
        match self.get_tag() {
           HeapCellValueTag::Str
            | HeapCellValueTag::Lis
            | HeapCellValueTag::CStr
            | HeapCellValueTag::PStr
            | HeapCellValueTag::PStrLoc
            | HeapCellValueTag::PStrOffset => {
               true
           }
           HeapCellValueTag::Atom => {
               cell_as_atom_cell!(self).get_arity() > 0
           }
           _ => { false }
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
    pub fn get_value(self) -> usize {
        self.val() as usize
    }

    #[inline]
    pub fn set_value(&mut self, val: usize) {
        self.set_val(val as u64);
    }

    #[inline]
    pub fn get_tag(self) -> HeapCellValueTag {
        match self.tag_or_err() {
            Ok(tag) => tag,
            Err(_) => match ConsPtr::from_bytes(self.into_bytes()).tag() {
                ConsPtrMaskTag::Cons => HeapCellValueTag::Cons,
                ConsPtrMaskTag::F64 => HeapCellValueTag::F64,
            },
        }
    }

    #[inline]
    pub fn to_atom(self) -> Option<Atom> {
        match self.tag() {
            HeapCellValueTag::Atom => Some(Atom::from((self.val() << 3) as usize)),
            _ => None,
        }
    }

    #[inline]
    pub fn to_pstr(self) -> Option<PartialString> {
        match self.tag() {
            HeapCellValueTag::PStr => {
                Some(PartialString::from(Atom::from((self.val() as usize) << 3)))
            }
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

    #[inline]
    pub fn to_untyped_arena_ptr(self) -> Option<UntypedArenaPtr> {
        match self.tag() {
            HeapCellValueTag::Cons => Some(UntypedArenaPtr::from_bytes(self.into_bytes())),
            _ => None,
        }
    }

    #[inline]
    pub fn get_forwarding_bit(self) -> Option<bool> {
        match self.get_tag() {
            HeapCellValueTag::Cons        // the list of non-forwardable cell tags.
                | HeapCellValueTag::F64
                // | HeapCellValueTag::Atom
                // | HeapCellValueTag::PStr
                | HeapCellValueTag::Fixnum
                | HeapCellValueTag::Char => None,
            _ => Some(self.f()),
        }
    }

    #[inline]
    pub fn set_forwarding_bit(&mut self, f: bool) {
        match self.get_tag() {
            HeapCellValueTag::Cons        // the list of non-forwardable cell tags.
                | HeapCellValueTag::F64
                // | HeapCellValueTag::Atom
                // | HeapCellValueTag::PStr
                | HeapCellValueTag::Fixnum
                | HeapCellValueTag::Char => {}
            _ => self.set_f(f),
        }
    }

    #[inline]
    pub fn get_mark_bit(self) -> bool {
        match self.get_tag() {
            HeapCellValueTag::Cons | HeapCellValueTag::F64 => {
                ConsPtr::from_bytes(self.into_bytes()).m()
            }
            _ => self.m(),
        }
    }

    #[inline]
    pub fn set_mark_bit(&mut self, m: bool) {
        match self.get_tag() {
            HeapCellValueTag::Cons | HeapCellValueTag::F64 => {
                let value = ConsPtr::from_bytes(self.into_bytes()).with_m(m);
                *self = HeapCellValue::from_bytes(value.into_bytes());
            }
            _ => self.set_m(m),
        }
    }

    pub fn order_category(self) -> Option<TermOrderCategory> {
        match Number::try_from(self).ok() {
            Some(Number::Integer(_)) | Some(Number::Fixnum(_)) | Some(Number::Rational(_)) => {
                Some(TermOrderCategory::Integer)
            }
            Some(Number::Float(_)) => Some(TermOrderCategory::FloatingPoint),
            None => match self.get_tag() {
                HeapCellValueTag::Var | HeapCellValueTag::StackVar | HeapCellValueTag::AttrVar => {
                    Some(TermOrderCategory::Variable)
                }
                HeapCellValueTag::Char => Some(TermOrderCategory::Atom),
                HeapCellValueTag::Atom => {
                    Some(if cell_as_atom_cell!(self).get_arity() > 0 {
                        TermOrderCategory::Compound
                    } else {
                        TermOrderCategory::Atom
                    })
                }
                HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc |
		HeapCellValueTag::CStr | HeapCellValueTag::Str => {
                    Some(TermOrderCategory::Compound)
                }
                _ => {
                    None
                }
            },
        }
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

const_assert!(mem::size_of::<HeapCellValue>() == 8);

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug)]
pub struct UntypedArenaPtr {
    ptr: B61,
    m: bool,
    #[allow(unused)] padding: B2,
}

const_assert!(mem::size_of::<UntypedArenaPtr>() == 8);

impl From<*const ArenaHeader> for UntypedArenaPtr {
    #[inline]
    fn from(ptr: *const ArenaHeader) -> UntypedArenaPtr {
        unsafe { mem::transmute(ptr) }
    }
}

impl From<UntypedArenaPtr> for *const ArenaHeader {
    #[inline]
    fn from(ptr: UntypedArenaPtr) -> *const ArenaHeader {
        unsafe { mem::transmute(ptr) }
    }
}

impl UntypedArenaPtr {
    #[inline]
    pub fn set_mark_bit(&mut self, m: bool) {
        self.set_m(m);
    }

    #[inline]
    pub fn get_ptr(self) -> *const u8 {
        self.ptr() as *const u8
    }

    #[inline]
    pub fn get_tag(self) -> ArenaHeaderTag {
        unsafe {
            let header = *(self.ptr() as *const ArenaHeader);
            header.get_tag()
        }
    }

    #[inline]
    pub fn payload_offset(self) -> *const u8 {
        unsafe {
            self.get_ptr()
                .offset(mem::size_of::<ArenaHeader>() as isize)
        }
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
            tag @ HeapCellValueTag::Str |
            tag @ HeapCellValueTag::Lis |
            tag @ HeapCellValueTag::PStrOffset |
            tag @ HeapCellValueTag::PStrLoc |
            tag @ HeapCellValueTag::Var |
            tag @ HeapCellValueTag::AttrVar => {
                HeapCellValue::build_with(tag, (self.get_value() + rhs) as u64)
            }
            _ => {
                self
            }
        }
    }
}

impl Sub<usize> for HeapCellValue {
    type Output = HeapCellValue;

    fn sub(self, rhs: usize) -> Self::Output {
        match self.get_tag() {
            tag @ HeapCellValueTag::Str |
            tag @ HeapCellValueTag::Lis |
            tag @ HeapCellValueTag::PStrOffset |
            tag @ HeapCellValueTag::PStrLoc |
            tag @ HeapCellValueTag::Var |
            tag @ HeapCellValueTag::AttrVar => {
                HeapCellValue::build_with(tag, (self.get_value() - rhs) as u64)
            }
            _ => {
                self
            }
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
                tag @ HeapCellValueTag::Str |
                tag @ HeapCellValueTag::Lis |
                tag @ HeapCellValueTag::PStrOffset |
                tag @ HeapCellValueTag::Var |
                tag @ HeapCellValueTag::AttrVar => {
                    HeapCellValue::build_with(tag, (self.get_value() + rhs.abs() as usize) as u64)
                }
                _ => {
                    self
                }
            }
        } else {
            self.sub(rhs as usize)
        }
    }
}

