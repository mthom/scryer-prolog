use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::machine_indices::*;
use crate::machine::partial_string::*;
use crate::parser::ast::*;
use crate::types::*;

use ordered_float::OrderedFloat;
use rug::{Integer, Rational};

use std::convert::TryFrom;

pub(crate) type Heap = Vec<HeapCellValue>;

impl From<Literal> for HeapCellValue {
    #[inline]
    fn from(literal: Literal) -> Self {
        match literal {
            Literal::Atom(name) => atom_as_cell!(name),
            Literal::Char(c) => char_as_cell!(c),
            Literal::Fixnum(n) => fixnum_as_cell!(n),
            Literal::Integer(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::Rational(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::Float(f) => HeapCellValue::from(f),
            Literal::String(s) => {
                if s == atom!("") {
                    empty_list_as_cell!()
                } else {
                    string_as_cstr_cell!(s)
                }
            }
        }
    }
}

impl TryFrom<HeapCellValue> for Literal {
    type Error = ();

    fn try_from(value: HeapCellValue) -> Result<Literal, ()> {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    Ok(Literal::Atom(name))
                } else {
                    Err(())
                }
            }
            (HeapCellValueTag::Char, c) => {
                Ok(Literal::Char(c))
            }
            (HeapCellValueTag::Fixnum, n) => {
                Ok(Literal::Fixnum(n))
            }
            (HeapCellValueTag::F64, f) => {
                Ok(Literal::Float(f))
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::Integer, n) => {
                         Ok(Literal::Integer(n))
                     }
                     (ArenaHeaderTag::Rational, n) => {
                         Ok(Literal::Rational(n))
                     }
                     (ArenaHeaderTag::F64, f) => {
                         // remove this redundancy.
                         Ok(Literal::Float(F64Ptr(f)))
                     }
                     _ => {
                         Err(())
                     }
                )
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                Ok(Literal::String(cstr_atom))
            }
            _ => {
                Err(())
            }
        )
    }
}

// sometimes we need to dereference variables that are found only in
// the heap without access to the full WAM (e.g., while detecting
// cycles in terms), and which therefore may only point other cells in
// the heap (thanks to the design of the WAM).
pub fn heap_bound_deref(heap: &[HeapCellValue], mut value: HeapCellValue) -> HeapCellValue {
    loop {
        let new_value = read_heap_cell!(value,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                heap[h]
            }
            _ => {
                value
            }
        );

        if new_value != value && new_value.is_var() {
            value = new_value;
            continue;
        }

        return value;
    }
}

pub fn heap_bound_store(heap: &[HeapCellValue], value: HeapCellValue) -> HeapCellValue {
    read_heap_cell!(value,
        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
            heap[h]
        }
        _ => {
            value
        }
    )
}

#[allow(dead_code)]
pub fn print_heap_terms<'a, I: Iterator<Item = &'a HeapCellValue>>(heap: I, h: usize) {
    for (index, term) in heap.enumerate() {
        println!("{} : {:?}", h + index, term);
    }
}

#[inline]
pub(crate) fn put_complete_string(
    heap: &mut Heap,
    s: &str,
    atom_tbl: &mut AtomTable,
) -> HeapCellValue {
    match allocate_pstr(heap, s, atom_tbl) {
        Some(h) => {
            heap.pop(); // pop the trailing variable cell from the heap planted by allocate_pstr.

            if heap.len() == h + 1 {
                let pstr_atom = cell_as_atom!(heap[h]);
                heap[h] = atom_as_cstr_cell!(pstr_atom);
                heap_loc_as_cell!(h)
            } else {
                heap.push(empty_list_as_cell!());
                pstr_loc_as_cell!(h)
            }
        }
        None => {
            empty_list_as_cell!()
        }
    }
}

#[inline]
pub(crate) fn put_partial_string(
    heap: &mut Heap,
    s: &str,
    atom_tbl: &mut AtomTable,
) -> HeapCellValue {
    match allocate_pstr(heap, s, atom_tbl) {
        Some(h) => {
            pstr_loc_as_cell!(h)
        }
        None => {
            empty_list_as_cell!()
        }
    }
}

#[inline]
pub(crate) fn allocate_pstr(
    heap: &mut Heap,
    mut src: &str,
    atom_tbl: &mut AtomTable,
) -> Option<usize> {
    let orig_h = heap.len();

    loop {
        if src == "" {
            return if orig_h == heap.len() {
                None
            } else {
                let tail_h = heap.len() - 1;
                heap[tail_h] = heap_loc_as_cell!(tail_h);

                Some(orig_h)
            };
        }

        let h = heap.len();

        let (pstr, rest_src) = match PartialString::new(src, atom_tbl) {
            Some(tuple) => tuple,
            None => {
                if src.len() > '\u{0}'.len_utf8() {
                    src = &src['\u{0}'.len_utf8()..];
                    continue;
                } else if orig_h == h {
                    return None;
                } else {
                    heap[h - 1] = heap_loc_as_cell!(h - 1);
                    return Some(orig_h);
                }
            }
        };

        heap.push(string_as_pstr_cell!(pstr));

        if rest_src != "" {
            heap.push(pstr_loc_as_cell!(h + 2));
            src = rest_src;
        } else {
            heap.push(heap_loc_as_cell!(h + 1));
            return Some(orig_h);
        }
    }
}

pub fn filtered_iter_to_heap_list<SrcT: Into<HeapCellValue>>(
    heap: &mut Heap,
    values: impl Iterator<Item = SrcT>,
    filter_fn: impl Fn(&Heap, HeapCellValue) -> bool,
) -> usize {
    let head_addr = heap.len();
    let mut h = head_addr;

    for value in values {
        let value = value.into();

        if filter_fn(heap, value) {
            heap.push(list_loc_as_cell!(h + 1));
            heap.push(value);

            h += 2;
        }
    }

    heap.push(empty_list_as_cell!());

    head_addr
}

#[inline(always)]
pub fn iter_to_heap_list<Iter, SrcT>(heap: &mut Heap, values: Iter) -> usize
where
    Iter: Iterator<Item = SrcT>,
    SrcT: Into<HeapCellValue>,
{
    filtered_iter_to_heap_list(heap, values, |_, _| true)
}

pub(crate) fn to_local_code_ptr(heap: &Heap, addr: HeapCellValue) -> Option<LocalCodePtr> {
    let extract_integer = |s: usize| -> Option<usize> {
        match Number::try_from(heap[s]) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => n.to_usize(),
            _ => None,
        }
    };

    read_heap_cell!(addr,
        (HeapCellValueTag::Str, s) => {
            let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

            if name == atom!("dir_entry") && arity == 1 {
                extract_integer(s+1).map(LocalCodePtr::DirEntry)
            } else {
                panic!(
                    "to_local_code_ptr crashed with p.i. {}/{}",
                    name.as_str(),
                    arity,
                );
            }
        }
        _ => {
            None
        }
    )
}

/*
impl<T: RawBlockTraits> HeapTemplate<T> {
    #[inline]
    pub(crate) fn new() -> Self {
        HeapTemplate {
            buf: RawBlock::new(),
            _marker: PhantomData,
        }
    }

    /*
        // TODO: move this to the WAM, then remove the temporary (and by
        // then, unnecessary and impossible) "arena" argument. OR, remove
        // this thing totally!  if we can. by that I mean, just convert a
        // little to a HeapCellValue. don't bother writing to the
        // heap at all. Each of these data is either already inlinable in a
        // HeapCellValue or a pointer to an GC'ed location in memory.
        #[inline]
        pub(crate) fn put_literal(&mut self, literal: Literal) -> HeapCellValue {
            match literal {
                Literal::Atom(name) => atom_as_cell!(name),
                Literal::Char(c) => char_as_cell!(c),
                Literal::EmptyList => empty_list_as_cell!(),
                Literal::Fixnum(n) => fixnum_as_cell!(n),
                Literal::Integer(bigint_ptr) => {
                    let h = self.push(typed_arena_ptr_as_cell!(bigint_ptr));
                    self[h]
                }
                Literal::Rational(bigint_ptr) => {
                    let h = self.push(typed_arena_ptr_as_cell!(bigint_ptr));
                    self[h]
                }
                Literal::Float(f) => typed_arena_ptr_as_cell!(f),
                Literal::String(s) => {
                    if s.as_str().is_empty() {
                        empty_list_as_cell!()
                    } else {
                        // TODO: how do we know where the tail is located?? well, there is no tail. separate tag?
                        untyped_arena_ptr_as_cell!(s) // self.put_complete_string(arena, &s)
                    }
                } // Literal::Usize(n) => Addr::Usize(n),
            }
        }
    */

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.h() == 0
    }

    #[inline]
    pub(crate) fn pop(&mut self) {
        let h = self.h();

        if h > 0 {
            self.truncate(h - 1);
        }
    }

    #[inline]
    pub(crate) fn push(&mut self, val: HeapCellValue) -> usize {
        let h = self.h();

        unsafe {
            let new_ptr = self.buf.alloc(mem::size_of::<HeapCellValue>());
            ptr::write(new_ptr as *mut _, val);
        }

        h
    }

    /*
    #[inline]
    pub(crate) fn atom_at(&self, h: usize) -> bool {
        if let HeapCellValue::Atom(..) = &self[h] {
            true
        } else {
            false
        }
    }

    #[inline]
    pub(crate) fn to_unifiable(&mut self, non_heap_value: HeapCellValue) -> Addr {
        match non_heap_value {
            HeapCellValue::Addr(addr) => addr,
            val @ HeapCellValue::Atom(..)
            | val @ HeapCellValue::Integer(_)
            | val @ HeapCellValue::DBRef(_)
            | val @ HeapCellValue::Rational(_) => Addr::Con(self.push(val)),
            val @ HeapCellValue::LoadStatePayload(_) => Addr::LoadStatePayload(self.push(val)),
            val @ HeapCellValue::NamedStr(..) => Addr::Str(self.push(val)),
            HeapCellValue::PartialString(pstr, has_tail) => {
                let h = self.push(HeapCellValue::PartialString(pstr, has_tail));

                if has_tail {
                    self.push(HeapCellValue::Addr(Addr::EmptyList));
                }

                Addr::Con(h)
            }
            val @ HeapCellValue::Stream(..) => Addr::Stream(self.push(val)),
            val @ HeapCellValue::TcpListener(..) => Addr::TcpListener(self.push(val)),
        }
    }
    */

    #[inline]
    pub(crate) fn truncate(&mut self, h: usize) {
        let new_ptr = self.buf.top as usize - h * mem::size_of::<HeapCellValue>();
        self.buf.ptr = new_ptr as *mut _;
    }

    #[inline]
    pub(crate) fn h(&self) -> usize {
        (self.buf.top as usize - self.buf.ptr as usize) / mem::size_of::<HeapCellValue>()
    }

    pub(crate) fn append(&mut self, vals: Vec<HeapCellValue>) {
        for val in vals {
            self.push(val);
        }
    }

    pub(crate) fn clear(&mut self) {
        if !self.buf.base.is_null() {
            self.truncate(0);
            self.buf.top = self.buf.base;
        }
    }

    /* TODO: get rid of this!!
    #[inline]
    pub(crate) fn index_addr<'a>(&'a self, addr: &Addr) -> RefOrOwned<'a, HeapCellValue> {
        match addr {
            &Addr::Con(h) | &Addr::Str(h) | &Addr::Stream(h) | &Addr::TcpListener(h) => {
                RefOrOwned::Borrowed(&self[h])
            }
            addr => RefOrOwned::Owned(HeapCellValue::Addr(*addr)),
        }
    }
    */
}

impl<T: RawBlockTraits> Index<u64> for HeapTemplate<T> {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: u64) -> &Self::Output {
        unsafe {
            let ptr =
                self.buf.top as usize - (index as usize + 1) * mem::size_of::<HeapCellValue>();
            &*(ptr as *const HeapCellValue)
        }
    }
}

impl<T: RawBlockTraits> Index<usize> for HeapTemplate<T> {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let ptr = self.buf.top as usize - (index + 1) * mem::size_of::<HeapCellValue>();
            &*(ptr as *const HeapCellValue)
        }
    }
}

impl<T: RawBlockTraits> IndexMut<usize> for HeapTemplate<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let ptr = self.buf.top as usize - (index + 1) * mem::size_of::<HeapCellValue>();
            &mut *(ptr as *mut HeapCellValue)
        }
    }
}
*/
