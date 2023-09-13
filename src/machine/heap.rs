use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::machine_indices::*;
use crate::machine::partial_string::*;
use crate::parser::ast::*;
use crate::types::*;

use crate::parser::dashu::{Integer, Rational};

use std::convert::TryFrom;

pub(crate) type Heap = Vec<HeapCellValue>;

impl From<Literal> for HeapCellValue {
    #[inline]
    fn from(literal: Literal) -> Self {
        match literal {
            Literal::Atom(name) => atom_as_cell!(name),
            Literal::Char(c) => char_as_cell!(c),
            Literal::CodeIndex(ptr) => {
                untyped_arena_ptr_as_cell!(UntypedArenaPtr::from(ptr))
            }
            Literal::Fixnum(n) => fixnum_as_cell!(n),
            Literal::Integer(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::Rational(bigint_ptr) => {
                typed_arena_ptr_as_cell!(bigint_ptr)
            }
            Literal::Float(f) => HeapCellValue::from(f.as_ptr()),
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
                Ok(Literal::Float(f.as_offset()))
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::Integer, n) => {
                         Ok(Literal::Integer(n))
                     }
                     (ArenaHeaderTag::Rational, n) => {
                         Ok(Literal::Rational(n))
                     }
                     (ArenaHeaderTag::IndexPtr, _ip) => {
                         Ok(Literal::CodeIndex(CodeIndex::from(cons_ptr)))
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
pub(crate) fn put_complete_string(heap: &mut Heap, s: &str, atom_tbl: &AtomTable) -> HeapCellValue {
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
            let h = heap.len();
            heap.push(empty_list_as_cell!());
            heap_loc_as_cell!(h)
        }
    }
}

#[inline]
pub(crate) fn put_partial_string(heap: &mut Heap, s: &str, atom_tbl: &AtomTable) -> HeapCellValue {
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
pub(crate) fn allocate_pstr(heap: &mut Heap, mut src: &str, atom_tbl: &AtomTable) -> Option<usize> {
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

pub(crate) fn to_local_code_ptr(heap: &Heap, addr: HeapCellValue) -> Option<usize> {
    let extract_integer = |s: usize| -> Option<usize> {
        match Number::try_from(heap[s]) {
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).ok(),
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                Some(value)
            },
            _ => None,
        }
    };

    read_heap_cell!(addr,
        (HeapCellValueTag::Str, s) => {
            let (name, arity) = cell_as_atom_cell!(heap[s]).get_name_and_arity();

            if name == atom!("dir_entry") && arity == 1 {
                extract_integer(s+1)
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
