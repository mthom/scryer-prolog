//! A macro to construct functor terms ready to be written to the WAM
//! heap.

use crate::atom_table::*;
use crate::instructions::IndexingCodePtr;
use crate::machine::heap::Heap;
use crate::parser::ast::Fixnum;
use crate::types::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FunctorElement {
    AbsoluteCell(HeapCellValue),
    Cell(HeapCellValue),
    InnerFunctor(u64, Vec<FunctorElement>),
    String(u64, String),
}

// helper macros
macro_rules! count {
    () => (0);
    ( $x:tt $($xs:tt)* ) => (1 + count!($($xs)*));
}

// core macros

/*
 * functor! is more declarative now, with fewer effects and more
 * work done at compile time using const functions. With these
 * advantages come new quirks: expressions must generally be wrapped
 * in round parentheses for rustc to parse them. See the tests module
 * below for examples, especially those involving atom!
 * subexpressions.
*/

macro_rules! functor {
    ($name:expr) => ({
        vec![FunctorElement::Cell(atom_as_cell!($name))]
    });
    ($name:expr, [$($dt:ident($($value:tt),*)),+]) => ({
        build_functor!([$($dt($($value),*)),*],
                       [FunctorElement::Cell(atom_as_cell!($name, count!($($dt) *)))],
                       1,
                       [])
    });
}

macro_rules! inner_functor {
    ($name:expr, $res_len:expr, [$($dt:ident($($value:tt),*)),+]) => ({
        build_functor!([$($dt($($value),*)),*],
                       [FunctorElement::Cell(atom_as_cell!($name, count!($($dt) *)))],
                       1 + $res_len,
                       [])
    });
}

macro_rules! build_functor {
    ([], [$($res:expr),*], $res_len:expr, [$($subfunctor:expr),*]) => ({
        vec![$($res,)* $($subfunctor),*]
    });
    ([indexing_code_ptr($e:expr) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
        let (inner_functor, cell_size) = indexing_code_ptr($e);
        let referent = if cell_size == 1 {
            heap_loc_as_cell!(1u64 + count!($($dt)*) + $res_len)
        } else {
            str_loc_as_cell!(1u64 + count!($($dt)*) + $res_len)
        };

        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell(referent)],
                       1 + cell_size + $res_len,
                       [$($subfunctor, )* FunctorElement::InnerFunctor(cell_size, inner_functor)])
    });
    ([fixnum($e:expr) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
         build_functor!([$($dt($($value),*)),*],
                        [$($res, )* FunctorElement::Cell(fixnum_as_cell!(/*FIXME this is not safe*/ unsafe{Fixnum::build_with_unchecked($e as i64)}))],
                        1 + $res_len,
                        [$($subfunctor),*])
    });
    ([cell($e:expr) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
         build_functor!([$($dt($($value),*)),*],
                        [$($res, )* FunctorElement::AbsoluteCell($e)],
                        1 + $res_len,
                        [$($subfunctor),*])
    });
    ([literal($e:expr) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
         build_functor!([$($dt($($value),*)),*],
                        [$($res, )* FunctorElement::AbsoluteCell(HeapCellValue::from($e))],
                        1 + $res_len,
                        [$($subfunctor),*])
    });
    ([number($n:expr, $arena:expr) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
         let number_cell = HeapCellValue::arena_from($n, $arena);

         build_functor!([$($dt($($value),*)),*],
                        [$($res, )* FunctorElement::Cell(number_cell)],
                        1 + $res_len,
                        [$($subfunctor),*])
    });
    ([list([]) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell(empty_list_as_cell!())],
                       1 + $res_len,
                       [$($subfunctor),*])
    });
    ([list([$id:ident($($id_value:tt),*) $(, $in_dt:ident($($in_value:tt),*))*]) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
        build_functor!([functor((atom!(".")), [$id($($id_value),*), list([$($in_dt($($in_value),*)),*])])
                        $(, $dt($($value),*))*],
                       [$($res),*],
                       $res_len,
                       [$($subfunctor),*])
    });
    ([string($s:expr) $(, $dt:ident($($value:tt),*))*], [$($res:expr),*], $res_len:expr, [$($subfunctor:expr),*]) => ({
        #[allow(unused_parens)]
        let string = $s;
        let pstr_len = cell_index!(Heap::compute_pstr_size(&string)) as u64;
        let result_len = 1 + count!($($dt)*) + $res_len;

        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell(pstr_loc_as_cell!(heap_index!(result_len as usize) as u64))],
                       1 + $res_len + pstr_len,
                       [$($subfunctor, )* FunctorElement::String(pstr_len, string)])
    });
    ([atom_as_cell($n:expr) $(, $dt:ident($($value:tt),*))*], [$($res:expr),*], $res_len:expr, [$($subfunctor:expr),*]) => ({
        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell(atom_as_cell!($n))],
                       1 + $res_len,
                       [$($subfunctor),*])
    });
    ([functor($stub:expr) $(, $dt:ident($($value:tt),*))*], [$($res:expr),*], $res_len:expr, [$($subfunctor:expr),*]) => ({
        let result_len = 1u64 + count!($($dt)*) + $res_len;
        let inner_functor_size = cell_index!(Heap::compute_functor_byte_size(&$stub)) as u64;

        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell(str_loc_as_cell!(result_len))],
                       1 + $res_len + inner_functor_size,
                       [$($subfunctor, )*
                        FunctorElement::InnerFunctor(inner_functor_size, $stub)])
    });
    ([$id:ident($n:expr) $(, $dt:ident($($value:tt),*))*], [$($res:expr),*], $res_len:expr, [$($subfunctor:expr),*]) => ({
        build_functor!([$($dt($($value),*)),*],
                       [$($res, )* FunctorElement::Cell($id!($n))],
                       1 + $res_len,
                       [$($subfunctor),*])
    });
    ([functor($name:expr, [$($in_dt:ident($($in_value:tt),*)),+]) $(, $dt:ident($($value:tt),*))*],
     [$($res:expr),*],
     $res_len:expr,
     [$($subfunctor:expr),*]) => ({
         let result_len = 1u64 + count!($($dt)*) + $res_len;
         let inner_functor = inner_functor!($name, 0, [$($in_dt($($in_value),*)),*]);
         let inner_functor_size = cell_index!(Heap::compute_functor_byte_size(&inner_functor)) as u64;

         build_functor!([$($dt($($value),*)),*],
                        [$($res, )* FunctorElement::Cell(str_loc_as_cell!(result_len))],
                        1 + $res_len + inner_functor_size,
                        [$($subfunctor, )*
                         FunctorElement::InnerFunctor(inner_functor_size, inner_functor)])
    });
}

pub(crate) fn indexing_code_ptr(code_ptr: IndexingCodePtr) -> (Vec<FunctorElement>, u64) {
    match code_ptr {
        IndexingCodePtr::DynamicExternal(o) => {
            (functor!(atom!("dynamic_external"), [fixnum(o)]), 2)
        }
        IndexingCodePtr::External(o) => (functor!(atom!("external"), [fixnum(o)]), 2),
        IndexingCodePtr::Internal(o) => (functor!(atom!("internal"), [fixnum(o)]), 2),
        IndexingCodePtr::Fail => (vec![FunctorElement::Cell(atom_as_cell!(atom!("fail")))], 1),
    }
}

pub(crate) fn variadic_functor(
    name: Atom,
    arity: usize,
    iter: impl Iterator<Item = Vec<FunctorElement>>,
) -> Vec<FunctorElement> {
    let mut arg_vec = vec![
        FunctorElement::Cell(atom_as_cell!(name, arity)),
        FunctorElement::Cell(list_loc_as_cell!(2)),
    ];

    let key_value_pairs: Vec<_> = iter.collect();
    let num_items = key_value_pairs.len();
    let mut functor_offset = 0;

    for (idx, kv_func) in key_value_pairs.iter().enumerate() {
        let functor_size = cell_index!(Heap::compute_functor_byte_size(kv_func));

        arg_vec.push(FunctorElement::Cell(str_loc_as_cell!(
            2 + num_items * 2 + functor_offset
        )));
        arg_vec.push(FunctorElement::Cell(list_loc_as_cell!(4 + 2 * idx)));

        functor_offset += functor_size;
    }

    arg_vec.pop();
    arg_vec.push(FunctorElement::Cell(empty_list_as_cell!()));

    arg_vec.extend(key_value_pairs.into_iter().map(|kv_func| {
        let inner_functor_size = cell_index!(Heap::compute_functor_byte_size(&kv_func));
        FunctorElement::InnerFunctor(inner_functor_size as u64, kv_func)
    }));

    arg_vec
}

#[cfg(test)]
#[allow(unused_parens)]
mod tests {
    use super::*;
    use indexmap::indexmap;
    use std::string::String;
    use FunctorElement::*;

    #[test]
    fn basic_terms() {
        let functor = functor!(
            atom!("first"),
            [atom_as_cell((atom!("a"))), char_as_cell('c')]
        );

        assert_eq!(functor.len(), 3);

        assert_eq!(functor[0], Cell(atom_as_cell!(atom!("first"), 2)));
        assert_eq!(functor[1], Cell(atom_as_cell!(atom!("a"))));
        assert_eq!(functor[2], Cell(char_as_cell!('c')));

        let functor = functor!(
            atom!("second"),
            [
                atom_as_cell((atom!("a"))),
                functor((atom!("b")), [fixnum(1), fixnum(2)]),
                char_as_cell('c')
            ]
        );

        assert_eq!(functor.len(), 5);

        assert_eq!(functor[0], Cell(atom_as_cell!(atom!("second"), 3)));
        assert_eq!(functor[1], Cell(atom_as_cell!(atom!("a"))));
        assert_eq!(functor[2], Cell(str_loc_as_cell!(4)));
        assert_eq!(functor[3], Cell(char_as_cell!('c')));
        assert_eq!(
            functor[4],
            InnerFunctor(3, functor!(atom!("b"), [fixnum(1), fixnum(2)]))
        );

        let functor = functor!(
            atom!("third"),
            [
                atom_as_cell((atom!("a"))),
                functor((atom!("b")), [fixnum(1), fixnum(2)]),
                functor((atom!("c")), [fixnum(1), fixnum(2)]),
                char_as_cell('c')
            ]
        );

        assert_eq!(functor.len(), 7);

        assert_eq!(functor[0], Cell(atom_as_cell!(atom!("third"), 4)));
        assert_eq!(functor[1], Cell(atom_as_cell!(atom!("a"))));
        assert_eq!(functor[2], Cell(str_loc_as_cell!(5)));
        assert_eq!(functor[3], Cell(str_loc_as_cell!(8)));
        assert_eq!(functor[4], Cell(char_as_cell!('c')));
        assert_eq!(
            functor[5],
            InnerFunctor(3, functor!(atom!("b"), [fixnum(1), fixnum(2)]))
        );
        assert_eq!(
            functor[6],
            InnerFunctor(3, functor!(atom!("c"), [fixnum(1), fixnum(2)]))
        );

        let functor = functor!(
            atom!("fourth"),
            [
                atom_as_cell((atom!("a"))),
                functor((atom!("b")), [fixnum(1), fixnum(2)]),
                functor((atom!("c")), [fixnum(1)]),
                functor((atom!("d")), [fixnum(453), fixnum(2)]),
                char_as_cell('c')
            ]
        );

        assert_eq!(functor.len(), 9);

        assert_eq!(functor[0], Cell(atom_as_cell!(atom!("fourth"), 5)));
        assert_eq!(functor[1], Cell(atom_as_cell!(atom!("a"))));
        assert_eq!(functor[2], Cell(str_loc_as_cell!(6)));
        assert_eq!(functor[3], Cell(str_loc_as_cell!(9)));
        assert_eq!(functor[4], Cell(str_loc_as_cell!(11)));
        assert_eq!(functor[5], Cell(char_as_cell!('c')));
        assert_eq!(
            functor[6],
            InnerFunctor(3, functor!(atom!("b"), [fixnum(1), fixnum(2)]))
        );
        assert_eq!(
            functor[7],
            InnerFunctor(2, functor!(atom!("c"), [fixnum(1)]))
        );
        assert_eq!(
            functor[8],
            InnerFunctor(3, functor!(atom!("d"), [fixnum(453), fixnum(2)]))
        );
    }

    #[test]
    fn basic_terms_in_heap() {
        let functor = functor!(
            atom!("first"),
            [atom_as_cell((atom!("a"))), char_as_cell('b')]
        );

        assert_eq!(functor.len(), 3);

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(functor);
        let loc = functor_writer(&mut heap).unwrap();

        assert_eq!(loc, str_loc_as_cell!(0));

        assert_eq!(heap[0], atom_as_cell!(atom!("first"), 2));
        assert_eq!(heap[1], atom_as_cell!(atom!("a")));
        assert_eq!(heap[2], char_as_cell!('b'));

        heap.truncate(2);

        let functor = functor!(
            atom!("second"),
            [
                atom_as_cell((atom!("a"))),
                functor((atom!("b")), [fixnum(1), fixnum(2)]),
                functor((atom!("c")), [fixnum(1), fixnum(2)]),
                char_as_cell('b')
            ]
        );

        assert_eq!(functor.len(), 7);

        let mut functor_writer = Heap::functor_writer(functor);
        let loc = functor_writer(&mut heap).unwrap();

        assert_eq!(loc, str_loc_as_cell!(2));

        assert_eq!(heap[2], atom_as_cell!(atom!("second"), 4));
        assert_eq!(heap[3], atom_as_cell!(atom!("a")));
        assert_eq!(heap[4], str_loc_as_cell!(7));
        assert_eq!(heap[5], str_loc_as_cell!(10));
        assert_eq!(heap[6], char_as_cell!('b'));
        assert_eq!(heap[7], atom_as_cell!(atom!("b"), 2));
        assert_eq!(heap[8], fixnum_as_cell!(Fixnum::build_with(1)));
        assert_eq!(heap[9], fixnum_as_cell!(Fixnum::build_with(2)));
        assert_eq!(heap[10], atom_as_cell!(atom!("c"), 2));
        assert_eq!(heap[11], fixnum_as_cell!(Fixnum::build_with(1)));
        assert_eq!(heap[12], fixnum_as_cell!(Fixnum::build_with(2)));
    }

    #[test]
    fn nested_functors() {
        let functor = functor!(
            atom!("first"),
            [
                atom_as_cell((atom!("a"))),
                functor(
                    (atom!("d")),
                    [
                        fixnum(1),
                        functor(
                            (atom!("b")),
                            [atom_as_cell((atom!("c"))), char_as_cell('c')]
                        )
                    ]
                ),
                functor((atom!("e")), [fixnum(453), fixnum(2)]),
                char_as_cell('b')
            ]
        );

        assert_eq!(functor.len(), 7);

        assert_eq!(functor[0], Cell(atom_as_cell!(atom!("first"), 4)));
        assert_eq!(functor[1], Cell(atom_as_cell!(atom!("a"))));
        assert_eq!(functor[2], Cell(str_loc_as_cell!(5)));
        assert_eq!(functor[3], Cell(str_loc_as_cell!(11)));
        assert_eq!(functor[4], Cell(char_as_cell!('b')));
        assert_eq!(
            functor[5],
            InnerFunctor(
                6,
                vec![
                    Cell(atom_as_cell!(atom!("d"), 2)),
                    Cell(fixnum_as_cell!(Fixnum::build_with(1))),
                    Cell(str_loc_as_cell!(3)),
                    InnerFunctor(
                        3,
                        functor!(atom!("b"), [atom_as_cell((atom!("c"))), char_as_cell('c')])
                    )
                ]
            )
        );
        assert_eq!(
            functor[6],
            InnerFunctor(3, functor!(atom!("e"), [fixnum(453), fixnum(2)]))
        );
    }

    #[test]
    fn nested_functors_in_heap() {
        let functor = functor!(
            atom!("first"),
            [
                atom_as_cell((atom!("a"))),
                functor(
                    (atom!("second")),
                    [
                        fixnum(1),
                        functor(
                            (atom!("third")),
                            [atom_as_cell((atom!("b"))), char_as_cell('c')]
                        )
                    ]
                ),
                functor((atom!("fourth")), [fixnum(453), fixnum(2)]),
                char_as_cell('b')
            ]
        );

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(functor);
        let loc = functor_writer(&mut heap).unwrap();

        assert_eq!(loc, str_loc_as_cell!(0));

        assert_eq!(heap.cell_len(), 14);

        assert_eq!(heap[0], atom_as_cell!(atom!("first"), 4));
        assert_eq!(heap[1], atom_as_cell!(atom!("a")));
        assert_eq!(heap[2], str_loc_as_cell!(5));
        assert_eq!(heap[3], str_loc_as_cell!(11));
        assert_eq!(heap[4], char_as_cell!('b'));
        assert_eq!(heap[5], atom_as_cell!(atom!("second"), 2));
        assert_eq!(heap[6], fixnum_as_cell!(Fixnum::build_with(1)));
        assert_eq!(heap[7], str_loc_as_cell!(8));
        assert_eq!(heap[8], atom_as_cell!(atom!("third"), 2));
        assert_eq!(heap[9], atom_as_cell!(atom!("b")));
        assert_eq!(heap[10], char_as_cell!('c'));
        assert_eq!(heap[11], atom_as_cell!(atom!("fourth"), 2));
        assert_eq!(heap[12], fixnum_as_cell!(Fixnum::build_with(453)));
        assert_eq!(heap[13], fixnum_as_cell!(Fixnum::build_with(2)));
    }

    #[test]
    fn functors_with_strings_in_heap() {
        let functor = functor!(atom!("first"), [string((String::from("a string")))]);

        assert_eq!(functor.len(), 3);

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(functor);
        let loc = functor_writer(&mut heap).unwrap();

        assert_eq!(loc, str_loc_as_cell!(0));
        assert_eq!(heap.cell_len(), 5);

        assert_eq!(heap[0], atom_as_cell!(atom!("first"), 1));
        assert_eq!(heap[1], pstr_loc_as_cell!(heap_index!(2)));
        assert_eq!(
            heap.slice_to_str(heap_index!(2), "a string".len()),
            "a string"
        );
        assert_eq!(heap[4], empty_list_as_cell!());

        heap.truncate(0);

        let functor = functor!(
            atom!("second"),
            [string((String::from("a stuttered\0 string")))]
        );

        let mut functor_writer = Heap::functor_writer(functor);
        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 10);

        assert_eq!(heap[0], atom_as_cell!(atom!("second"), 1));
        assert_eq!(heap[1], pstr_loc_as_cell!(heap_index!(2)));
        assert_eq!(
            heap.slice_to_str(heap_index!(2), "a stuttered".len()),
            "a stuttered"
        );
        assert_eq!(heap[4], list_loc_as_cell!(5));
        assert_eq!(heap[5], char_as_cell!('\u{0}'));
        assert_eq!(heap[6], pstr_loc_as_cell!(heap_index!(7)));
        assert_eq!(
            heap.slice_to_str(heap_index!(7), " string".len()),
            " string"
        );
        assert_eq!(heap[9], empty_list_as_cell!());
    }

    #[test]
    fn functors_with_lists_in_heap() {
        let functor = functor!(
            atom!("first"),
            [list([fixnum(1), atom_as_cell((atom!("a"))), fixnum(2)])]
        );

        assert_eq!(functor.len(), 3);

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(functor);

        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 11);

        assert_eq!(heap[0], atom_as_cell!(atom!("first"), 1));
        assert_eq!(heap[1], str_loc_as_cell!(2));
        assert_eq!(heap[2], atom_as_cell!(atom!("."), 2));
        assert_eq!(heap[3], fixnum_as_cell!(Fixnum::build_with(1)));
        assert_eq!(heap[4], str_loc_as_cell!(5));
        assert_eq!(heap[5], atom_as_cell!(atom!("."), 2));
        assert_eq!(heap[6], atom_as_cell!(atom!("a")));
        assert_eq!(heap[7], str_loc_as_cell!(8));
        assert_eq!(heap[8], atom_as_cell!(atom!("."), 2));
        assert_eq!(heap[9], fixnum_as_cell!(Fixnum::build_with(2)));
        assert_eq!(heap[10], empty_list_as_cell!());
    }

    #[test]
    fn inlined_atoms() {
        let atom_table = AtomTable::new();
        let inlined = AtomTable::build_with(&atom_table, "inline");

        assert!(inlined.is_inlined());
        assert_eq!(&*inlined.as_str(), "inline");

        let non_inlined = AtomTable::build_with(&atom_table, "longer non-inlined atom");

        assert!(!non_inlined.is_inlined());
        assert_eq!(&*non_inlined.as_str(), "longer non-inlined atom");
    }

    #[test]
    fn functors_with_indexing_code_ptr() {
        let code_ptr = IndexingCodePtr::Internal(0);
        let functor = functor!(
            atom!("first"),
            [
                string((String::from("a string"))),
                indexing_code_ptr(code_ptr)
            ]
        );

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(functor);

        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 8);

        assert_eq!(heap[0], atom_as_cell!(atom!("first"), 2));
        assert_eq!(heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(heap[2], str_loc_as_cell!(6));
        assert_eq!(
            heap.slice_to_str(heap_index!(3), "a string".len()),
            "a string"
        );
        assert_eq!(heap[5], empty_list_as_cell!());
        assert_eq!(heap[6], atom_as_cell!(atom!("internal"), 1));
        assert_eq!(heap[7], fixnum_as_cell!(Fixnum::build_with(0)));

        heap.truncate(0);

        let functor = functor!(
            atom!("second"),
            [
                string((String::from("a string"))),
                functor(
                    (atom!("third")),
                    [
                        atom_as_cell((atom!("a"))),
                        string((String::from("another string"))),
                        indexing_code_ptr(code_ptr)
                    ]
                )
            ]
        );

        let mut functor_writer = Heap::functor_writer(functor);
        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 15);

        assert_eq!(heap[0], atom_as_cell!(atom!("second"), 2));
        assert_eq!(heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(heap[2], str_loc_as_cell!(6));
        assert_eq!(
            heap.slice_to_str(heap_index!(3), "a string".len()),
            "a string"
        );
        assert_eq!(heap[5], empty_list_as_cell!());
        assert_eq!(heap[6], atom_as_cell!(atom!("third"), 3));
        assert_eq!(heap[7], atom_as_cell!(atom!("a")));
        assert_eq!(heap[8], pstr_loc_as_cell!(heap_index!(10)));
        assert_eq!(heap[9], str_loc_as_cell!(13));
        assert_eq!(
            heap.slice_to_str(heap_index!(10), "another string".len()),
            "another string"
        );
        assert_eq!(heap[12], empty_list_as_cell!());
        assert_eq!(heap[13], atom_as_cell!(atom!("internal"), 1));
        assert_eq!(heap[14], fixnum_as_cell!(Fixnum::build_with(0)));

        let functor = functor!(
            atom!("fourth"),
            [
                string((String::from("a string"))),
                functor(
                    (atom!("a")),
                    [
                        functor(
                            (atom!("fifth")),
                            [
                                fixnum(5),
                                string((String::from("another string"))),
                                indexing_code_ptr(code_ptr)
                            ]
                        ),
                        string((String::from("and another")))
                    ]
                )
            ]
        );

        heap.truncate(0);

        let mut functor_writer = Heap::functor_writer(functor);
        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 21);

        assert_eq!(heap[0], atom_as_cell!(atom!("fourth"), 2));
        assert_eq!(heap[1], pstr_loc_as_cell!(heap_index!(3)));
        assert_eq!(heap[2], str_loc_as_cell!(6));
        assert_eq!(
            heap.slice_to_str(heap_index!(3), "a string".len()),
            "a string"
        );
        assert_eq!(heap[5], empty_list_as_cell!());
        assert_eq!(heap[6], atom_as_cell!(atom!("a"), 2));
        assert_eq!(heap[7], str_loc_as_cell!(9));
        assert_eq!(heap[8], pstr_loc_as_cell!(heap_index!(18))); // <-- wrong!
        assert_eq!(heap[9], atom_as_cell!(atom!("fifth"), 3));
        assert_eq!(heap[10], fixnum_as_cell!(Fixnum::build_with(5)));
        assert_eq!(heap[11], pstr_loc_as_cell!(heap_index!(13)));
        assert_eq!(heap[12], str_loc_as_cell!(16));
        assert_eq!(
            heap.slice_to_str(heap_index!(13), "another string".len()),
            "another string"
        );
        assert_eq!(heap[15], empty_list_as_cell!());
        assert_eq!(heap[16], atom_as_cell!(atom!("internal"), 1));
        assert_eq!(heap[17], fixnum_as_cell!(Fixnum::build_with(0)));
        assert_eq!(
            heap.slice_to_str(heap_index!(18), "and another".len()),
            "and another"
        );
        assert_eq!(heap[20], empty_list_as_cell!());

        let constants = indexmap![
            atom_as_cell!(atom!("a")) => IndexingCodePtr::External(2),
            atom_as_cell!(atom!("d")) => IndexingCodePtr::External(7),
        ];

        let functor = variadic_functor(
            atom!("switch_on_constants"),
            1,
            constants
                .iter()
                .map(|(c, ptr)| functor!(atom!(":"), [cell((*c)), indexing_code_ptr((*ptr))])),
        );

        heap.truncate(0);

        let mut functor_writer = Heap::functor_writer(functor);
        functor_writer(&mut heap).unwrap();

        assert_eq!(heap[0], atom_as_cell!(atom!("switch_on_constants"), 1));
        assert_eq!(heap[1], list_loc_as_cell!(2));
        assert_eq!(heap[2], str_loc_as_cell!(6));
        assert_eq!(heap[3], list_loc_as_cell!(4));
        assert_eq!(heap[4], str_loc_as_cell!(11));
        assert_eq!(heap[5], empty_list_as_cell!());
        assert_eq!(heap[6], atom_as_cell!(atom!(":"), 2));
        assert_eq!(heap[7], atom_as_cell!(atom!("a")));
        assert_eq!(heap[8], str_loc_as_cell!(9));
        assert_eq!(heap[9], atom_as_cell!(atom!("external"), 1));
        assert_eq!(heap[10], fixnum_as_cell!(Fixnum::build_with(2)));
        assert_eq!(heap[11], atom_as_cell!(atom!(":"), 2));
        assert_eq!(heap[12], atom_as_cell!(atom!("d")));
        assert_eq!(heap[13], str_loc_as_cell!(14));
        assert_eq!(heap[14], atom_as_cell!(atom!("external"), 1));
        assert_eq!(heap[15], fixnum_as_cell!(Fixnum::build_with(7)));
    }

    #[test]
    fn undefined_procedure_functor() {
        // existence_error
        let culprit = functor!(atom!("/"), [atom_as_cell((atom!("a"))), fixnum(1)]);

        let stub = functor!(
            atom!("existence_error"),
            [
                atom_as_cell((atom!("procedure"))),
                functor((culprit.clone()))
            ]
        );

        println!("{stub:?}");

        // now the error form
        let lineless_error_form = functor!(atom!("error"), [functor(stub), functor(culprit)]);

        println!("{lineless_error_form:?}");

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(lineless_error_form);

        functor_writer(&mut heap).unwrap();

        assert_eq!(heap[0], atom_as_cell!(atom!("error"), 2));
        assert_eq!(heap[1], str_loc_as_cell!(3));
        assert_eq!(heap[2], str_loc_as_cell!(9));
        assert_eq!(heap[3], atom_as_cell!(atom!("existence_error"), 2));
        assert_eq!(heap[4], atom_as_cell!(atom!("procedure")));
        assert_eq!(heap[5], str_loc_as_cell!(6)); // is str_loc_as_cell!(3)
        assert_eq!(heap[6], atom_as_cell!(atom!("/"), 2));
        assert_eq!(heap[7], atom_as_cell!(atom!("a")));
        assert_eq!(heap[8], fixnum_as_cell!(Fixnum::build_with(1)));
        assert_eq!(heap[9], atom_as_cell!(atom!("/"), 2));
        assert_eq!(heap[10], atom_as_cell!(atom!("a")));
        assert_eq!(heap[11], fixnum_as_cell!(Fixnum::build_with(1)));
    }

    #[test]
    fn argless_functor() {
        let name = functor!(atom!("[]"));

        assert_eq!(name.len(), 1);

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(name);
        let loc = functor_writer(&mut heap).unwrap();

        assert_eq!(loc, heap_loc_as_cell!(0));
    }

    #[test]
    fn predefined_subfunctors() {
        let stub = functor!(atom!("sub"), [atom_as_cell((atom!("[]")))]);
        let name = functor!(atom!("super"), [functor(stub)]);

        let mut heap = Heap::new();
        let mut functor_writer = Heap::functor_writer(name);

        functor_writer(&mut heap).unwrap();

        assert_eq!(heap.cell_len(), 4);

        assert_eq!(heap[0], atom_as_cell!(atom!("super"), 1));
        assert_eq!(heap[1], str_loc_as_cell!(2));
        assert_eq!(heap[2], atom_as_cell!(atom!("sub"), 1));
        assert_eq!(heap[3], empty_list_as_cell!());
    }
}
