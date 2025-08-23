use crate::heap_print::*;
pub use crate::machine::heap::*;
pub use crate::machine::machine_state::*;
pub use crate::machine::streams::*;
pub use crate::machine::*;
pub use crate::parser::ast::*;

#[cfg(test)]
use crate::machine::copier::CopierTarget;
use crate::read::TermWriteResult;

#[cfg(test)]
use std::ops::{Deref, DerefMut, Index, IndexMut, Range};

// a mini-WAM for test purposes.

pub struct MockWAM {
    pub machine_st: MachineState,
    pub op_dir: OpDir,
    //pub flags: MachineFlags,
}

#[allow(dead_code)]
impl MockWAM {
    pub fn new() -> Self {
        let op_dir = default_op_dir();

        Self {
            machine_st: MachineState::new(),
            op_dir,
        }
    }

    pub fn write_parsed_term_to_heap(
        &mut self,
        input_stream: Stream,
    ) -> Result<TermWriteResult, CompilationError> {
        self.machine_st.read(input_stream, &self.op_dir)
    }

    pub fn parse_and_write_parsed_term_to_heap(
        &mut self,
        term_string: &'static str,
    ) -> Result<TermWriteResult, CompilationError> {
        let stream = Stream::from_static_string(term_string, &mut self.machine_st.arena);
        self.write_parsed_term_to_heap(stream)
    }

    pub fn parse_and_print_term(
        &mut self,
        term_string: &'static str,
    ) -> Result<String, CompilationError> {
        let term_write_result = self.parse_and_write_parsed_term_to_heap(term_string)?;
        print_heap_terms(&self.machine_st.heap, term_write_result.heap_loc);

        let mut printer = HCPrinter::new(
            &mut self.machine_st.heap,
            &mut self.machine_st.stack,
            &self.machine_st.arena,
            &self.op_dir,
            PrinterOutputter::new(),
            term_write_result.heap_loc,
        );

        printer.var_names = term_write_result
            .var_dict
            .into_iter()
            .map(|(var, cell)| match var {
                VarKey::VarPtr(var) => (cell, var.clone()),
                VarKey::AnonVar(_) => (cell, VarPtr::from(var.to_string())),
            })
            .collect();

        Ok(printer.print().result())
    }
}

impl Default for MockWAM {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
pub struct TermCopyingMockWAM<'a> {
    pub wam: &'a mut MockWAM,
}

#[cfg(test)]
impl<'a> Index<usize> for TermCopyingMockWAM<'a> {
    type Output = HeapCellValue;

    #[inline]
    fn index(&self, index: usize) -> &HeapCellValue {
        &self.wam.machine_st.heap[index]
    }
}

#[cfg(test)]
impl<'a> IndexMut<usize> for TermCopyingMockWAM<'a> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut HeapCellValue {
        &mut self.wam.machine_st.heap[index]
    }
}

#[cfg(test)]
impl<'a> Deref for TermCopyingMockWAM<'a> {
    type Target = MockWAM;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.wam
    }
}

#[cfg(test)]
impl<'a> DerefMut for TermCopyingMockWAM<'a> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.wam
    }
}

#[cfg(test)]
impl<'a> CopierTarget for TermCopyingMockWAM<'a> {
    fn store(&self, val: HeapCellValue) -> HeapCellValue {
        read_heap_cell!(val,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                self.wam.machine_st.heap[h]
            }
            (HeapCellValueTag::StackVar, s) => {
                self.wam.machine_st.stack[s]
            }
            _ => {
                val
            }
        )
    }

    fn deref(&self, mut val: HeapCellValue) -> HeapCellValue {
        loop {
            let value = self.store(val);

            if value.is_var() && value != val {
                val = value;
                continue;
            }

            return val;
        }
    }

    fn push_attr_var_queue(&mut self, attr_var_loc: usize) {
        self.wam
            .machine_st
            .attr_var_init
            .attr_var_queue
            .push(attr_var_loc);
    }

    fn stack(&mut self) -> &mut Stack {
        &mut self.wam.machine_st.stack
    }

    fn threshold(&self) -> usize {
        self.wam.machine_st.heap.cell_len()
    }

    #[inline(always)]
    fn copy_pstr_to_threshold(&mut self, pstr_loc: usize) -> Result<usize, usize> {
        self.wam.machine_st.heap.copy_pstr_within(pstr_loc)
    }

    #[inline(always)]
    fn as_slice_from<'b>(&'b self, from: usize) -> Box<dyn Iterator<Item = u8> + 'b> {
        Box::new(self.wam.machine_st.heap.as_slice()[from..].iter().cloned())
    }

    #[inline(always)]
    fn reserve(&mut self, num_cells: usize) -> Result<HeapWriter<'_>, usize> {
        self.wam.machine_st.heap.reserve(num_cells)
    }

    #[inline(always)]
    fn copy_slice_to_end(&mut self, bounds: Range<usize>) -> Result<(), usize> {
        self.wam.machine_st.heap.copy_slice_to_end(bounds)
    }
}

#[cfg(test)]
pub fn all_cells_marked_and_unforwarded(heap: &Heap, offset: usize) {
    for curr_idx in offset..heap.cell_len() {
        let cell = heap[curr_idx];

        assert!(
            cell.get_mark_bit(),
            "cell {cell:?} at index {curr_idx} is not marked"
        );
        assert!(
            !cell.get_forwarding_bit(),
            "cell {cell:?} at index {curr_idx} is forwarded"
        );
    }
}

#[cfg(test)]
pub fn unmark_all_cells(heap: &mut Heap, offset: usize) {
    for idx in offset..heap.cell_len() {
        heap[idx].set_mark_bit(false);
    }
}

#[cfg(test)]
pub fn all_cells_unmarked(iter: &impl SizedHeap) {
    let mut idx = 0;
    let cell_len = iter.cell_len();

    while idx < cell_len {
        let curr_idx = idx;
        idx += 1;
        let cell = iter[curr_idx];

        assert!(
            !cell.get_mark_bit(),
            "cell {cell:?} at index {curr_idx} is still marked"
        );
    }
}

#[cfg(test)]
pub(crate) fn write_parsed_term_to_heap(
    machine_st: &mut MachineState,
    input_stream: Stream,
    op_dir: &OpDir,
) -> Result<TermWriteResult, CompilationError> {
    machine_st.read(input_stream, op_dir)
}

#[cfg(test)]
pub(crate) fn parse_and_write_parsed_term_to_heap(
    machine_st: &mut MachineState,
    term_string: &'static str,
    op_dir: &OpDir,
) -> Result<TermWriteResult, CompilationError> {
    let stream = Stream::from_static_string(term_string, &mut machine_st.arena);
    write_parsed_term_to_heap(machine_st, stream, op_dir)
}

impl Machine {
    /// For use in tests.
    #[allow(clippy::unbuffered_bytes)]
    pub fn test_load_file(&mut self, file: &str) -> Vec<u8> {
        let stream = Stream::from_owned_string(
            std::fs::read_to_string(AsRef::<std::path::Path>::as_ref(file)).unwrap(),
            &mut self.machine_st.arena,
        );

        self.load_file(file, stream);
        self.user_output.bytes().map(|b| b.unwrap()).collect()
    }

    /// For use in tests.
    #[allow(clippy::unbuffered_bytes)]
    pub fn test_load_string(&mut self, code: &str) -> Vec<u8> {
        let stream = Stream::from_owned_string(code.to_owned(), &mut self.machine_st.arena);

        self.load_file("<stdin>", stream);
        self.user_output.bytes().map(|b| b.unwrap()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::functor_macro::FunctorElement;

    #[test]
    fn unify_tests() {
        let mut wam = MachineState::new();
        let mut op_dir = default_op_dir();

        op_dir.insert((atom!("+"), Fixity::In), OpDesc::build_with(500, YFX));
        op_dir.insert((atom!("-"), Fixity::In), OpDesc::build_with(500, YFX));
        op_dir.insert((atom!("*"), Fixity::In), OpDesc::build_with(500, YFX));
        op_dir.insert((atom!("/"), Fixity::In), OpDesc::build_with(400, YFX));
        op_dir.insert((atom!("="), Fixity::In), OpDesc::build_with(700, XFX));

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(b,a).", &op_dir).unwrap();

            unify!(
                wam,
                str_loc_as_cell!(0),
                str_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.fail = false;
        wam.heap.clear();

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(b,b).", &op_dir).unwrap();

            unify!(
                wam,
                str_loc_as_cell!(1),
                heap_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(!wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.fail = false;
        wam.heap.clear();

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(f(A),Y).", &op_dir).unwrap();

            unify!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(!wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.fail = false;
        wam.heap.clear();

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(f(A),Y).", &op_dir).unwrap();

            unify!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(!wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.fail = false;
        wam.heap.clear();

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(f(A),A).", &op_dir).unwrap();

            unify!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(!wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.fail = false;
        wam.heap.clear();

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(A,f(A)).", &op_dir).unwrap();

            all_cells_unmarked(&wam.heap);

            unify!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(!wam.fail);
        }

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_pstr("this is a string"); // 0

            let h = section.cell_len();
            assert_eq!(h, 3);

            section.push_cell(heap_loc_as_cell!(h)); // 3
            section.push_pstr("this is a string"); // 4

            let h = section.cell_len();
            assert_eq!(h + 1, 8);

            section.push_cell(pstr_loc_as_cell!(heap_index!(h + 1))); // 7
            section.push_pstr("this is a string"); // 8

            section.push_cell(pstr_loc_as_cell!(heap_index!(h + 1)));
        });

        unify!(wam, pstr_loc_as_cell!(0), pstr_loc_as_cell!(heap_index!(4)));

        assert!(!wam.fail);

        assert_eq!(
            wam.heap
                .slice_to_str(heap_index!(0), "this is a string".len()),
            "this is a string"
        );
        assert_eq!(wam.heap[3], pstr_loc_as_cell!(heap_index!(8)));
        assert_eq!(
            wam.heap
                .slice_to_str(heap_index!(4), "this is a string".len()),
            "this is a string"
        );
        assert_eq!(wam.heap[7], pstr_loc_as_cell!(heap_index!(8)));
        assert_eq!(
            wam.heap
                .slice_to_str(heap_index!(8), "this is a string".len()),
            "this is a string"
        );
        assert_eq!(wam.heap[11], pstr_loc_as_cell!(heap_index!(8)));

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(atom!("b")));
            section.push_cell(heap_loc_as_cell!(0));

            section.push_cell(list_loc_as_cell!(6));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(atom_as_cell!(atom!("b")));
            section.push_cell(heap_loc_as_cell!(5));
        });

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(!wam.fail);

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(atom!("b")));
            section.push_cell(heap_loc_as_cell!(0));

            section.push_cell(list_loc_as_cell!(6));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(atom_as_cell!(atom!("c")));
            section.push_cell(heap_loc_as_cell!(5));
        });

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(wam.fail);

        wam.fail = false;
        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(atom_as_cell!(atom!("b")));
            section.push_cell(heap_loc_as_cell!(5));

            section.push_cell(list_loc_as_cell!(6));
            section.push_cell(atom_as_cell!(atom!("a")));
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(atom_as_cell!(atom!("b")));
            section.push_cell(heap_loc_as_cell!(0));
        });

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(!wam.fail);
        all_cells_unmarked(&wam.heap);
        wam.heap.clear();

        {
            let term_write_result_1 =
                parse_and_write_parsed_term_to_heap(&mut wam, "X = g(X,y).", &op_dir).unwrap();

            print_heap_terms(&wam.heap, term_write_result_1.heap_loc);

            unify!(wam, heap_loc_as_cell!(2), str_loc_as_cell!(4));

            assert_eq!(wam.heap[2], str_loc_as_cell!(4));
        }
    }

    #[test]
    fn test_unify_with_occurs_check() {
        let mut wam = MachineState::new();
        let mut op_dir = default_op_dir();

        op_dir.insert((atom!("+"), Fixity::In), OpDesc::build_with(500, YFX));
        op_dir.insert((atom!("-"), Fixity::In), OpDesc::build_with(500, YFX));
        op_dir.insert((atom!("*"), Fixity::In), OpDesc::build_with(400, YFX));
        op_dir.insert((atom!("/"), Fixity::In), OpDesc::build_with(400, YFX));

        {
            parse_and_write_parsed_term_to_heap(&mut wam, "f(X,X).", &op_dir).unwrap();

            let term_write_result_2 =
                parse_and_write_parsed_term_to_heap(&mut wam, "f(A,f(A)).", &op_dir).unwrap();

            all_cells_unmarked(&wam.heap);

            unify_with_occurs_check!(
                wam,
                str_loc_as_cell!(0),
                str_loc_as_cell!(term_write_result_2.heap_loc)
            );

            assert!(wam.fail);
        }
    }

    #[test]
    fn test_term_compare() {
        use std::cmp::Ordering;

        let mut wam = MachineState::new();

        // clear the heap of resource error data etc
        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(heap_loc_as_cell!(0));
            section.push_cell(heap_loc_as_cell!(1));
        });

        assert_eq!(
            compare_term_test!(wam, wam.heap[0], wam.heap[1]),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(wam, wam.heap[1], wam.heap[0]),
            Some(Ordering::Greater)
        );

        assert_eq!(
            compare_term_test!(wam, wam.heap[0], wam.heap[0]),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(wam, wam.heap[1], wam.heap[1]),
            Some(Ordering::Equal)
        );

        let cstr_cell = wam.heap.allocate_cstr("string").unwrap();

        assert_eq!(
            compare_term_test!(wam, atom_as_cell!(atom!("atom")), cstr_cell),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                atom_as_cell!(atom!("atom")),
                atom_as_cell!(atom!("atom"))
            ),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                atom_as_cell!(atom!("atom")),
                atom_as_cell!(atom!("aaa"))
            ),
            Some(Ordering::Greater)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                fixnum_as_cell!(Fixnum::build_with(6)),
                heap_loc_as_cell!(1)
            ),
            Some(Ordering::Greater)
        );

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("f"), 1));
            section.push_cell(heap_loc_as_cell!(1));
        });

        assert_eq!(
            compare_term_test!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(0)),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(wam, heap_loc_as_cell!(0), atom_as_cell!(atom!("a"))),
            Some(Ordering::Greater)
        );

        wam.heap.clear();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            // [1,2,3]
            section.push_cell(list_loc_as_cell!(1));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(1)));
            section.push_cell(list_loc_as_cell!(3));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(2)));
            section.push_cell(list_loc_as_cell!(5));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(3)));
            section.push_cell(empty_list_as_cell!());

            // [1,2]
            section.push_cell(list_loc_as_cell!(8));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(1)));
            section.push_cell(list_loc_as_cell!(10));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(2)));
            section.push_cell(empty_list_as_cell!());
        });

        assert_eq!(
            compare_term_test!(wam, heap_loc_as_cell!(7), heap_loc_as_cell!(7)),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(7)),
            Some(Ordering::Greater)
        );

        assert_eq!(
            compare_term_test!(wam, empty_list_as_cell!(), heap_loc_as_cell!(7)),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                empty_list_as_cell!(),
                fixnum_as_cell!(Fixnum::build_with(1))
            ),
            Some(Ordering::Greater)
        );

        let cstr_cell = wam.heap.allocate_cstr("string").unwrap();

        assert_eq!(
            compare_term_test!(wam, empty_list_as_cell!(), cstr_cell),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(wam, empty_list_as_cell!(), atom_as_cell!(atom!("atom"))),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(wam, atom_as_cell!(atom!("atom")), empty_list_as_cell!()),
            Some(Ordering::Greater)
        );

        let one_p_one = HeapCellValue::from(float_alloc!(1.1, &mut wam.arena));

        assert_eq!(
            compare_term_test!(wam, one_p_one, fixnum_as_cell!(Fixnum::build_with(1))),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(wam, fixnum_as_cell!(Fixnum::build_with(1)), one_p_one),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn is_cyclic_term_tests() {
        let mut wam = MachineState::new();

        let mut writer = wam.heap.reserve(96).unwrap();

        writer.write_with(|section| {
            section.push_cell(atom_as_cell!(atom!("f")));
            section.push_cell(fixnum_as_cell!(Fixnum::build_with(555)));
            section.push_cell(heap_loc_as_cell!(0));
        });

        assert!(!wam.is_cyclic_term(0));
        assert!(!wam.is_cyclic_term(1));
        assert!(!wam.is_cyclic_term(2));

        all_cells_unmarked(&wam.heap);
        wam.heap.clear();

        let mut functor_writer = Heap::functor_writer(functor!(
            atom!("f"),
            [atom_as_cell((atom!("a"))), atom_as_cell((atom!("b")))]
        ));

        functor_writer(&mut wam.heap).unwrap();

        let h = wam.heap.cell_len();
        wam.heap.push_cell(str_loc_as_cell!(0)).unwrap();

        assert!(!wam.is_cyclic_term(h));

        all_cells_unmarked(&wam.heap);

        assert!(!wam.is_cyclic_term(1));

        all_cells_unmarked(&wam.heap);

        assert!(!wam.is_cyclic_term(2));

        all_cells_unmarked(&wam.heap);

        wam.heap[2] = str_loc_as_cell!(0);

        print_heap_terms(&wam.heap, 0);

        assert!(wam.is_cyclic_term(2));

        all_cells_unmarked(&wam.heap);

        wam.heap[2] = atom_as_cell!(atom!("b"));
        wam.heap[1] = str_loc_as_cell!(0);

        assert!(wam.is_cyclic_term(1));

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        let h = wam.heap.cell_len();
        wam.heap.allocate_cstr("a string").unwrap();

        assert!(!wam.is_cyclic_term(h));
    }
}
