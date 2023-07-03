pub use crate::arena::*;
pub use crate::atom_table::*;
use crate::heap_print::*;
pub use crate::machine::heap::*;
pub use crate::machine::*;
pub use crate::machine::machine_state::*;
pub use crate::machine::stack::*;
pub use crate::machine::streams::*;
pub use crate::macros::*;
pub use crate::parser::ast::*;
use crate::read::*;
pub use crate::types::*;

#[cfg(test)]
use crate::machine::copier::CopierTarget;

#[cfg(test)]
use std::ops::{Deref, DerefMut, Index, IndexMut};

// a mini-WAM for test purposes.

pub struct MockWAM {
    pub machine_st: MachineState,
    pub op_dir: OpDir,
    pub flags: MachineFlags,
}

impl MockWAM {
    pub fn new() -> Self {
        let op_dir = default_op_dir();

        Self {
            machine_st: MachineState::new(),
            op_dir,
            flags: MachineFlags::default(),
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

        print_heap_terms(self.machine_st.heap.iter(), term_write_result.heap_loc);

        let mut printer = HCPrinter::new(
            &mut self.machine_st.heap,
            &mut self.machine_st.atom_tbl,
            &mut self.machine_st.stack,
            &self.op_dir,
            self.machine_st.flags,
            PrinterOutputter::new(),
            heap_loc_as_cell!(term_write_result.heap_loc),
        );

        printer.var_names = term_write_result
            .var_dict
            .into_iter()
            .map(|(var, cell)| (cell, var))
            .collect();

        Ok(printer.print().result())
    }
}

#[cfg(test)]
pub struct TermCopyingMockWAM<'a> {
    pub wam: &'a mut MockWAM,
}

#[cfg(test)]
impl<'a> Index<usize> for TermCopyingMockWAM<'a> {
    type Output = HeapCellValue;

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

    fn deref(&self) -> &Self::Target {
        &self.wam
    }
}

#[cfg(test)]
impl<'a> DerefMut for TermCopyingMockWAM<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.wam
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

    fn push(&mut self, val: HeapCellValue) {
        self.wam.machine_st.heap.push(val);
    }

    fn stack(&mut self) -> &mut Stack {
        &mut self.wam.machine_st.stack
    }

    fn threshold(&self) -> usize {
        self.wam.machine_st.heap.len()
    }
}

#[cfg(test)]
pub fn all_cells_marked_and_unforwarded(heap: &[HeapCellValue]) {
    for (idx, cell) in heap.iter().enumerate() {
        assert_eq!(
            cell.get_mark_bit(),
            true,
            "cell {:?} at index {} is not marked",
            cell,
            idx
        );
        assert!(
            !cell.get_forwarding_bit(),
            "cell {:?} at index {} is forwarded",
            cell,
            idx
        );
    }
}

#[cfg(test)]
pub fn all_cells_unmarked(heap: &Heap) {
    for (idx, cell) in heap.iter().enumerate() {
        assert!(
            !cell.get_mark_bit(),
            "cell {:?} at index {} is still marked",
            cell,
            idx
        );

        assert!(
            !cell.get_forwarding_bit(),
            "cell {:?} at index {} is still forwarded",
            cell,
            idx
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
    pub fn with_test_streams() -> Self {
        use ref_thread_local::RefThreadLocal;

        let mut machine_st = MachineState::new();

        let user_input = Stream::Null(StreamOptions::default());
        let user_output = Stream::from_owned_string("".to_owned(), &mut machine_st.arena);
        let user_error = Stream::stderr(&mut machine_st.arena);

        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let mut wam = Machine {
            machine_st,
            indices: IndexStore::new(),
            code: Code::new(),
            user_input,
            user_output,
            user_error,
            load_contexts: vec![],
            runtime,
	        foreign_function_table: Default::default(),
        };

        let mut lib_path = current_dir();

        lib_path.pop();
        lib_path.push("lib");

        wam.add_impls_to_indices();

        bootstrapping_compile(
            Stream::from_static_string(
                LIBRARIES.borrow()["ops_and_meta_predicates"],
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(
                atom!("ops_and_meta_predicates.pl"),
                lib_path.clone(),
            ),
        )
            .unwrap();

        bootstrapping_compile(
            Stream::from_static_string(
                LIBRARIES.borrow()["builtins"],
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(atom!("builtins.pl"), lib_path.clone()),
        )
            .unwrap();

        if let Some(ref mut builtins) = wam.indices.modules.get_mut(&atom!("builtins")) {
            load_module(
                &mut wam.machine_st,
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                builtins,
            );

            import_builtin_impls(&wam.indices.code_dir, builtins);
        } else {
            unreachable!()
        }

        lib_path.pop(); // remove the "lib" at the end

        bootstrapping_compile(
            Stream::from_static_string(include_str!("../loader.pl"), &mut wam.machine_st.arena),
            &mut wam,
            ListingSource::from_file_and_path(atom!("loader.pl"), lib_path.clone()),
        )
            .unwrap();

        wam.configure_modules();

        if let Some(loader) = wam.indices.modules.get(&atom!("loader")) {
            load_module(
                &mut wam.machine_st,
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                loader,
            );
        } else {
            unreachable!()
        }

        wam.load_special_forms();
        wam.load_top_level();
        wam.configure_streams();

        wam
    }

    pub fn test_load_file(&mut self, file: &str) -> Vec<u8> {
        use std::io::Read;

        let stream = Stream::from_owned_string(
            std::fs::read_to_string(AsRef::<std::path::Path>::as_ref(file)).unwrap(),
            &mut self.machine_st.arena,
        );

        self.load_file(file.into(), stream);
        self.user_output.bytes().map(|b| b.unwrap()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify_tests() {
        let mut wam = MachineState::new();
        let mut op_dir = default_op_dir();

        op_dir.insert(
            (atom!("+"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("-"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("*"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("/"), Fixity::In),
            OpDesc::build_with(400, YFX as u8),
        );
        op_dir.insert(
            (atom!("="), Fixity::In),
            OpDesc::build_with(700, XFX as u8),
        );

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

        wam.heap.push(pstr_as_cell!(atom!("this is a string")));
        wam.heap.push(heap_loc_as_cell!(1));

        wam.heap.push(pstr_as_cell!(atom!("this is a string")));
        wam.heap.push(pstr_loc_as_cell!(4));

        wam.heap.push(pstr_offset_as_cell!(0));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(6)));

        unify!(wam, pstr_loc_as_cell!(0), pstr_loc_as_cell!(2));

        assert!(!wam.fail);

        assert_eq!(wam.heap[1], pstr_loc_as_cell!(4));

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        wam.heap.push(list_loc_as_cell!(1));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(3));
        wam.heap.push(atom_as_cell!(atom!("b")));
        wam.heap.push(heap_loc_as_cell!(0));

        wam.heap.push(list_loc_as_cell!(6));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(8));
        wam.heap.push(atom_as_cell!(atom!("b")));
        wam.heap.push(heap_loc_as_cell!(5));

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(!wam.fail);

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        wam.heap.push(list_loc_as_cell!(1));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(3));
        wam.heap.push(atom_as_cell!(atom!("b")));
        wam.heap.push(heap_loc_as_cell!(0));

        wam.heap.push(list_loc_as_cell!(6));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(8));
        wam.heap.push(atom_as_cell!(atom!("c")));
        wam.heap.push(heap_loc_as_cell!(5));

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(wam.fail);

        wam.fail = false;
        all_cells_unmarked(&wam.heap);
        wam.heap.clear();

        wam.heap.push(list_loc_as_cell!(1));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(3));
        wam.heap.push(atom_as_cell!(atom!("b")));
        wam.heap.push(heap_loc_as_cell!(5));

        wam.heap.push(list_loc_as_cell!(6));
        wam.heap.push(atom_as_cell!(atom!("a")));
        wam.heap.push(list_loc_as_cell!(8));
        wam.heap.push(atom_as_cell!(atom!("b")));
        wam.heap.push(heap_loc_as_cell!(0));

        unify!(wam, heap_loc_as_cell!(0), heap_loc_as_cell!(5));

        assert!(!wam.fail);
        all_cells_unmarked(&wam.heap);
        wam.heap.clear();

        {
            let term_write_result_1 =
                parse_and_write_parsed_term_to_heap(&mut wam, "X = g(X,y).", &op_dir).unwrap();

            print_heap_terms(wam.heap.iter(), term_write_result_1.heap_loc);

            unify!(wam, heap_loc_as_cell!(2), str_loc_as_cell!(4));

            assert_eq!(wam.heap[2], str_loc_as_cell!(4));
        }
    }

    #[test]
    fn test_unify_with_occurs_check() {
        let mut wam = MachineState::new();
        let mut op_dir = default_op_dir();

        op_dir.insert(
            (atom!("+"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("-"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("*"), Fixity::In),
            OpDesc::build_with(400, YFX as u8),
        );
        op_dir.insert(
            (atom!("/"), Fixity::In),
            OpDesc::build_with(400, YFX as u8),
        );

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

        wam.heap.push(heap_loc_as_cell!(0));
        wam.heap.push(heap_loc_as_cell!(1));

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

        assert_eq!(
            compare_term_test!(
                wam,
                atom_as_cell!(atom!("atom")),
                atom_as_cstr_cell!(atom!("string"))
            ),
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

        wam.heap.push(atom_as_cell!(atom!("f"), 1));
        wam.heap.push(heap_loc_as_cell!(1));

        assert_eq!(
            compare_term_test!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(0)
            ),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                heap_loc_as_cell!(0),
                atom_as_cell!(atom!("a"))
            ),
            Some(Ordering::Greater)
        );

        wam.heap.clear();

        // [1,2,3]
        wam.heap.push(list_loc_as_cell!(1));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(1)));
        wam.heap.push(list_loc_as_cell!(3));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(2)));
        wam.heap.push(list_loc_as_cell!(5));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(3)));
        wam.heap.push(empty_list_as_cell!());

        // [1,2]
        wam.heap.push(list_loc_as_cell!(8));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(1)));
        wam.heap.push(list_loc_as_cell!(10));
        wam.heap.push(fixnum_as_cell!(Fixnum::build_with(2)));
        wam.heap.push(empty_list_as_cell!());

        assert_eq!(
            compare_term_test!(
                wam,
                heap_loc_as_cell!(7),
                heap_loc_as_cell!(7)
            ),
            Some(Ordering::Equal)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                heap_loc_as_cell!(0),
                heap_loc_as_cell!(7)
            ),
            Some(Ordering::Greater)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                empty_list_as_cell!(),
                heap_loc_as_cell!(7)
            ),
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

        assert_eq!(
            compare_term_test!(
                wam,
                empty_list_as_cell!(),
                atom_as_cstr_cell!(atom!("string"))
            ),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                empty_list_as_cell!(),
                atom_as_cell!(atom!("atom"))
            ),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                atom_as_cell!(atom!("atom")),
                empty_list_as_cell!()
            ),
            Some(Ordering::Greater)
        );

        let one_p_one = HeapCellValue::from(float_alloc!(1.1, &mut wam.arena));

        assert_eq!(
            compare_term_test!(
                wam,
                one_p_one,
                fixnum_as_cell!(Fixnum::build_with(1))
            ),
            Some(Ordering::Less)
        );

        assert_eq!(
            compare_term_test!(
                wam,
                fixnum_as_cell!(Fixnum::build_with(1)),
                one_p_one
            ),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn is_cyclic_term_tests() {
        let mut wam = MachineState::new();

        assert!(!wam.is_cyclic_term(atom_as_cell!(atom!("f"))));
        assert!(!wam.is_cyclic_term(fixnum_as_cell!(Fixnum::build_with(555))));

        wam.heap.push(heap_loc_as_cell!(0));

        assert!(!wam.is_cyclic_term(heap_loc_as_cell!(0)));

        all_cells_unmarked(&wam.heap);
        wam.heap.clear();

        wam.heap.extend(functor!(atom!("f"), [atom(atom!("a")), atom(atom!("b"))]));

        assert!(!wam.is_cyclic_term(str_loc_as_cell!(0)));

        all_cells_unmarked(&wam.heap);

        assert!(!wam.is_cyclic_term(heap_loc_as_cell!(1)));

        all_cells_unmarked(&wam.heap);

        assert!(!wam.is_cyclic_term(heap_loc_as_cell!(2)));

        all_cells_unmarked(&wam.heap);

        wam.heap[2] = str_loc_as_cell!(0);

        print_heap_terms(wam.heap.iter(), 0);

        assert!(wam.is_cyclic_term(str_loc_as_cell!(0)));

        all_cells_unmarked(&wam.heap);

        wam.heap[2] = atom_as_cell!(atom!("b"));
        wam.heap[1] = str_loc_as_cell!(0);

        assert!(wam.is_cyclic_term(str_loc_as_cell!(0)));

        all_cells_unmarked(&wam.heap);

        assert!(wam.is_cyclic_term(heap_loc_as_cell!(1)));

        all_cells_unmarked(&wam.heap);

        wam.heap.clear();

        wam.heap.push(pstr_as_cell!(atom!("a string")));
        wam.heap.push(empty_list_as_cell!());

        assert!(!wam.is_cyclic_term(pstr_loc_as_cell!(0)));
    }
}
