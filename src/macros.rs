/* A simple macro to count the arguments in a variadic list
 * of token trees.
*/

macro_rules! char_as_cell {
    ($c: expr) => {
        HeapCellValue::from_bytes(AtomCell::new_char_inlined($c).into_bytes())
    };
}

macro_rules! fixnum_as_cell {
    ($n: expr) => {
        HeapCellValue::from_bytes($n.into_bytes())
    };
}

macro_rules! integer_as_cell {
    ($n: expr) => {{
        match $n {
            Number::Float(_) => unreachable!(),
            Number::Fixnum(n) => fixnum_as_cell!(n),
            Number::Rational(r) => typed_arena_ptr_as_cell!(r),
            Number::Integer(n) => typed_arena_ptr_as_cell!(n),
        }
    }};
}

macro_rules! empty_list_as_cell {
    () => {
        // the empty list atom has the fixed index of 8 (8 >> 3 == 1 in the condensed atom representation).
        atom_as_cell!(atom!("[]"))
    };
}

macro_rules! atom_as_cell {
    ($atom:expr) => {
        HeapCellValue::from_bytes(AtomCell::build_with($atom.index, 0).into_bytes())
    };
    ($atom:expr, $arity:expr) => {
        HeapCellValue::from_bytes(AtomCell::build_with($atom.index, $arity as u8).into_bytes())
    };
}

macro_rules! cell_as_atom {
    ($cell:expr) => {
        AtomCell::from_bytes($cell.into_bytes()).get_name()
    };
}

macro_rules! cell_as_atom_cell {
    ($cell:expr) => {
        AtomCell::from_bytes($cell.into_bytes())
    };
}

macro_rules! cell_as_f64_offset {
    ($cell:expr) => {{
        let offset = $cell.get_value() as usize;
        F64Offset::from(offset)
    }};
}

macro_rules! cell_as_code_index_offset {
    ($cell:expr) => {{
        let offset = $cell.get_value() as usize;
        CodeIndexOffset::from(offset)
    }};
}

macro_rules! cell_as_untyped_arena_ptr {
    ($cell:expr) => {
        UntypedArenaPtr::from_bytes($cell.to_untyped_arena_ptr_bytes())
    };
}

macro_rules! pstr_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::PStrLoc, $h as u64)
    };
}

macro_rules! list_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::Lis, $h as u64)
    };
}

macro_rules! str_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::Str, $h as u64)
    };
}

macro_rules! stack_loc {
    (OrFrame, $b:expr, $idx:expr) => ({
        $b + prelude_size::<OrFrame>() + $idx * std::mem::size_of::<HeapCellValue>()
    });
    (AndFrame, $e:expr, $idx:expr) => ({
        $e + prelude_size::<AndFrame>() + ($idx  - 1) * std::mem::size_of::<HeapCellValue>()
    });
}

macro_rules! stack_loc_as_cell {
    (OrFrame, $b:expr, $idx:expr) => {
        stack_loc_as_cell!(stack_loc!(OrFrame, $b, $idx))
    };
    (AndFrame, $b:expr, $idx:expr) => {
        stack_loc_as_cell!(stack_loc!(AndFrame, $b, $idx))
    };
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::StackVar, $h as u64)
    };
}

macro_rules! heap_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::Var, $h as u64)
    };
}

macro_rules! attr_var_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::AttrVar, $h as u64)
    };
}

#[allow(unused)]
macro_rules! attr_var_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::AttrVar, $h as u64)
    };
}

macro_rules! typed_arena_ptr_as_cell {
    ($ptr:expr) => {
        raw_ptr_as_cell!($ptr.header_ptr())
    };
}

macro_rules! raw_ptr_as_cell {
    ($ptr:expr) => {{
        // Cell is 64-bit, but raw ptr is 32-bit in 32-bit systems
        let ptr: *const _ = $ptr;
        // This needs to expose provenance because it needs to be turned back into a pointer
        // in contexts where there is no available provenance locally. For example, in
        // `ConsPtr::as_ptr`.
        HeapCellValue::from_ptr_addr(ptr.expose_provenance())
    }};
}

macro_rules! untyped_arena_ptr_as_cell {
    ($ptr:expr) => {
        HeapCellValue::from_bytes(UntypedArenaPtr::into_bytes($ptr))
    };
}

macro_rules! stream_as_cell {
    ($ptr:expr) => {
        raw_ptr_as_cell!($ptr.as_ptr())
    };
}

macro_rules! cell_as_stream {
    ($cell:expr) => {{
        let ptr = cell_as_untyped_arena_ptr!($cell);
        Stream::from_tag(ptr.get_tag(), ptr)
    }};
}

macro_rules! cell_as_load_state_payload {
    ($cell:expr) => {{
        let ptr = cell_as_untyped_arena_ptr!($cell);
        unsafe { ptr.as_typed_ptr::<LiveLoadState>() }
    }};
}

macro_rules! match_untyped_arena_ptr_pat_body {
    ($ptr:ident, Integer, $n:ident, $code:expr) => {{
        let $n = unsafe { $ptr.as_typed_ptr::<Integer>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, Rational, $n:ident, $code:expr) => {{
        let $n = unsafe { $ptr.as_typed_ptr::<Rational>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, OssifiedOpDir, $n:ident, $code:expr) => {{
        let $n = unsafe { $ptr.as_typed_ptr::<OssifiedOpDir>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, LiveLoadState, $n:ident, $code:expr) => {{
        let $n = unsafe { $ptr.as_typed_ptr::<LiveLoadState>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, Stream, $s:ident, $code:expr) => {{
        let $s = Stream::from_tag($ptr.get_tag(), $ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, TcpListener, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<TcpListener>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, HttpListener, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<HttpListener>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, HttpResponse, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<HttpResponse>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, PipeReader, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<PipeReader>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, PipeWriter, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<PipeWriter>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, ChildProcess, $listener:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $listener = unsafe { $ptr.as_typed_ptr::<std::process::Child>() };
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, $($tags:tt)|+, $s:ident, $code:expr) => {{
        let $s = Stream::from_tag($ptr.get_tag(), $ptr);
        #[allow(unused_braces)]
        $code
    }};
}

macro_rules! match_untyped_arena_ptr_pat {
    (Stream) => {
        ArenaHeaderTag::InputFileStream
            | ArenaHeaderTag::OutputFileStream
            | ArenaHeaderTag::NamedTcpStream
            | ArenaHeaderTag::NamedTlsStream
            | ArenaHeaderTag::HttpReadStream
            | ArenaHeaderTag::HttpWriteStream
            | ArenaHeaderTag::ReadlineStream
            | ArenaHeaderTag::StaticStringStream
            | ArenaHeaderTag::ByteStream
            | ArenaHeaderTag::CallbackStream
            | ArenaHeaderTag::InputChannelStream
            | ArenaHeaderTag::StandardOutputStream
            | ArenaHeaderTag::StandardErrorStream
            | ArenaHeaderTag::PipeReader
            | ArenaHeaderTag::PipeWriter
    };
    ($tag:ident) => {
        ArenaHeaderTag::$tag
    };
}

macro_rules! match_untyped_arena_ptr {
    ($ptr:expr, $( ($(ArenaHeaderTag::$tag:tt)|+, $n:ident) => $code:block $(,)?)+ $(_ => $misc_code:expr $(,)?)?) => ({
        let ptr_id = $ptr;

        #[allow(clippy::toplevel_ref_arg)]
        match ptr_id.get_tag() {
            $($(match_untyped_arena_ptr_pat!($tag) => {
                match_untyped_arena_ptr_pat_body!(ptr_id, $tag, $n, $code)
            })+)+
            $(_ => $misc_code)?
        }
    });
}

macro_rules! read_heap_cell_pat_body {
    ($cell:ident, Cons, $n:ident, $code:expr) => {{
        let $n = cell_as_untyped_arena_ptr!($cell);
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, F64Offset, $n:ident, $code:expr) => {{
        let $n = cell_as_f64_offset!($cell);
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, CodeIndexOffset, $n:ident, $code:expr) => {{
        let $n = cell_as_code_index_offset!($cell);
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, Atom, ($name:ident, $arity:ident), $code:expr) => {{
        let ($name, $arity) = cell_as_atom_cell!($cell).get_name_and_arity();
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, Fixnum, $value:ident, $code:expr) => {{
        let $value = Fixnum::from_bytes($cell.into_bytes());
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, CutPoint, $value:ident, $code:expr) => {{
        let $value = Fixnum::from_bytes($cell.into_bytes());
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, Fixnum | CutPoint, $value:ident, $code:expr) => {{
        let $value = Fixnum::from_bytes($cell.into_bytes());
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, CutPoint | Fixnum, $value:ident, $code:expr) => {{
        let $value = Fixnum::from_bytes($cell.into_bytes());
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, $($tags:tt)|+, $value:ident, $code:expr) => {{
        let $value = $cell.get_value() as usize;
        #[allow(unused_braces)]
        $code
    }};
}

macro_rules! read_heap_cell_pat {
    (($(HeapCellValueTag::$tag:tt)|+, $n:tt)) => {
        $(HeapCellValueTag::$tag)|+
    };
    (($(HeapCellValueTag::$tag:tt)|+)) => {
        $(HeapCellValueTag::$tag)|+
    };
    (_) => { _ };
}

macro_rules! read_heap_cell_pat_expander {
    ($cell_id:ident, ($(HeapCellValueTag::$tag:tt)|+, $n:tt), $code:block) => ({
        read_heap_cell_pat_body!($cell_id, $($tag)|+, $n, $code)
    });
    ($cell_id:ident, ($(HeapCellValueTag::$tag:tt)|+), $code:block) => ({
        $code
    });
    ($cell_id:ident, _, $code:block) => ({
        $code
    });
}

macro_rules! read_heap_cell {
    ($cell:expr, $($pat:tt $(if $guard_expr:expr)? => $code:block $(,)?)+) => ({
        let cell_id = $cell;

        match cell_id.get_tag() {
            $(read_heap_cell_pat!($pat) $(if $guard_expr)? => {
                read_heap_cell_pat_expander!(cell_id, $pat, $code)
            })+
        }
    });
}

macro_rules! compare_number_instr {
    ($cmp: expr, $at_1: expr, $at_2: expr) => {{
        $cmp.set_terms($at_1, $at_2);
        ClauseType::Inlined(InlinedClauseType::CompareNumber($cmp)).to_instr()
    }};
}

macro_rules! interm {
    ($n: expr) => {
        ArithmeticTerm::Interm($n)
    };
}

macro_rules! ar_reg {
    ($r: expr) => {
        ArithmeticTerm::Reg($r)
    };
}

macro_rules! unmark_cell_bits {
    ($e:expr) => {{
        let mut result = $e;

        result.set_mark_bit(false);
        result.set_forwarding_bit(false);

        result
    }};
}

macro_rules! index_store {
    ($code_dir:expr, $op_dir:expr, $modules:expr) => {
        IndexStore {
            code_dir: $code_dir,
            extensible_predicates: ExtensiblePredicates::with_hasher(FxBuildHasher::default()),
            local_extensible_predicates: LocalExtensiblePredicates::with_hasher(
                FxBuildHasher::default(),
            ),
            global_variables: GlobalVarDir::with_hasher(FxBuildHasher::default()),
            goal_expansion_indices: GoalExpansionIndices::with_hasher(FxBuildHasher::default()),
            meta_predicates: MetaPredicateDir::with_hasher(FxBuildHasher::default()),
            modules: $modules,
            op_dir: $op_dir,
            streams: StreamDir::new(),
            stream_aliases: StreamAliasDir::with_hasher(FxBuildHasher::default()),
        }
    };
}

macro_rules! unify {
    ($machine_st:expr, $($value:expr),*) => {{
        $($machine_st.pdl.push($value);)*
        $machine_st.unify()
    }};
}

macro_rules! unify_fn {
    ($machine_st:expr, $($value:expr),*) => {{
        $($machine_st.pdl.push($value);)*
        ($machine_st.unify_fn)(&mut $machine_st)
    }};
}

macro_rules! unify_with_occurs_check {
    ($machine_st:expr, $($value:expr),*) => {{
        $($machine_st.pdl.push($value);)*
        $machine_st.unify_with_occurs_check()
    }};
}

macro_rules! compare_term_test {
    ($machine_st:expr, $e1:expr, $e2:expr) => {{
        $machine_st.pdl.push($e2);
        $machine_st.pdl.push($e1);

        $machine_st.compare_term_test(VarComparison::Distinct)
    }};
    ($machine_st:expr, $e1:expr, $e2:expr, $var_comparison:expr) => {{
        $machine_st.pdl.push($e2);
        $machine_st.pdl.push($e1);

        $machine_st.compare_term_test($var_comparison)
    }};
}

macro_rules! step_or_resource_error {
    ($machine_st:expr, $val:expr) => {{
        match $val {
            Ok(r) => r,
            Err(err_loc) => {
                $machine_st.throw_resource_error(err_loc);
                return;
            }
        }
    }};
    ($machine_st:expr, $val:expr, $fail:block) => {{
        match $val {
            Ok(r) => r,
            Err(err_loc) => {
                $machine_st.throw_resource_error(err_loc);
                $fail
            }
        }
    }};
}

macro_rules! resource_error_call_result {
    ($machine_st:expr, $val:expr) => {
        step_or_resource_error!($machine_st, $val, {
            return Err(vec![]);
        })
    };
}

macro_rules! heap_index {
    ($idx:expr) => {
        ($idx) * std::mem::size_of::<HeapCellValue>()
    };
}

macro_rules! cell_index {
    ($idx:expr) => {
        (($idx) / std::mem::size_of::<HeapCellValue>())
    };
}
