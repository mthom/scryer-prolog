/* A simple macro to count the arguments in a variadic list
 * of token trees.
 */
macro_rules! count_tt {
    () => { 0 };
    ($odd:tt $($a:tt $b:tt)*) => { (count_tt!($($a)*) << 1) | 1 };
    ($($a:tt $even:tt)*) => { count_tt!($($a)*) << 1 };
}

macro_rules! char_as_cell {
    ($c: expr) => {
        HeapCellValue::build_with(HeapCellValueTag::Char, $c as u64)
    };
}

macro_rules! fixnum_as_cell {
    ($n: expr) => {
        HeapCellValue::from_bytes($n.into_bytes()) //HeapCellValueTag::Fixnum, $n.get_num() as u64)
    };
}

macro_rules! cell_as_fixnum {
    ($cell:expr) => {
        Fixnum::from_bytes($cell.into_bytes())
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
        HeapCellValue::from_bytes(
            AtomCell::build_with($atom.flat_index(), 0, HeapCellValueTag::Atom).into_bytes(),
        )
    };
    ($atom:expr, $arity:expr) => {
        HeapCellValue::from_bytes(
            AtomCell::build_with($atom.flat_index(), $arity as u16, HeapCellValueTag::Atom)
                .into_bytes(),
        )
    };
}

macro_rules! cell_as_ossified_op_dir {
    ($cell:expr) => {{
        let ptr_u64 = cell_as_untyped_arena_ptr!($cell);
        TypedArenaPtr::new(ptr_u64.payload_offset() as *mut OssifiedOpDir)
    }};
}

macro_rules! cell_as_string {
    ($cell:expr) => {
        PartialString::from(cell_as_atom!($cell))
    };
}

macro_rules! cell_as_atom {
    ($cell:expr) => {{
        let cell = AtomCell::from_bytes($cell.into_bytes());
        let name = cell.get_index() << 3;

        Atom::from(name as usize)
    }};
}

macro_rules! cell_as_atom_cell {
    ($cell:expr) => {
        AtomCell::from_bytes($cell.into_bytes())
    };
}

macro_rules! cell_as_f64_ptr {
    ($cell:expr) => {{
        let offset = $cell.get_value();
        F64Ptr::from_offset(offset)
    }};
}

macro_rules! cell_as_untyped_arena_ptr {
    ($cell:expr) => {
        UntypedArenaPtr::from(u64::from($cell) as *const ArenaHeader)
    };
}

macro_rules! pstr_as_cell {
    ($atom:expr) => {
        HeapCellValue::from_bytes(
            AtomCell::build_with($atom.flat_index(), 0, HeapCellValueTag::PStr).into_bytes(),
        )
    };
}

macro_rules! pstr_loc_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::PStrLoc, $h as u64)
    };
}

macro_rules! pstr_offset_as_cell {
    ($h:expr) => {
        HeapCellValue::build_with(HeapCellValueTag::PStrOffset, $h as u64)
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

#[macro_export]
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
        untyped_arena_ptr_as_cell!($ptr.header_ptr())
    };
}

macro_rules! untyped_arena_ptr_as_cell {
    ($ptr:expr) => {
        HeapCellValue::from_bytes(unsafe { std::mem::transmute($ptr) })
    };
}

macro_rules! atom_as_cstr_cell {
    ($atom:expr) => {{
        let offset = $atom.flat_index();

        HeapCellValue::from_bytes(
            AtomCell::build_with(offset as u64, 0, HeapCellValueTag::CStr).into_bytes(),
        )
    }};
}

macro_rules! string_as_cstr_cell {
    ($ptr:expr) => {{
        let atom: Atom = $ptr.into();
        let offset = atom.flat_index();

        HeapCellValue::from_bytes(
            AtomCell::build_with(offset as u64, 0, HeapCellValueTag::CStr).into_bytes(),
        )
    }};
}

macro_rules! string_as_pstr_cell {
    ($ptr:expr) => {{
        let atom: Atom = $ptr.into();
        let offset = atom.flat_index();

        HeapCellValue::from_bytes(
            AtomCell::build_with(offset as u64, 0, HeapCellValueTag::PStr).into_bytes(),
        )
    }};
}

macro_rules! stream_as_cell {
    ($ptr:expr) => {
        untyped_arena_ptr_as_cell!($ptr.as_ptr())
    };
}

macro_rules! cell_as_stream {
    ($cell:expr) => {{
        let ptr = cell_as_untyped_arena_ptr!($cell);
        Stream::from_tag(ptr.get_tag(), ptr.payload_offset())
    }};
}

macro_rules! cell_as_load_state_payload {
    ($cell:expr) => { unsafe {
        let ptr = cell_as_untyped_arena_ptr!($cell);
        let ptr = std::mem::transmute::<_, *mut LiveLoadState>(ptr.payload_offset());

        TypedArenaPtr::new(ptr)
    }};
}

macro_rules! match_untyped_arena_ptr_pat_body {
    ($ptr:ident, Integer, $n:ident, $code:expr) => {{
        let payload_ptr = unsafe { std::mem::transmute::<_, *mut Integer>($ptr.payload_offset()) };
        let $n = TypedArenaPtr::new(payload_ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, Rational, $n:ident, $code:expr) => {{
        let payload_ptr = unsafe { std::mem::transmute::<_, *mut Rational>($ptr.payload_offset()) };
        let $n = TypedArenaPtr::new(payload_ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, OssifiedOpDir, $n:ident, $code:expr) => {{
        let $n = cell_as_ossified_op_dir!($cell);
        #[allow(unused_braces)]
        $code
    }};
    ($cell:ident, LiveLoadState, $n:ident, $code:expr) => {{
        let $n = cell_as_load_state_payload!($cell);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, Stream, $s:ident, $code:expr) => {{
        let $s = Stream::from_tag($ptr.get_tag(), $ptr.payload_offset());
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, TcpListener, $listener:ident, $code:expr) => {{
        let payload_ptr = unsafe { std::mem::transmute::<_, *mut TcpListener>($ptr.payload_offset()) };
        #[allow(unused_mut)]
        let mut $listener = TypedArenaPtr::new(payload_ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, HttpListener, $listener:ident, $code:expr) => {{
        let payload_ptr = unsafe { std::mem::transmute::<_, *mut HttpListener>($ptr.payload_offset()) };
        #[allow(unused_mut)]
        let mut $listener = TypedArenaPtr::new(payload_ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, HttpResponse, $listener:ident, $code:expr) => {{
        let payload_ptr = unsafe { std::mem::transmute::<_, *mut HttpResponse>($ptr.payload_offset()) };
        #[allow(unused_mut)]
        let mut $listener = TypedArenaPtr::new(payload_ptr);
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, IndexPtr, $ip:ident, $code:expr) => {{
        #[allow(unused_mut)]
        let mut $ip = TypedArenaPtr::new(unsafe { std::mem::transmute::<_, *mut IndexPtr>($ptr.get_ptr()) });
        #[allow(unused_braces)]
        $code
    }};
    ($ptr:ident, $($tags:tt)|+, $s:ident, $code:expr) => {{
        let $s = Stream::from_tag($ptr.get_tag(), $ptr.payload_offset());
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
            | ArenaHeaderTag::StandardOutputStream
            | ArenaHeaderTag::StandardErrorStream
    };
    (IndexPtr) => {
        ArenaHeaderTag::IndexPtrUndefined |
        ArenaHeaderTag::IndexPtrDynamicUndefined |
        ArenaHeaderTag::IndexPtrDynamicIndex |
        ArenaHeaderTag::IndexPtrIndex
    };
    ($tag:ident) => {
        ArenaHeaderTag::$tag
    };
}

macro_rules! match_untyped_arena_ptr {
    ($ptr:expr, $( ($(ArenaHeaderTag::$tag:tt)|+, $n:ident) => $code:block $(,)?)+ $(_ => $misc_code:expr $(,)?)?) => ({
        let ptr_id = $ptr;

        match ptr_id.get_tag() {
            $($(match_untyped_arena_ptr_pat!($tag) => {
                match_untyped_arena_ptr_pat_body!(ptr_id, $tag, $n, $code)
            })+)+
            $(_ => $misc_code)?
        }
    });
}

macro_rules! read_heap_cell_pat_body {
    ($cell:ident, Cons, $n:ident, $code:expr) => ({
        let $n = cell_as_untyped_arena_ptr!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, F64, $n:ident, $code:expr) => ({
        let $n = cell_as_f64_ptr!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, Atom, ($name:ident, $arity:ident), $code:expr) => ({
        let ($name, $arity) = cell_as_atom_cell!($cell).get_name_and_arity();
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, PStr, $atom:ident, $code:expr) => ({
        let $atom = cell_as_atom!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, CStr, $atom:ident, $code:expr) => ({
        let $atom = cell_as_atom!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, CStr | PStr, $atom:ident, $code:expr) => ({
        let $atom = cell_as_atom!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, PStr | CStr, $atom:ident, $code:expr) => ({
        let $atom = cell_as_atom!($cell);
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, Fixnum, $value:ident, $code:expr) => ({
        let $value = Fixnum::from_bytes($cell.into_bytes());
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, Char, $value:ident, $code:expr) => ({
        let $value = unsafe { char::from_u32_unchecked($cell.get_value() as u32) };
        #[allow(unused_braces)]
        $code
    });
    ($cell:ident, $($tags:tt)|+, $value:ident, $code:expr) => ({
        let $value = $cell.get_value() as usize;
        #[allow(unused_braces)]
        $code
    });
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

macro_rules! functor {
    ($name:expr, [$($dt:ident($($value:expr),*)),+], [$($aux:ident),*]) => ({
        {
            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();
            let arity: usize = count_tt!($($dt) +);

            #[allow(unused_variables)]
            let aux_lens: [usize; count_tt!($($aux) *)] = [$($aux.len()),*];

            let mut result =
                vec![ atom_as_cell!($name, arity as u16),
                      $(functor_term!( $dt($($value),*), arity, aux_lens, addendum ),)+ ];

            $(
                result.extend($aux.iter());
            )*

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr, [$($dt:ident($($value:expr),*)),+]) => ({
        {
            let arity: usize = count_tt!($($dt) +);

            #[allow(unused_variables, unused_mut)]
            let mut addendum = Heap::new();

            let mut result =
                vec![ atom_as_cell!($name, arity as u16),
                      $(functor_term!( $dt($($value),*), arity, [], addendum ),)+ ];

            result.extend(addendum.into_iter());
            result
        }
    });
    ($name:expr) => ({
        vec![ atom_as_cell!($name) ]
    });
}

macro_rules! functor_term {
    (str(0), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        str_loc_as_cell!($arity + 1)
    });
    (str($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let len: usize = $aux_lens[0 .. $e].iter().sum();
        str_loc_as_cell!($arity + 1 + len)
    });
    (str($h:expr, 0), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        str_loc_as_cell!($arity + $h + 1)
    });
    (str($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let len: usize = $aux_lens[0 .. $e].iter().sum();
        str_loc_as_cell!($arity + $h + 1 + len)
    });
    (literal($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::from($e)
    );
    (integer($e:expr, $arena:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::arena_from(Number::arena_from($e, $arena), $arena)
    );
    (fixnum($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        fixnum_as_cell!(Fixnum::build_with($e as i64))
    );
    (indexing_code_ptr($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => ({
        let stub =
            match $e {
                IndexingCodePtr::DynamicExternal(o) => functor!(atom!("dynamic_external"), [fixnum(o)]),
                IndexingCodePtr::External(o) => functor!(atom!("external"), [fixnum(o)]),
                IndexingCodePtr::Internal(o) => functor!(atom!("internal"), [fixnum(o)]),
                IndexingCodePtr::Fail => {
                    vec![atom_as_cell!(atom!("fail"))]
                },
            };

        let len: usize = $aux_lens.iter().sum();
        let h = len + $arity + 1 + $addendum.len() + $h;

        $addendum.extend(stub.into_iter());

        str_loc_as_cell!(h)
    });
    (number($arena:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        HeapCellValue::from(($e, $arena))
    );
    (atom($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        atom_as_cell!($e)
    );
    (string($h:expr, $e:expr), $arity:expr, $aux_lens:expr, $addendum: ident) => ({
        let len: usize = $aux_lens.iter().sum();
        let h = len + $arity + 1 + $addendum.len() + $h;

        let cell = string_as_pstr_cell!($e);

        $addendum.push(cell);
        $addendum.push(empty_list_as_cell!());

        heap_loc_as_cell!(h)
    });
    (boolean($e:expr), $arity:expr, $aux_lens:expr, $addendum: ident) => ({
        if $e {
            functor_term!(atom(atom!("true")), $arity, $aux_lens, $addendum)
        } else {
            functor_term!(atom(atom!("false")), $arity, $aux_lens, $addendum)
        }
    });
    (cell($e:expr), $arity:expr, $aux_lens:expr, $addendum:ident) => (
        $e
    );
}

macro_rules! compare_number_instr {
    ($cmp: expr, $at_1: expr, $at_2: expr) => {{
        $cmp.set_terms($at_1, $at_2);
        call_clause!(ClauseType::Inlined(InlinedClauseType::CompareNumber($cmp)), 0)
    }};
}

macro_rules! call_clause {
    ($clause_type:expr, $pvs:expr) => {{
        let mut instr = $clause_type.to_instr();
        instr.perm_vars_mut().map(|pvs| *pvs = $pvs);
        instr
    }};
}

macro_rules! call_clause_by_default {
    ($clause_type:expr, $pvs:expr) => {{
        let mut instr = $clause_type.to_instr().to_default();
        instr.perm_vars_mut().map(|pvs| *pvs = $pvs);
        instr
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
            local_extensible_predicates: LocalExtensiblePredicates::with_hasher(FxBuildHasher::default()),
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

        $machine_st.compare_term_test()
    }};
}
