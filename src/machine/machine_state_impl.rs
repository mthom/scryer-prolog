use crate::arena::*;
use crate::atom_table::*;
use crate::types::*;
use crate::clause_types::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::instructions::*;
use crate::machine::arithmetic_ops::*;
use crate::machine::attributed_variables::*;
use crate::machine::code_repo::CodeRepo;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::machine::INTERRUPT;
use crate::parser::ast::*;
use crate::parser::rug::{Integer, Rational};

use crate::try_numeric_result;

use ordered_float::*;

use indexmap::IndexSet;

use std::cmp::Ordering;
use std::convert::TryFrom;

impl MachineState {
    pub(crate) fn new() -> Self {
        MachineState {
            arena: Arena::new(),
            atom_tbl: AtomTable::new(),
            pdl: Vec::with_capacity(1024),
            s: HeapPtr::default(),
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: LocalCodePtr::default(),
            attr_var_init: AttrVarInitializer::new(0),
            fail: false,
            heap: Heap::with_capacity(256 * 256),
            mode: MachineMode::Write,
            stack: Stack::new(),
            registers: [heap_loc_as_cell!(0); MAX_ARITY + 1], // self.registers[0] is never used.
            trail: vec![],
            tr: 0,
            hb: 0,
            block: 0,
            ball: Ball::new(),
            lifted_heap: Heap::new(),
            interms: vec![Number::default(); 256],
            last_call: false,
            flags: MachineFlags::default(),
            cc: 0,
            global_clock: 0,
            dynamic_mode: FirstOrNext::First,
            unify_fn: MachineState::unify,
            bind_fn: MachineState::bind,
        }
    }

    #[inline]
    pub(crate) fn store(&self, value: HeapCellValue) -> HeapCellValue {
        read_heap_cell!(value,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                self.heap[h]
            }
            (HeapCellValueTag::StackVar, s) => {
                self.stack[s]
            }
            _ => {
                value
            }
        )
    }

    pub fn deref(&self, mut addr: HeapCellValue) -> HeapCellValue {
        loop {
            let value = self.store(addr);

            if value.is_var() && value != addr {
                addr = value;
                continue;
            }

            return addr;
        }
    }

    pub fn trail(&mut self, r: TrailRef) {
        match r {
            TrailRef::Ref(r) => {
                let h = r.get_value() as usize;

                match r.get_tag() {
                    RefTag::HeapCell => {
                        if h < self.hb {
                            self.trail.push(TrailEntry::build_with(
                                TrailEntryTag::TrailedHeapVar,
                                h as u64,
                            ));

                            self.tr += 1;
                        }
                    }
                    RefTag::StackCell => {
                        if h < self.b {
                            self.trail.push(TrailEntry::build_with(
                                TrailEntryTag::TrailedStackVar,
                                h as u64,
                            ));

                            self.tr += 1;
                        }
                    }
                    RefTag::AttrVar => {
                        if h < self.hb {
                            self.trail.push(TrailEntry::build_with(
                                TrailEntryTag::TrailedAttrVar,
                                h as u64,
                            ));

                            self.tr += 1;
                        }
                    }
                }
            }
            TrailRef::AttrVarHeapLink(h) => {
                if h < self.hb {
                    self.trail.push(TrailEntry::build_with(
                        TrailEntryTag::TrailedAttrVarHeapLink,
                        h as u64,
                    ));

                    self.tr += 1;
                }
            }
            TrailRef::AttrVarListLink(h, l) => {
                if h < self.hb {
                    self.trail.push(TrailEntry::build_with(
                        TrailEntryTag::TrailedAttrVarListLink,
                        h as u64,
                    ));

                    self.trail.push(TrailEntry::from_bytes(
                        list_loc_as_cell!(l).into_bytes()
                    ));

                    self.tr += 2;
                }
            }
            TrailRef::BlackboardEntry(key_atom) => {
                self.trail.push(TrailEntry::build_with(
                    TrailEntryTag::TrailedBlackboardEntry,
                    key_atom.index as u64,
                ));

                self.tr += 1;
            }
            TrailRef::BlackboardOffset(key_atom, value_cell) => {
                self.trail.push(TrailEntry::build_with(
                    TrailEntryTag::TrailedBlackboardOffset,
                    key_atom.index as u64,
                ));

                self.trail.push(TrailEntry::from_bytes(
                    value_cell.into_bytes(),
                ));

                self.tr += 2;
            }
        }
    }

    pub fn allocate(&mut self, num_cells: usize) {
        let e = self.stack.allocate_and_frame(num_cells);
        let and_frame = self.stack.index_and_frame_mut(e);

        and_frame.prelude.e = self.e;
        and_frame.prelude.cp = self.cp;

        self.e = e;
        self.p += 1;
    }

    pub fn bind(&mut self, r1: Ref, a2: HeapCellValue) {
        let t1 = self.store(r1.as_heap_cell_value());
        let t2 = self.store(a2);

        if t1.is_var() && (!t2.is_var() || a2 < r1) {
            match r1.get_tag() {
                RefTag::StackCell => {
                    self.stack[r1.get_value() as usize] = t2;
                }
                RefTag::HeapCell => {
                    self.heap[r1.get_value() as usize] = t2;
                }
                RefTag::AttrVar => {
                    self.bind_attr_var(r1.get_value() as usize, t2);
                }
            };

            self.trail(TrailRef::Ref(r1));
        } else {
            read_heap_cell!(a2,
                (HeapCellValueTag::StackVar, s) => {
                    self.stack[s] = t1;
                    self.trail(TrailRef::Ref(Ref::stack_cell(s)));
                }
                (HeapCellValueTag::Var, h) => {
                    self.heap[h] = t1;
                    self.trail(TrailRef::Ref(Ref::heap_cell(h)));
                }
                (HeapCellValueTag::AttrVar, h) => {
                    self.bind_attr_var(h, t1);
                }
                _ => {
                    unreachable!();
                }
            );
        }
    }

    pub fn bind_attr_var(&mut self, h: usize, addr: HeapCellValue) {
        read_heap_cell!(addr,
            (HeapCellValueTag::Var, hc) => {
                self.heap[hc] = attr_var_as_cell!(h);
                self.trail(TrailRef::Ref(Ref::heap_cell(hc)));
            }
            (HeapCellValueTag::StackVar, hc) => {
                self.stack[hc] = attr_var_as_cell!(h);
                self.trail(TrailRef::Ref(Ref::stack_cell(hc)));
            }
            _ => {
                self.push_attr_var_binding(h, addr);
                self.heap[h] = addr;
                self.trail(TrailRef::Ref(Ref::attr_var(h)));
            }
        )
    }

    fn unify_structure(&mut self, s1: usize, value: HeapCellValue) {
        // s1 is the value of a STR cell.
        let (n1, a1) = cell_as_atom_cell!(self.heap[s1]).get_name_and_arity();

        read_heap_cell!(value,
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if n1 == n2 && a1 == a2 {
                    for idx in 0..a1 {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Lis, l2) => {
                if a1 == 2 && n1 == atom!(".") {
                    for idx in 0..2 {
                        self.pdl.push(heap_loc_as_cell!(l2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Atom, (n2, a2)) => {
                if !(a1 == 0 && a2 == 0 && n1 == n2) {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::AttrVar, h) => {
                self.bind(Ref::attr_var(h), str_loc_as_cell!(s1));
            }
            (HeapCellValueTag::Var, h) => {
                self.bind(Ref::heap_cell(h), str_loc_as_cell!(s1));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.bind(Ref::stack_cell(s), str_loc_as_cell!(s1));
            }
            _ => {
                self.fail = true;
            }
        )
    }

    fn unify_list(&mut self, l1: usize, d2: HeapCellValue) {
        read_heap_cell!(d2,
            (HeapCellValueTag::Lis, l2) => {
                for idx in 0..2 {
                    self.pdl.push(heap_loc_as_cell!(l2 + idx));
                    self.pdl.push(heap_loc_as_cell!(l1 + idx));
                }
            }
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if a2 == 2 && n2 == atom!(".") {
                    for idx in 0..2 {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(l1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr | HeapCellValueTag::PStr) => {
                self.unify_partial_string(list_loc_as_cell!(l1), d2)
            }
            (HeapCellValueTag::AttrVar, h) => {
                self.bind(Ref::attr_var(h), list_loc_as_cell!(l1));
            }
            (HeapCellValueTag::Var, h) => {
                self.bind(Ref::heap_cell(h), list_loc_as_cell!(l1));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.bind(Ref::stack_cell(s), list_loc_as_cell!(l1));
            }
            _ => {
                self.fail = true;
            }
        )
    }

    pub fn unify_complete_string(&mut self, atom: Atom, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            self.bind(r, atom_as_cstr_cell!(atom));
            return;
        }

        read_heap_cell!(value,
            (HeapCellValueTag::CStr, cstr_atom) => {
                self.fail = atom != cstr_atom;
            }
            (HeapCellValueTag::Str | HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                self.unify_partial_string(atom_as_cstr_cell!(atom), value);

                if !self.pdl.is_empty() {
                    self.unify();
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }

    // d1's tag is LIS, STR or PSTRLOC.
    pub fn unify_partial_string(&mut self, d1: HeapCellValue, d2: HeapCellValue) {
        if let Some(r) = d2.as_var() {
            self.bind(r, d1);
            return;
        }

        let s1 = self.heap.len();

        self.heap.push(d1);
        self.heap.push(d2);

        let mut pstr_iter1 = HeapPStrIter::new(&self.heap, s1);
        let mut pstr_iter2 = HeapPStrIter::new(&self.heap, s1 + 1);

        match compare_pstr_prefixes(&mut pstr_iter1, &mut pstr_iter2) {
            PStrCmpResult::Ordered(Ordering::Equal) => {}
            PStrCmpResult::Ordered(Ordering::Less) => {
                if pstr_iter2.focus.as_var().is_none() {
                    self.fail = true;
                } else {
                    self.pdl.push(empty_list_as_cell!());
                    self.pdl.push(pstr_iter2.focus);
                }
            }
            PStrCmpResult::Ordered(Ordering::Greater) => {
                if pstr_iter1.focus.as_var().is_none() {
                    self.fail = true;
                } else {
                    self.pdl.push(empty_list_as_cell!());
                    self.pdl.push(pstr_iter1.focus);
                }
            }
            continuable @ PStrCmpResult::FirstIterContinuable(iteratee) |
            continuable @ PStrCmpResult::SecondIterContinuable(iteratee) => {
                if continuable.is_second_iter() {
                    std::mem::swap(&mut pstr_iter1, &mut pstr_iter2);
                }

                let mut chars_iter = PStrCharsIter {
                    iter: pstr_iter1,
                    item: Some(iteratee),
                };

                let mut focus = pstr_iter2.focus;

                'outer: loop {
                    while let Some(c) = chars_iter.peek() {
                        read_heap_cell!(focus,
                            (HeapCellValueTag::Lis, l) => {
                                let val = pstr_iter2.heap[l];

                                self.pdl.push(val);
                                self.pdl.push(char_as_cell!(c));

                                focus = pstr_iter2.heap[l+1];
                            }
                            (HeapCellValueTag::Str, s) => {
                                let (name, arity) = cell_as_atom_cell!(pstr_iter2.heap[s])
                                    .get_name_and_arity();

                                if name == atom!(".") && arity == 2 {
                                    self.pdl.push(pstr_iter2.heap[s+1]);
                                    self.pdl.push(char_as_cell!(c));

                                    focus = pstr_iter2.heap[s+2];
                                } else {
                                    self.fail = true;
                                    break 'outer;
                                }
                            }
                            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                                match chars_iter.item.unwrap() {
                                    PStrIteratee::Char(focus, _) => {
                                        self.pdl.push(self.heap[focus]);
                                        self.pdl.push(heap_loc_as_cell!(h));
                                    }
                                    PStrIteratee::PStrSegment(focus, _, n) => {
                                        read_heap_cell!(self.heap[focus],
                                            (HeapCellValueTag::CStr | HeapCellValueTag::PStr, pstr_atom) => {
                                                if focus < self.heap.len() - 2 {
                                                    self.heap.pop();
                                                    self.heap.pop();
                                                }

                                                if n == 0 {
                                                    let target_cell = match self.heap[focus].get_tag() {
                                                        HeapCellValueTag::CStr => {
                                                            atom_as_cstr_cell!(pstr_atom)
                                                        }
                                                        HeapCellValueTag::PStr => {
                                                            pstr_loc_as_cell!(focus)
                                                        }
                                                        _ => {
                                                            unreachable!()
                                                        }
                                                    };

                                                    self.pdl.push(target_cell);
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = self.heap.len();

                                                    self.heap.push(pstr_offset_as_cell!(focus));
                                                    self.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    self.pdl.push(pstr_loc_as_cell!(h_len));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            (HeapCellValueTag::PStrOffset, pstr_loc) => {
                                                let n0 = cell_as_fixnum!(self.heap[focus+1])
                                                    .get_num() as usize;

                                                if pstr_loc < self.heap.len() - 2 {
                                                    self.heap.pop();
                                                    self.heap.pop();
                                                }

                                                if n == n0 {
                                                    self.pdl.push(pstr_loc_as_cell!(focus));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = self.heap.len();

                                                    self.heap.push(pstr_offset_as_cell!(pstr_loc));
                                                    self.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    self.pdl.push(pstr_loc_as_cell!(h_len));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            _ => {
                                            }
                                        );

                                        if focus < self.heap.len() - 2 {
                                            self.heap.pop();
                                            self.heap.pop();
                                        }

                                        self.pdl.push(self.heap[focus]);
                                        self.pdl.push(heap_loc_as_cell!(h));

                                        return;
                                    }
                                }

                                break 'outer;
                            }
                            _ => {
                                self.fail = true;
                                break 'outer;
                            }
                        );

                        chars_iter.next();
                    }

                    chars_iter.iter.next();

                    self.pdl.push(chars_iter.iter.focus);
                    self.pdl.push(focus);

                    break;
                }
            }
            PStrCmpResult::Unordered => {
                self.pdl.push(pstr_iter1.focus);
                self.pdl.push(pstr_iter2.focus);
            }
        }

        self.heap.pop();
        self.heap.pop();
    }

    pub fn unify_atom(&mut self, atom: Atom, value: HeapCellValue) {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                self.fail = !(arity == 0 && name == atom);
            }
            (HeapCellValueTag::Char, c1) => {
                if let Some(c2) = atom.as_char() {
                    self.fail = c1 != c2;
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::AttrVar, h) => {
                self.bind(Ref::attr_var(h), atom_as_cell!(atom));
            }
            (HeapCellValueTag::Var, h) => {
                self.bind(Ref::heap_cell(h), atom_as_cell!(atom));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.bind(Ref::stack_cell(s), atom_as_cell!(atom));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    pub fn unify_char(&mut self, c: char, value: HeapCellValue) {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if let Some(c2) = name.as_char() {
                    self.fail = !(c == c2 && arity == 0);
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Char, c2) => {
                if c != c2 {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::AttrVar, h) => {
                self.bind(Ref::attr_var(h), char_as_cell!(c));
            }
            (HeapCellValueTag::Var, h) => {
                self.bind(Ref::heap_cell(h), char_as_cell!(c));
            }
            (HeapCellValueTag::StackVar, s) => {
                self.bind(Ref::stack_cell(s), char_as_cell!(c));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    pub fn unify_fixnum(&mut self, n1: Fixnum, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            self.bind(r, fixnum_as_cell!(n1));
            return;
        }

        match Number::try_from(value) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if n1.get_num() == n2.get_num() => {}
                Number::Integer(n2) if n1.get_num() == *n2 => {}
                Number::Rational(n2) if n1.get_num() == *n2 => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    pub fn unify_big_int(&mut self, n1: TypedArenaPtr<Integer>, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            self.bind(r, typed_arena_ptr_as_cell!(n1));
            return;
        }

        match Number::try_from(value) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if *n1 == n2.get_num() => {}
                Number::Integer(n2) if *n1 == *n2 => {}
                Number::Rational(n2) if *n1 == *n2 => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    pub fn unify_rational(&mut self, n1: TypedArenaPtr<Rational>, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            self.bind(r, typed_arena_ptr_as_cell!(n1));
            return;
        }

        match Number::try_from(value) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if *n1 == n2.get_num() => {}
                Number::Integer(n2) if *n1 == *n2 => {}
                Number::Rational(n2) if *n1 == *n2 => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    pub fn unify_f64(&mut self, f1: F64Ptr, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            self.bind(r, typed_arena_ptr_as_cell!(f1));
            return;
        }

        read_heap_cell!(value,
            (HeapCellValueTag::F64, f2) => {
                self.fail = **f1 != **f2;
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                     (ArenaHeaderTag::F64, f2) => {
                         self.fail = **f1 != **F64Ptr(f2);
                     }
                     _ => {
                         self.fail = true;
                     }
                );
            }
            _ => {
                self.fail = true;
            }
        );
    }

    pub fn unify_constant(&mut self, ptr: UntypedArenaPtr, value: HeapCellValue) {
        if let Some(ptr2) = value.to_untyped_arena_ptr() {
            if ptr.get_ptr() == ptr2.get_ptr() {
                return;
            }
        }

        match_untyped_arena_ptr!(ptr,
             (ArenaHeaderTag::Integer, int_ptr) => {
                 self.unify_big_int(int_ptr, value);
             }
             (ArenaHeaderTag::Rational, rat_ptr) => {
                 self.unify_rational(rat_ptr, value);
             }
             _ => {
                 if let Some(r) = value.as_var() {
                     self.bind(r, untyped_arena_ptr_as_cell!(ptr));
                 } else {
                     self.fail = true;
                 }
             }
        );
    }

    pub fn unify(&mut self) {
        let mut tabu_list: IndexSet<(usize, usize)> = IndexSet::new();
        // self.fail = false;

        while !(self.pdl.is_empty() || self.fail) {
            let s1 = self.pdl.pop().unwrap();
            let s1 = self.deref(s1);

            let s2 = self.pdl.pop().unwrap();
            let s2 = self.deref(s2);

            if s1 != s2 {
                let d1 = self.store(s1);
                let d2 = self.store(s2);

                read_heap_cell!(d1,
                    (HeapCellValueTag::AttrVar, h) => {
                        self.bind(Ref::attr_var(h), d2);
                    }
                    (HeapCellValueTag::Var, h) => {
                        self.bind(Ref::heap_cell(h), d2);
                    }
                    (HeapCellValueTag::StackVar, s) => {
                        self.bind(Ref::stack_cell(s), d2);
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert!(arity == 0);
                        self.unify_atom(name, d2);
                    }
                    (HeapCellValueTag::Str, s1) => {
                        if d2.is_constant() {
                            self.fail = true;
                            break;
                        }

                        let s2 = s2.get_value() as usize;

                        if tabu_list.contains(&(s1, s2)) {
                            continue;
                        }

                        self.unify_structure(s1, d2);

                        if !self.fail {
                            tabu_list.insert((s1, s2));
                        }
                    }
                    (HeapCellValueTag::Lis, l1) => {
                        if d2.is_ref() {
                            let l2 = s2.get_value();

                            if tabu_list.contains(&(l1, l2)) {
                                continue;
                            }

                            tabu_list.insert((l1, l2));
                        }

                        self.unify_list(l1, d2);
                    }
                    (HeapCellValueTag::PStrLoc, pstr1_loc) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::PStrLoc |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::Str,
                             pstr2_loc) => {
                                if tabu_list.contains(&(pstr1_loc, pstr2_loc)) {
                                    continue;
                                }
                            }
                            (HeapCellValueTag::CStr |
                             HeapCellValueTag::AttrVar |
                             HeapCellValueTag::Var |
                             HeapCellValueTag::StackVar) => {
                            }
                            _ => {
                                self.fail = true;
                                break;
                            }
                        );

                        self.unify_partial_string(d1, d2);

                        if !self.fail && !d2.is_constant() {
                            tabu_list.insert((pstr1_loc, d2.get_value()));
                        }
                    }
                    (HeapCellValueTag::CStr) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::AttrVar, h) => {
                                self.bind(Ref::attr_var(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::Var, h) => {
                                self.bind(Ref::heap_cell(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::StackVar, s) => {
                                self.bind(Ref::stack_cell(s), d1);
                                continue;
                            }
                            (HeapCellValueTag::Str |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::PStrLoc) => {
                            }
                            (HeapCellValueTag::CStr) => {
                                self.fail = d1 != d2;
                                continue;
                            }
                            _ => {
                                self.fail = true;
                                return;
                            }
                        );

                        self.unify_partial_string(d2, d1);
                    }
                    (HeapCellValueTag::F64, f1) => {
                        self.unify_f64(f1, d2);
                    }
                    (HeapCellValueTag::Fixnum, n1) => {
                        self.unify_fixnum(n1, d2);
                    }
                    (HeapCellValueTag::Char, c1) => {
                        self.unify_char(c1, d2);
                    }
                    (HeapCellValueTag::Cons, ptr_1) => {
                        self.unify_constant(ptr_1, d2);
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
        }
    }

    pub(super) fn set_ball(&mut self) {
        self.ball.reset();

        let addr = self.registers[1];
        self.ball.boundary = self.heap.len();

        copy_term(
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.ball.stub),
            addr,
            AttrVarPolicy::DeepCopy,
        );
    }

    pub fn copy_term(&mut self, attr_var_policy: AttrVarPolicy) {
        let old_h = self.heap.len();

        let a1 = self.registers[1];
        let a2 = self.registers[2];

        copy_term(CopyTerm::new(self), a1, attr_var_policy);

        unify_fn!(self, heap_loc_as_cell!(old_h), a2);
    }

    pub(super) fn unwind_stack(&mut self) {
        self.b = self.block;
        self.fail = true;
    }

    #[inline]
    pub fn bind_with_occurs_check(&mut self, r: Ref, value: HeapCellValue) -> bool {
        if let RefTag::StackCell = r.get_tag() {
            // local variable optimization -- r cannot occur in the
            // heap structure bound to value, so don't bother
            // traversing value.
            self.bind(r, value);
            return false;
        }

        let mut occurs_triggered = false;

        if !value.is_constant() {
            for addr in stackful_preorder_iter(&mut self.heap, value) {
                let addr = unmark_cell_bits!(addr);

                if let Some(inner_r) = addr.as_var() {
                    if r == inner_r {
                        occurs_triggered = true;
                        break;
                    }
                }
            }
        }

        if occurs_triggered {
            self.fail = true;
        } else {
            self.bind(r, value);
        }

        return occurs_triggered;
    }

    #[inline]
    pub(super) fn bind_with_occurs_check_wrapper(&mut self, r: Ref, value: HeapCellValue) {
        self.bind_with_occurs_check(r, value);
    }

    #[inline]
    pub(super) fn bind_with_occurs_check_with_error_wrapper(
        &mut self,
        r: Ref,
        value: HeapCellValue,
    ) {
        if self.bind_with_occurs_check(r, value) {
            let err = self.representation_error(RepFlag::Term);
            let stub = functor_stub(atom!("unify_with_occurs_check"), 2);
            let err = self.error_form(err, stub);

            self.throw_exception(err);
        }
    }

    pub(super) fn unify_with_occurs_check_with_error(&mut self) {
        let mut throw_error = false;
        self.unify_with_occurs_check_loop(|| throw_error = true);

        if throw_error {
            let err = self.representation_error(RepFlag::Term);
            let stub = functor_stub(atom!("unify_with_occurs_check"), 2);
            let err = self.error_form(err, stub);

            self.throw_exception(err);
        }
    }

    pub(super) fn unify_with_occurs_check(&mut self) {
        self.unify_with_occurs_check_loop(|| {})
    }

    fn unify_structure_with_occurs_check(
        &mut self,
        s1: usize,
        value: HeapCellValue,
        mut occurs_trigger: impl FnMut(),
    ) {
        // s1 is the value of a STR cell.
        let (n1, a1) = cell_as_atom_cell!(self.heap[s1]).get_name_and_arity();

        read_heap_cell!(value,
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if n1 == n2 && a1 == a2 {
                    for idx in 0..a1 {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Lis, l2) => {
                if a1 == 2 && n1 == atom!(".") {
                    for idx in 0..2 {
                        self.pdl.push(heap_loc_as_cell!(l2+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Atom, (n2, a2)) => {
                if !(a1 == 0 && a2 == 0 && n1 == n2) {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::AttrVar, h) => {
                if self.bind_with_occurs_check(Ref::attr_var(h), str_loc_as_cell!(s1)) {
                    occurs_trigger();
                }
            }
            (HeapCellValueTag::Var, h) => {
                if self.bind_with_occurs_check(Ref::heap_cell(h), str_loc_as_cell!(s1)) {
                    occurs_trigger();
                }
            }
            (HeapCellValueTag::StackVar, s) => {
                if self.bind_with_occurs_check(Ref::stack_cell(s), str_loc_as_cell!(s1)) {
                    occurs_trigger();
                }
            }
            _ => {
                self.fail = true;
            }
        )
    }

    // the return value of unify_partial_string_with_occurs_check is
    // interpreted as follows:
    //
    // Some(None) -- the strings are equal, nothing to unify
    // Some(Some(f2,f1)) -- prefixes equal, try to unify focus values f2, f1
    // None -- prefixes not equal, unification fails
    //
    // d1's tag is assumed to be one of LIS, STR or PSTRLOC.
    pub fn unify_partial_string_with_occurs_check(
        &mut self,
        d1: HeapCellValue,
        d2: HeapCellValue,
        mut occurs_trigger: impl FnMut(),
    ) {
        if let Some(r) = d2.as_var() {
            if self.bind_with_occurs_check(r, d1) {
                occurs_trigger();
            }

            return;
        }

        let s1 = self.heap.len();

        self.heap.push(d1);
        self.heap.push(d2);

        let mut pstr_iter1 = HeapPStrIter::new(&self.heap, s1);
        let mut pstr_iter2 = HeapPStrIter::new(&self.heap, s1 + 1);

        match compare_pstr_prefixes(&mut pstr_iter1, &mut pstr_iter2) {
            PStrCmpResult::Ordered(Ordering::Equal) => {}
            PStrCmpResult::Ordered(Ordering::Less) => {
                if pstr_iter2.focus.as_var().is_none() {
                    self.fail = true;
                } else {
                    self.pdl.push(empty_list_as_cell!());
                    self.pdl.push(pstr_iter2.focus);
                }
            }
            PStrCmpResult::Ordered(Ordering::Greater) => {
                if pstr_iter1.focus.as_var().is_none() {
                    self.fail = true;
                } else {
                    self.pdl.push(empty_list_as_cell!());
                    self.pdl.push(pstr_iter1.focus);
                }
            }
            continuable @ PStrCmpResult::FirstIterContinuable(iteratee) |
            continuable @ PStrCmpResult::SecondIterContinuable(iteratee) => {
                if continuable.is_second_iter() {
                    std::mem::swap(&mut pstr_iter1, &mut pstr_iter2);
                }

                let mut chars_iter = PStrCharsIter {
                    iter: pstr_iter1,
                    item: Some(iteratee),
                };

                let mut focus = pstr_iter2.focus;

                'outer: loop {
                    while let Some(c) = chars_iter.peek() {
                        read_heap_cell!(focus,
                            (HeapCellValueTag::Lis, l) => {
                                let val = pstr_iter2.heap[l];

                                self.pdl.push(val);
                                self.pdl.push(char_as_cell!(c));

                                focus = pstr_iter2.heap[l+1];
                            }
                            (HeapCellValueTag::Str, s) => {
                                let (name, arity) = cell_as_atom_cell!(pstr_iter2.heap[s])
                                    .get_name_and_arity();

                                if name == atom!(".") && arity == 2 {
                                    self.pdl.push(pstr_iter2.heap[s+1]);
                                    self.pdl.push(char_as_cell!(c));

                                    focus = pstr_iter2.heap[s+2];
                                } else {
                                    self.fail = true;
                                    break 'outer;
                                }
                            }
                            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                                match chars_iter.item.unwrap() {
                                    PStrIteratee::Char(focus, _) => {
                                        self.pdl.push(self.heap[focus]);
                                        self.pdl.push(heap_loc_as_cell!(h));
                                    }
                                    PStrIteratee::PStrSegment(focus, _, n) => {
                                        read_heap_cell!(self.heap[focus],
                                            (HeapCellValueTag::CStr | HeapCellValueTag::PStr, pstr_atom) => {
                                                if focus < self.heap.len() - 2 {
                                                    self.heap.pop();
                                                    self.heap.pop();
                                                }

                                                if n == 0 {
                                                    let target_cell = match self.heap[focus].get_tag() {
                                                        HeapCellValueTag::CStr => {
                                                            atom_as_cstr_cell!(pstr_atom)
                                                        }
                                                        HeapCellValueTag::PStr => {
                                                            pstr_loc_as_cell!(focus)
                                                        }
                                                        _ => {
                                                            unreachable!()
                                                        }
                                                    };

                                                    self.pdl.push(target_cell);
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = self.heap.len();

                                                    self.heap.push(pstr_offset_as_cell!(focus));
                                                    self.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    self.pdl.push(pstr_loc_as_cell!(h_len));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            (HeapCellValueTag::PStrOffset, pstr_loc) => {
                                                let n0 = cell_as_fixnum!(self.heap[focus+1])
                                                    .get_num() as usize;

                                                if pstr_loc < self.heap.len() - 2 {
                                                    self.heap.pop();
                                                    self.heap.pop();
                                                }

                                                if n == n0 {
                                                    self.pdl.push(pstr_loc_as_cell!(focus));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = self.heap.len();

                                                    self.heap.push(pstr_offset_as_cell!(pstr_loc));
                                                    self.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    self.pdl.push(pstr_loc_as_cell!(h_len));
                                                    self.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            _ => {
                                            }
                                        );

                                        if focus < self.heap.len() - 2 {
                                            self.heap.pop();
                                            self.heap.pop();
                                        }

                                        self.pdl.push(self.heap[focus]);
                                        self.pdl.push(heap_loc_as_cell!(h));

                                        return;
                                    }
                                }

                                break 'outer;
                            }
                            _ => {
                                self.fail = true;
                                break 'outer;
                            }
                        );

                        chars_iter.next();
                    }

                    chars_iter.iter.next();

                    self.pdl.push(chars_iter.iter.focus);
                    self.pdl.push(focus);

                    break;
                }
            }
            PStrCmpResult::Unordered => {
                self.pdl.push(pstr_iter1.focus);
                self.pdl.push(pstr_iter2.focus);
            }
        }

        self.heap.pop();
        self.heap.pop();
    }

    fn unify_list_with_occurs_trigger(
        &mut self,
        l1: usize,
        d2: HeapCellValue,
        mut occurs_trigger: impl FnMut(),
    ) {
        read_heap_cell!(d2,
            (HeapCellValueTag::Lis, l2) => {
                for idx in 0..2 {
                    self.pdl.push(heap_loc_as_cell!(l2+idx));
                    self.pdl.push(heap_loc_as_cell!(l1+idx));
                }
            }
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if a2 == 2 && n2 == atom!(".") {
                    for idx in 0..2 {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(l1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr | HeapCellValueTag::PStr) => {
                self.unify_partial_string_with_occurs_check(
                    list_loc_as_cell!(l1),
                    d2,
                    &mut occurs_trigger,
                )
            }
            (HeapCellValueTag::AttrVar, h) => {
                if self.bind_with_occurs_check(Ref::attr_var(h), list_loc_as_cell!(l1)) {
                    occurs_trigger();
                }
            }
            (HeapCellValueTag::Var, h) => {
                if self.bind_with_occurs_check(Ref::heap_cell(h), list_loc_as_cell!(l1)) {
                    occurs_trigger();
                }
            }
            (HeapCellValueTag::StackVar, s) => {
                if self.bind_with_occurs_check(Ref::stack_cell(s), list_loc_as_cell!(l1)) {
                    occurs_trigger();
                }
            }
            _ => {
                self.fail = true;
            }
        )
    }

    pub(super) fn unify_with_occurs_check_loop(&mut self, mut occurs_trigger: impl FnMut()) {
        let mut tabu_list: IndexSet<(usize, usize)> = IndexSet::new();

        // self.fail = false;

        while !(self.pdl.is_empty() || self.fail) {
            let s1 = self.pdl.pop().unwrap();
            let s1 = self.deref(s1);

            let s2 = self.pdl.pop().unwrap();
            let s2 = self.deref(s2);

            if s1 != s2 {
                let d1 = self.store(s1);
                let d2 = self.store(s2);

                read_heap_cell!(d1,
                    (HeapCellValueTag::AttrVar, h) => {
                        if self.bind_with_occurs_check(Ref::attr_var(h), d2) {
                            occurs_trigger();
                        }
                    }
                    (HeapCellValueTag::Var, h) => {
                        if self.bind_with_occurs_check(Ref::heap_cell(h), d2) {
                            occurs_trigger();
                        }
                    }
                    (HeapCellValueTag::StackVar, s) => {
                        if self.bind_with_occurs_check(Ref::stack_cell(s), d2) {
                            occurs_trigger();
                        }
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert!(arity == 0);
                        self.unify_atom(name, d2);
                    }
                    (HeapCellValueTag::Str, s1) => {
                        if d2.is_constant() {
                            self.fail = true;
                            break;
                        }

                        let s2 = s2.get_value() as usize;

                        if tabu_list.contains(&(s1, s2)) {
                            continue;
                        }

                        self.unify_structure_with_occurs_check(s1, d2, &mut occurs_trigger);

                        if !self.fail {
                            tabu_list.insert((s1, s2));
                        }
                    }
                    (HeapCellValueTag::Lis, l1) => {
                        if d2.is_ref() {
                            let l2 = s2.get_value() as usize;

                            if tabu_list.contains(&(l1, l2)) {
                                continue;
                            }

                            tabu_list.insert((l1, l2));
                        }

                        self.unify_list_with_occurs_trigger(l1, d2, &mut occurs_trigger);
                    }
                    (HeapCellValueTag::PStrLoc, pstr1_loc) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::PStrLoc |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::Str,
                             pstr2_loc) => {
                                if tabu_list.contains(&(pstr1_loc, pstr2_loc)) {
                                    continue;
                                }
                            }
                            (HeapCellValueTag::CStr |
                             HeapCellValueTag::AttrVar |
                             HeapCellValueTag::Var |
                             HeapCellValueTag::StackVar) => {
                            }
                            _ => {
                                self.fail = true;
                                break;
                            }
                        );

                        self.unify_partial_string_with_occurs_check(
                            d1,
                            d2,
                            &mut occurs_trigger,
                        );

                        if !self.fail && !d2.is_constant() {
                            tabu_list.insert((pstr1_loc, d2.get_value()));
                        }
                    }
                    (HeapCellValueTag::CStr) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::AttrVar, h) => {
                                self.bind(Ref::attr_var(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::Var, h) => {
                                self.bind(Ref::heap_cell(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::StackVar, s) => {
                                self.bind(Ref::stack_cell(s), d1);
                                continue;
                            }
                            (HeapCellValueTag::Str |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::PStrLoc) => {
                            }
                            _ => {
                                self.fail = true;
                                return;
                            }
                        );

                        self.unify_partial_string(d2, d1);
                    }
                    (HeapCellValueTag::F64, f1) => {
                        self.unify_f64(f1, d2);
                    }
                    (HeapCellValueTag::Fixnum, n1) => {
                        self.unify_fixnum(n1, d2);
                    }
                    (HeapCellValueTag::Char, c1) => {
                        self.unify_char(c1, d2);
                    }
                    (HeapCellValueTag::Cons, ptr_1) => {
                        self.unify_constant(ptr_1, d2);
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
        }
    }

    fn read_s(&mut self) -> HeapCellValue {
        match &self.s {
            &HeapPtr::HeapCell(h) => self.deref(self.heap[h]),
            &HeapPtr::PStrChar(h, n) => {
                read_heap_cell!(self.heap[h],
                    (HeapCellValueTag::PStr, pstr_atom) => {
                        let pstr = PartialString::from(pstr_atom);

                        if let Some(c) = pstr.as_str_from(n).chars().next() {
                            char_as_cell!(c)
                        } else { // if has_tail {
                            self.deref(self.heap[h+1]) // heap_loc_as_cell!(h+1)
                        }
                        // } else {
                        //     empty_list_as_cell!()
                        // }
                    }
                    (HeapCellValueTag::CStr, cstr_atom) => {
                        let pstr = PartialString::from(cstr_atom);

                        if let Some(c) = pstr.as_str_from(n).chars().next() {
                            char_as_cell!(c)
                        } else { // if has_tail {
                            empty_list_as_cell!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                )
            }
            &HeapPtr::PStrLocation(h, n) => {
                read_heap_cell!(self.heap[h],
                    (HeapCellValueTag::PStr, pstr_atom) => {
                        if n < pstr_atom.len() {
                            let h_len = self.heap.len();

                            self.heap.push(pstr_offset_as_cell!(h));
                            self.heap.push(fixnum_as_cell!(Fixnum::build_with(n as i64)));

                            pstr_loc_as_cell!(h_len)
                        } else {
                            self.deref(self.heap[h+1])
                        }
                    }
                    (HeapCellValueTag::CStr, cstr_atom) => {
                        if n < cstr_atom.len() {
                            let h_len = self.heap.len();

                            self.heap.push(pstr_offset_as_cell!(h));
                            self.heap.push(fixnum_as_cell!(Fixnum::build_with(n as i64)));

                            pstr_loc_as_cell!(h_len)
                        } else {
                            empty_list_as_cell!()
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                )
            }
        }
    }

    pub fn compare_term_test(&mut self) -> Option<Ordering> {
        let mut tabu_list = IndexSet::new();

        while !self.pdl.is_empty() {
            let s1 = self.pdl.pop().unwrap();
            let s1 = self.deref(s1);

            let s2 = self.pdl.pop().unwrap();
            let s2 = self.deref(s2);

            if s1 == s2 {
                continue;
            }

            let v1 = self.store(s1);
            let v2 = self.store(s2);

            let order_cat_v1 = v1.order_category();
            let order_cat_v2 = v2.order_category();

            if order_cat_v1 != order_cat_v2 {
                self.pdl.clear();
                return Some(order_cat_v1.cmp(&order_cat_v2));
            }

            match order_cat_v1 {
                Some(TermOrderCategory::Variable) => {
                    let v1 = v1.as_var().unwrap();
                    let v2 = v2.as_var().unwrap();

                    if v1 != v2 {
                        self.pdl.clear();
                        return Some(v1.cmp(&v2));
                    }
                }
                Some(TermOrderCategory::FloatingPoint) => {
                    let v1 = cell_as_f64_ptr!(v1);
                    let v2 = cell_as_f64_ptr!(v2);

                    if v1 != v2 {
                        self.pdl.clear();
                        return Some(v1.cmp(&v2));
                    }
                }
                Some(TermOrderCategory::Integer) => {
                    let v1 = Number::try_from(v1).unwrap();
                    let v2 = Number::try_from(v2).unwrap();

                    if v1 != v2 {
                        self.pdl.clear();
                        return Some(v1.cmp(&v2));
                    }
                }
                Some(TermOrderCategory::Atom) => {
                    read_heap_cell!(v1,
                        (HeapCellValueTag::Atom, (n1, _a1)) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::Atom, (n2, _a2)) => {
                                    if n1 != n2 {
                                        self.pdl.clear();
                                        return Some(n1.cmp(&n2));
                                    }
                                }
                                (HeapCellValueTag::Char, c2) => {
                                    if let Some(c1) = n1.as_char() {
                                        if c1 != c2 {
                                            self.pdl.clear();
                                            return Some(c1.cmp(&c2));
                                        }
                                    } else {
                                        self.pdl.clear();
                                        return Some(Ordering::Greater);
                                    }
                                }
                                _ => {
                                    unreachable!();
                                }
                            )
                        }
                        (HeapCellValueTag::Char, c1) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::Atom, (n2, _a2)) => {
                                    if let Some(c2) = n2.as_char() {
                                        if c1 != c2 {
                                            self.pdl.clear();
                                            return Some(c1.cmp(&c2));
                                        }
                                    } else {
                                        self.pdl.clear();
                                        return Some(Ordering::Less);
                                    }
                                }
                                (HeapCellValueTag::Char, c2) => {
                                    if c1 != c2 {
                                        self.pdl.clear();
                                        return Some(c1.cmp(&c2));
                                    }
                                }
                                _ => {
                                    unreachable!()
                                }
                            )
                        }
                        _ => {
                            unreachable!()
                        }
                    )
                }
                Some(TermOrderCategory::Compound) => {
                    fn stalled_pstr_iter_handler(
                        string_iter: HeapPStrIter,
                        stalled_iter: HeapPStrIter,
                        pdl: &mut Vec<HeapCellValue>,
                    ) -> Option<Ordering> {
                        let l = read_heap_cell!(stalled_iter.focus,
                            (HeapCellValueTag::Str, s) => {
                                let (name, arity) = cell_as_atom_cell!(stalled_iter.heap[s])
                                    .get_name_and_arity();

                                if !(name == atom!(".") && arity == 2) {
                                    pdl.clear();
                                    return Some((atom!("."),2).cmp(&(name,arity)));
                                }

                                s+1
                            }
                            (HeapCellValueTag::Lis, l) => {
                                l
                            }
                            _ => {
                                unreachable!()
                            }
                        );

                        let c2 = stalled_iter.heap[l];
                        let c1 = string_iter.chars().next().unwrap();

                        pdl.push(c2);
                        pdl.push(char_as_cell!(c1));

                        None
                    }

                    fn pstr_comparator(
                        heap: &[HeapCellValue],
                        pdl: &mut Vec<HeapCellValue>,
                        s1: usize,
                        s2: usize,
                    ) -> Option<Ordering> {
                        let mut iter1 = HeapPStrIter::new(heap, s1);
                        let mut iter2 = HeapPStrIter::new(heap, s2);

                        match compare_pstr_prefixes(&mut iter1, &mut iter2) {
                            PStrCmpResult::Ordered(ordering) => Some(ordering),
                            _ => {
                                if iter1.num_steps() == 0 && iter2.num_steps() == 0 {
                                    return match iter2.focus.get_tag() {
                                        HeapCellValueTag::CStr | HeapCellValueTag::PStrLoc => {
                                            let result = stalled_pstr_iter_handler(iter2, iter1, pdl);

                                            if let Some(ordering) = result {
                                                Some(ordering.reverse())
                                            } else {
                                                let pdl_len = pdl.len();
                                                pdl.swap(pdl_len - 2, pdl_len - 1);
                                                result
                                            }
                                        }
                                        _ => {
                                            stalled_pstr_iter_handler(iter1, iter2, pdl)
                                        }
                                    };
                                }

                                pdl.push(iter2.focus);
                                pdl.push(iter1.focus);

                                None
                            }
                        }
                    }

                    read_heap_cell!(v1,
                        (HeapCellValueTag::Lis, l1) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::CStr | HeapCellValueTag::PStrLoc) => {
                                    let h = self.heap.len();

                                    self.heap.push(v1);
                                    self.heap.push(v2);

                                    if let Some(ordering) = pstr_comparator(
                                        &self.heap, &mut self.pdl, h, h+1
                                    ) {
                                        if ordering != Ordering::Equal {
                                            self.heap.pop();
                                            self.heap.pop();

                                            self.pdl.clear();

                                            return Some(ordering);
                                        }
                                    }

                                    self.heap.pop();
                                    self.heap.pop();
                                }
                                (HeapCellValueTag::Lis, l2) => {
                                    if tabu_list.contains(&(l1, l2)) {
                                        continue;
                                    }

                                    tabu_list.insert((l1, l2));

                                    self.pdl.push(self.heap[l2 + 1]);
                                    self.pdl.push(self.heap[l1 + 1]);

                                    self.pdl.push(self.heap[l2]);
                                    self.pdl.push(self.heap[l1]);
                                }
                                (HeapCellValueTag::Str, s2) => {
                                    if tabu_list.contains(&(l1, s2)) {
                                        continue;
                                    }

                                    let (name, arity) = cell_as_atom_cell!(self.heap[s2])
                                        .get_name_and_arity();

                                    match (atom!("."), 2).cmp(&(name, arity)) {
                                        Ordering::Equal => {
                                            tabu_list.insert((l1, s2));

                                            self.pdl.push(self.heap[s2 + 2]);
                                            self.pdl.push(self.heap[l1 + 1]);

                                            self.pdl.push(self.heap[s2 + 1]);
                                            self.pdl.push(self.heap[l1]);
                                        }
                                        ordering => {
                                            self.pdl.clear();
                                            return Some(ordering);
                                        }
                                    }
                                }
                                _ => {
                                    unreachable!();
                                }
                            )
                        }
                        (HeapCellValueTag::CStr | HeapCellValueTag::PStrLoc) => {
                            let h = self.heap.len();

                            self.heap.push(v1);
                            self.heap.push(v2);

                            if let Some(ordering) = pstr_comparator(
                                &self.heap, &mut self.pdl, h, h+1,
                            ) {
                                if ordering != Ordering::Equal {
                                    self.heap.pop();
                                    self.heap.pop();

                                    self.pdl.clear();

                                    return Some(ordering);
                                }
                            }

                            self.heap.pop();
                            self.heap.pop();
                        }
                        (HeapCellValueTag::Str, s1) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::Str, s2) => {
                                    if tabu_list.contains(&(s1, s2)) {
                                        continue;
                                    }

                                    let (n1, a1) = cell_as_atom_cell!(self.heap[s1])
                                        .get_name_and_arity();

                                    let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                                        .get_name_and_arity();

                                    match (n1,a1).cmp(&(n2,a2)) {
                                        Ordering::Equal => {
                                            tabu_list.insert((s1, s2));

                                            for idx in (1 .. a1+1).rev() {
                                                self.pdl.push(self.heap[s2+idx]);
                                                self.pdl.push(self.heap[s1+idx]);
                                            }
                                        }
                                        ordering => {
                                            self.pdl.clear();
                                            return Some(ordering);
                                        }
                                    }
                                }
                                (HeapCellValueTag::Lis, l2) => {
                                    if tabu_list.contains(&(s1, l2)) {
                                        continue;
                                    }

                                    tabu_list.insert((s1, l2));

                                    let (n1, a1) = cell_as_atom_cell!(self.heap[s1])
                                        .get_name_and_arity();

                                    match (n1,a1).cmp(&(atom!("."), 2)) {
                                        Ordering::Equal => {
                                            self.pdl.push(self.heap[l2]);
                                            self.pdl.push(self.heap[s1+1]);

                                            self.pdl.push(self.heap[l2+1]);
                                            self.pdl.push(self.heap[s1+2]);
                                        }
                                        ordering => {
                                            self.pdl.clear();
                                            return Some(ordering);
                                        }
                                    }
                                }
                                (HeapCellValueTag::CStr | HeapCellValueTag::PStrLoc) => {
                                    let h = self.heap.len();

                                    self.heap.push(v1);
                                    self.heap.push(v2);

                                    if let Some(ordering) = pstr_comparator(
                                        &self.heap, &mut self.pdl, h, h+1,
                                    ) {
                                        if ordering != Ordering::Equal {
                                            self.heap.pop();
                                            self.heap.pop();

                                            self.pdl.clear();

                                            return Some(ordering);
                                        }
                                    }

                                    self.heap.pop();
                                    self.heap.pop();
                                }
                                _ => {
                                    unreachable!()
                                }
                            )
                        }
                        _ => {
                            unreachable!()
                        }
                    );
                }
                None => {
                    if v1 != v2 {
                        self.pdl.clear();
                        return None;
                    }
                }
            }
        }

        Some(Ordering::Equal)
    }

    fn increment_s_ptr(&mut self, rhs: usize) {
        match &mut self.s {
            HeapPtr::HeapCell(ref mut h) => {
                *h += rhs;
            }
            &mut HeapPtr::PStrChar(h, ref mut n) | &mut HeapPtr::PStrLocation(h, ref mut n) => {
                read_heap_cell!(self.heap[h],
                    (HeapCellValueTag::PStr | HeapCellValueTag::CStr, pstr_atom) => {
                        let pstr = PartialString::from(pstr_atom);

                        for c in pstr.as_str_from(*n).chars().take(rhs) {
                            *n += c.len_utf8();
                        }

                        self.s = HeapPtr::PStrLocation(h, *n);
                    }
                    _ => {
                        unreachable!()
                    }
                )
            }
        }
    }

    pub(super) fn unwind_trail(
        &mut self,
        a1: usize,
        a2: usize,
        global_variables: &mut GlobalVarDir,
    ) {
        // the sequence is reversed to respect the chronology of trail
        // additions, now that deleted attributes can be undeleted by
        // backtracking.
        for i in (a1..a2).rev() {
            let h = self.trail[i].get_value() as usize;

            match self.trail[i].get_tag() {
                TrailEntryTag::TrailedHeapVar => {
                    self.heap[h] = heap_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedStackVar => {
                    self.stack[h] = stack_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVar => {
                    self.heap[h] = attr_var_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVarHeapLink => {
                    self.heap[h] = heap_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVarListLink => {
                    let l = self.trail[i + 1].get_value();
                    self.heap[h] = list_loc_as_cell!(l);
                }
                TrailEntryTag::TrailedBlackboardEntry => {
                    let key = Atom::from(h);

                    match global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = None,
                        None => unreachable!(),
                    }
                }
                TrailEntryTag::TrailedBlackboardOffset => {
                    let key = Atom::from(h);
                    let value_cell = HeapCellValue::from(u64::from(self.trail[i + 1]));

                    match global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = Some(value_cell),
                        None => unreachable!(),
                    }
                }
        TrailEntryTag::TrailedAttachedValue => {
        }
            }
        }
    }

    pub fn match_partial_string(&mut self, value: HeapCellValue, string: Atom, has_tail: bool) {
        let h = self.heap.len();
        self.heap.push(value);

        let mut heap_pstr_iter = HeapPStrIter::new(&self.heap, h);
        let s = string.as_str();

        match heap_pstr_iter.compare_pstr_to_string(s) {
            Some(PStrPrefixCmpResult { focus, offset, prefix_len }) if prefix_len == s.len() => {
                let focus_addr = self.heap[focus];

                read_heap_cell!(focus_addr,
                    (HeapCellValueTag::PStr | HeapCellValueTag::CStr, pstr_atom) => {
                        if has_tail {
                            self.s = HeapPtr::PStrLocation(focus, offset);
                            self.mode = MachineMode::Read;
                        } else if offset == pstr_atom.len() {
                            let focus_addr = heap_pstr_iter.focus;
                            unify!(self, focus_addr, empty_list_as_cell!());
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::PStrLoc | HeapCellValueTag::PStrOffset, h) => {
                        if has_tail {
                            let (h, _) = pstr_loc_and_offset(&self.heap, h);

                            self.s = HeapPtr::PStrLocation(h, offset);
                            self.mode = MachineMode::Read;
                        } else {
                            let end_cell = heap_pstr_iter.focus;
                            self.fail = end_cell != empty_list_as_cell!();
                        }
                    }
                    _ => {
                        let focus = heap_pstr_iter.focus();

                        if has_tail {
                            self.s = HeapPtr::HeapCell(focus);
                            self.mode = MachineMode::Read;
                        } else {
                            let focus = heap_pstr_iter.focus;
                            unify!(self, focus, empty_list_as_cell!());
                        }
                    }
                );
            }
            Some(PStrPrefixCmpResult { prefix_len, .. }) => {
                // TODO: this is woefully insufficient! you need to
                // match the remaining portion of string if offset <
                // pstr.len().
                let focus = heap_pstr_iter.focus();
                let tail_addr = self.heap[focus];

                let h = self.heap.len();

                let target_cell = if has_tail {
                    self.s = HeapPtr::HeapCell(h + 1);
                    self.mode = MachineMode::Read;

                    put_partial_string(
                        &mut self.heap,
                        &string.as_str()[prefix_len ..],
                        &mut self.atom_tbl,
                    )
                } else {
                    put_complete_string(
                        &mut self.heap,
                        &string.as_str()[prefix_len ..],
                        &mut self.atom_tbl,
                    )
                };

                unify!(self, tail_addr, target_cell);
            }
            None => {
                self.fail = true;
            }
        }
    }

    pub(super) fn write_literal_to_var(&mut self, deref_v: HeapCellValue, lit: HeapCellValue) {
        let store_v = self.store(deref_v);

        read_heap_cell!(lit,
            (HeapCellValueTag::Atom, (atom, arity)) => {
                if arity == 0 {
                    self.unify_atom(atom, store_v);
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Char, c) => {
                self.unify_char(c, store_v);
            }
            (HeapCellValueTag::Fixnum, n) => {
                self.unify_fixnum(n, store_v);
            }
            (HeapCellValueTag::F64, f64_ptr) => {
                self.unify_f64(f64_ptr, store_v);
            }
            (HeapCellValueTag::Cons, ptr) => {
                match_untyped_arena_ptr!(ptr,
                     (ArenaHeaderTag::Integer, n) => {
                         self.unify_big_int(n, store_v);
                     }
                     (ArenaHeaderTag::Rational, r) => {
                         self.unify_rational(r, store_v);
                     }
                     _ => {
                         self.fail = true;
                     }
                )
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                match store_v.get_tag() {
                    HeapCellValueTag::PStrLoc
                    | HeapCellValueTag::Lis
                    | HeapCellValueTag::Str => {
                        self.match_partial_string(store_v, cstr_atom, false);
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            _ => {
                unreachable!()
            }
        )
    }

    pub fn execute_arith_instr(&mut self, instr: &ArithmeticInstruction) {
        let stub_gen = || functor_stub(atom!("is"), 2);

        match instr {
            &ArithmeticInstruction::Add(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(
                    self,
                    try_numeric_result!(add(n1, n2, &mut self.arena), stub_gen)
                );
                self.p += 1;
            }
            &ArithmeticInstruction::Sub(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(
                    self,
                    try_numeric_result!(sub(n1, n2, &mut self.arena), stub_gen)
                );
                self.p += 1;
            }
            &ArithmeticInstruction::Mul(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(
                    self,
                    try_numeric_result!(mul(n1, n2, &mut self.arena), stub_gen)
                );
                self.p += 1;
            }
            &ArithmeticInstruction::Max(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, max(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Min(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, min(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::IntPow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, int_pow(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Gcd(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, gcd(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Pow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, pow(n1, n2, atom!("**")));
                self.p += 1;
            }
            &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                let stub_gen = || functor_stub(atom!("(rdiv)"), 2);

                let r1 = try_or_fail!(self, self.get_rational(a1, stub_gen));
                let r2 = try_or_fail!(self, self.get_rational(a2, stub_gen));

                self.interms[t - 1] = Number::Rational(arena_alloc!(
                    try_or_fail_gen!(self, rdiv(r1, r2)),
                    self.arena
                ));
                self.p += 1;
            }
            &ArithmeticInstruction::IntFloorDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] =
                    try_or_fail_gen!(self, int_floor_div(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::IDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, idiv(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Abs(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = abs(n1, &mut self.arena);
                self.p += 1;
            }
            &ArithmeticInstruction::Sign(ref a1, t) => {
                let n = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = sign(n);
                self.p += 1;
            }
            &ArithmeticInstruction::Neg(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = neg(n1, &mut self.arena);
                self.p += 1;
            }
            &ArithmeticInstruction::BitwiseComplement(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    try_or_fail_gen!(self, bitwise_complement(n1, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Div(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, div(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Shr(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, shr(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Shl(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, shl(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Xor(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, xor(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::And(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, and(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Or(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, or(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Mod(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, modulus(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Rem(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail_gen!(self, remainder(n1, n2, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Cos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, cos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, sin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Tan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, tan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sqrt(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, sqrt(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Log(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, log(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Exp(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, exp(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ACos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, acos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ASin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, asin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail_gen!(self, atan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan2(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail_gen!(self, atan2(n1, n2))));
                self.p += 1;
            }
            &ArithmeticInstruction::Float(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail_gen!(self, float(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Truncate(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = truncate(n1, &mut self.arena);
                self.p += 1;
            }
            &ArithmeticInstruction::Round(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = try_or_fail_gen!(self, round(n1, &mut self.arena));
                self.p += 1;
            }
            &ArithmeticInstruction::Ceiling(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = ceiling(n1, &mut self.arena);
                self.p += 1;
            }
            &ArithmeticInstruction::Floor(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = floor(n1, &mut self.arena);
                self.p += 1;
            }
            &ArithmeticInstruction::Plus(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1;
                self.p += 1;
            }
        };
    }

    pub fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, c, reg) => {
                let value = self.deref(self[reg]);
                self.write_literal_to_var(value, c);
            }
            &FactInstruction::GetList(_, reg) => {
                let deref_v = self.deref(self[reg]);
                let store_v = self.store(deref_v);

                read_heap_cell!(store_v,
                    (HeapCellValueTag::PStrLoc, h) => {
                        let (h, n) = pstr_loc_and_offset(&self.heap, h);

                        self.s = HeapPtr::PStrChar(h, n.get_num() as usize);
                        self.mode = MachineMode::Read;
                    }
                    (HeapCellValueTag::CStr) => {
                        let h = self.heap.len();
                        self.heap.push(store_v);

                        self.s = HeapPtr::PStrChar(h, 0);
                        self.mode = MachineMode::Read;
                    }
                    (HeapCellValueTag::Lis, l) => {
                        self.s = HeapPtr::HeapCell(l);
                        self.mode = MachineMode::Read;
                    }
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                        let h = self.heap.len();

                        self.heap.push(list_loc_as_cell!(h+1));
                        self.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));

                        self.mode = MachineMode::Write;
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &FactInstruction::GetPartialString(_, string, reg, has_tail) => {
                let deref_v = self.deref(self[reg]);
                let store_v = self.store(deref_v);

                read_heap_cell!(store_v,
                    (HeapCellValueTag::Str | HeapCellValueTag::Lis |
                     HeapCellValueTag::PStrLoc | HeapCellValueTag::AttrVar |
                     HeapCellValueTag::StackVar | HeapCellValueTag::Var |
                     HeapCellValueTag::CStr) => {
                        self.match_partial_string(store_v, string, has_tail);
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &FactInstruction::GetStructure(ref ct, arity, reg) => {
                let deref_v = self.deref(self[reg]);
                let store_v = self.store(deref_v);

                read_heap_cell!(store_v,
                    (HeapCellValueTag::Str, a) => {
                        let result = self.heap[a];

                        read_heap_cell!(result,
                            (HeapCellValueTag::Atom, (name, narity)) => {
                                if narity == arity && ct.name() == name {
                                    self.s = HeapPtr::HeapCell(a + 1);
                                    self.mode = MachineMode::Read;
                                } else {
                                    self.fail = true;
                                }
                            }
                            _ => {
                                unreachable!();
                            }
                        );
                    }
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                        let h = self.heap.len();

                        self.heap.push(str_loc_as_cell!(h+1));
                        self.heap.push(atom_as_cell!(ct.name(), arity));

                        self.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));

                        self.mode = MachineMode::Write;
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &FactInstruction::GetVariable(norm, arg) => {
                self[norm] = self.registers[arg];
            }
            &FactInstruction::GetValue(norm, arg) => {
                let norm_addr = self[norm];
                let reg_addr = self.registers[arg];

                unify_fn!(self, norm_addr, reg_addr);
            }
            &FactInstruction::UnifyConstant(v) => {
                match self.mode {
                    MachineMode::Read => {
                        let addr = self.read_s();

                        self.write_literal_to_var(addr, v);
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        self.heap.push(v);
                    }
                };
            }
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        self[reg] = self.read_s();
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let h = self.heap.len();

                        self.heap.push(heap_loc_as_cell!(h));
                        self[reg] = heap_loc_as_cell!(h);
                    }
                };
            }
            &FactInstruction::UnifyLocalValue(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg];
                        let value = self.read_s();

                        unify_fn!(self, reg_addr, value);
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let value = self.store(self.deref(self[reg]));
                        let h = self.heap.len();

                        read_heap_cell!(value,
                            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, hc) => {
                                let value = self.heap[hc];

                                self.heap.push(value);
                                self.increment_s_ptr(1);

                                return;
                            }
                            _ => {
                            }
                        );

                        self.heap.push(heap_loc_as_cell!(h));
                        (self.bind_fn)(self, Ref::heap_cell(h), value);
                    }
                };
            }
            &FactInstruction::UnifyValue(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg];
                        let value = self.read_s();

                        unify_fn!(self, reg_addr, value);
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let h = self.heap.len();
                        self.heap.push(heap_loc_as_cell!(h));

                        let addr = self.store(self[reg]);
                        (self.bind_fn)(self, Ref::heap_cell(h), addr);

                        // the former code of this match arm was:

                        // let addr = self.store(self[reg]);
                        // self.heap.push(HeapCellValue::Addr(addr));

                        // the old code didn't perform the occurs
                        // check when enabled and so it was changed to
                        // the above, which is only slightly less
                        // efficient when the occurs_check is disabled.
                    }
                };
            }
            &FactInstruction::UnifyVoid(n) => {
                match self.mode {
                    MachineMode::Read => {
                        self.increment_s_ptr(n);
                    }
                    MachineMode::Write => {
                        let h = self.heap.len();

                        for i in h..h + n {
                            self.heap.push(heap_loc_as_cell!(i));
                        }
                    }
                };
            }
        };
    }

    pub(super) fn execute_indexing_instr(
        &mut self,
        indexing_lines: &Vec<IndexingLine>,
        code_repo: &CodeRepo,
    ) {
        fn dynamic_external_of_clause_is_valid(
            machine_st: &mut MachineState,
            code: &Code,
            p: usize,
        ) -> bool {
            match &code[p] {
                Line::Choice(ChoiceInstruction::DynamicInternalElse(..)) => {
                    machine_st.dynamic_mode = FirstOrNext::First;
                    return true;
                }
                _ => {}
            }

            match &code[p - 1] {
                &Line::Choice(ChoiceInstruction::DynamicInternalElse(birth, death, _)) => {
                    if birth < machine_st.cc && Death::Finite(machine_st.cc) <= death {
                        return true;
                    } else {
                        return false;
                    }
                }
                _ => {}
            }

            true
        }

        let mut index = 0;
        let addr = match &indexing_lines[0] {
            &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(arg, ..)) => {
                self.store(self.deref(self[temp_v!(arg)]))
            }
            _ => {
                unreachable!()
            }
        };

        loop {
            match &indexing_lines[index] {
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, c, l, s)) => {
                    let offset = read_heap_cell!(addr,
                        (HeapCellValueTag::Var
                         | HeapCellValueTag::StackVar
                         | HeapCellValueTag::AttrVar) => {
                            v
                        }
                        (HeapCellValueTag::PStrLoc
                         | HeapCellValueTag::Lis
                         | HeapCellValueTag::CStr) => {
                            l
                        }
                        (HeapCellValueTag::Fixnum
                         | HeapCellValueTag::Char
                         | HeapCellValueTag::F64) => {
                            c
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            // if arity == 0 { c } else { s }
                            debug_assert!(arity == 0);
                            c
                        }
                        (HeapCellValueTag::Str) => {
                            s
                        }
                        (HeapCellValueTag::Cons, ptr) => {
                            match ptr.get_tag() {
                                ArenaHeaderTag::Rational | ArenaHeaderTag::Integer |
                                ArenaHeaderTag::F64 => {
                                    c
                                }
                                _ => {
                                    IndexingCodePtr::Fail
                                }
                            }
                        }
                        _ => {
                            unreachable!();
                        }
                    );

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            // either points directly to a
                            // DynamicInternalElse, or just ahead of
                            // one. Or neither!
                            let p = self.p.local().abs_loc();

                            if !dynamic_external_of_clause_is_valid(self, &code_repo.code, p + o) {
                                self.fail = true;
                            } else {
                                self.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref hm)) => {
                    let lit = read_heap_cell!(addr,
                        (HeapCellValueTag::Char, c) => {
                            Literal::Char(c)
                        }
                        (HeapCellValueTag::Fixnum, n) => {
                            Literal::Fixnum(n)
                        }
                        (HeapCellValueTag::F64, f) => {
                            Literal::Float(f)
                        }
                        (HeapCellValueTag::Atom, (atom, arity)) => {
                            debug_assert_eq!(arity, 0);
                            Literal::Atom(atom)
                        }
                        (HeapCellValueTag::Cons, cons_ptr) => {
                            match_untyped_arena_ptr!(cons_ptr,
                                 (ArenaHeaderTag::Rational, r) => {
                                     Literal::Rational(r)
                                 }
                                 (ArenaHeaderTag::F64, f) => {
                                     Literal::Float(F64Ptr(f))
                                 }
                                 (ArenaHeaderTag::Integer, n) => {
                                     Literal::Integer(n)
                                 }
                                 _ => {
                                     unreachable!()
                                 }
                            )
                        }
                        _ => {
                            unreachable!()
                        }
                    );

                    let offset = match hm.get(&lit) {
                        Some(offset) => *offset,
                        _ => IndexingCodePtr::Fail,
                    };

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            // either points directly to a
                            // DynamicInternalElse, or just ahead of
                            // one. Or neither!
                            let p = self.p.local().abs_loc();

                            if !dynamic_external_of_clause_is_valid(self, &code_repo.code, p + o) {
                                self.fail = true;
                            } else {
                                self.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref hm)) => {
                    let offset = read_heap_cell!(addr,
                        (HeapCellValueTag::Atom, (name, arity)) => {
                            match hm.get(&(name, arity)) {
                                Some(offset) => *offset,
                                None => IndexingCodePtr::Fail,
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();

                            match hm.get(&(name, arity)) {
                                Some(offset) => *offset,
                                None => IndexingCodePtr::Fail,
                            }
                        }
                        _ => {
                            IndexingCodePtr::Fail
                        }
                    );

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            let p = self.p.local().abs_loc();

                            if !dynamic_external_of_clause_is_valid(self, &code_repo.code, p + o) {
                                self.fail = true;
                            } else {
                                self.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                &IndexingLine::IndexedChoice(_) => {
                    if let LocalCodePtr::DirEntry(p) = self.p.local() {
                        self.p = CodePtr::Local(LocalCodePtr::IndexingBuf(p, index, 0));
                    } else {
                        unreachable!()
                    }

                    break;
                }
                &IndexingLine::DynamicIndexedChoice(_) => {
                    self.dynamic_mode = FirstOrNext::First;

                    if let LocalCodePtr::DirEntry(p) = self.p.local() {
                        self.p = CodePtr::Local(LocalCodePtr::IndexingBuf(p, index, 0));
                    } else {
                        unreachable!()
                    }

                    break;
                }
            }
        }
    }

    pub(super) fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::GetVariable(norm, arg) => {
                self[norm] = self.registers[arg];
            }
            &QueryInstruction::PutConstant(_, c, reg) => {
                self[reg] = c;
            }
            &QueryInstruction::PutList(_, reg) => {
                self[reg] = list_loc_as_cell!(self.heap.len());
            }
            &QueryInstruction::PutPartialString(_, string, reg, has_tail) => {
                let pstr_addr = if has_tail {
                    if string != atom!("") {
                        let h = self.heap.len();
                        self.heap.push(string_as_pstr_cell!(string));

                        // the tail will be pushed by the next
                        // instruction, so don't push one here.

                        pstr_loc_as_cell!(h)
                    } else {
                        empty_list_as_cell!()
                    }
                } else {
                    string_as_cstr_cell!(string)
                };

                self[reg] = pstr_addr;
            }
            &QueryInstruction::PutStructure(ref ct, arity, reg) => {
                let h = self.heap.len();

                self.heap.push(atom_as_cell!(ct.name(), arity));
                self[reg] = str_loc_as_cell!(h);
            }
            &QueryInstruction::PutUnsafeValue(n, arg) => {
                let s = stack_loc!(AndFrame, self.e, n);
                let addr = self.store(self.deref(stack_loc_as_cell!(s)));

                if addr.is_protected(self.e) {
                    self.registers[arg] = addr;
                } else {
                    let h = self.heap.len();

                    self.heap.push(heap_loc_as_cell!(h));
                    (self.bind_fn)(self, Ref::heap_cell(h), addr);

                    self.registers[arg] = heap_loc_as_cell!(h);
                }
            }
            &QueryInstruction::PutValue(norm, arg) => {
                self.registers[arg] = self[norm];
            }
            &QueryInstruction::PutVariable(norm, arg) => {
                match norm {
                    RegType::Perm(n) => {
                        self[norm] = stack_loc_as_cell!(AndFrame, self.e, n);
                        self.registers[arg] = self[norm];
                    }
                    RegType::Temp(_) => {
                        let h = self.heap.len();
                        self.heap.push(heap_loc_as_cell!(h));

                        self[norm] = heap_loc_as_cell!(h);
                        self.registers[arg] = heap_loc_as_cell!(h);
                    }
                };
            }
            &QueryInstruction::SetConstant(c) => {
                self.heap.push(c);
            }
            &QueryInstruction::SetLocalValue(reg) => {
                let addr = self.deref(self[reg]);
                let stored_v = self.store(addr);

                if stored_v.is_stack_var() {
                    let h = self.heap.len();
                    self.heap.push(heap_loc_as_cell!(h));
                    (self.bind_fn)(self, Ref::heap_cell(h), stored_v);
                } else {
                    self.heap.push(stored_v);
                }
            }
            &QueryInstruction::SetVariable(reg) => {
                let h = self.heap.len();
                self.heap.push(heap_loc_as_cell!(h));
                self[reg] = heap_loc_as_cell!(h);
            }
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self.store(self[reg]);
                self.heap.push(heap_val);
            }
            &QueryInstruction::SetVoid(n) => {
                let h = self.heap.len();

                for i in h..h + n {
                    self.heap.push(heap_loc_as_cell!(i));
                }
            }
        }
    }

    pub(super) fn handle_internal_call_n(&mut self, arity: usize) {
        let arity = arity + 1;
        let pred = self.registers[1];

        for i in 2..arity {
            self.registers[i - 1] = self.registers[i];
        }

        if arity > 1 {
            self.registers[arity - 1] = pred;
            return;
        }

        self.fail = true;
    }

    pub(super) fn setup_call_n(&mut self, arity: usize) -> Option<PredicateKey> {
        let addr = self.store(self.deref(self.registers[arity]));

        let (name, narity) = read_heap_cell!(addr,
            (HeapCellValueTag::Str, s) => {
                let (name, narity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();

                if narity + arity > MAX_ARITY {
                    let stub = functor_stub(atom!("call"), arity + 1);
                    let err = self.representation_error(RepFlag::MaxArity);
                    let representation_error = self.error_form(err, stub);

                    self.throw_exception(representation_error);
                    return None;
                }

                for i in (1..arity).rev() {
                    self.registers[i + narity] = self.registers[i];
                }

                for i in 1..narity + 1 {
                    self.registers[i] = self.heap[s + i];
                }

                (name, narity)
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    (name, 0)
                } else {
                    self.fail = true;
                    return None;
                }
            }
            (HeapCellValueTag::Char, c) => {
                (self.atom_tbl.build_with(&c.to_string()), 0)
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar, _h) => {
                let stub = functor_stub(atom!("call"), arity + 1);
                let err = self.instantiation_error();
                let instantiation_error = self.error_form(err, stub);

                self.throw_exception(instantiation_error);
                return None;
            }
            _ => {
                let stub = functor_stub(atom!("call"), arity + 1);
                let err = self.type_error(ValidType::Callable, addr);
                let type_error = self.error_form(err, stub);

                self.throw_exception(type_error);
                return None;
            }
        );

        Some((name, arity + narity - 1))
    }

    #[inline]
    pub fn is_cyclic_term(&mut self, addr: HeapCellValue) -> bool {
        if addr.is_constant() {
            return false;
        }

        let addr = self.store(self.deref(addr));
        let mut iter = stackful_preorder_iter(&mut self.heap, addr);

        while let Some(value) = iter.next() {
            if value.is_forwarded() {
                let value = heap_bound_store(iter.heap, heap_bound_deref(iter.heap, value));

                if value.is_compound() {
                    return true;
                }
            }
        }

        false
    }

    // arg(+N, +Term, ?Arg)
    pub fn try_arg(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("arg"), 3);
        let n = self.store(self.deref(self.registers[1]));

        read_heap_cell!(n,
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                // 8.5.2.3 a)
                let err = self.instantiation_error();
                return Err(self.error_form(err, stub_gen()));
            }
            _ => {
                let n = match Number::try_from(n) {
                    Ok(Number::Fixnum(n)) => Number::Fixnum(n),
                    Ok(Number::Integer(n)) => Number::Integer(n),
                    _ => {
                        let err = self.type_error(ValidType::Integer, n);
                        return Err(self.error_form(err, stub_gen()));
                    }
                };

                if n < 0 {
                    // 8.5.2.3 e)
                    let err = self.domain_error(DomainErrorType::NotLessThanZero, n);
                    return Err(self.error_form(err, stub_gen()));
                }

                let n = match n {
                    Number::Fixnum(n) => n.get_num() as usize,
                    Number::Integer(n) => n.to_usize().unwrap(),
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let term = self.deref(self.registers[2]);

                read_heap_cell!(self.store(term),
                    (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                        let err = self.instantiation_error();
                        return Err(self.error_form(err, stub_gen()));
                    }
                    (HeapCellValueTag::Str, o) => {
                        let arity = cell_as_atom_cell!(self.heap[o]).get_arity();

                        if 1 <= n && n <= arity {
                            let a3 = self.registers[3];
                            unify_fn!(self, a3, heap_loc_as_cell!(o + n));
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::Lis, l) => {
                        if n == 1 || n == 2 {
                            let a3 = self.registers[3];
                            unify_fn!(self, a3, heap_loc_as_cell!(l + n - 1));
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::PStrLoc, pstr_loc) => {
                        if n == 1 || n == 2 {
                            let a3 = self.registers[3];
                            let (h, offset) = pstr_loc_and_offset(&self.heap, pstr_loc);

                            let pstr = cell_as_string!(self.heap[h]);
                            let offset = offset.get_num() as usize;

                            if let Some(c) = pstr.as_str_from(offset).chars().next() {
                                if n == 1 {
                                    self.unify_char(c, a3);
                                } else {
                                    let offset = (offset + c.len_utf8()) as i64;
                                    let h_len = self.heap.len();
                                    let pstr_atom: Atom = pstr.into();

                                    if pstr_atom.len() > offset as usize {
                                        self.heap.push(pstr_offset_as_cell!(h));
                                        self.heap.push(fixnum_as_cell!(Fixnum::build_with(offset)));

                                        unify_fn!(self, pstr_loc_as_cell!(h_len), a3);
                                    } else {
                                        match self.heap[h].get_tag() {
                                            HeapCellValueTag::CStr => {
                                                self.unify_atom(atom!("[]"), self.store(self.deref(a3)));
                                            }
                                            HeapCellValueTag::PStr => {
                                                unify_fn!(self, self.heap[h+1], a3);
                                            }
                                            _ => {
                                                unreachable!();
                                            }
                                        }
                                    }
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::CStr, cstr_atom) => {
                        let cstr = PartialString::from(cstr_atom);

                        if let Some(c) = cstr.as_str_from(0).chars().next() {
                            if n == 1 {
                                self.unify_char(c, self.store(self.deref(self.registers[3])));
                            } else if n == 2 {
                                let offset = c.len_utf8() as i64;
                                let h_len = self.heap.len();

                                if cstr_atom.len() > offset as usize {
                                    self.heap.push(atom_as_cstr_cell!(cstr_atom));
                                    self.heap.push(pstr_offset_as_cell!(h_len));
                                    self.heap.push(fixnum_as_cell!(Fixnum::build_with(offset)));

                                    unify_fn!(self, pstr_loc_as_cell!(h_len+1), self.registers[3]);
                                } else {
                                    self.unify_atom(atom!("[]"), self.store(self.deref(self.registers[3])));
                                }
                            } else {
                                self.fail = true;
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        // 8.5.2.3 d)
                        let err = self.type_error(ValidType::Compound, term);
                        return Err(self.error_form(err, stub_gen()));
                    }
                )
            }
        );

        Ok(())
    }

    pub fn compare_numbers(&mut self, cmp: CompareNumberQT, n1: Number, n2: Number) {
        let ordering = n1.cmp(&n2);

        self.fail = match cmp {
            CompareNumberQT::GreaterThan if ordering == Ordering::Greater => false,
            CompareNumberQT::GreaterThanOrEqual if ordering != Ordering::Less => false,
            CompareNumberQT::LessThan if ordering == Ordering::Less => false,
            CompareNumberQT::LessThanOrEqual if ordering != Ordering::Greater => false,
            CompareNumberQT::NotEqual if ordering != Ordering::Equal => false,
            CompareNumberQT::Equal if ordering == Ordering::Equal => false,
            _ => true,
        };

        self.p += 1;
    }

    pub fn compare_term(&mut self, qt: CompareTermQT) {
        let a1 = self.registers[1];
        let a2 = self.registers[2];

        match compare_term_test!(self, a1, a2) {
            Some(Ordering::Greater) => match qt {
                CompareTermQT::GreaterThan | CompareTermQT::GreaterThanOrEqual => {}
                _ => self.fail = true,
            },
            Some(Ordering::Equal) => match qt {
                CompareTermQT::GreaterThanOrEqual | CompareTermQT::LessThanOrEqual => {}
                _ => self.fail = true,
            },
            Some(Ordering::Less) => match qt {
                CompareTermQT::LessThan | CompareTermQT::LessThanOrEqual => {}
                _ => self.fail = true,
            },
            None => {
                self.fail = true;
            }
        }
    }

    // returns true on failure, false on success.
    pub fn eq_test(&mut self, h1: HeapCellValue, h2: HeapCellValue) -> bool {
        if h1 == h2 {
            return false;
        }

        compare_term_test!(self, h1, h2)
            .map(|o| o != Ordering::Equal)
            .unwrap_or(true)
    }

    pub fn reset_block(&mut self, addr: HeapCellValue) {
        read_heap_cell!(self.store(addr),
            (HeapCellValueTag::Fixnum, n) => {
                self.block = n.get_num() as usize;
            }
            _ => {
                self.fail = true;
            }
        )
    }

    pub fn execute_inlined(&mut self, inlined: &InlinedClauseType) {
        match inlined {
            &InlinedClauseType::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self, self.get_number(at_1));
                let n2 = try_or_fail!(self, self.get_number(at_2));

                self.compare_numbers(cmp, n1, n2);
            }
            &InlinedClauseType::IsAtom(r1) => {
                let d = self.store(self.deref(self[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity == 0 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::Char) => {
                        self.p += 1;
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsAtomic(r1) => {
                let d = self.store(self.deref(self[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Char | HeapCellValueTag::Fixnum | HeapCellValueTag::F64 |
                     HeapCellValueTag::Cons) => {
                        self.p += 1;
                    }
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity == 0 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsInteger(r1) => {
                let d = self.store(self.deref(self[r1]));

                match Number::try_from(d) {
                    Ok(Number::Fixnum(_)) => {
                        self.p += 1;
                    }
                    Ok(Number::Integer(_)) => {
                        self.p += 1;
                    }
                    Ok(Number::Rational(n)) => {
                        if n.denom() == &1 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsCompound(r1) => {
                let d = self.store(self.deref(self[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Str | HeapCellValueTag::Lis |
                     HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr) => {
                        self.p += 1;
                    }
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity > 0 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsFloat(r1) => {
                let d = self.store(self.deref(self[r1]));

                match Number::try_from(d) {
                    Ok(Number::Float(_)) => {
                        self.p += 1;
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsNumber(r1) => {
                let d = self.store(self.deref(self[r1]));

                match Number::try_from(d) {
                    Ok(Number::Fixnum(_)) => {
                        self.p += 1;
                    }
                    Ok(Number::Integer(_)) => {
                        self.p += 1;
                    }
                    Ok(Number::Rational(n)) => {
                        if n.denom() == &1 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    Ok(Number::Float(_)) => {
                        self.p += 1;
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsRational(r1) => {
                let d = self.store(self.deref(self[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Cons, ptr) => {
                        match_untyped_arena_ptr!(ptr,
                             (ArenaHeaderTag::Rational, _r) => {
                                 self.p += 1;
                             }
                             _ => {
                                 self.fail = true;
                             }
                        );
                    }
                    _ => {
                        self.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsNonVar(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d.get_tag() {
                    HeapCellValueTag::AttrVar
                    | HeapCellValueTag::Var
                    | HeapCellValueTag::StackVar => {
                        self.fail = true;
                    }
                    _ => {
                        self.p += 1;
                    }
                }
            }
            &InlinedClauseType::IsVar(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d.get_tag() {
                    HeapCellValueTag::AttrVar
                    | HeapCellValueTag::Var
                    | HeapCellValueTag::StackVar => {
                        self.p += 1;
                    }
                    _ => {
                        self.fail = true;
                    }
                }
            }
        }
    }

    #[inline(always)]
    fn try_functor_compound_case(&mut self, name: Atom, arity: usize) {
        self.try_functor_unify_components(atom_as_cell!(name), arity);
    }

    fn try_functor_unify_components(&mut self, name: HeapCellValue, arity: usize) {
        let a2 = self.deref(self.registers[2]);
        self.write_literal_to_var(a2, name);

        if !self.fail {
            let a3 = self.store(self.deref(self.registers[3]));
            self.unify_fixnum(Fixnum::build_with(arity as i64), a3);
        }
    }

    fn try_functor_fabricate_struct(&mut self, name: Atom, arity: usize, r: Ref) {
        let h = self.heap.len();

        let f_a = if name == atom!(".") && arity == 2 {
            self.heap.push(heap_loc_as_cell!(h));
            self.heap.push(heap_loc_as_cell!(h+1));

            list_loc_as_cell!(h)
        } else {
            self.heap.push(atom_as_cell!(name, arity));

            for i in 0..arity {
                self.heap.push(heap_loc_as_cell!(h + i + 1));
            }

            if arity == 0 {
                heap_loc_as_cell!(h)
            } else {
                str_loc_as_cell!(h)
            }
        };

        (self.bind_fn)(self, r, f_a);
    }

    pub fn try_functor(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("functor"), 3);
        let a1 = self.store(self.deref(self.registers[1]));

        read_heap_cell!(a1,
            (HeapCellValueTag::Cons | HeapCellValueTag::Char | HeapCellValueTag::Fixnum |
             HeapCellValueTag::F64) => {
                self.try_functor_unify_components(a1, 0);
            }
            (HeapCellValueTag::Atom, (_name, arity)) => {
                debug_assert_eq!(arity, 0);
                self.try_functor_unify_components(a1, 0);
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();
                self.try_functor_compound_case(name, arity);
            }
            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr) => {
                self.try_functor_compound_case(atom!("."), 2);
            }
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let deref_name = self.deref(self.registers[2]);
                let store_name = self.store(deref_name);

                let arity = self.store(self.deref(self.registers[3]));

                if store_name.is_var() || arity.is_var() {
                    // 8.5.1.3 a) & 8.5.1.3 b)
                    let err = self.instantiation_error();
                    return Err(self.error_form(err, stub_gen()));
                }

                let arity = match Number::try_from(arity) {
                    Ok(Number::Fixnum(n)) => Some(n.get_num()),
                    Ok(Number::Integer(n)) => n.to_i64(),
                    Ok(Number::Rational(n)) if n.denom() == &1 => n.numer().to_i64(),
                    _ => {
                        let err = self.type_error(ValidType::Integer, arity);
                        return Err(self.error_form(err, stub_gen()));
                    }
                };

                let arity = match arity {
                    Some(arity) => arity,
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                if arity > MAX_ARITY as i64 {
                    // 8.5.1.3 f)
                    let err = self.representation_error(RepFlag::MaxArity);
                    return Err(self.error_form(err, stub_gen()));
                } else if arity < 0 {
                    // 8.5.1.3 g)
                    let arity = Number::Fixnum(Fixnum::build_with(arity));
                    let err = self.domain_error(DomainErrorType::NotLessThanZero, arity);

                    return Err(self.error_form(err, stub_gen()));
                }

                read_heap_cell!(store_name,
                    (HeapCellValueTag::Cons | HeapCellValueTag::Char | HeapCellValueTag::Fixnum |
                     HeapCellValueTag::F64) if arity == 0 => {
                        self.bind(a1.as_var().unwrap(), deref_name);
                    }
                    (HeapCellValueTag::Atom, (name, atom_arity)) => {
                        debug_assert_eq!(atom_arity, 0);
                        self.try_functor_fabricate_struct(
                            name,
                            arity as usize,
                            a1.as_var().unwrap(),
                        );
                    }
                    (HeapCellValueTag::Char, c) => {
                        let c = self.atom_tbl.build_with(&c.to_string());

                        self.try_functor_fabricate_struct(
                            c,
                            arity as usize,
                            a1.as_var().unwrap(),
                        );
                    }
                    _ => {
                        let err = self.type_error(ValidType::Atomic, store_name);
                        return Err(self.error_form(err, stub_gen()));
                    } // 8.5.1.3 c)
                );
            }
            _ => {
                self.fail = true;
            }
        );

        Ok(())
    }

    pub fn try_from_list(
        &mut self,
        value: HeapCellValue,
        stub_gen: impl Fn() -> FunctorStub,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        let deref_v = self.deref(value);
        let store_v = self.store(deref_v);

        read_heap_cell!(store_v,
            (HeapCellValueTag::Lis, l) => {
                self.try_from_inner_list(vec![], l, stub_gen, store_v)
            }
            (HeapCellValueTag::PStrLoc, h) => {
                self.try_from_partial_string(vec![], h, stub_gen, store_v)
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                let err = self.instantiation_error();
                Err(self.error_form(err, stub_gen()))
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if name == atom!("[]") && arity == 0 {
                    Ok(vec![])
                } else {
                    let err = self.type_error(ValidType::List, store_v);
                    Err(self.error_form(err, stub_gen()))
                }
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                let cstr = cstr_atom.as_str();
                Ok(cstr.chars().map(|c| char_as_cell!(c)).collect())
            }
            _ => {
                let err = self.type_error(ValidType::List, store_v);
                Err(self.error_form(err, stub_gen()))
            }
        )
    }

    fn try_from_inner_list(
        &mut self,
        mut result: Vec<HeapCellValue>,
        mut l: usize,
        stub_gen: impl Fn() -> FunctorStub,
        a1: HeapCellValue,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        result.push(self.heap[l]);
        l += 1;

        loop {
            let deref_v = self.deref(self.heap[l]);
            let store_v = self.store(self.heap[l]);

            read_heap_cell!(store_v,
                (HeapCellValueTag::Lis, hcp) => {
                    result.push(self.heap[hcp]);
                    l = hcp + 1;
                }
                (HeapCellValueTag::PStrOffset) => {
                    return self.try_from_partial_string(result, deref_v.get_value(), stub_gen, a1);
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    if name == atom!("[]") && arity == 0 {
                        break;
                    } else {
                        let err = self.type_error(ValidType::List, a1);
                        return Err(self.error_form(err, stub_gen()));
                    }
                }
                _ => {
                    if store_v.is_var() {
                        let err = self.instantiation_error();
                        return Err(self.error_form(err, stub_gen()));
                    } else {
                        let err = self.type_error(ValidType::List, a1);
                        return Err(self.error_form(err, stub_gen()));
                    }
                }
            );
        }

        Ok(result)
    }

    fn try_from_partial_string(
        &mut self,
        mut chars: Vec<HeapCellValue>,
        h: usize,
        stub_gen: impl Fn() -> FunctorStub,
        a1: HeapCellValue,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        let mut heap_pstr_iter = HeapPStrIter::new(&self.heap, h);

        while let Some(iteratee) = heap_pstr_iter.next() {
            match iteratee {
                PStrIteratee::Char(_, c) =>
                    chars.push(char_as_cell!(c)),
                PStrIteratee::PStrSegment(_, pstr_atom, n) => {
                    let pstr = PartialString::from(pstr_atom);
                    chars.extend(pstr.as_str_from(n).chars().map(|c| char_as_cell!(c)));
                }
            }
        }

        match self.heap[h].get_tag() {
            HeapCellValueTag::PStr => {
                if heap_pstr_iter.at_string_terminator() {
                    Ok(chars)
                } else {
                    read_heap_cell!(self.heap[heap_pstr_iter.focus()],
                        (HeapCellValueTag::Lis, l) => {
                            self.try_from_inner_list(chars, l, stub_gen, a1)
                        }
                        (HeapCellValueTag::Atom, (name, arity)) => {
                            if name == atom!(".") && arity == 2 {
                                let l = heap_pstr_iter.focus() + 1;
                                self.try_from_inner_list(chars, l, stub_gen, a1)
                            } else {
                                let err = self.type_error(ValidType::List, a1);
                                Err(self.error_form(err, stub_gen()))
                            }
                        }
                        _ => {
                            let err = self.type_error(ValidType::List, a1);
                            Err(self.error_form(err, stub_gen()))
                        }
                    )
                }
            }
            HeapCellValueTag::CStr => Ok(chars),
            _ => {
                unreachable!()
            }
        }
    }

    // returns true on failure.
    pub fn ground_test(&mut self) -> bool {
        if self.registers[1].is_constant() {
            return false;
        }

        let value = self.store(self.deref(self.registers[1]));

        if value.is_stack_var() {
            return true;
        }

        for v in stackful_preorder_iter(&mut self.heap, value) {
            let v = unmark_cell_bits!(v);

            if v.is_var() {
                return true;
            }
        }

        false
    }

    pub fn integers_to_bytevec(
        &mut self,
        value: HeapCellValue,
        stub_gen: impl Fn() -> FunctorStub,
    ) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();

        match self.try_from_list(value, stub_gen) {
            Err(_) => {
                unreachable!()
            }
            Ok(addrs) => {
                for addr in addrs {
                    let addr = self.store(self.deref(addr));

                    match Number::try_from(addr) {
                        Ok(Number::Fixnum(n)) => match u8::try_from(n.get_num()) {
                            Ok(b) => bytes.push(b),
                            Err(_) => {}
                        },
                        Ok(Number::Integer(n)) => {
                            if let Some(b) = n.to_u8() {
                                bytes.push(b);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        bytes
    }

    // see 8.4.4.3 of Draft Technical Corrigendum 2 for an error guide.
    pub fn project_onto_key(&mut self, value: HeapCellValue) -> Result<HeapCellValue, MachineStub> {
        let stub_gen = || functor_stub(atom!("keysort"), 2);
        let store_v = self.store(self.deref(value));

        if store_v.is_var() {
            let err = self.instantiation_error();
            return Err(self.error_form(err, stub_gen()));
        }

        read_heap_cell!(store_v,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s]).get_name_and_arity();

                if name == atom!("-") && arity == 2 {
                    Ok(heap_loc_as_cell!(s + 1))
                } else {
                    let err = self.type_error(ValidType::Pair, self.heap[s]);
                    Err(self.error_form(err, stub_gen()))
                }
            }
            _ => {
                let err = self.type_error(ValidType::Pair, store_v);
                Err(self.error_form(err, stub_gen()))
            }
        )
    }

    pub fn setup_built_in_call(&mut self, ct: BuiltInClauseType) {
        self.num_of_args = ct.arity();
        self.b0 = self.b;

        self.p = CodePtr::BuiltInClause(ct, self.p.local());
    }

    pub fn deallocate(&mut self) {
        let e = self.e;
        let frame = self.stack.index_and_frame(e);

        self.cp = frame.prelude.cp;
        self.e = frame.prelude.e;

        if e > self.b {
            self.stack.truncate(e);
        }

        self.p += 1;
    }

    fn throw_interrupt_exception(&mut self) {
        let err = self.interrupt_error();
        let src = functor_stub(atom!("repl"), 0);
        let err = self.error_form(err, src);

        self.throw_exception(err);
    }

    fn handle_call_clause(
        &mut self,
        indices: &mut IndexStore,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        cut_policy: &mut Box<dyn CutPolicy>,
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
        ct: &ClauseType,
        arity: usize,
        lco: bool,
        use_default_cp: bool,
    ) {
        let interrupted = INTERRUPT.load(std::sync::atomic::Ordering::Relaxed);

        match INTERRUPT.compare_exchange(
            interrupted,
            false,
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
        ) {
            Ok(interruption) => {
                if interruption {
                    self.throw_interrupt_exception();
                    return;
                }
            }
            Err(_) => unreachable!(),
        }

        let mut default_call_policy: Box<dyn CallPolicy> = Box::new(DefaultCallPolicy {});

        let call_policy = if use_default_cp {
            &mut default_call_policy
        } else {
            call_policy
        };

        self.last_call = lco;

        match ct {
            &ClauseType::BuiltIn(ref ct) => try_or_fail!(
                self,
                call_policy.call_builtin(
                    self,
                    ct,
                    &indices.code_dir,
                    &indices.op_dir,
                    &indices.stream_aliases,
                )
            ),
            &ClauseType::CallN => try_or_fail!(
                self,
                call_policy.call_n(
                    self,
                    arity,
                    &indices.code_dir,
                    &indices.op_dir,
                    &indices.stream_aliases,
                )
            ),
            &ClauseType::Inlined(ref ct) => {
                self.execute_inlined(ct);

                if lco {
                    self.p = CodePtr::Local(self.cp);
                }
            }
            &ClauseType::Named(ref name, _, ref idx) => {
                try_or_fail!(self, call_policy.context_call(self, *name, arity, idx))
            }
            &ClauseType::System(ref ct) => try_or_fail!(
                self,
                self.system_call(
                    ct,
                    code_repo,
                    indices,
                    call_policy,
                    cut_policy,
                    current_input_stream,
                    current_output_stream,
                )
            ),
        };

        self.last_call = false;
    }

    pub fn execute_ctrl_instr(
        &mut self,
        indices: &mut IndexStore,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        cut_policy: &mut Box<dyn CutPolicy>,
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
        instr: &ControlInstruction,
    ) {
        match instr {
            &ControlInstruction::Allocate(num_cells) => {
                self.allocate(num_cells);
            }
            &ControlInstruction::CallClause(ref ct, arity, _, lco, use_default_cp) => self
                .handle_call_clause(
                    indices,
                    code_repo,
                    call_policy,
                    cut_policy,
                    current_input_stream,
                    current_output_stream,
                    ct,
                    arity,
                    lco,
                    use_default_cp,
                ),
            &ControlInstruction::Deallocate => self.deallocate(),
            &ControlInstruction::JmpBy(arity, offset, _, lco) => {
                if !lco {
                    self.cp.assign_if_local(self.p.clone() + 1);
                }

                self.num_of_args = arity;
                self.b0 = self.b;
                self.p += offset;
            }
            &ControlInstruction::RevJmpBy(offset) => {
                self.p -= offset;
            }
            &ControlInstruction::Proceed => {
                self.p = CodePtr::Local(self.cp);
            }
        };
    }

    pub(super) fn execute_dynamic_indexed_choice_instr(
        &mut self,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        global_variables: &mut GlobalVarDir,
    ) {
        let p = self.p.local();

        match code_repo.find_living_dynamic(p, self.cc) {
            Some((offset, oi, ii, is_next_clause)) => {
                self.p = CodePtr::Local(LocalCodePtr::IndexingBuf(p.abs_loc(), oi, ii));

                match self.dynamic_mode {
                    FirstOrNext::First if !is_next_clause => {
                        self.p = CodePtr::Local(LocalCodePtr::DirEntry(p.abs_loc() + offset));
                    }
                    FirstOrNext::First => {
                        // there's a leading DynamicElse that sets self.cc.
                        // self.cc = self.global_clock;

                        match code_repo.find_living_dynamic(
                            LocalCodePtr::IndexingBuf(p.abs_loc(), oi, ii + 1),
                            self.cc,
                        ) {
                            Some(_) => {
                                self.registers[self.num_of_args + 1] =
                                    fixnum_as_cell!(Fixnum::build_with(self.cc as i64));
                                self.num_of_args += 1;

                                self.execute_indexed_choice_instr(
                                    &IndexedChoiceInstruction::Try(offset),
                                    call_policy,
                                    global_variables,
                                );

                                self.num_of_args -= 1;
                            }
                            None => {
                                self.p =
                                    CodePtr::Local(LocalCodePtr::DirEntry(p.abs_loc() + offset));
                            }
                        }
                    }
                    FirstOrNext::Next => {
                        let n = self
                            .stack
                            .index_or_frame(self.b)
                            .prelude
                            .univ_prelude
                            .num_cells;

                        self.cc = cell_as_fixnum!(self.stack[n - 1]).get_num() as usize;

                        if is_next_clause {
                            match code_repo.find_living_dynamic(
                                LocalCodePtr::IndexingBuf(p.abs_loc(), oi, ii + 1),
                                self.cc,
                            ) {
                                Some(_) => {
                                    try_or_fail!(
                                        self,
                                        call_policy.retry(self, offset, global_variables,)
                                    )
                                }
                                None => {
                                    try_or_fail!(
                                        self,
                                        call_policy.trust(self, offset, global_variables,)
                                    )
                                }
                            }
                        } else {
                            try_or_fail!(self, call_policy.trust(self, offset, global_variables))
                        }
                    }
                }
            }
            None => {
                self.fail = true;
            }
        }

        self.dynamic_mode = FirstOrNext::Next;
    }

    pub(super) fn execute_indexed_choice_instr(
        &mut self,
        instr: &IndexedChoiceInstruction,
        call_policy: &mut Box<dyn CallPolicy>,
        global_variables: &mut GlobalVarDir,
    ) {
        match instr {
            &IndexedChoiceInstruction::Try(offset) => {
                let n = self.num_of_args;
                let b = self.stack.allocate_or_frame(n);
                let or_frame = self.stack.index_or_frame_mut(b);

                or_frame.prelude.univ_prelude.num_cells = n;
                or_frame.prelude.e = self.e;
                or_frame.prelude.cp = self.cp;
                or_frame.prelude.b = self.b;
                or_frame.prelude.bp = self.p.local() + 1;
                or_frame.prelude.tr = self.tr;
                or_frame.prelude.h = self.heap.len();
                or_frame.prelude.b0 = self.b0;

                self.b = b;

                for i in 1..n + 1 {
                    self.stack.index_or_frame_mut(b)[i - 1] = self.registers[i];
                }

                self.hb = self.heap.len();
                self.p = CodePtr::Local(dir_entry!(self.p.local().abs_loc() + offset));
            }
            &IndexedChoiceInstruction::Retry(l) => {
                try_or_fail!(self, call_policy.retry(self, l, global_variables));
            }
            &IndexedChoiceInstruction::Trust(l) => {
                try_or_fail!(self, call_policy.trust(self, l, global_variables));
            }
        };
    }

    pub(super) fn execute_choice_instr(
        &mut self,
        instr: &ChoiceInstruction,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        global_variables: &mut GlobalVarDir,
    ) {
        match instr {
            &ChoiceInstruction::DynamicElse(..) => {
                if let FirstOrNext::First = self.dynamic_mode {
                    self.cc = self.global_clock;
                }

                let p = self.p.local().abs_loc();

                match code_repo.find_living_dynamic_else(p, self.cc) {
                    Some((p, next_i)) => {
                        self.p = CodePtr::Local(LocalCodePtr::DirEntry(p));

                        match self.dynamic_mode {
                            FirstOrNext::First if next_i == 0 => {
                                self.p = CodePtr::Local(LocalCodePtr::DirEntry(p + 1));
                            }
                            FirstOrNext::First => {
                                self.cc = self.global_clock;

                                match code_repo.find_living_dynamic_else(p + next_i, self.cc) {
                                    Some(_) => {
                                        self.registers[self.num_of_args + 1] =
                                            fixnum_as_cell!(Fixnum::build_with(self.cc as i64));
                                        self.num_of_args += 1;

                                        self.execute_choice_instr(
                                            &ChoiceInstruction::TryMeElse(next_i),
                                            code_repo,
                                            call_policy,
                                            global_variables,
                                        );

                                        self.num_of_args -= 1;
                                    }
                                    None => {
                                        self.p += 1;
                                    }
                                }
                            }
                            FirstOrNext::Next => {
                                let n = self
                                    .stack
                                    .index_or_frame(self.b)
                                    .prelude
                                    .univ_prelude
                                    .num_cells;

                                self.cc = cell_as_fixnum!(self.stack.index_or_frame(self.b)[n - 1])
                                    .get_num() as usize;

                                if next_i > 0 {
                                    match code_repo.find_living_dynamic_else(p + next_i, self.cc) {
                                        Some(_) => {
                                            try_or_fail!(
                                                self,
                                                call_policy.retry_me_else(
                                                    self,
                                                    next_i,
                                                    global_variables,
                                                )
                                            )
                                        }
                                        None => {
                                            try_or_fail!(
                                                self,
                                                call_policy.trust_me(self, global_variables)
                                            )
                                        }
                                    }
                                } else {
                                    try_or_fail!(self, call_policy.trust_me(self, global_variables))
                                }
                            }
                        }
                    }
                    None => {
                        self.fail = true;
                    }
                }

                self.dynamic_mode = FirstOrNext::Next;
            }
            &ChoiceInstruction::DynamicInternalElse(..) => {
                let p = self.p.local().abs_loc();

                match code_repo.find_living_dynamic_else(p, self.cc) {
                    Some((p, next_i)) => {
                        self.p = CodePtr::Local(LocalCodePtr::DirEntry(p));

                        match self.dynamic_mode {
                            FirstOrNext::First if next_i == 0 => {
                                self.p = CodePtr::Local(LocalCodePtr::DirEntry(p + 1));
                            }
                            FirstOrNext::First => {
                                match code_repo.find_living_dynamic_else(p + next_i, self.cc) {
                                    Some(_) => {
                                        self.registers[self.num_of_args + 1] =
                                            fixnum_as_cell!(Fixnum::build_with(self.cc as i64));
                                        self.num_of_args += 1;

                                        self.execute_choice_instr(
                                            &ChoiceInstruction::TryMeElse(next_i),
                                            code_repo,
                                            call_policy,
                                            global_variables,
                                        );

                                        self.num_of_args -= 1;
                                    }
                                    None => {
                                        self.p += 1;
                                    }
                                }
                            }
                            FirstOrNext::Next => {
                                let n = self
                                    .stack
                                    .index_or_frame(self.b)
                                    .prelude
                                    .univ_prelude
                                    .num_cells;

                                self.cc = cell_as_fixnum!(self.stack.index_or_frame(self.b)[n - 1])
                                    .get_num() as usize;

                                if next_i > 0 {
                                    match code_repo.find_living_dynamic_else(p + next_i, self.cc) {
                                        Some(_) => {
                                            try_or_fail!(
                                                self,
                                                call_policy.retry_me_else(
                                                    self,
                                                    next_i,
                                                    global_variables,
                                                )
                                            )
                                        }
                                        None => {
                                            try_or_fail!(
                                                self,
                                                call_policy.trust_me(self, global_variables,)
                                            )
                                        }
                                    }
                                } else {
                                    try_or_fail!(
                                        self,
                                        call_policy.trust_me(self, global_variables,)
                                    )
                                }
                            }
                        }
                    }
                    None => {
                        self.fail = true;
                    }
                }

                self.dynamic_mode = FirstOrNext::Next;
            }
            &ChoiceInstruction::TryMeElse(offset) => {
                let n = self.num_of_args;
                let b = self.stack.allocate_or_frame(n);
                let or_frame = self.stack.index_or_frame_mut(b);

                or_frame.prelude.univ_prelude.num_cells = n;
                or_frame.prelude.e = self.e;
                or_frame.prelude.cp = self.cp;
                or_frame.prelude.b = self.b;
                or_frame.prelude.bp = self.p.local() + offset;
                or_frame.prelude.tr = self.tr;
                or_frame.prelude.h = self.heap.len();
                or_frame.prelude.b0 = self.b0;

                self.b = b;

                for i in 1..n + 1 {
                    self.stack.index_or_frame_mut(b)[i - 1] = self.registers[i];
                }

                self.hb = self.heap.len();
                self.p += 1;
            }
            &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(
                    self,
                    call_policy.retry_me_else(self, offset, global_variables)
                )
            }
            &ChoiceInstruction::DefaultTrustMe(_) => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(self, call_policy.trust_me(self, global_variables))
            }
            &ChoiceInstruction::RetryMeElse(offset) => {
                try_or_fail!(
                    self,
                    call_policy.retry_me_else(self, offset, global_variables)
                )
            }
            &ChoiceInstruction::TrustMe(_) => {
                try_or_fail!(self, call_policy.trust_me(self, global_variables))
            }
        }
    }

    pub(super) fn execute_cut_instr(
        &mut self,
        instr: &CutInstruction,
        cut_policy: &mut Box<dyn CutPolicy>,
    ) {
        match instr {
            &CutInstruction::NeckCut => {
                let b = self.b;
                let b0 = self.b0;

                if b > b0 {
                    self.b = b0;

                    if b > self.e {
                        self.stack.truncate(b);
                    }
                }

                self.p += 1;
            }
            &CutInstruction::GetLevel(r) => {
                let b0 = self.b0;

                self[r] = fixnum_as_cell!(Fixnum::build_with(b0 as i64));
                self.p += 1;
            }
            &CutInstruction::GetLevelAndUnify(r) => {
                let b0 = self[perm_v!(1)];
                let a = self[r];

                unify_fn!(self, a, b0);
                self.p += 1;
            }
            &CutInstruction::Cut(r) => {
                if !cut_policy.cut(self, r) {
                    self.p += 1;
                }
            }
        }
    }
}
