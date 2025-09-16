use crate::arena::*;
use crate::forms::*;
use crate::heap_iter::{stackful_preorder_iter, NonListElider};
use crate::machine::machine_state::*;
use crate::machine::*;
use crate::offset_table::*;
use crate::types::*;

use std::ops::{Deref, DerefMut};

use derive_more::*;
use fxhash::FxBuildHasher;
use indexmap::IndexSet;
use num_order::NumOrd;

impl MachineState {
    pub(crate) fn partial_string_to_pdl(&mut self, pstr_loc: usize, l: usize) {
        let (c, succ_cell) = self.heap.last_str_char_and_tail(pstr_loc);

        self.pdl.push(heap_loc_as_cell!(l + 1));
        self.pdl.push(succ_cell);

        self.pdl.push(heap_loc_as_cell!(l));
        self.pdl.push(char_as_cell!(c));
    }
}

pub(crate) trait Unifier: DerefMut<Target = MachineState> {
    fn unify_structure(&mut self, s1: usize, value: HeapCellValue) {
        // s1 is the value of a STR cell.
        let (n1, a1) = cell_as_atom_cell!(self.heap[s1]).get_name_and_arity();

        read_heap_cell!(value,
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if n1 == n2 && a1 == a2 {
                    for idx in (0..a1).rev() {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Lis, l2) => {
                if a1 == 2 && n1 == atom!(".") {
                    for idx in (0..2).rev() {
                        self.pdl.push(heap_loc_as_cell!(l2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(s1+1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Atom, (n2, a2)) => {
                self.fail = !(a1 == 0 && a2 == 0 && n1 == n2);
            }
            (HeapCellValueTag::AttrVar, h) => {
                Self::bind(self, Ref::attr_var(h), str_loc_as_cell!(s1));
            }
            (HeapCellValueTag::Var, h) => {
                Self::bind(self, Ref::heap_cell(h), str_loc_as_cell!(s1));
            }
            (HeapCellValueTag::StackVar, s) => {
                Self::bind(self, Ref::stack_cell(s), str_loc_as_cell!(s1));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn unify_list(&mut self, l1: usize, value: HeapCellValue) {
        read_heap_cell!(value,
            (HeapCellValueTag::Lis, l2) => {
                for idx in (0..2).rev() {
                    self.pdl.push(heap_loc_as_cell!(l2 + idx));
                    self.pdl.push(heap_loc_as_cell!(l1 + idx));
                }
            }
            (HeapCellValueTag::Str, s2) => {
                let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                    .get_name_and_arity();

                if a2 == 2 && n2 == atom!(".") {
                    for idx in (0..2).rev() {
                        self.pdl.push(heap_loc_as_cell!(s2+1+idx));
                        self.pdl.push(heap_loc_as_cell!(l1+idx));
                    }
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::PStrLoc, l) => {
                Self::unify_partial_string(self, l, list_loc_as_cell!(l1))
            }
            (HeapCellValueTag::AttrVar, h) => {
                Self::bind(self, Ref::attr_var(h), list_loc_as_cell!(l1));
            }
            (HeapCellValueTag::Var, h) => {
                Self::bind(self, Ref::heap_cell(h), list_loc_as_cell!(l1));
            }
            (HeapCellValueTag::StackVar, s) => {
                Self::bind(self, Ref::stack_cell(s), list_loc_as_cell!(l1));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn unify_partial_string(&mut self, pstr_loc: usize, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, pstr_loc_as_cell!(pstr_loc));
            return;
        }

        let machine_st = self.deref_mut();

        read_heap_cell!(value,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(machine_st.heap[s])
                    .get_name_and_arity();

                if name == atom!(".") && arity == 2 {
                    machine_st.partial_string_to_pdl(pstr_loc, s+1);
                } else {
                    machine_st.fail = true;
                }
            }
            (HeapCellValueTag::Lis, l) => {
                machine_st.partial_string_to_pdl(pstr_loc, l);
            }
            (HeapCellValueTag::PStrLoc, other_pstr_loc) => {
                match machine_st.heap.compare_pstr_segments(pstr_loc, other_pstr_loc) {
                    PStrSegmentCmpResult::Continue(v1, v2) => {
                        machine_st.pdl.push(v1.offset_by(pstr_loc));
                        machine_st.pdl.push(v2.offset_by(other_pstr_loc));
                    }
                    _ => {
                        machine_st.fail = true;
                    }
                }
            }
            _ => {
                machine_st.fail = true;
            }
        );
    }

    fn unify_ginteger(&mut self, n: GInteger, value: HeapCellValue) {
        match n {
            GInteger::Integer(integer) => self.unify_big_int(integer, value),
            GInteger::Fixnum(fixnum) => self.unify_fixnum(fixnum, value),
        }
    }

    fn unify_atom(&mut self, atom: Atom, value: HeapCellValue) {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                self.fail = !(arity == 0 && name == atom);
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                self.fail = !(arity == 0 && name == atom);
            }
            (HeapCellValueTag::AttrVar, h) => {
                Self::bind(self, Ref::attr_var(h), atom_as_cell!(atom));
            }
            (HeapCellValueTag::Var, h) => {
                Self::bind(self, Ref::heap_cell(h), atom_as_cell!(atom));
            }
            (HeapCellValueTag::StackVar, s) => {
                Self::bind(self, Ref::stack_cell(s), atom_as_cell!(atom));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn unify_char(&mut self, c: char, value: HeapCellValue) {
        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if let Some(c2) = name.as_char() {
                    self.fail = !(c == c2 && arity == 0);
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if let Some(c2) = name.as_char() {
                    self.fail = !(c == c2 && arity == 0);
                } else {
                    self.fail = true;
                }
            }
            (HeapCellValueTag::AttrVar, h) => {
                Self::bind(self, Ref::attr_var(h), char_as_cell!(c));
            }
            (HeapCellValueTag::Var, h) => {
                Self::bind(self, Ref::heap_cell(h), char_as_cell!(c));
            }
            (HeapCellValueTag::StackVar, s) => {
                Self::bind(self, Ref::stack_cell(s), char_as_cell!(c));
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn unify_fixnum(&mut self, n1: Fixnum, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, fixnum_as_cell!(n1));
            return;
        }

        let machine_st = self.deref();

        match Number::try_from((value, &machine_st.arena.f64_tbl)) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if n1.get_num() == n2.get_num() => {}
                Number::Integer(n2) if (*n2).num_eq(&n1.get_num()) => {}
                Number::Rational(n2) if (*n2).num_eq(&Integer::from(n1.get_num())) => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    fn unify_big_integer(&mut self, n1: TypedArenaPtr<Integer>, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, typed_arena_ptr_as_cell!(n1));
            return;
        }

        let machine_st = self.deref();

        match Number::try_from((value, &machine_st.arena.f64_tbl)) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if (*n1).num_eq(&n2.get_num()) => {}
                Number::Integer(n2) if (*n1).num_eq(&*n2) => {}
                Number::Rational(n2) if (*n2).num_eq(&*n1) => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    fn unify_big_rational(&mut self, n1: TypedArenaPtr<Rational>, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, typed_arena_ptr_as_cell!(n1));
            return;
        }

        let machine_st = self.deref_mut();

        match Number::try_from((value, &machine_st.arena.f64_tbl)) {
            Ok(n2) => match n2 {
                Number::Fixnum(n2) if (*n1).num_eq(&Integer::from(n2.get_num())) => {}
                Number::Integer(n2) if (*n1).num_eq(&*n2) => {}
                Number::Rational(n2) if n1 == n2 => {}
                _ => {
                    self.fail = true;
                }
            },
            Err(_) => {
                self.fail = true;
            }
        }
    }

    fn unify_f64(&mut self, f1: F64Offset, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, HeapCellValue::from(f1));
            return;
        }

        read_heap_cell!(value,
            (HeapCellValueTag::F64Offset, f2) => {
                let machine_st = self.deref_mut();

                let f1 = machine_st.arena.f64_tbl.get_entry(f1);
                let f2 = machine_st.arena.f64_tbl.get_entry(f2);

                self.fail = f1 != f2;
            }
            _ => {
                self.fail = true;
            }
        );
    }

    fn unify_constant(&mut self, ptr: UntypedArenaPtr, value: HeapCellValue) {
        if let Some(ptr2) = value.to_untyped_arena_ptr() {
            if ptr.get_ptr() == ptr2.get_ptr() {
                return;
            }
        }

        match_untyped_arena_ptr!(ptr,
             (ArenaHeaderTag::Integer, int_ptr) => {
                 Self::unify_big_integer(self, int_ptr, value);
             }
             (ArenaHeaderTag::Rational, rat_ptr) => {
                 Self::unify_big_rational(self, rat_ptr, value);
             }
             (ArenaHeaderTag::Stream, stream) => {
                 read_heap_cell!(value,
                     (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                         Self::bind(self, value.as_var().unwrap(), untyped_arena_ptr_as_cell!(ptr));
                     }
                     (HeapCellValueTag::Atom, (name, arity)) => {
                         if arity > 0 {
                             self.fail = true;
                         } else {
                             let stream_options = stream.options();

                             if let Some(alias) = stream_options.get_alias() {
                                 self.fail = name != alias;
                             } else {
                                 self.fail = true;
                             }
                         }
                     }
                     _ => {
                         self.fail = true;
                     }
                 );
             }
             _ => {
                 if let Some(r) = value.as_var() {
                     Self::bind(self, r, untyped_arena_ptr_as_cell!(ptr));
                 } else {
                     self.fail = true;
                 }
             }
        );
    }

    fn unify_internal(&mut self) {
        let mut tabu_list = IndexSet::with_hasher(FxBuildHasher::default());

        while !(self.pdl.is_empty() || self.fail) {
            let s1 = self.pdl.pop().unwrap();
            let s1 = (self.deref() as &MachineState).deref(s1);

            let s2 = self.pdl.pop().unwrap();
            let s2 = (self.deref() as &MachineState).deref(s2);

            if s1 != s2 {
                let d1 = self.store(s1);
                let d2 = self.store(s2);

                read_heap_cell!(d1,
                    (HeapCellValueTag::AttrVar, h) => {
                        Self::bind(self, Ref::attr_var(h), d2);
                    }
                    (HeapCellValueTag::Var, h) => {
                        Self::bind(self, Ref::heap_cell(h), d2);
                    }
                    (HeapCellValueTag::StackVar, s) => {
                        Self::bind(self, Ref::stack_cell(s), d2);
                    }
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);
                        Self::unify_atom(self, name, d2);
                    }
                    (HeapCellValueTag::Str, s1) => {
                        if tabu_list.contains(&(d1, d2)) {
                            continue;
                        }

                        Self::unify_structure(self, s1, d2);

                        if !self.fail {
                            let d2 = self.store(d2);
                            tabu_list.insert((d1, d2));
                        }
                    }
                    (HeapCellValueTag::Lis, l1) => {
                        if d2.is_ref() && tabu_list.contains(&(d1, d2)) {
                            continue;
                        }

                        Self::unify_list(self, l1, d2);

                        if !self.fail {
                            let d2 = self.store(d2);
                            tabu_list.insert((d1, d2));
                        }
                    }
                    (HeapCellValueTag::PStrLoc, l) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::PStrLoc |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::Str) => {
                                if tabu_list.contains(&(d1, d2)) {
                                    continue;
                                }
                            }
                            (HeapCellValueTag::AttrVar |
                             HeapCellValueTag::Var |
                             HeapCellValueTag::StackVar) => {
                            }
                            _ => {
                                self.fail = true;
                                break;
                            }
                        );

                        Self::unify_partial_string(self, l, d2);

                        if !self.fail && !d2.is_constant() {
                            let d2 = self.store(d2);
                            tabu_list.insert((d1, d2));
                        }
                    }
                    (HeapCellValueTag::F64Offset, f1) => {
                        Self::unify_f64(self, f1, d2);
                    }
                    (HeapCellValueTag::Fixnum, n1) => {
                        Self::unify_fixnum(self, n1, d2);
                    }
                    (HeapCellValueTag::Cons, ptr_1) => {
                        Self::unify_constant(self, ptr_1, d2);
                    }
                    (HeapCellValueTag::CutPoint, n1) => {
                        Self::unify_fixnum(self, n1, d2);
                    }
                    _ => {
                        unreachable!();
                    }
                );
            }
        }
    }

    fn bind(&mut self, r: Ref, value: HeapCellValue);
}

#[inline]
fn bind_with_occurs_check<U: Unifier>(unifier: &mut U, r: Ref, value: HeapCellValue) -> bool {
    if let RefTag::StackCell = r.get_tag() {
        // local variable optimization -- r cannot occur in the
        // heap structure bound to value, so don't bother
        // traversing value.
        U::bind(unifier, r, value);
        return false;
    }

    let mut occurs_triggered = false;

    if !value.is_constant() {
        let machine_st: &mut MachineState = unifier.deref_mut();
        machine_st.heap[0] = value;

        for cell in
            stackful_preorder_iter::<NonListElider>(&mut machine_st.heap, &mut machine_st.stack, 0)
        {
            let cell = unmark_cell_bits!(cell);

            if let Some(inner_r) = cell.as_var() {
                if r == inner_r {
                    occurs_triggered = true;
                    break;
                }
            }
        }
    }

    if occurs_triggered {
        unifier.fail = true;
    } else {
        U::bind(unifier, r, value);
    }

    occurs_triggered
}

#[derive(Deref, DerefMut)]
#[deref(forward)]
pub(crate) struct DefaultUnifier<'a> {
    machine_st: &'a mut MachineState,
}

impl<'a> From<&'a mut MachineState> for DefaultUnifier<'a> {
    #[inline(always)]
    fn from(machine_st: &'a mut MachineState) -> Self {
        Self { machine_st }
    }
}

impl<'a> Unifier for DefaultUnifier<'a> {
    fn bind(&mut self, r: Ref, value: HeapCellValue) {
        self.machine_st.bind(r, value);
    }
}

pub(crate) struct CompositeUnifierForOccursCheck<U> {
    unifier: U,
}

impl<U: Unifier> Deref for CompositeUnifierForOccursCheck<U> {
    type Target = MachineState;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.unifier.deref()
    }
}

impl<U: Unifier> DerefMut for CompositeUnifierForOccursCheck<U> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.unifier.deref_mut()
    }
}

impl<U: Unifier> From<U> for CompositeUnifierForOccursCheck<U> {
    #[inline(always)]
    fn from(unifier: U) -> Self {
        Self { unifier }
    }
}

impl<U: Unifier> Unifier for CompositeUnifierForOccursCheck<U> {
    fn bind(&mut self, r: Ref, value: HeapCellValue) {
        bind_with_occurs_check(&mut self.unifier, r, value);
    }
}

pub(crate) struct CompositeUnifierForOccursCheckWithError<U: Unifier> {
    unifier: U,
}

impl<U: Unifier> Deref for CompositeUnifierForOccursCheckWithError<U> {
    type Target = MachineState;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.unifier.deref()
    }
}

impl<U: Unifier> DerefMut for CompositeUnifierForOccursCheckWithError<U> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.unifier.deref_mut()
    }
}

impl<U: Unifier> From<U> for CompositeUnifierForOccursCheckWithError<U> {
    #[inline(always)]
    fn from(unifier: U) -> Self {
        Self { unifier }
    }
}

impl<U: Unifier> Unifier for CompositeUnifierForOccursCheckWithError<U> {
    fn bind(&mut self, r: Ref, value: HeapCellValue) {
        if bind_with_occurs_check(&mut self.unifier, r, value) {
            let err = self.representation_error(RepFlag::Term);
            let stub = functor_stub(atom!("unify_with_occurs_check"), 2);
            let err = self.error_form(err, stub);

            self.throw_exception(err);
        }
    }
}
