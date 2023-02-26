use crate::arena::*;
use crate::forms::*;
use crate::heap_iter::stackful_preorder_iter;
use crate::machine::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::types::*;

use std::cmp::Ordering;
use std::ops::{Deref, DerefMut};

use derive_deref::*;
use fxhash::FxBuildHasher;
use indexmap::IndexSet;

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
            (HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr | HeapCellValueTag::PStr) => {
                Self::unify_partial_string(self, list_loc_as_cell!(l1), value)
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

    fn unify_complete_string(&mut self, atom: Atom, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            if atom == atom!("") {
                Self::bind(self, r, atom_as_cell!(atom!("[]")));
            } else {
                Self::bind(self, r, atom_as_cstr_cell!(atom));
            }

            return;
        }

        read_heap_cell!(value,
            (HeapCellValueTag::Atom, (cstr_atom, arity)) if atom == atom!("") => {
                debug_assert_eq!(arity, 0);
                self.fail = cstr_atom != atom!("[]");
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if arity == 0 {
                    self.fail = atom == atom!("") && name != atom!("[]");
                } else {
                    // this is intentionally the same policy for
                    // value.tag() == Lis and PStrLoc. they're not
                    // grouped together to allow for arity == 0.
                    Self::unify_partial_string(self, atom_as_cstr_cell!(atom), value);

                    if !self.pdl.is_empty() {
                        Self::unify_internal(self);
                    }
                }
            }
            (HeapCellValueTag::CStr, cstr_atom) => {
                self.fail = atom != cstr_atom;
            }
            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                Self::unify_partial_string(self, atom_as_cstr_cell!(atom), value);

                if !self.pdl.is_empty() {
                    Self::unify_internal(self);
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }

    // the return value of unify_partial_string is interpreted as
    // follows:
    //
    // Some(None) -- the strings are equal, nothing to unify
    // Some(Some(f2,f1)) -- prefixes equal, try to unify focus values f2, f1
    // None -- prefixes not equal, unification fails
    //
    // d1's tag is assumed to be one of LIS, STR or PSTRLOC.
    fn unify_partial_string(&mut self, value_1: HeapCellValue, value_2: HeapCellValue) {
        if let Some(r) = value_2.as_var() {
            Self::bind(self, r, value_1);
            return;
        }

        let machine_st = self.deref_mut();

        let s1 = machine_st.heap.len();

        machine_st.heap.push(value_1);
        machine_st.heap.push(value_2);

        let mut pstr_iter1 = HeapPStrIter::new(&machine_st.heap, s1);
        let mut pstr_iter2 = HeapPStrIter::new(&machine_st.heap, s1 + 1);

        match compare_pstr_prefixes(&mut pstr_iter1, &mut pstr_iter2) {
            PStrCmpResult::Ordered(Ordering::Equal) => {}
            PStrCmpResult::Ordered(Ordering::Less) => {
                if pstr_iter2.focus.as_var().is_none() {
                    machine_st.fail = true;
                } else {
                    machine_st.pdl.push(empty_list_as_cell!());
                    machine_st.pdl.push(pstr_iter2.focus);
                }
            }
            PStrCmpResult::Ordered(Ordering::Greater) => {
                if pstr_iter1.focus.as_var().is_none() {
                    machine_st.fail = true;
                } else {
                    machine_st.pdl.push(empty_list_as_cell!());
                    machine_st.pdl.push(pstr_iter1.focus);
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

                                machine_st.pdl.push(val);
                                machine_st.pdl.push(char_as_cell!(c));

                                focus = pstr_iter2.heap[l+1];
                            }
                            (HeapCellValueTag::Str, s) => {
                                let (name, arity) = cell_as_atom_cell!(pstr_iter2.heap[s])
                                    .get_name_and_arity();

                                if name == atom!(".") && arity == 2 {
                                    machine_st.pdl.push(pstr_iter2.heap[s+1]);
                                    machine_st.pdl.push(char_as_cell!(c));

                                    focus = pstr_iter2.heap[s+2];
                                } else {
                                    machine_st.fail = true;
                                    break 'outer;
                                }
                            }
                            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h) => {
                                match chars_iter.item.unwrap() {
                                    PStrIteratee::Char(focus, _) => {
                                        machine_st.pdl.push(machine_st.heap[focus]);
                                        machine_st.pdl.push(heap_loc_as_cell!(h));
                                    }
                                    PStrIteratee::PStrSegment(focus, _, n) => {
                                        read_heap_cell!(machine_st.heap[focus],
                                            (HeapCellValueTag::CStr | HeapCellValueTag::PStr, pstr_atom) => {
                                                if focus < machine_st.heap.len() - 2 {
                                                    machine_st.heap.pop();
                                                    machine_st.heap.pop();
                                                }

                                                if n == 0 {
                                                    let target_cell = match machine_st.heap[focus].get_tag() {
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

                                                    machine_st.pdl.push(target_cell);
                                                    machine_st.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = machine_st.heap.len();

                                                    machine_st.heap.push(pstr_offset_as_cell!(focus));
                                                    machine_st.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    machine_st.pdl.push(pstr_loc_as_cell!(h_len));
                                                    machine_st.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            (HeapCellValueTag::PStrOffset, pstr_loc) => {
                                                let n0 = cell_as_fixnum!(machine_st.heap[focus+1])
                                                    .get_num() as usize;

                                                if pstr_loc < machine_st.heap.len() - 2 {
                                                    machine_st.heap.pop();
                                                    machine_st.heap.pop();
                                                }

                                                if n == n0 {
                                                    machine_st.pdl.push(pstr_loc_as_cell!(focus));
                                                    machine_st.pdl.push(heap_loc_as_cell!(h));
                                                } else {
                                                    let h_len = machine_st.heap.len();

                                                    machine_st.heap.push(pstr_offset_as_cell!(pstr_loc));
                                                    machine_st.heap.push(fixnum_as_cell!(
                                                        Fixnum::build_with(n as i64)
                                                    ));

                                                    machine_st.pdl.push(pstr_loc_as_cell!(h_len));
                                                    machine_st.pdl.push(heap_loc_as_cell!(h));
                                                }

                                                return;
                                            }
                                            _ => {
                                            }
                                        );

                                        if focus < machine_st.heap.len() - 2 {
                                            machine_st.heap.pop();
                                            machine_st.heap.pop();
                                        }

                                        machine_st.pdl.push(machine_st.heap[focus]);
                                        machine_st.pdl.push(heap_loc_as_cell!(h));

                                        return;
                                    }
                                }

                                break 'outer;
                            }
                            _ => {
                                machine_st.fail = true;
                                break 'outer;
                            }
                        );

                        chars_iter.next();
                    }

                    chars_iter.iter.next();

                    machine_st.pdl.push(focus);
                    machine_st.pdl.push(chars_iter.iter.focus);

                    break;
                }
            }
            PStrCmpResult::Unordered => {
                machine_st.pdl.push(pstr_iter1.focus);
                machine_st.pdl.push(pstr_iter2.focus);
            }
        }

        machine_st.heap.pop();
        machine_st.heap.pop();
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
            (HeapCellValueTag::CStr, cstr_atom) if atom == atom!("[]") => {
                self.fail = cstr_atom != atom!("");
            }
            (HeapCellValueTag::Char, c1) => {
                if let Some(c2) = atom.as_char() {
                    self.fail = c1 != c2;
                } else {
                    self.fail = true;
                }
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
            (HeapCellValueTag::Char, c2) => {
                if c != c2 {
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

    fn unify_big_num<N>(&mut self, n1: TypedArenaPtr<N>, value: HeapCellValue)
        where N: PartialEq<Rational>
               + PartialEq<Integer>
               + PartialEq<i64>
               + ArenaAllocated
    {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, typed_arena_ptr_as_cell!(n1));
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

    fn unify_f64(&mut self, f1: F64Ptr, value: HeapCellValue) {
        if let Some(r) = value.as_var() {
            Self::bind(self, r, HeapCellValue::from(f1));
            return;
        }

        read_heap_cell!(value,
            (HeapCellValueTag::F64, f2) => {
                self.fail = **f1 != **f2;
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
                 Self::unify_big_num(self, int_ptr, value);
             }
             (ArenaHeaderTag::Rational, rat_ptr) => {
                 Self::unify_big_num(self, rat_ptr, value);
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
                        if d2.is_ref() {
                            if tabu_list.contains(&(d1, d2)) {
                                continue;
                            }
                        }

                        Self::unify_list(self, l1, d2);

                        if !self.fail {
                            let d2 = self.store(d2);
                            tabu_list.insert((d1, d2));
                        }
                    }
                    (HeapCellValueTag::PStrLoc) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::PStrLoc |
                             HeapCellValueTag::Lis |
                             HeapCellValueTag::Str) => {
                                if tabu_list.contains(&(d1, d2)) {
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

                        Self::unify_partial_string(self, d1, d2);

                        if !self.fail && !d2.is_constant() {
                            let d2 = self.store(d2);
                            tabu_list.insert((d1, d2));
                        }
                    }
                    (HeapCellValueTag::CStr) => {
                        read_heap_cell!(d2,
                            (HeapCellValueTag::AttrVar, h) => {
                                Self::bind(self, Ref::attr_var(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::Var, h) => {
                                Self::bind(self, Ref::heap_cell(h), d1);
                                continue;
                            }
                            (HeapCellValueTag::StackVar, s) => {
                                Self::bind(self, Ref::stack_cell(s), d1);
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

                        Self::unify_partial_string(self, d2, d1);
                    }
                    (HeapCellValueTag::F64, f1) => {
                        Self::unify_f64(self, f1, d2);
                    }
                    (HeapCellValueTag::Fixnum, n1) => {
                        Self::unify_fixnum(self, n1, d2);
                    }
                    (HeapCellValueTag::Char, c1) => {
                        Self::unify_char(self, c1, d2);
                    }
                    (HeapCellValueTag::Cons, ptr_1) => {
                        Self::unify_constant(self, ptr_1, d2);
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
        for addr in stackful_preorder_iter(&mut unifier.heap, value) {
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
        unifier.fail = true;
    } else {
        U::bind(unifier, r, value);
    }

    return occurs_triggered;
}

#[derive(Deref, DerefMut)]
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

#[derive(Deref, DerefMut)]
pub(crate) struct AttributelessUnifier<'a> {
    machine_st: &'a mut MachineState,
}

impl<'a> From<&'a mut MachineState> for AttributelessUnifier<'a> {
    #[inline(always)]
    fn from(machine_st: &'a mut MachineState) -> Self {
        Self { machine_st }
    }
}

impl<'a> Unifier for AttributelessUnifier<'a> {
    // this bind is identical to MachineState::bind except that it
    // treats attributed variables as plain non-attributed heap
    // variables except when writing to the trail.
    fn bind(&mut self, r1: Ref, a2: HeapCellValue) {
        let t1 = self.store(r1.as_heap_cell_value());
        let t2 = self.store(a2);

        if t1.is_var() && (!t2.is_var() || a2 < r1) {
            match r1.get_tag() {
                RefTag::StackCell => {
                    self.stack[r1.get_value() as usize] = t2;
                    self.trail(TrailRef::Ref(r1));
                }
                RefTag::HeapCell | RefTag::AttrVar => {
                    self.heap[r1.get_value() as usize] = t2;
                    self.trail(TrailRef::Ref(r1));
                }
            };
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
                    self.heap[h] = t1;
                    self.trail(TrailRef::Ref(Ref::attr_var(h)));
                }
                _ => {
                    unreachable!();
                }
            );
        }
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
