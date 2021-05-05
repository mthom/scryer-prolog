use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;
use prolog_parser::{clause_name, perm_v, temp_v};

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::indexing::*;
use crate::instructions::*;
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
use crate::rug::Integer;
use ordered_float::*;

use indexmap::{IndexMap, IndexSet};

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::rc::Rc;

impl MachineState {
    pub(crate) fn new() -> Self {
        MachineState {
            atom_tbl: TabledData::new(Rc::new("".to_owned())),
            s: HeapPtr::default(),
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: LocalCodePtr::default(),
            attr_var_init: AttrVarInitializer::new(0),
            fail: false,
            heap: Heap::new(),
            mode: MachineMode::Write,
            stack: Stack::new(),
            registers: vec![Addr::HeapCell(0); MAX_ARITY + 1], // self.registers[0] is never used.
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
    pub(crate) fn machine_flags(&self) -> MachineFlags {
        self.flags
    }

    pub(crate) fn store(&self, addr: Addr) -> Addr {
        match addr {
            Addr::AttrVar(h) | Addr::HeapCell(h) => self.heap[h].as_addr(h),
            Addr::StackCell(fr, sc) => self.stack.index_and_frame(fr)[sc],
            Addr::PStrLocation(h, n) => {
                if let &HeapCellValue::PartialString(ref pstr, has_tail) = &self.heap[h] {
                    if !pstr.at_end(n) {
                        Addr::PStrLocation(h, n)
                    } else if has_tail {
                        Addr::HeapCell(h + 1)
                    } else {
                        Addr::EmptyList
                    }
                } else {
                    unreachable!()
                }
            }
            addr => addr,
        }
    }

    pub(crate) fn deref(&self, mut addr: Addr) -> Addr {
        loop {
            let value = self.store(addr);

            if value.is_ref() && value != addr {
                addr = value;
                continue;
            }

            return addr;
        }
    }

    fn bind_attr_var(&mut self, h: usize, addr: Addr) {
        match addr.as_var() {
            Some(Ref::HeapCell(hc)) => {
                self.heap[hc] = HeapCellValue::Addr(Addr::AttrVar(h));
                self.trail(TrailRef::Ref(Ref::HeapCell(hc)));
            }
            Some(Ref::StackCell(fr, sc)) => {
                self.stack.index_and_frame_mut(fr)[sc] = Addr::AttrVar(h);
                self.trail(TrailRef::Ref(Ref::StackCell(fr, sc)));
            }
            _ => {
                self.push_attr_var_binding(h, addr);
                self.heap[h] = HeapCellValue::Addr(addr);
                self.trail(TrailRef::Ref(Ref::AttrVar(h)));
            }
        }
    }

    pub(super) fn bind(&mut self, r1: Ref, a2: Addr) {
        let t1 = self.store(r1.as_addr());
        let t2 = self.store(a2);

        if t1.is_ref() && (!t2.is_ref() || a2 < r1) {
            match r1 {
                Ref::StackCell(fr, sc) => {
                    self.stack.index_and_frame_mut(fr)[sc] = t2;
                }
                Ref::HeapCell(h) => {
                    self.heap[h] = HeapCellValue::Addr(t2);
                }
                Ref::AttrVar(h) => {
                    return self.bind_attr_var(h, t2);
                }
            };

            self.trail(TrailRef::from(r1));
        } else {
            match a2.as_var() {
                Some(Ref::StackCell(fr, sc)) => {
                    self.stack.index_and_frame_mut(fr)[sc] = t1;
                    self.trail(TrailRef::Ref(Ref::StackCell(fr, sc)));
                }
                Some(Ref::HeapCell(h)) => {
                    self.heap[h] = HeapCellValue::Addr(t1);
                    self.trail(TrailRef::Ref(Ref::HeapCell(h)));
                }
                Some(Ref::AttrVar(h)) => {
                    self.bind_attr_var(h, t1);
                }
                None => {}
            }
        }
    }

    #[inline]
    pub(super) fn bind_with_occurs_check_with_error_wrapper(&mut self, r: Ref, addr: Addr) {
        if self.bind_with_occurs_check(r, addr) {
            let err = self.representation_error(
                RepFlag::Term,
                clause_name!("unify_with_occurs_check"),
                2,
            );

            self.throw_exception(err);
        }
    }

    #[inline]
    pub(super) fn bind_with_occurs_check_wrapper(&mut self, r: Ref, addr: Addr) {
        self.bind_with_occurs_check(r, addr);
    }

    #[inline]
    pub(super) fn bind_with_occurs_check(&mut self, r: Ref, addr: Addr) -> bool {
        if let Ref::StackCell(..) = r {
            // local variable optimization -- r cannot occur in the
            // data structure bound to addr, so don't bother
            // traversing it.
            self.bind(r, addr);
            return false;
        }

        let mut occurs_triggered = false;

        for addr in self.acyclic_pre_order_iter(addr) {
            if let Some(inner_r) = addr.as_var() {
                if r == inner_r {
                    occurs_triggered = true;
                    break;
                }
            }
        }

        self.fail = occurs_triggered;
        self.bind(r, addr);

        return occurs_triggered;
    }

    pub(super) fn unify_with_occurs_check_with_error(&mut self, a1: Addr, a2: Addr) {
        let mut throw_error = false;
        self.unify_with_occurs_check_loop(a1, a2, || throw_error = true);

        if throw_error {
            let err = self.representation_error(
                RepFlag::Term,
                clause_name!("unify_with_occurs_check"),
                2,
            );

            self.throw_exception(err);
        }
    }

    pub(super) fn unify_with_occurs_check(&mut self, a1: Addr, a2: Addr) {
        self.unify_with_occurs_check_loop(a1, a2, || {})
    }

    pub(super) fn unify_with_occurs_check_loop(
        &mut self,
        a1: Addr,
        a2: Addr,
        mut occurs_trigger: impl FnMut(),
    ) {
        let mut pdl = vec![a1, a2];
        let mut tabu_list: IndexSet<(Addr, Addr)> = IndexSet::new();

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                let d1 = self.store(d1);
                let d2 = self.store(d2);

                if tabu_list.contains(&(d1, d2)) {
                    continue;
                } else {
                    tabu_list.insert((d1, d2));
                }

                match (d1, d2) {
                    (Addr::AttrVar(h), addr) | (addr, Addr::AttrVar(h)) => {
                        if self.bind_with_occurs_check(Ref::AttrVar(h), addr) {
                            occurs_trigger();
                        }
                    }
                    (Addr::HeapCell(h), addr) | (addr, Addr::HeapCell(h)) => {
                        if self.bind_with_occurs_check(Ref::HeapCell(h), addr) {
                            occurs_trigger();
                        }
                    }
                    (Addr::StackCell(fr, sc), addr) | (addr, Addr::StackCell(fr, sc)) => {
                        if self.bind_with_occurs_check(Ref::StackCell(fr, sc), addr) {
                            occurs_trigger();
                        }
                    }
                    (Addr::Lis(a1), Addr::Str(a2)) | (Addr::Str(a2), Addr::Lis(a1)) => {
                        if let &HeapCellValue::NamedStr(n2, ref f2, _) = &self.heap[a2] {
                            if f2.as_str() == "." && n2 == 2 {
                                pdl.push(Addr::HeapCell(a1));
                                pdl.push(Addr::HeapCell(a2 + 1));

                                pdl.push(Addr::HeapCell(a1 + 1));
                                pdl.push(Addr::HeapCell(a2 + 2));

                                continue;
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::PStrLocation(h, n), Addr::Lis(l))
                    | (Addr::Lis(l), Addr::PStrLocation(h, n)) => {
                        if let HeapCellValue::PartialString(ref pstr, _) = &self.heap[h] {
                            if let Some(c) = pstr.range_from(n..).next() {
                                pdl.push(Addr::PStrLocation(h, n + c.len_utf8()));
                                pdl.push(Addr::HeapCell(l + 1));

                                pdl.push(Addr::Char(c));
                                pdl.push(Addr::HeapCell(l));
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::PStrLocation(h1, n1), Addr::PStrLocation(h2, n2)) => {
                        if let &HeapCellValue::PartialString(ref pstr1, has_tail_1) = &self.heap[h1]
                        {
                            if let &HeapCellValue::PartialString(ref pstr2, has_tail_2) =
                                &self.heap[h2]
                            {
                                let pstr1_s = pstr1.as_str_from(n1);
                                let pstr2_s = pstr2.as_str_from(n2);

                                let m_len = if pstr1_s.starts_with(pstr2_s) {
                                    pstr2_s.len()
                                } else if pstr2_s.starts_with(pstr1_s) {
                                    pstr1_s.len()
                                } else {
                                    self.fail = true;
                                    return;
                                };

                                if pstr1.at_end(n1 + m_len) {
                                    if has_tail_1 {
                                        pdl.push(Addr::HeapCell(h1 + 1));
                                    } else {
                                        pdl.push(Addr::EmptyList);
                                    }

                                    if pstr2.at_end(n2 + m_len) {
                                        if has_tail_2 {
                                            pdl.push(Addr::HeapCell(h2 + 1));
                                        } else {
                                            pdl.push(Addr::EmptyList);
                                        }
                                    } else {
                                        pdl.push(Addr::PStrLocation(h2, n2 + m_len));
                                    }
                                } else {
                                    pdl.push(Addr::PStrLocation(h1, n1 + m_len));

                                    if pstr2.at_end(n2 + m_len) {
                                        if has_tail_2 {
                                            pdl.push(Addr::HeapCell(h2 + 1));
                                        } else {
                                            pdl.push(Addr::EmptyList);
                                        }
                                    } else {
                                        pdl.push(Addr::PStrLocation(h2, n2 + m_len));
                                    }
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    }
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1, _) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2, _) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1..n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::Con(c1), Addr::Con(c2)) => match (&self.heap[c1], &self.heap[c2]) {
                        (&HeapCellValue::Atom(ref n1, _), &HeapCellValue::Atom(ref n2, _))
                            if n1.as_str() == n2.as_str() => {}
                        (
                            &HeapCellValue::DBRef(ref db_ref_1),
                            &HeapCellValue::DBRef(ref db_ref_2),
                        ) if db_ref_1 == db_ref_2 => {}
                        (v1, v2) => {
                            if let Ok(n1) = Number::try_from(v1) {
                                if let Ok(n2) = Number::try_from(v2) {
                                    if n1 == n2 {
                                        continue;
                                    }
                                }
                            }

                            self.fail = true;
                        }
                    },
                    (Addr::Con(h), Addr::Char(c)) | (Addr::Char(c), Addr::Con(h)) => {
                        match &self.heap[h] {
                            &HeapCellValue::Atom(ref name, _) if name.is_char() => {
                                if name.as_str().chars().next() != Some(c) {
                                    self.fail = true;
                                    return;
                                }
                            }
                            _ => {
                                self.fail = true;
                                return;
                            }
                        }
                    }
                    (Addr::Stream(s1), Addr::Stream(s2)) => {
                        if s1 != s2 {
                            self.fail = true;
                        }
                    }
                    (v, Addr::Con(h)) | (Addr::Con(h), v) => {
                        if let Ok(n1) = Number::try_from(&self.heap[h]) {
                            if let Ok(v) = Number::try_from(&HeapCellValue::Addr(v)) {
                                if n1 == v {
                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    (a1, a2) => {
                        if let Ok(n1) = Number::try_from(&HeapCellValue::Addr(a1)) {
                            if let Ok(n2) = Number::try_from(&HeapCellValue::Addr(a2)) {
                                if n1 == n2 {
                                    continue;
                                }
                            }
                        }

                        if a1 != a2 {
                            self.fail = true;
                        }
                    }
                };
            }
        }
    }

    pub(super) fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];

        let mut tabu_list: IndexSet<(Addr, Addr)> = IndexSet::new();

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                let d1 = self.store(d1);
                let d2 = self.store(d2);

                if tabu_list.contains(&(d1, d2)) {
                    continue;
                } else {
                    tabu_list.insert((d1, d2));
                }

                match (d1, d2) {
                    (Addr::AttrVar(h), addr) | (addr, Addr::AttrVar(h)) => {
                        self.bind(Ref::AttrVar(h), addr);
                    }
                    (Addr::HeapCell(h), addr) | (addr, Addr::HeapCell(h)) => {
                        self.bind(Ref::HeapCell(h), addr);
                    }
                    (Addr::StackCell(fr, sc), addr) | (addr, Addr::StackCell(fr, sc)) => {
                        self.bind(Ref::StackCell(fr, sc), addr);
                    }
                    (Addr::Lis(a1), Addr::Str(a2)) | (Addr::Str(a2), Addr::Lis(a1)) => {
                        if let &HeapCellValue::NamedStr(n2, ref f2, _) = &self.heap[a2] {
                            if f2.as_str() == "." && n2 == 2 {
                                pdl.push(Addr::HeapCell(a1));
                                pdl.push(Addr::HeapCell(a2 + 1));

                                pdl.push(Addr::HeapCell(a1 + 1));
                                pdl.push(Addr::HeapCell(a2 + 2));

                                continue;
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::PStrLocation(h, n), Addr::Lis(l))
                    | (Addr::Lis(l), Addr::PStrLocation(h, n)) => {
                        if let HeapCellValue::PartialString(ref pstr, _) = &self.heap[h] {
                            if let Some(c) = pstr.range_from(n..).next() {
                                pdl.push(Addr::PStrLocation(h, n + c.len_utf8()));
                                pdl.push(Addr::HeapCell(l + 1));

                                pdl.push(Addr::Char(c));
                                pdl.push(Addr::HeapCell(l));
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::PStrLocation(h1, n1), Addr::PStrLocation(h2, n2)) => {
                        if let &HeapCellValue::PartialString(ref pstr1, has_tail_1) = &self.heap[h1]
                        {
                            if let &HeapCellValue::PartialString(ref pstr2, has_tail_2) =
                                &self.heap[h2]
                            {
                                let pstr1_s = pstr1.as_str_from(n1);
                                let pstr2_s = pstr2.as_str_from(n2);

                                let m_len = if pstr1_s.starts_with(pstr2_s) {
                                    pstr2_s.len()
                                } else if pstr2_s.starts_with(pstr1_s) {
                                    pstr1_s.len()
                                } else {
                                    self.fail = true;
                                    return;
                                };

                                if pstr1.at_end(n1 + m_len) {
                                    if has_tail_1 {
                                        pdl.push(Addr::HeapCell(h1 + 1));
                                    } else {
                                        pdl.push(Addr::EmptyList);
                                    }

                                    if pstr2.at_end(n2 + m_len) {
                                        if has_tail_2 {
                                            pdl.push(Addr::HeapCell(h2 + 1));
                                        } else {
                                            pdl.push(Addr::EmptyList);
                                        }
                                    } else {
                                        pdl.push(Addr::PStrLocation(h2, n2 + m_len));
                                    }
                                } else {
                                    pdl.push(Addr::PStrLocation(h1, n1 + m_len));

                                    if pstr2.at_end(n2 + m_len) {
                                        if has_tail_2 {
                                            pdl.push(Addr::HeapCell(h2 + 1));
                                        } else {
                                            pdl.push(Addr::EmptyList);
                                        }
                                    } else {
                                        pdl.push(Addr::PStrLocation(h2, n2 + m_len));
                                    }
                                }
                            }
                        }
                    }
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    }
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1, _) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2, _) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1..n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::Con(c1), Addr::Con(c2)) => match (&self.heap[c1], &self.heap[c2]) {
                        (&HeapCellValue::Atom(ref n1, _), &HeapCellValue::Atom(ref n2, _))
                            if n1.as_str() == n2.as_str() => {}
                        (
                            &HeapCellValue::DBRef(ref db_ref_1),
                            &HeapCellValue::DBRef(ref db_ref_2),
                        ) if db_ref_1 == db_ref_2 => {}
                        (v1, v2) => {
                            if let Ok(n1) = Number::try_from(v1) {
                                if let Ok(n2) = Number::try_from(v2) {
                                    if n1 == n2 {
                                        continue;
                                    }
                                }
                            }

                            self.fail = true;
                        }
                    },
                    (Addr::Con(h), Addr::Char(c)) | (Addr::Char(c), Addr::Con(h)) => {
                        match &self.heap[h] {
                            &HeapCellValue::Atom(ref name, _) if name.is_char() => {
                                if name.as_str().chars().next() != Some(c) {
                                    self.fail = true;
                                    return;
                                }
                            }
                            _ => {
                                self.fail = true;
                                return;
                            }
                        }
                    }
                    (Addr::Stream(s1), Addr::Stream(s2)) => {
                        if s1 != s2 {
                            self.fail = true;
                        }
                    }
                    (v, Addr::Con(h)) | (Addr::Con(h), v) => {
                        if let Ok(n1) = Number::try_from(&self.heap[h]) {
                            if let Ok(v) = Number::try_from(&HeapCellValue::Addr(v)) {
                                if n1 == v {
                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    (a1, a2) => {
                        if let Ok(n1) = Number::try_from(&HeapCellValue::Addr(a1)) {
                            if let Ok(n2) = Number::try_from(&HeapCellValue::Addr(a2)) {
                                if n1 == n2 {
                                    continue;
                                }
                            }
                        }

                        if a1 != a2 {
                            self.fail = true;
                        }
                    }
                };
            }
        }
    }

    pub(super) fn trail(&mut self, r: TrailRef) {
        match r {
            TrailRef::Ref(Ref::HeapCell(h)) => {
                if h < self.hb {
                    self.trail.push(TrailRef::Ref(Ref::HeapCell(h)));
                    self.tr += 1;
                }
            }
            TrailRef::Ref(Ref::AttrVar(h)) => {
                if h < self.hb {
                    self.trail.push(TrailRef::Ref(Ref::AttrVar(h)));
                    self.tr += 1;
                }
            }
            TrailRef::AttrVarHeapLink(h) => {
                if h < self.hb {
                    self.trail.push(TrailRef::AttrVarHeapLink(h));
                    self.tr += 1;
                }
            }
            TrailRef::AttrVarListLink(h, l) => {
                if h < self.hb {
                    self.trail.push(TrailRef::AttrVarListLink(h, l));
                    self.tr += 1;
                }
            }
            TrailRef::Ref(Ref::StackCell(b, sc)) => {
                if b < self.b {
                    self.trail.push(TrailRef::Ref(Ref::StackCell(b, sc)));
                    self.tr += 1;
                }
            }
            TrailRef::BlackboardOffset(key_h, value_h) => {
                self.trail.push(TrailRef::BlackboardOffset(key_h, value_h));
                self.tr += 1;
            }
            TrailRef::BlackboardEntry(key_h) => {
                self.trail.push(TrailRef::BlackboardEntry(key_h));
                self.tr += 1;
            }
        }
    }

    fn increment_s_ptr(&mut self, rhs: usize) {
        match &mut self.s {
            HeapPtr::HeapCell(ref mut h) => {
                *h += rhs;
            }
            &mut HeapPtr::PStrChar(h, ref mut n) | &mut HeapPtr::PStrLocation(h, ref mut n) => {
                match &self.heap[h] {
                    &HeapCellValue::PartialString(ref pstr, _) => {
                        for c in pstr.range_from(*n..).take(rhs) {
                            *n += c.len_utf8();
                        }

                        self.s = HeapPtr::PStrLocation(h, *n);
                    }
                    _ => {}
                }
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
            match self.trail[i] {
                TrailRef::Ref(Ref::HeapCell(h)) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::HeapCell(h))
                }
                TrailRef::Ref(Ref::AttrVar(h)) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::AttrVar(h))
                }
                TrailRef::Ref(Ref::StackCell(fr, sc)) => {
                    self.stack.index_and_frame_mut(fr)[sc] = Addr::StackCell(fr, sc)
                }
                TrailRef::AttrVarHeapLink(h) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::HeapCell(h));
                }
                TrailRef::AttrVarListLink(h, l) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::Lis(l));
                }
                TrailRef::BlackboardOffset(key_h, value_h) => {
                    let key = atom_from!(
                        self,
                        self.store(self.deref(self.heap[key_h].as_addr(key_h)))
                    );

                    let value_addr = self.heap[value_h].as_addr(value_h);

                    match global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = Some(value_addr),
                        None => unreachable!(),
                    }
                }
                TrailRef::BlackboardEntry(key_h) => {
                    let key = atom_from!(
                        self,
                        self.store(self.deref(self.heap[key_h].as_addr(key_h)))
                    );

                    match global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = None,
                        None => unreachable!(),
                    }
                }
            }
        }
    }

    pub(super) fn match_partial_string(&mut self, addr: Addr, string: &String, has_tail: bool) {
        let mut heap_pstr_iter = self.heap_pstr_iter(addr);

        match compare_pstr_to_string(&mut heap_pstr_iter, string) {
            Some(prefix_len) if prefix_len == string.len() => {
                let focus = heap_pstr_iter.focus();

                match focus {
                    Addr::PStrLocation(h, n) => {
                        if has_tail {
                            self.s = HeapPtr::PStrLocation(h, n);
                            self.mode = MachineMode::Read;
                        } else {
                            self.fail = true;
                        }
                    }
                    addr => {
                        if has_tail {
                            let h = self.heap.h();

                            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                            self.bind(Ref::HeapCell(h), addr);

                            self.s = HeapPtr::HeapCell(h);
                            self.mode = MachineMode::Read;
                        } else {
                            if let Some(var) = addr.as_var() {
                                self.bind(var, Addr::EmptyList);
                            } else {
                                self.fail = addr != Addr::EmptyList;
                            }
                        }
                    }
                }
            }
            Some(prefix_len) => match heap_pstr_iter.focus() {
                addr if addr.is_ref() => {
                    let h = self.heap.h();

                    let pstr_addr = if has_tail {
                        self.s = HeapPtr::HeapCell(h + 1);
                        self.mode = MachineMode::Read;

                        self.heap.allocate_pstr(&string[prefix_len..])
                    } else {
                        self.heap.put_complete_string(&string[prefix_len..])
                    };

                    self.bind(addr.as_var().unwrap(), pstr_addr);
                }
                Addr::Lis(l) => {
                    let h = self.heap.h();

                    let pstr_addr = if has_tail {
                        self.s = HeapPtr::HeapCell(h + 1);
                        self.mode = MachineMode::Read;

                        self.heap.allocate_pstr(&string[prefix_len..])
                    } else {
                        self.heap.put_complete_string(&string[prefix_len..])
                    };

                    (self.unify_fn)(self, Addr::Lis(l), pstr_addr);
                }
                _ => {
                    self.fail = true;
                }
            },
            None => {
                self.fail = true;
            }
        }
    }

    pub(super) fn write_constant_to_var(&mut self, addr: Addr, c: &Constant) {
        match self.store(self.deref(addr)) {
            Addr::Con(c1) => {
                match &self.heap[c1] {
                    HeapCellValue::Atom(ref n1, _) => {
                        self.fail = match c {
                            Constant::Atom(ref n2, _) => n1 != n2,
                            Constant::Char(c) if n1.is_char() => {
                                Some(*c) != n1.as_str().chars().next()
                            }
                            _ => true,
                        };
                    }
                    HeapCellValue::Integer(ref n1) => {
                        self.fail = match c {
                            Constant::Fixnum(n2) => n1.to_isize() != Some(*n2),
                            Constant::Integer(ref n2) => n1 != n2,
                            Constant::Usize(n2) => n1.to_usize() != Some(*n2),
                            _ => true,
                        };
                    }
                    HeapCellValue::Rational(ref r1) => {
                        self.fail = if let Constant::Rational(ref r2) = c {
                            r1 != r2
                        } else {
                            true
                        }
                    }
                    HeapCellValue::PartialString(..) => {
                        if let Constant::String(ref s2) = c {
                            self.match_partial_string(Addr::PStrLocation(c1, 0), &s2, false);
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                };
            }
            Addr::Char(ch) => {
                self.fail = match c {
                    Constant::Atom(ref n2, _) if n2.is_char() => {
                        Some(ch) != n2.as_str().chars().next()
                    }
                    Constant::Char(c) => *c != ch,
                    _ => true,
                };
            }
            Addr::EmptyList => {
                if let Constant::EmptyList = c {
                } else {
                    self.fail = true;
                }
            }
            Addr::Lis(l) => {
                let addr = self.heap.put_constant(c.clone());
                self.unify(Addr::Lis(l), addr);
            }
            Addr::PStrLocation(h, n) => {
                if let Constant::String(ref s2) = c {
                    self.match_partial_string(Addr::PStrLocation(h, n), &s2, false)
                } else {
                    self.fail = true;
                };
            }
            Addr::Stream(_) => {
                self.fail = true;
            }
            addr => {
                let c = self.heap.put_constant(c.clone());

                if let Some(r) = addr.as_var() {
                    self.bind(r, c);
                } else {
                    self.unify(addr, c);
                }
            }
        };
    }

    pub(super) fn execute_arith_instr(&mut self, instr: &ArithmeticInstruction) {
        let stub = MachineError::functor_stub(clause_name!("is"), 2);

        match instr {
            &ArithmeticInstruction::Add(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 + n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Sub(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 - n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Mul(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 * n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Max(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.max(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Min(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.min(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::IntPow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.int_pow(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Gcd(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.gcd(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Pow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.pow(n1, n2, "(**)"));
                self.p += 1;
            }
            &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);

                let (r1, stub) = try_or_fail!(self, self.get_rational(a1, stub));
                let (r2, _) = try_or_fail!(self, self.get_rational(a2, stub));

                self.interms[t - 1] =
                    Number::Rational(Rc::new(try_or_fail!(self, self.rdiv(r1, r2))));
                self.p += 1;
            }
            &ArithmeticInstruction::IntFloorDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.int_floor_div(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::IDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.idiv(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Abs(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1.abs();
                self.p += 1;
            }
            &ArithmeticInstruction::Sign(ref a1, t) => {
                let n = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = self.sign(n);
                self.p += 1;
            }
            &ArithmeticInstruction::Neg(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = -n1;
                self.p += 1;
            }
            &ArithmeticInstruction::BitwiseComplement(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = try_or_fail!(self, self.bitwise_complement(n1));
                self.p += 1;
            }
            &ArithmeticInstruction::Div(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.div(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Shr(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.shr(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Shl(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.shl(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Xor(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.xor(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::And(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.and(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Or(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.or(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Mod(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.modulus(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Rem(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.remainder(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Cos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.cos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.sin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Tan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.tan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sqrt(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.sqrt(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Log(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.log(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Exp(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.exp(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ACos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.acos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ASin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.asin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.atan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan2(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.atan2(n1, n2))));
                self.p += 1;
            }
            &ArithmeticInstruction::Float(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.float(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Truncate(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = self.truncate(n1);
                self.p += 1;
            }
            &ArithmeticInstruction::Round(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = try_or_fail!(self, self.round(n1));
                self.p += 1;
            }
            &ArithmeticInstruction::Ceiling(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = self.ceiling(n1);
                self.p += 1;
            }
            &ArithmeticInstruction::Floor(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = self.floor(n1);
                self.p += 1;
            }
            &ArithmeticInstruction::Plus(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1;
                self.p += 1;
            }
        };
    }

    pub(super) fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, ref c, reg) => {
                let addr = self[reg];
                self.write_constant_to_var(addr, c);
            }
            &FactInstruction::GetList(_, reg) => {
                let addr = self.store(self.deref(self[reg]));

                match addr {
                    Addr::PStrLocation(h, n) => {
                        self.s = HeapPtr::PStrChar(h, n);
                        self.mode = MachineMode::Read;
                    }
                    addr @ Addr::AttrVar(_)
                    | addr @ Addr::StackCell(..)
                    | addr @ Addr::HeapCell(_) => {
                        let h = self.heap.h();

                        self.heap.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
                        self.bind(addr.as_var().unwrap(), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    }
                    Addr::Lis(a) => {
                        self.s = HeapPtr::HeapCell(a);
                        self.mode = MachineMode::Read;
                    }
                    _ => {
                        self.fail = true;
                    }
                };
            }
            &FactInstruction::GetPartialString(_, ref string, reg, has_tail) => {
                let addr = self.store(self.deref(self[reg]));
                self.match_partial_string(addr, string, has_tail);
            }
            &FactInstruction::GetStructure(ref ct, arity, reg) => {
                let addr = self.deref(self[reg]);

                match self.store(addr) {
                    Addr::Str(a) => {
                        let result = &self.heap[a];

                        if let &HeapCellValue::NamedStr(narity, ref s, _) = result {
                            if narity == arity && ct.name() == *s {
                                self.s = HeapPtr::HeapCell(a + 1);
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        }
                    }
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        let h = self.heap.h();

                        self.heap.push(HeapCellValue::Addr(Addr::Str(h + 1)));
                        self.heap
                            .push(HeapCellValue::NamedStr(arity, ct.name(), ct.spec()));

                        self.bind(addr.as_var().unwrap(), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    }
                    _ => {
                        self.fail = true;
                    }
                };
            }
            &FactInstruction::GetVariable(norm, arg) => {
                self[norm] = self.registers[arg];
            }
            &FactInstruction::GetValue(norm, arg) => {
                let norm_addr = self[norm];
                let reg_addr = self.registers[arg];

                (self.unify_fn)(self, norm_addr, reg_addr);
            }
            &FactInstruction::UnifyConstant(ref c) => {
                match self.mode {
                    MachineMode::Read => {
                        let addr = self.s.read(&self.heap);

                        self.write_constant_to_var(addr, c);
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let addr = self.heap.put_constant(c.clone());

                        if !addr.is_heap_bound() {
                            self.heap.push(HeapCellValue::Addr(addr));
                        }
                    }
                };
            }
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        self[reg] = self.s.read(&self.heap);
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let h = self.heap.h();

                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        self[reg] = Addr::HeapCell(h);
                    }
                };
            }
            &FactInstruction::UnifyLocalValue(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg];

                        (self.unify_fn)(self, reg_addr, self.s.read(&self.heap));
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let addr = self.store(self.deref(self[reg]));
                        let h = self.heap.h();

                        if let Addr::HeapCell(hc) = addr {
                            let val = self.heap.clone(hc);

                            self.heap.push(val);
                            self.increment_s_ptr(1);

                            return;
                        }

                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        (self.bind_fn)(self, Ref::HeapCell(h), addr);
                    }
                };
            }
            &FactInstruction::UnifyValue(reg) => {
                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg];

                        (self.unify_fn)(self, reg_addr, self.s.read(&self.heap));
                        self.increment_s_ptr(1);
                    }
                    MachineMode::Write => {
                        let h = self.heap.h();
                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));

                        let addr = self.store(self[reg]);
                        (self.bind_fn)(self, Ref::HeapCell(h), addr);

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
                        let h = self.heap.h();

                        for i in h..h + n {
                            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(i)));
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
                    let offset = match addr {
                        Addr::LoadStatePayload(_) | Addr::Stream(_) | Addr::TcpListener(_) => {
                            IndexingCodePtr::Fail
                        }
                        Addr::HeapCell(_) | Addr::StackCell(..) | Addr::AttrVar(..) => v,
                        Addr::PStrLocation(..) => l,
                        Addr::Char(_)
                        | Addr::Con(_)
                        | Addr::CutPoint(_)
                        | Addr::EmptyList
                        | Addr::Fixnum(_)
                        | Addr::Float(_)
                        | Addr::Usize(_) => c,
                        Addr::Lis(_) => l,
                        Addr::Str(_) => s,
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
                    };
                }
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref hm)) => {
                    let offset = match addr.as_constant_index(&self) {
                        Some(c) => match hm.get(&c) {
                            Some(offset) => *offset,
                            _ => IndexingCodePtr::Fail,
                        },
                        None => IndexingCodePtr::Fail,
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
                    };
                }
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref hm)) => {
                    let offset = match addr {
                        Addr::Str(s) => {
                            if let &HeapCellValue::NamedStr(arity, ref name, _) = &self.heap[s] {
                                match hm.get(&(name.clone(), arity)) {
                                    Some(offset) => *offset,
                                    _ => IndexingCodePtr::Fail,
                                }
                            } else {
                                IndexingCodePtr::Fail
                            }
                        }
                        _ => IndexingCodePtr::Fail,
                    };

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
            &QueryInstruction::PutConstant(_, ref c, reg) => {
                self[reg] = self.heap.put_constant(c.clone());
            }
            &QueryInstruction::PutList(_, reg) => {
                self[reg] = Addr::Lis(self.heap.h());
            }
            &QueryInstruction::PutPartialString(_, ref string, reg, has_tail) => {
                let pstr_addr = if has_tail {
                    if !string.is_empty() {
                        let pstr_addr = self.heap.allocate_pstr(&string);
                        self.heap.pop(); // the tail will be added by the next instruction.
                        pstr_addr
                    } else {
                        Addr::EmptyList
                    }
                } else {
                    self.heap.put_complete_string(&string)
                };

                self[reg] = pstr_addr;
            }
            &QueryInstruction::PutStructure(ref ct, arity, reg) => {
                let h = self.heap.h();

                self.heap
                    .push(HeapCellValue::NamedStr(arity, ct.name(), ct.spec()));
                self[reg] = Addr::Str(h);
            }
            &QueryInstruction::PutUnsafeValue(n, arg) => {
                let e = self.e;
                let addr = self.store(self.deref(Addr::StackCell(e, n)));

                if addr.is_protected(e) {
                    self.registers[arg] = addr;
                } else {
                    let h = self.heap.h();

                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                    (self.bind_fn)(self, Ref::HeapCell(h), addr);

                    self.registers[arg] = self.heap[h].as_addr(h);
                }
            }
            &QueryInstruction::PutValue(norm, arg) => {
                self.registers[arg] = self[norm];
            }
            &QueryInstruction::PutVariable(norm, arg) => {
                match norm {
                    RegType::Perm(n) => {
                        let e = self.e;

                        self[norm] = Addr::StackCell(e, n);
                        self.registers[arg] = self[norm];
                    }
                    RegType::Temp(_) => {
                        let h = self.heap.h();
                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));

                        self[norm] = Addr::HeapCell(h);
                        self.registers[arg] = Addr::HeapCell(h);
                    }
                };
            }
            &QueryInstruction::SetConstant(ref c) => {
                let addr = self.heap.put_constant(c.clone());

                if !addr.is_heap_bound() {
                    self.heap.push(HeapCellValue::Addr(addr));
                }
            }
            &QueryInstruction::SetLocalValue(reg) => {
                let addr = self.deref(self[reg]);
                let h = self.heap.h();

                if addr < Ref::HeapCell(h) {
                    self.heap.push(HeapCellValue::Addr(addr));
                    return;
                }

                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                (self.bind_fn)(self, Ref::HeapCell(h), addr);
            }
            &QueryInstruction::SetVariable(reg) => {
                let h = self.heap.h();
                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self[reg] = Addr::HeapCell(h);
            }
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self.store(self[reg]);
                self.heap.push(HeapCellValue::Addr(heap_val));
            }
            &QueryInstruction::SetVoid(n) => {
                let h = self.heap.h();

                for i in h..h + n {
                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(i)));
                }
            }
        }
    }

    pub(super) fn set_ball(&mut self) {
        self.ball.reset();

        let addr = self[temp_v!(1)];
        self.ball.boundary = self.heap.h();

        copy_term(
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.ball.stub),
            addr,
            AttrVarPolicy::DeepCopy,
        );
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

        let (name, narity) = match addr {
            Addr::Str(a) => {
                let result = self.heap.clone(a);

                if let HeapCellValue::NamedStr(narity, name, _) = result {
                    let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);

                    if narity + arity > MAX_ARITY {
                        let representation_error = self.error_form(
                            MachineError::representation_error(RepFlag::MaxArity),
                            stub,
                        );

                        self.throw_exception(representation_error);
                        return None;
                    }

                    for i in (1..arity).rev() {
                        self.registers[i + narity] = self.registers[i];
                    }

                    for i in 1..narity + 1 {
                        self.registers[i] = self.heap[a + i].as_addr(a + i);
                    }

                    (name, narity)
                } else {
                    self.fail = true;
                    return None;
                }
            }
            Addr::Char(c) => (clause_name!(c.to_string(), self.atom_tbl), 0),
            Addr::Con(h) => match &self.heap[h] {
                HeapCellValue::Atom(ref name, _) => (name.clone(), 0),
                _ => {
                    self.fail = true;
                    return None;
                }
            },
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
                let instantiation_error =
                    self.error_form(MachineError::instantiation_error(), stub);

                self.throw_exception(instantiation_error);
                return None;
            }
            addr => {
                let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
                let type_error = self.error_form(
                    MachineError::type_error(self.heap.h(), ValidType::Callable, addr),
                    stub,
                );

                self.throw_exception(type_error);
                return None;
            }
        };

        Some((name, arity + narity - 1))
    }

    pub(super) fn unwind_stack(&mut self) {
        self.b = self.block;
        self.fail = true;
    }

    pub(crate) fn is_cyclic_term(&self, addr: Addr) -> bool {
        let mut seen = IndexSet::new();
        let mut fail = false;
        let mut iter = self.pre_order_iter(addr);
        let mut parent_stack = vec![];

        let is_composite = |addr: Addr| match addr {
            Addr::Str(_) | Addr::Lis(_) | Addr::PStrLocation(..) => true,
            _ => false,
        };

        'outer: loop {
            if let Some(addr) = iter.stack().last().cloned() {
                let addr = self.store(self.deref(addr));

                if is_composite(addr) {
                    if !seen.contains(&addr) {
                        seen.insert(addr);
                    } else {
                        // when we again encounter a seen composite
                        // term, check that it precedes itself as a
                        // parent in the post-order traversal. in the
                        // future, when value cells have mark bits,
                        // use them to designate parenthood instead of
                        // this linear search.

                        for (_, prec_addr) in parent_stack.iter().rev().cloned() {
                            if prec_addr == addr {
                                fail = true;
                                break 'outer;
                            }
                        }
                    }

                    let arity = match addr {
                        Addr::Str(h) => match &self.heap[h] {
                            &HeapCellValue::NamedStr(arity, ..) => arity,
                            _ => unreachable!(),
                        },
                        _ => 2,
                    };

                    parent_stack.push((arity, addr));
                }
            }

            if iter.next().is_none() {
                break;
            } else {
                while let Some((rem_children, addr)) = parent_stack.pop() {
                    if rem_children > 0 {
                        parent_stack.push((rem_children - 1, addr));
                        break;
                    }
                }
            }
        }

        fail
    }

    // arg(+N, +Term, ?Arg)
    pub(super) fn try_arg(&mut self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("arg"), 3);
        let n = self.store(self.deref(self[temp_v!(1)]));

        match n {
            Addr::HeapCell(_) | Addr::StackCell(..) => {
                // 8.5.2.3 a)
                return Err(self.error_form(MachineError::instantiation_error(), stub));
            }
            addr => {
                let n = match Number::try_from((addr, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Integer::from(n),
                    Ok(Number::Integer(n)) => Integer::from(n.as_ref()),
                    _ => {
                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::Integer, addr),
                            stub,
                        ));
                    }
                };

                if n < 0 {
                    // 8.5.2.3 e)
                    let n = Number::from(n);
                    let dom_err = MachineError::domain_error(DomainErrorType::NotLessThanZero, n);

                    return Err(self.error_form(dom_err, stub));
                }

                let n = match n.to_usize() {
                    Some(n) => n,
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let term = self.store(self.deref(self[temp_v!(2)]));

                match term {
                    Addr::HeapCell(_) | Addr::StackCell(..) | Addr::AttrVar(_) => {
                        // 8.5.2.3 b)
                        return Err(self.error_form(MachineError::instantiation_error(), stub));
                    }
                    Addr::Str(o) => match self.heap.clone(o) {
                        HeapCellValue::NamedStr(arity, _, _) if 1 <= n && n <= arity => {
                            let a3 = self[temp_v!(3)];
                            let h_a = Addr::HeapCell(o + n);

                            (self.unify_fn)(self, a3, h_a);
                        }
                        _ => {
                            self.fail = true;
                        }
                    },
                    Addr::Lis(l) => {
                        if n == 1 || n == 2 {
                            let a3 = self[temp_v!(3)];
                            let h_a = Addr::HeapCell(l + n - 1);

                            (self.unify_fn)(self, a3, h_a);
                        } else {
                            self.fail = true;
                        }
                    }
                    Addr::PStrLocation(h, offset) => {
                        if n == 1 || n == 2 {
                            let a3 = self[temp_v!(3)];
                            let h_a =
                                if let HeapCellValue::PartialString(ref pstr, _) = &self.heap[h] {
                                    if let Some(c) = pstr.range_from(offset..).next() {
                                        if n == 1 {
                                            Addr::Char(c)
                                        } else {
                                            Addr::PStrLocation(h, offset + c.len_utf8())
                                        }
                                    } else {
                                        unreachable!()
                                    }
                                } else {
                                    unreachable!()
                                };

                            (self.unify_fn)(self, a3, h_a);
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        // 8.5.2.3 d)
                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::Compound, term),
                            stub,
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    fn compare_numbers(&mut self, cmp: CompareNumberQT, n1: Number, n2: Number) {
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

    pub(super) fn compare_term(&mut self, qt: CompareTermQT) {
        let a1 = self[temp_v!(1)];
        let a2 = self[temp_v!(2)];

        match self.compare_term_test(&a1, &a2) {
            Some(Ordering::Greater) => match qt {
                CompareTermQT::GreaterThan | CompareTermQT::GreaterThanOrEqual => return,
                _ => self.fail = true,
            },
            Some(Ordering::Equal) => match qt {
                CompareTermQT::GreaterThanOrEqual | CompareTermQT::LessThanOrEqual => return,
                _ => self.fail = true,
            },
            Some(Ordering::Less) => match qt {
                CompareTermQT::LessThan | CompareTermQT::LessThanOrEqual => return,
                _ => self.fail = true,
            },
            None => {
                self.fail = true;
            }
        };
    }

    // returns true on failure.
    pub(super) fn eq_test(&self, a1: Addr, a2: Addr) -> bool {
        let mut iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        while let Some((v1, v2)) = iter.next() {
            match (v1, v2) {
                (Addr::Str(s1), Addr::Str(s2)) => {
                    if let HeapCellValue::NamedStr(ar1, n1, _) = &self.heap[s1] {
                        if let HeapCellValue::NamedStr(ar2, n2, _) = &self.heap[s2] {
                            if ar1 != ar2 || n1 != n2 {
                                return true;
                            }
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }
                (Addr::PStrLocation(..), Addr::Lis(_)) | (Addr::Lis(_), Addr::PStrLocation(..)) => {
                    continue;
                }
                (pstr1 @ Addr::PStrLocation(..), pstr2 @ Addr::PStrLocation(..)) => {
                    let mut i1 = self.heap_pstr_iter(pstr1);
                    let mut i2 = self.heap_pstr_iter(pstr2);

                    let ordering = compare_pstr_prefixes(&mut i1, &mut i2);

                    if let Some(ordering) = ordering {
                        if ordering != Ordering::Equal {
                            return true;
                        }
                    }

                    let (lstack, rstack) = iter.stack();

                    lstack.pop();
                    lstack.pop();

                    rstack.pop();
                    rstack.pop();

                    lstack.push(i1.focus());
                    rstack.push(i2.focus());
                }
                (Addr::Lis(_), Addr::Lis(_)) => {
                    continue;
                }
                (Addr::Con(h1), Addr::Con(h2)) => match (&self.heap[h1], &self.heap[h2]) {
                    (
                        &HeapCellValue::Atom(ref n1, ref spec_1),
                        &HeapCellValue::Atom(ref n2, ref spec_2),
                    ) => {
                        if n1 != n2 || spec_1 != spec_2 {
                            return true;
                        }
                    }
                    (&HeapCellValue::DBRef(ref db_ref_1), &HeapCellValue::DBRef(ref db_ref_2)) => {
                        if db_ref_1 != db_ref_2 {
                            return true;
                        }
                    }
                    (v1, v2) => {
                        if let Ok(n1) = Number::try_from(v1) {
                            if let Ok(n2) = Number::try_from(v2) {
                                if n1 == n2 {
                                    continue;
                                }
                            }
                        }

                        return true;
                    }
                },
                (Addr::Con(h), Addr::Char(c)) | (Addr::Char(c), Addr::Con(h)) => {
                    match &self.heap[h] {
                        &HeapCellValue::Atom(ref name, _) if name.is_char() => {
                            if name.as_str().chars().next() != Some(c) {
                                return true;
                            }
                        }
                        _ => {
                            return true;
                        }
                    }
                }
                (a1, a2) => {
                    if let Ok(n1) = Number::try_from((a1, &self.heap)) {
                        if let Ok(n2) = Number::try_from((a2, &self.heap)) {
                            if n1 != n2 {
                                return true;
                            } else {
                                continue;
                            }
                        }
                    }

                    if a1 != a2 {
                        return true;
                    }
                }
            }
        }

        // did the two iterators expire at the same step?
        iter.first_to_expire != Ordering::Equal
    }

    pub(super) fn compare_term_test(&self, a1: &Addr, a2: &Addr) -> Option<Ordering> {
        let mut iter = self.zipped_acyclic_pre_order_iter(*a1, *a2);

        while let Some((v1, v2)) = iter.next() {
            let order_cat_v1 = v1.order_category(&self.heap);
            let order_cat_v2 = v2.order_category(&self.heap);

            if order_cat_v1 != order_cat_v2 {
                return Some(order_cat_v1.cmp(&order_cat_v2));
            }

            match order_cat_v1 {
                Some(TermOrderCategory::Variable) => {
                    let v1 = v1.as_var().unwrap();
                    let v2 = v2.as_var().unwrap();

                    if v1 != v2 {
                        return Some(v1.cmp(&v2));
                    }
                }
                Some(TermOrderCategory::FloatingPoint) => {
                    if let Addr::Float(f1) = v1 {
                        if let Addr::Float(f2) = v2 {
                            return Some(f1.cmp(&f2));
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }
                Some(TermOrderCategory::Integer) => match (v1, v2) {
                    (Addr::Con(h1), Addr::Con(h2)) => {
                        if let Ok(n1) = Number::try_from(&self.heap[h1]) {
                            if let Ok(n2) = Number::try_from(&self.heap[h2]) {
                                if n1 != n2 {
                                    return Some(n1.cmp(&n2));
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Con(h1), v2) => {
                        if let Ok(n1) = Number::try_from(&self.heap[h1]) {
                            if let Ok(n2) = Number::try_from(&HeapCellValue::Addr(v2)) {
                                if n1 != n2 {
                                    return Some(n1.cmp(&n2));
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (v1, Addr::Con(h2)) => {
                        if let Ok(n1) = Number::try_from(&HeapCellValue::Addr(v1)) {
                            if let Ok(n2) = Number::try_from(&self.heap[h2]) {
                                if n1 != n2 {
                                    return Some(n1.cmp(&n2));
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (v1, v2) => {
                        if let Ok(n1) = Number::try_from(&HeapCellValue::Addr(v1)) {
                            if let Ok(n2) = Number::try_from(&HeapCellValue::Addr(v2)) {
                                if n1 != n2 {
                                    return Some(n1.cmp(&n2));
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                },
                Some(TermOrderCategory::Atom) => match (v1, v2) {
                    (Addr::Con(h1), Addr::Con(h2)) => {
                        if let HeapCellValue::Atom(ref n1, _) = &self.heap[h1] {
                            if let HeapCellValue::Atom(ref n2, _) = &self.heap[h2] {
                                if n1 != n2 {
                                    return Some(n1.cmp(&n2));
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Con(h1), Addr::Char(c)) => {
                        if let HeapCellValue::Atom(ref n1, _) = &self.heap[h1] {
                            if n1.is_char() {
                                if n1.as_str().chars().next() != Some(c) {
                                    return Some(n1.as_str().chars().next().cmp(&Some(c)));
                                }
                            } else {
                                return Some(Ordering::Greater);
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Char(c), Addr::Con(h1)) => {
                        if let HeapCellValue::Atom(ref n1, _) = &self.heap[h1] {
                            if n1.is_char() {
                                if n1.as_str().chars().next() != Some(c) {
                                    return Some(Some(c).cmp(&n1.as_str().chars().next()));
                                }
                            } else {
                                return Some(Ordering::Less);
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::EmptyList, Addr::Con(h)) => {
                        if let HeapCellValue::Atom(ref n1, _) = &self.heap[h] {
                            if "[]" != n1.as_str() {
                                return Some("[]".cmp(n1.as_str()));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Con(h), Addr::EmptyList) => {
                        if let HeapCellValue::Atom(ref n1, _) = &self.heap[h] {
                            if "[]" != n1.as_str() {
                                return Some(n1.as_str().cmp("[]"));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Char(c1), Addr::Char(c2)) => {
                        if c1 != c2 {
                            return Some(c1.cmp(&c2));
                        }
                    }
                    (Addr::Char(c), Addr::EmptyList) => {
                        return if c == '[' {
                            Some(Ordering::Less)
                        } else {
                            Some(c.cmp(&'['))
                        };
                    }
                    (Addr::EmptyList, Addr::Char(c)) => {
                        return if c == '[' {
                            Some(Ordering::Greater)
                        } else {
                            Some('['.cmp(&c))
                        };
                    }
                    (Addr::EmptyList, Addr::EmptyList) => {}
                    _ => {
                        return None;
                    }
                },
                Some(TermOrderCategory::Compound) => match (v1, v2) {
                    (Addr::Lis(_), Addr::Lis(_)) => {}
                    (pstr1 @ Addr::PStrLocation(..), pstr2 @ Addr::PStrLocation(..)) => {
                        let mut i1 = self.heap_pstr_iter(pstr1);
                        let mut i2 = self.heap_pstr_iter(pstr2);

                        let ordering = compare_pstr_prefixes(&mut i1, &mut i2);

                        if let Some(ordering) = ordering {
                            if ordering != Ordering::Equal {
                                return Some(ordering);
                            }
                        } else {
                            let (lstack, rstack) = iter.stack();

                            lstack.pop();
                            lstack.pop();

                            rstack.pop();
                            rstack.pop();

                            lstack.push(i1.focus());
                            rstack.push(i2.focus());
                        }
                    }
                    (Addr::Str(h1), Addr::Str(h2)) => {
                        if let HeapCellValue::NamedStr(a1, ref n1, _) = &self.heap[h1] {
                            if let HeapCellValue::NamedStr(a2, ref n2, _) = &self.heap[h2] {
                                if a1 != a2 || n1.as_str() != n2.as_str() {
                                    return Some(
                                        a1.cmp(&a2).then_with(|| n1.as_str().cmp(n2.as_str())),
                                    );
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Lis(_), Addr::PStrLocation(..))
                    | (Addr::PStrLocation(..), Addr::Lis(_)) => {}
                    (Addr::Lis(_), Addr::Str(s)) => {
                        if let &HeapCellValue::NamedStr(a1, ref n1, _) = &self.heap[s] {
                            if a1 != 2 || n1.as_str() != "." {
                                return Some(a1.cmp(&2).then_with(|| n1.as_str().cmp(".")));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Str(s), Addr::Lis(_)) => {
                        if let &HeapCellValue::NamedStr(a1, ref n1, _) = &self.heap[s] {
                            if a1 != 2 || n1.as_str() != "." {
                                return Some(2.cmp(&a1).then_with(|| ".".cmp(n1.as_str())));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::PStrLocation(..), Addr::Str(s)) => {
                        if let &HeapCellValue::NamedStr(a1, ref n1, _) = &self.heap[s] {
                            if a1 != 2 || n1.as_str() != "." {
                                return Some(a1.cmp(&2).then_with(|| n1.as_str().cmp(".")));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (Addr::Str(s), Addr::PStrLocation(..)) => {
                        if let &HeapCellValue::NamedStr(a1, ref n1, _) = &self.heap[s] {
                            if a1 != 2 || n1.as_str() != "." {
                                return Some(2.cmp(&a1).then_with(|| ".".cmp(n1.as_str())));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {
                        return None;
                    }
                },
                None => {
                    return None;
                }
            }
        }

        Some(iter.first_to_expire)
    }

    pub(super) fn reset_block(&mut self, addr: Addr) {
        match self.store(addr) {
            Addr::Usize(b) => self.block = b,
            _ => self.fail = true,
        };
    }

    pub(super) fn execute_inlined(&mut self, inlined: &InlinedClauseType) {
        match inlined {
            &InlinedClauseType::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self, self.get_number(at_1));
                let n2 = try_or_fail!(self, self.get_number(at_2));

                self.compare_numbers(cmp, n1, n2);
            }
            &InlinedClauseType::IsAtom(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::Con(h) => {
                        if let HeapCellValue::Atom(..) = &self.heap[h] {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    Addr::Char(_) => self.p += 1,
                    Addr::EmptyList => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsAtomic(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::Char(_)
                    | Addr::Con(_)
                    | Addr::EmptyList
                    | Addr::Fixnum(_)
                    | Addr::Float(_)
                    | Addr::Usize(_) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsInteger(r1) => {
                let d = self.store(self.deref(self[r1]));

                match Number::try_from((d, &self.heap)) {
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

                match d {
                    Addr::Str(_) | Addr::Lis(_) | Addr::PStrLocation(..) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsFloat(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::Float(_) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsNumber(r1) => match self.store(self.deref(self[r1])) {
                Addr::Float(_) => self.p += 1,
                d => match Number::try_from((d, &self.heap)) {
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
                },
            },
            &InlinedClauseType::IsRational(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::Con(h) => {
                        if let HeapCellValue::Rational(_) = &self.heap[h] {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => {
                        self.fail = true;
                    }
                };
            }
            &InlinedClauseType::IsNonVar(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                        self.fail = true;
                    }
                    _ => {
                        self.p += 1;
                    }
                };
            }
            &InlinedClauseType::IsVar(r1) => {
                let d = self.store(self.deref(self[r1]));

                match d {
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        self.p += 1;
                    }
                    _ => {
                        self.fail = true;
                    }
                };
            }
        }
    }

    fn try_functor_compound_case(
        &mut self,
        name: ClauseName,
        arity: usize,
        spec: Option<SharedOpDesc>,
    ) {
        let name = self.heap.to_unifiable(HeapCellValue::Atom(name, spec));
        self.try_functor_unify_components(name, arity);
    }

    fn try_functor_unify_components(&mut self, name: Addr, arity: usize) {
        let a2 = self[temp_v!(2)];
        let a3 = self[temp_v!(3)];

        (self.unify_fn)(self, a2, name);

        if !self.fail {
            (self.unify_fn)(self, a3, Addr::Usize(arity));
        }
    }

    fn try_functor_fabricate_struct(
        &mut self,
        name: ClauseName,
        arity: usize,
        spec: Option<SharedOpDesc>,
        op_dir: &OpDir,
        r: Ref,
    ) {
        let spec = spec.and_then(|spec| {
            if spec.arity() != arity {
                fetch_op_spec(name.clone(), arity, op_dir)
            } else {
                Some(spec)
            }
        });

        let f_a = if name.as_str() == "." && arity == 2 {
            Addr::Lis(self.heap.h())
        } else {
            self.heap
                .to_unifiable(HeapCellValue::NamedStr(arity, name, spec))
        };

        let h = self.heap.h();

        for i in 0..arity {
            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h + i)));
        }

        (self.bind_fn)(self, r, f_a);
    }

    pub(super) fn try_functor(&mut self, op_dir: &OpDir) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("functor"), 3);
        let a1 = self.store(self.deref(self[temp_v!(1)]));

        match a1 {
            Addr::Stream(_) => {
                self.fail = true;
            }
            Addr::Char(_)
            | Addr::Con(_)
            | Addr::Fixnum(_)
            | Addr::Float(_)
            | Addr::EmptyList
            | Addr::Usize(_) => {
                self.try_functor_unify_components(a1, 0);
            }
            Addr::Str(o) => match self.heap.clone(o) {
                HeapCellValue::NamedStr(arity, name, spec) => {
                    let spec = fetch_op_spec_from_existing(name.clone(), arity, spec, &op_dir);

                    self.try_functor_compound_case(name, arity, spec)
                }
                _ => {
                    self.fail = true;
                }
            },
            Addr::Lis(_) | Addr::PStrLocation(..) => {
                let spec = fetch_op_spec_from_existing(clause_name!("."), 2, None, &op_dir);

                self.try_functor_compound_case(clause_name!("."), 2, spec)
            }
            Addr::AttrVar(..) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                let name = self.store(self.deref(self[temp_v!(2)]));
                let arity = self.store(self.deref(self[temp_v!(3)]));

                if name.is_ref() || arity.is_ref() {
                    // 8.5.1.3 a) & 8.5.1.3 b)
                    return Err(self.error_form(MachineError::instantiation_error(), stub));
                }

                let arity = match Number::try_from((arity, &self.heap)) {
                    Ok(Number::Fixnum(n)) => Some(n),
                    Ok(Number::Integer(n)) => n.to_isize(),
                    Ok(Number::Rational(n)) if n.denom() == &1 => n.numer().to_isize(),
                    _ => match arity {
                        arity => {
                            return Err(self.error_form(
                                MachineError::type_error(self.heap.h(), ValidType::Integer, arity),
                                stub,
                            ));
                        }
                    },
                };

                let arity = match arity {
                    Some(arity) => arity,
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                if arity > MAX_ARITY as isize {
                    // 8.5.1.3 f)
                    let rep_err = MachineError::representation_error(RepFlag::MaxArity);
                    return Err(self.error_form(rep_err, stub));
                } else if arity < 0 {
                    // 8.5.1.3 g)
                    let arity = Number::Integer(Rc::new(Integer::from(arity)));
                    let dom_err =
                        MachineError::domain_error(DomainErrorType::NotLessThanZero, arity);

                    return Err(self.error_form(dom_err, stub));
                }

                match name {
                    Addr::Char(_)
                    | Addr::Con(_)
                    | Addr::Fixnum(_)
                    | Addr::Float(_)
                    | Addr::EmptyList
                    | Addr::PStrLocation(..)
                    | Addr::Usize(_)
                        if arity == 0 =>
                    {
                        (self.unify_fn)(self, a1, name);
                    }
                    Addr::Con(h) => {
                        if let HeapCellValue::Atom(name, spec) = self.heap.clone(h) {
                            self.try_functor_fabricate_struct(
                                name,
                                arity as usize,
                                spec,
                                &op_dir,
                                a1.as_var().unwrap(),
                            );
                        } else {
                            // 8.5.1.3 e)
                            return Err(self.error_form(
                                MachineError::type_error(self.heap.h(), ValidType::Atom, name),
                                stub,
                            ));
                        }
                    }
                    Addr::Char(c) => {
                        self.try_functor_fabricate_struct(
                            clause_name!(c.to_string(), self.atom_tbl),
                            arity as usize,
                            None,
                            &op_dir,
                            a1.as_var().unwrap(),
                        );
                    }
                    _ => {
                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::Atomic, name),
                            stub,
                        ));
                    } // 8.5.1.3 c)
                }
            }
            _ => {
                self.fail = true;
            }
        }

        Ok(())
    }

    pub(super) fn term_dedup(&self, list: &mut Vec<Addr>) {
        let mut result = vec![];

        for a2 in list.iter() {
            if let Some(a1) = result.last() {
                if self.compare_term_test(&a1, &a2) == Some(Ordering::Equal) {
                    continue;
                }
            }

            result.push(*a2);
        }

        *list = result;
    }

    pub(super) fn integers_to_bytevec(&self, r: RegType, caller: MachineStub) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();

        match self.try_from_list(r, caller) {
            Err(_) => {
                unreachable!()
            }
            Ok(addrs) => {
                for addr in addrs {
                    let addr = self.store(self.deref(addr));

                    match Number::try_from((addr, &self.heap)) {
                        Ok(Number::Fixnum(n)) => {
                            match u8::try_from(n) {
                                Ok(b) => {
                                    bytes.push(b);
                                }
                                Err(_) => {}
                            }

                            continue;
                        }
                        Ok(Number::Integer(n)) => {
                            if let Some(b) = n.to_u8() {
                                bytes.push(b);
                            }

                            continue;
                        }
                        _ => {}
                    }
                }
            }
        }
        bytes
    }

    pub(super) fn try_from_list(
        &self,
        r: RegType,
        caller: MachineStub,
    ) -> Result<Vec<Addr>, MachineStub> {
        let a1 = self.store(self.deref(self[r]));

        match a1 {
            Addr::Lis(l) => self.try_from_inner_list(vec![], l, caller, a1),
            Addr::PStrLocation(h, n) => self.try_from_partial_string(vec![], h, n, caller, a1),
            Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                Err(self.error_form(MachineError::instantiation_error(), caller))
            }
            Addr::EmptyList => Ok(vec![]),
            _ => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::List, a1),
                caller,
            )),
        }
    }

    fn try_from_inner_list(
        &self,
        mut result: Vec<Addr>,
        mut l: usize,
        caller: MachineStub,
        a1: Addr,
    ) -> Result<Vec<Addr>, MachineStub> {
        result.push(self.heap[l].as_addr(l));
        l += 1;

        loop {
            match &self.heap[l] {
                HeapCellValue::Addr(ref addr) => match self.store(self.deref(*addr)) {
                    Addr::Lis(hcp) => {
                        result.push(self.heap[hcp].as_addr(hcp));
                        l = hcp + 1;
                    }
                    Addr::PStrLocation(h, n) => {
                        return self.try_from_partial_string(result, h, n, caller, a1);
                    }
                    Addr::EmptyList => {
                        break;
                    }
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                        return Err(self.error_form(MachineError::instantiation_error(), caller))
                    }
                    _ => {
                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::List, a1),
                            caller,
                        ))
                    }
                },
                _ => {
                    return Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::List, a1),
                        caller,
                    ))
                }
            }
        }

        Ok(result)
    }

    fn try_from_partial_string(
        &self,
        mut chars: Vec<Addr>,
        mut h: usize,
        mut n: usize,
        caller: MachineStub,
        a1: Addr,
    ) -> Result<Vec<Addr>, MachineStub> {
        loop {
            if let &HeapCellValue::PartialString(ref pstr, has_tail) = &self.heap[h] {
                chars.extend(pstr.range_from(n..).map(Addr::Char));

                if !has_tail {
                    return Ok(chars);
                }

                let tail = self.heap[h + 1].as_addr(h + 1);

                match self.store(self.deref(tail)) {
                    Addr::EmptyList => {
                        return Ok(chars);
                    }
                    Addr::Lis(l) => {
                        return self.try_from_inner_list(chars, l, caller, a1);
                    }
                    Addr::PStrLocation(h1, n1) => {
                        chars.push(Addr::Char('\u{0}'));

                        h = h1;
                        n = n1;
                    }
                    _ => {
                        return Err(self.error_form(
                            MachineError::type_error(self.heap.h(), ValidType::List, a1),
                            caller,
                        ))
                    }
                }
            } else {
                unreachable!()
            }
        }
    }

    // see 8.4.4.3 of Draft Technical Corrigendum 2 for an error guide.
    pub(super) fn project_onto_key(&self, a: Addr) -> Result<Addr, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.store(self.deref(a)) {
            Addr::HeapCell(_) | Addr::StackCell(..) => {
                Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            Addr::Str(s) => match self.heap.clone(s) {
                HeapCellValue::NamedStr(2, ref name, Some(_)) if *name == clause_name!("-") => {
                    Ok(Addr::HeapCell(s + 1))
                }
                _ => Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Pair,
                        self.heap[s].as_addr(s),
                    ),
                    stub,
                )),
            },
            a => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Pair, a),
                stub,
            )),
        }
    }

    pub(super) fn copy_term(&mut self, attr_var_policy: AttrVarPolicy) {
        let old_h = self.heap.h();

        let a1 = self[temp_v!(1)];
        let a2 = self[temp_v!(2)];

        copy_term(CopyTerm::new(self), a1, attr_var_policy);

        (self.unify_fn)(self, Addr::HeapCell(old_h), a2);
    }

    // returns true on failure.
    pub(super) fn structural_eq_test(&self) -> bool {
        let a1 = self[temp_v!(1)];
        let a2 = self[temp_v!(2)];

        let mut var_pairs = IndexMap::new();

        let iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        for (v1, v2) in iter {
            match (
                self.heap.index_addr(&v1).as_ref(),
                self.heap.index_addr(&v2).as_ref(),
            ) {
                (
                    HeapCellValue::Addr(Addr::Lis(_)),
                    HeapCellValue::Addr(Addr::PStrLocation(..)),
                )
                | (
                    HeapCellValue::Addr(Addr::PStrLocation(..)),
                    HeapCellValue::Addr(Addr::Lis(_)),
                ) => {}
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) => {
                    if ar1 != ar2 || n1 != n2 {
                        return true;
                    }
                }
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) => {}
                (
                    &HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    &HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    &HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    &HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    &HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    &HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    &HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    &HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    &HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    &HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    &HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                ) => match (var_pairs.get(&v1), var_pairs.get(&v2)) {
                    (Some(ref v2_p), Some(ref v1_p)) if **v1_p == v1 && **v2_p == v2 => {
                        continue;
                    }
                    (Some(_), _) | (_, Some(_)) => {
                        return true;
                    }
                    (None, None) => {
                        var_pairs.insert(v1, v2);
                        var_pairs.insert(v2, v1);
                    }
                },
                (
                    HeapCellValue::PartialString(ref pstr1, has_tail_1),
                    HeapCellValue::PartialString(ref pstr2, has_tail_2),
                ) => {
                    if has_tail_1 != has_tail_2 {
                        return true;
                    }

                    let pstr1_iter = pstr1.range_from(0..);
                    let pstr2_iter = pstr2.range_from(0..);

                    for (c1, c2) in pstr1_iter.zip(pstr2_iter) {
                        if c1 != c2 {
                            return true;
                        }
                    }
                }
                (
                    HeapCellValue::Addr(Addr::PStrLocation(..)),
                    HeapCellValue::Addr(Addr::PStrLocation(..)),
                ) => {}
                (
                    HeapCellValue::Atom(ref n1, ref spec_1),
                    HeapCellValue::Atom(ref n2, ref spec_2),
                ) => {
                    if n1 != n2 || spec_1 != spec_2 {
                        return true;
                    }
                }
                (HeapCellValue::DBRef(ref db_ref_1), HeapCellValue::DBRef(ref db_ref_2)) => {
                    if db_ref_1 != db_ref_2 {
                        return true;
                    }
                }
                (v1, v2) => {
                    if let Ok(n1) = Number::try_from(v1) {
                        if let Ok(n2) = Number::try_from(v2) {
                            if n1 != n2 {
                                return true;
                            } else {
                                continue;
                            }
                        } else {
                            return true;
                        }
                    }

                    match (v1, v2) {
                        (HeapCellValue::Addr(a1), HeapCellValue::Addr(a2)) => {
                            if a1 != a2 {
                                return true;
                            }
                        }
                        _ => {
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    // returns true on failure.
    pub(super) fn ground_test(&self) -> bool {
        let a = self.store(self.deref(self[temp_v!(1)]));

        for v in self.acyclic_pre_order_iter(a) {
            match v {
                Addr::HeapCell(..) => return true,
                Addr::StackCell(..) => return true,
                Addr::AttrVar(..) => return true,
                _ => {}
            }
        }

        false
    }

    pub(super) fn setup_built_in_call(&mut self, ct: BuiltInClauseType) {
        self.num_of_args = ct.arity();
        self.b0 = self.b;

        self.p = CodePtr::BuiltInClause(ct, self.p.local());
    }

    pub(super) fn allocate(&mut self, num_cells: usize) {
        let e = self.stack.allocate_and_frame(num_cells);
        let and_frame = self.stack.index_and_frame_mut(e);

        and_frame.prelude.e = self.e;
        and_frame.prelude.cp = self.cp;

        self.e = e;
        self.p += 1;
    }

    pub(super) fn deallocate(&mut self) {
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
        let err = MachineError::interrupt_error();
        let src = functor!("repl");
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
            &ClauseType::Named(ref name, _, ref idx) | &ClauseType::Op(ref name, _, ref idx) => {
                try_or_fail!(
                    self,
                    call_policy.context_call(self, name.clone(), arity, idx)
                )
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

    pub(super) fn execute_ctrl_instr(
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
                                self.registers[self.num_of_args + 1] = Addr::Usize(self.cc);
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

                        self.cc = match self.stack.index_or_frame(self.b)[n - 1] {
                            Addr::Usize(cc) => cc,
                            _ => unreachable!(),
                        };

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
                            try_or_fail!(self, call_policy.trust(self, offset, global_variables,))
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
                or_frame.prelude.h = self.heap.h();
                or_frame.prelude.b0 = self.b0;

                or_frame.prelude.attr_var_init_queue_b = self.attr_var_init.attr_var_queue.len();
                or_frame.prelude.attr_var_init_bindings_b = self.attr_var_init.bindings.len();

                self.b = b;

                for i in 1..n + 1 {
                    self.stack.index_or_frame_mut(b)[i - 1] = self.registers[i];
                }

                self.hb = self.heap.h();
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
                                        self.registers[self.num_of_args + 1] = Addr::Usize(self.cc);
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

                                self.cc = match self.stack.index_or_frame(self.b)[n - 1] {
                                    Addr::Usize(cc) => cc,
                                    _ => unreachable!(),
                                };

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
                                        self.registers[self.num_of_args + 1] = Addr::Usize(self.cc);
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

                                self.cc = match self.stack.index_or_frame(self.b)[n - 1] {
                                    Addr::Usize(cc) => cc,
                                    _ => unreachable!(),
                                };

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
                or_frame.prelude.h = self.heap.h();
                or_frame.prelude.b0 = self.b0;
                or_frame.prelude.attr_var_init_queue_b = self.attr_var_init.attr_var_queue.len();
                or_frame.prelude.attr_var_init_bindings_b = self.attr_var_init.attr_var_queue.len();

                self.b = b;

                for i in 1..n + 1 {
                    self.stack.index_or_frame_mut(b)[i - 1] = self.registers[i];
                }

                self.hb = self.heap.h();
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

                self[r] = Addr::CutPoint(b0);
                self.p += 1;
            }
            &CutInstruction::GetLevelAndUnify(r) => {
                let b0 = self[perm_v!(1)];
                let a = self[r];

                (self.unify_fn)(self, a, b0);
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
