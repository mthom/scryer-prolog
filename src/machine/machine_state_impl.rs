use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::machine::attributed_variables::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::stack::*;
use crate::machine::unify::*;
use crate::offset_table::*;
use crate::parser::ast::*;
use crate::parser::dashu::{Integer, Rational};
use crate::types::*;

use indexmap::IndexSet;

use std::cmp::Ordering;
use std::convert::TryFrom;

impl MachineState {
    pub(crate) fn new() -> Self {
        let mut heap = Heap::with_cell_capacity(256 * 256).unwrap();

        // the cell at index 0 is an interstitial cell reserved for use by the runtime.
        heap.push_cell(empty_list_as_cell!()).unwrap();
        heap.store_resource_error();

        MachineState {
            arena: Arena::new(),
            atom_tbl: AtomTable::new(),
            pdl: Vec::with_capacity(1024),
            s: HeapPtr::default(),
            s_offset: 0,
            p: 0,
            oip: 0,
            iip: 0,
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: 0,
            attr_var_init: AttrVarInitializer::new(0),
            fail: false,
            heap,
            mode: MachineMode::Write,
            stack: Stack::new(),
            registers: [heap_loc_as_cell!(0); MAX_ARITY + 1], // self.registers[0] is never used.
            trail: vec![],
            tr: 0,
            hb: 0,
            block: 0,
            scc_block: 0,
            ball: Ball::new(),
            ball_stack: vec![],
            lifted_heap: Heap::new(),
            interms: vec![Number::default(); 256],
            cont_pts: Vec::with_capacity(256),
            cwil: CWIL::new(),
            flags: MachineFlags::default(),
            cc: 0,
            global_clock: 0,
            dynamic_mode: FirstOrNext::First,
            unify_fn: MachineState::unify,
            bind_fn: MachineState::bind,
            run_cleaners_fn: |_| false,
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

    #[inline]
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
            TrailRef::AttrVarListLink(h, l) => {
                if h < self.hb {
                    self.trail.push(TrailEntry::build_with(
                        TrailEntryTag::TrailedAttrVarListLink,
                        h as u64,
                    ));

                    self.trail.push(TrailEntry::build_with(
                        TrailEntryTag::TrailedAttachedValue,
                        l as u64,
                    ));

                    self.tr += 2;
                }
            }
            TrailRef::BlackboardEntry(key_atom) => {
                self.trail.push(TrailEntry::build_with(
                    TrailEntryTag::TrailedBlackboardEntry,
                    key_atom.index,
                ));

                self.tr += 1;
            }
            TrailRef::BlackboardOffset(key_atom, value_cell) => {
                self.trail.push(TrailEntry::build_with(
                    TrailEntryTag::TrailedBlackboardOffset,
                    key_atom.index,
                ));

                self.trail
                    .push(TrailEntry::from_bytes(value_cell.into_bytes()));

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
                    self.trail(TrailRef::Ref(r1));
                }
                RefTag::HeapCell => {
                    self.heap[r1.get_value() as usize] = t2;
                    self.trail(TrailRef::Ref(r1));
                }
                RefTag::AttrVar => {
                    self.bind_attr_var(r1.get_value() as usize, t2);
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

    #[inline]
    pub(super) fn bind_with_occurs_check_wrapper(&mut self, r: Ref, value: HeapCellValue) {
        let mut unifier = CompositeUnifierForOccursCheck::from(DefaultUnifier::from(self));
        unifier.bind(r, value);
    }

    #[inline]
    pub(super) fn bind_with_occurs_check_with_error_wrapper(
        &mut self,
        r: Ref,
        value: HeapCellValue,
    ) {
        let mut unifier = CompositeUnifierForOccursCheckWithError::from(DefaultUnifier::from(self));

        unifier.bind(r, value);
    }

    pub fn unify(&mut self) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_internal();
    }

    pub fn unify_atom(&mut self, atom: Atom, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_atom(atom, value);
    }

    pub fn unify_char(&mut self, c: char, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_char(c, value);
    }

    pub fn unify_fixnum(&mut self, n1: Fixnum, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_fixnum(n1, value);
    }

    pub fn unify_ginteger(&mut self, n1: GInteger, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_ginteger(n1, value);
    }

    pub fn unify_big_int(&mut self, n1: TypedArenaPtr<Integer>, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_big_integer(n1, value);
    }

    pub fn unify_rational(&mut self, n1: TypedArenaPtr<Rational>, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_big_rational(n1, value);
    }

    pub fn unify_f64(&mut self, f1: F64Offset, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_f64(f1, value);
    }

    pub fn unify_constant(&mut self, ptr: UntypedArenaPtr, value: HeapCellValue) {
        let mut unifier = DefaultUnifier::from(self);
        unifier.unify_constant(ptr, value);
    }

    pub(super) fn unify_with_occurs_check_with_error(&mut self) {
        let mut unifier = CompositeUnifierForOccursCheckWithError::from(DefaultUnifier::from(self));

        unifier.unify_internal();
    }

    pub(super) fn unify_with_occurs_check(&mut self) {
        let mut unifier = CompositeUnifierForOccursCheck::from(DefaultUnifier::from(self));
        unifier.unify_internal();
    }

    #[inline(always)]
    pub(super) fn effective_block(&self) -> usize {
        std::cmp::max(self.block, self.scc_block)
    }

    pub(super) fn set_ball(&mut self) {
        self.ball.reset();

        let addr = self.registers[1];

        self.ball.boundary = self.heap.cell_len();
        self.ball.pstr_boundary = step_or_resource_error!(
            self,
            copy_term(
                CopyBallTerm::new(
                    &mut self.attr_var_init.attr_var_queue,
                    &mut self.stack,
                    &mut self.heap,
                    &mut self.ball.stub,
                ),
                addr,
                AttrVarPolicy::DeepCopy,
            )
        );
    }

    #[inline(always)]
    pub(super) fn unwind_stack(&mut self) {
        self.b = self.effective_block();
        self.fail = true;
    }

    // return the read value and the succeeding HeapPtr
    pub(crate) fn read_s(&mut self) -> (HeapCellValue, usize) {
        match self.s {
            HeapPtr::HeapCell(h) => (self.deref(self.heap[h + self.s_offset]), 1),
            HeapPtr::PStr(byte_index) => {
                let mut char_iter = self.heap.char_iter(byte_index);

                if self.s_offset == 0 {
                    // read the car of the list
                    let c = char_iter.next().unwrap();
                    (char_as_cell!(c), c.len_utf8())
                } else {
                    // read the (self.s_offset)^{th} cdr of the list
                    // self.s_offset is the number of bytes offset into the PStr
                    // in this context, *not* the number of heap cells.
                    let new_h = byte_index + self.s_offset;
                    self.s_offset = 0;

                    if self.heap.char_iter(new_h).next().is_some() {
                        self.s = HeapPtr::PStr(new_h);
                        (pstr_loc_as_cell!(new_h), 0)
                    } else {
                        let h = Heap::pstr_tail_idx(new_h);
                        self.s = HeapPtr::HeapCell(h);
                        (self.deref(heap_loc_as_cell!(h)), 0)
                    }
                }
            }
        }
    }

    pub fn compare_term_test(&mut self, var_comparison: VarComparison) -> Option<Ordering> {
        let mut tabu_list = IndexSet::new();

        while let Some(s1) = self.pdl.pop() {
            let s1 = self.deref(s1);

            let s2 = self.pdl.pop().unwrap();
            let s2 = self.deref(s2);

            if s1 == s2 {
                continue;
            }

            let v1 = self.store(s1);
            let v2 = self.store(s2);

            let order_cat_v1 = v1.order_category(&self.heap);
            let order_cat_v2 = v2.order_category(&self.heap);

            if order_cat_v1 != order_cat_v2 {
                self.pdl.clear();
                return Some(order_cat_v1.cmp(&order_cat_v2));
            }

            match order_cat_v1 {
                Some(TermOrderCategory::Variable) => {
                    if let VarComparison::Distinct = var_comparison {
                        let v1 = v1.as_var().unwrap();
                        let v2 = v2.as_var().unwrap();

                        if v1 != v2 {
                            self.pdl.clear();
                            return Some(v1.cmp(&v2));
                        }
                    }
                }
                Some(TermOrderCategory::FloatingPoint) => {
                    let v1 = cell_as_f64_offset!(v1);
                    let v2 = cell_as_f64_offset!(v2);

                    let v1 = self.arena.f64_tbl.get_entry(v1);
                    let v2 = self.arena.f64_tbl.get_entry(v2);

                    if v1 != v2 {
                        self.pdl.clear();
                        return Some(v1.cmp(&v2));
                    }
                }
                Some(TermOrderCategory::Integer) => {
                    let v1 = Number::try_from((v1, &self.arena.f64_tbl)).unwrap();
                    let v2 = Number::try_from((v2, &self.arena.f64_tbl)).unwrap();

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
                                (HeapCellValueTag::Str, s) => {
                                    let n2 = cell_as_atom_cell!(self.heap[s])
                                        .get_name();

                                    if n1 != n2 {
                                        self.pdl.clear();
                                        return Some(n1.cmp(&n2));
                                    }
                                }
                                _ => {
                                    unreachable!();
                                }
                            )
                        }
                        (HeapCellValueTag::Str, s) => {
                            let n1 = cell_as_atom_cell!(self.heap[s])
                                .get_name();

                            read_heap_cell!(v2,
                                (HeapCellValueTag::Atom, (n2, _a2)) => {
                                    if n1 != n2 {
                                        self.pdl.clear();
                                        return Some(n1.cmp(&n2));
                                    }
                                }
                                (HeapCellValueTag::Str, s) => {
                                    let n2 = cell_as_atom_cell!(self.heap[s])
                                        .get_name();

                                    if n1 != n2 {
                                        self.pdl.clear();
                                        return Some(n1.cmp(&n2));
                                    }
                                }
                                _ => {
                                    unreachable!();
                                }
                            )
                        }
                        _ => {
                            unreachable!()
                        }
                    )
                }
                Some(TermOrderCategory::Compound) => {
                    read_heap_cell!(v1,
                        (HeapCellValueTag::Lis, l1) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::PStrLoc, l2) => {
                                    if tabu_list.contains(&(l1, l2)) {
                                        continue;
                                    }

                                    tabu_list.insert((l1, l2));

                                    // like the action of
                                    // partial_string_to_pdl here but
                                    // the ordering of PDL pushes is
                                    // (crucially for comparison
                                    // correctness) different.
                                    let (c, succ_cell) = self.heap.last_str_char_and_tail(l2);

                                    self.pdl.push(succ_cell);
                                    self.pdl.push(heap_loc_as_cell!(l1 + 1));

                                    self.pdl.push(char_as_cell!(c));
                                    self.pdl.push(heap_loc_as_cell!(l1));
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

                                    match (2, atom!(".")).cmp(&(arity, name)) {
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
                        (HeapCellValueTag::PStrLoc, l1) => {
                            read_heap_cell!(v2,
                                (HeapCellValueTag::PStrLoc, l2) => {
                                    if tabu_list.contains(&(l1, l2)) {
                                        continue;
                                    }

                                    tabu_list.insert((l1, l2));

                                    match self.heap.compare_pstr_segments(l1, l2) {
                                        PStrSegmentCmpResult::Continue(v1, v2) => {
                                            self.pdl.push(v1.offset_by(l1));
                                            self.pdl.push(v2.offset_by(l2));
                                        }
                                        PStrSegmentCmpResult::Less => {
                                            self.pdl.clear();
                                            return Some(Ordering::Less);
                                        }
                                        PStrSegmentCmpResult::Greater => {
                                            self.pdl.clear();
                                            return Some(Ordering::Greater);
                                        }
                                    }
                                }
                                (HeapCellValueTag::Lis, l2) => {
                                    if tabu_list.contains(&(l1, l2)) {
                                        continue;
                                    }

                                    tabu_list.insert((l1, l2));

                                    let (c, succ_cell) = self.heap.last_str_char_and_tail(l1);

                                    self.pdl.push(succ_cell);
                                    self.pdl.push(heap_loc_as_cell!(l2 + 1));

                                    self.pdl.push(char_as_cell!(c));
                                    self.pdl.push(heap_loc_as_cell!(l2));
                                }
                                (HeapCellValueTag::Str, s2) => {
                                    if tabu_list.contains(&(l1, s2)) {
                                        continue;
                                    }

                                    tabu_list.insert((l1, s2));

                                    let (n2, a2) = cell_as_atom_cell!(self.heap[s2])
                                        .get_name_and_arity();

                                    match (2, atom!(".")).cmp(&(a2,n2)) {
                                        Ordering::Equal => {
                                            let (c, succ_cell) = self.heap.last_str_char_and_tail(l1);

                                            self.pdl.push(heap_loc_as_cell!(s2+2));
                                            self.pdl.push(succ_cell);

                                            self.pdl.push(heap_loc_as_cell!(s2+1));
                                            self.pdl.push(char_as_cell!(c));
                                        }
                                        ordering => {
                                            self.pdl.clear();
                                            return Some(ordering);
                                        }
                                    }
                                }
                                _ => {
                                    unreachable!()
                                }
                            );
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

                                    match (a1,n1).cmp(&(a2, n2)) {
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

                                    match (a1,n1).cmp(&(2, atom!("."))) {
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
                                (HeapCellValueTag::PStrLoc, l2) => {
                                    let (n1, a1) = cell_as_atom_cell!(self.heap[s1])
                                        .get_name_and_arity();

                                    match (a1,n1).cmp(&(2, atom!("."))) {
                                        Ordering::Equal => {
                                            let (c, succ_cell) = self.heap.last_str_char_and_tail(l2);

                                            self.pdl.push(succ_cell);
                                            self.pdl.push(heap_loc_as_cell!(s1+2));

                                            self.pdl.push(char_as_cell!(c));
                                            self.pdl.push(heap_loc_as_cell!(s1+1));
                                        }
                                        ordering => {
                                            self.pdl.clear();
                                            return Some(ordering);
                                        }
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

    pub(crate) fn setup_call_n_init_goal_info(
        &mut self,
        goal: HeapCellValue,
        arity: usize,
    ) -> Result<(Atom, usize, usize), MachineStub> {
        Ok(read_heap_cell!(goal,
            (HeapCellValueTag::Str, s) => {
                let (name, narity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if narity + arity > MAX_ARITY {
                    let stub = functor_stub(atom!("call"), arity + 1);
                    let err = self.representation_error(RepFlag::MaxArity);
                    return Err(self.error_form(err, stub));
                }

                (name, narity, s)
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                if name == atom!("[]") {
                    let stub = functor_stub(atom!("call"), arity + 1);
                    let err = self.type_error(ValidType::Callable, goal);
                    return Err(self.error_form(err, stub));
                }

                (name, 0, 0)
            }
            /*
            (HeapCellValueTag::Char, c) => {
                (AtomTable::build_with(&self.atom_tbl, &c.to_string()), 0, 0)
            }
            */
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                let stub = functor_stub(atom!("call"), arity + 1);
                let err = self.instantiation_error();
                return Err(self.error_form(err, stub));
            }
            _ => {
                let stub = functor_stub(atom!("call"), arity + 1);
                let err = self.type_error(ValidType::Callable, goal);
                return Err(self.error_form(err, stub));
            }
        ))
    }

    pub(crate) fn setup_call_n(&mut self, arity: usize) -> Result<PredicateKey, MachineStub> {
        let addr = self.store(self.deref(self.registers[arity]));
        let (name, narity, s) = self.setup_call_n_init_goal_info(addr, arity)?;

        if narity > 0 {
            for i in (1..arity).rev() {
                self.registers[i + narity] = self.registers[i];
            }

            for i in 1..narity + 1 {
                self.registers[i] = self.heap[s + i];
            }
        }

        Ok((name, arity + narity - 1))
    }

    #[inline]
    pub fn is_cyclic_term(&mut self, term_loc: usize) -> bool {
        if self.heap[term_loc].is_stack_var() {
            return false;
        }

        let mut iter = cycle_detecting_stackless_preorder_iter(&mut self.heap, term_loc);
        for _ in iter.by_ref() {}
        iter.cycle_found()
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
                let n = match Number::try_from((n, &self.arena.f64_tbl)) {
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
                    Number::Integer(n) if usize::try_from(&*n).is_ok() => (&*n).try_into().unwrap(),
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
                            unify_fn!(*self, a3, heap_loc_as_cell!(o + n));
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::Lis, l) => {
                        if n == 1 || n == 2 {
                            let a3 = self.registers[3];
                            unify_fn!(*self, a3, heap_loc_as_cell!(l + n - 1));
                        } else {
                            self.fail = true;
                        }
                    }
                    (HeapCellValueTag::PStrLoc, pstr_loc) => {
                        if n == 1 || n == 2 {
                            let a3 = self.registers[3];
                            let mut char_iter = self.heap.char_iter(pstr_loc);

                            if let Some(c) = char_iter.next() {
                                if n == 1 {
                                    self.unify_char(c, a3);
                                } else if char_iter.next().is_some() {
                                    unify_fn!(*self, pstr_loc_as_cell!(pstr_loc + c.len_utf8()), a3);
                                } else {
                                    let tail_idx = Heap::pstr_tail_idx(pstr_loc + c.len_utf8());
                                    unify_fn!(*self, self.heap[tail_idx], a3);
                                }
                            } else {
                                unreachable!()
                            }
                        } else {
                            self.fail = true;
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

    // returns true on failure, false on success.
    pub fn eq_test(&mut self, h1: HeapCellValue, h2: HeapCellValue) -> bool {
        if h1 == h2 {
            return false;
        }

        compare_term_test!(self, h1, h2)
            .map(|o| o != Ordering::Equal)
            .unwrap_or(true)
    }

    #[inline(always)]
    fn try_functor_compound_case(&mut self, name: Atom, arity: usize) {
        self.try_functor_unify_components(atom_as_cell!(name), arity);
    }

    fn try_functor_unify_components(&mut self, name: HeapCellValue, arity: usize) {
        let a2 = self.deref(self.registers[2]);
        unify!(self, a2, name);

        if !self.fail {
            let a3 = self.store(self.deref(self.registers[3]));
            self.unify_fixnum(
                /* FIXME this is not safe */
                unsafe { Fixnum::build_with_unchecked(arity as i64) },
                a3,
            );
        }
    }

    fn try_functor_fabricate_struct(
        &mut self,
        name: Atom,
        arity: usize,
        r: Ref,
    ) -> Result<(), usize> {
        let h = self.heap.cell_len();
        let mut writer = self.heap.reserve(arity + 1)?;

        let f_a = if name == atom!(".") && arity == 2 {
            writer.write_with(|section| {
                section.push_cell(heap_loc_as_cell!(h));
                section.push_cell(heap_loc_as_cell!(h + 1));
            });

            list_loc_as_cell!(h)
        } else {
            writer.write_with(|section| {
                section.push_cell(atom_as_cell!(name, arity));

                for i in 0..arity {
                    section.push_cell(heap_loc_as_cell!(h + i + 1));
                }
            });

            if arity == 0 {
                heap_loc_as_cell!(h)
            } else {
                str_loc_as_cell!(h)
            }
        };

        (self.bind_fn)(self, r, f_a);
        Ok(())
    }

    pub fn try_functor(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("functor"), 3);
        let a1 = self.store(self.deref(self.registers[1]));

        read_heap_cell!(a1,
            (HeapCellValueTag::Cons | HeapCellValueTag::Fixnum | // | HeapCellValueTag::Char
             HeapCellValueTag::F64Offset) => {
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
            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => { // | HeapCellValueTag::CStr) => {
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

                let type_error = |machine_st: &mut Self, arity| {
                    let err = machine_st.type_error(ValidType::Integer, arity);
                    Err(machine_st.error_form(err, stub_gen()))
                };

                let arity = match Number::try_from((arity, &self.arena.f64_tbl)) {
                    Ok(Number::Float(_)) => {
                        return type_error(self, arity);
                    }
                    Ok(Number::Rational(n)) if !n.denominator().is_one() => {
                        return type_error(self, arity);
                    }
                    Ok(n) if n > MAX_ARITY => {
                        // 8.5.1.3 f)
                        let err = self.representation_error(RepFlag::MaxArity);
                        return Err(self.error_form(err, stub_gen()));
                    }
                    Ok(n) if n < 0 => {
                        // 8.5.1.3 g)
                        let err = self.domain_error(DomainErrorType::NotLessThanZero, n);
                        return Err(self.error_form(err, stub_gen()));
                    }
                    Ok(Number::Rational(n)) => {
                        let value: i64 = n.numerator().try_into().unwrap();
                        value
                    },
                    Ok(Number::Fixnum(n)) => n.get_num(),
                    Ok(Number::Integer(n)) => {
                        let value: i64 = (&*n).try_into().unwrap();
                        value
                    },
                    Err(_) => {
                        return type_error(self, arity);
                    }
                };

                read_heap_cell!(store_name,
                    (HeapCellValueTag::Cons | HeapCellValueTag::Fixnum | HeapCellValueTag::F64Offset)
                        if arity == 0 => {
                            self.bind(a1.as_var().unwrap(), deref_name);
                        }
                    (HeapCellValueTag::Atom, (name, atom_arity)) => {
                        debug_assert_eq!(atom_arity, 0);
                        resource_error_call_result!(
                            self,
                            self.try_functor_fabricate_struct(
                                name,
                                arity as usize,
                                a1.as_var().unwrap(),
                            )
                        );
                    }
                    (HeapCellValueTag::Str, s) => {
                        let (name, atom_arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        if atom_arity == 0 {
                            resource_error_call_result!(
                                self,
                                self.try_functor_fabricate_struct(
                                    name,
                                    arity as usize,
                                    a1.as_var().unwrap(),
                                )
                            );
                        } else {
                            let err = self.type_error(ValidType::Atomic, store_name);
                            return Err(self.error_form(err, stub_gen()));
                        }
                    }
                    (HeapCellValueTag::Cons | HeapCellValueTag::Fixnum |
                     HeapCellValueTag::F64Offset) if arity != 0 => {
                        let err = self.type_error(ValidType::Atom, store_name);
                        return Err(self.error_form(err, stub_gen())); // 8.5.1.3 e)
                    }
                    _ => {
                        let err = self.type_error(ValidType::Atomic, store_name);
                        return Err(self.error_form(err, stub_gen())); // 8.5.1.3 c)
                    }
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
        stub_gen: impl Fn() -> MachineStub,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        let value = self.store(self.deref(value));

        read_heap_cell!(value,
            (HeapCellValueTag::Lis, l) => {
                self.try_from_inner_list(vec![], l, stub_gen, value)
            }
            (HeapCellValueTag::PStrLoc, pstr_loc) => {
                self.try_from_partial_string(vec![], pstr_loc, stub_gen, value)
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar | HeapCellValueTag::Var) => {
                let err = self.instantiation_error();
                Err(self.error_form(err, stub_gen()))
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                if name == atom!("[]") && arity == 0 {
                    Ok(vec![])
                } else {
                    let err = self.type_error(ValidType::List, value);
                    Err(self.error_form(err, stub_gen()))
                }
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if name == atom!("[]") && arity == 0 {
                    Ok(vec![])
                } else {
                    let err = self.type_error(ValidType::List, value);
                    Err(self.error_form(err, stub_gen()))
                }
            }
            _ => {
                let err = self.type_error(ValidType::List, value);
                Err(self.error_form(err, stub_gen()))
            }
        )
    }

    fn try_from_inner_list(
        &mut self,
        mut result: Vec<HeapCellValue>,
        mut l: usize,
        stub_gen: impl Fn() -> MachineStub,
        a1: HeapCellValue,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        result.push(self.heap[l]);
        l += 1;

        loop {
            let value = self.store(self.deref(self.heap[l]));

            read_heap_cell!(value,
                (HeapCellValueTag::Lis, hcp) => {
                    result.push(self.heap[hcp]);
                    l = hcp + 1;
                }
                (HeapCellValueTag::PStrLoc, pstr_loc) => {
                    return self.try_from_partial_string(result, pstr_loc, stub_gen, a1);
                }
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s])
                        .get_name_and_arity();

                    if name == atom!("[]") && arity == 0 {
                        break;
                    } else {
                        let err = self.type_error(ValidType::List, a1);
                        return Err(self.error_form(err, stub_gen()));
                    }
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
                    if value.is_var() {
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
        pstr_loc: usize,
        stub_gen: impl Fn() -> MachineStub,
        a1: HeapCellValue,
    ) -> Result<Vec<HeapCellValue>, MachineStub> {
        self.heap[0] = pstr_loc_as_cell!(pstr_loc);
        let mut heap_pstr_iter = HeapPStrIter::new(&self.heap, 0);

        while let Some(iteratee) = heap_pstr_iter.next() {
            match iteratee {
                PStrIteratee::Char { value: c, .. } => chars.push(char_as_cell!(c)),
                PStrIteratee::PStrSlice {
                    slice_loc,
                    slice_len,
                } => {
                    let pstr = heap_pstr_iter.heap.slice_to_str(slice_loc, slice_len);
                    chars.extend(pstr.chars().map(|c| char_as_cell!(c)));
                }
            }
        }

        let end_cell = heap_pstr_iter.heap[heap_pstr_iter.focus()];

        if heap_pstr_iter.is_cyclic() || end_cell != empty_list_as_cell!() {
            let err = self.type_error(ValidType::List, a1);
            return Err(self.error_form(err, stub_gen()));
        }

        Ok(chars)
    }

    // returns true on failure.
    pub fn ground_test(&mut self) -> bool {
        let term = self.store(self.deref(self.registers[1]));

        if term.is_stack_var() {
            return true;
        }

        for term in eager_stackful_preorder_iter(&mut self.heap, term) {
            if term.is_var() {
                return true;
            }
        }

        false
    }

    pub fn integers_to_bytevec(
        &mut self,
        value: HeapCellValue,
        stub_gen: impl Fn() -> MachineStub,
    ) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();

        match self.try_from_list(value, stub_gen) {
            Err(_) => {
                unreachable!()
            }
            Ok(addrs) => {
                for addr in addrs {
                    let addr = self.store(self.deref(addr));

                    match Number::try_from((addr, &self.arena.f64_tbl)) {
                        Ok(Number::Fixnum(n)) => {
                            if let Ok(b) = u8::try_from(n.get_num()) {
                                bytes.push(b)
                            }
                        }
                        Ok(Number::Integer(n)) => {
                            let b: u8 = (&*n).try_into().unwrap();

                            bytes.push(b);
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

    pub fn deallocate(&mut self) {
        let e = self.e;
        let frame = self.stack.index_and_frame(e);

        self.cp = frame.prelude.cp;
        self.e = frame.prelude.e;

        if self.e > self.b {
            let frame = self.stack.index_and_frame(self.e);
            let size = AndFrame::size_of(frame.prelude.num_cells);

            self.stack.truncate(self.e + size);
        }

        self.p += 1;
    }

    pub fn throw_interrupt_exception(&mut self) {
        let err = self.interrupt_error();
        let src = functor_stub(atom!("repl"), 0);
        let err = self.error_form(err, src);

        self.throw_exception(err);
    }
}
