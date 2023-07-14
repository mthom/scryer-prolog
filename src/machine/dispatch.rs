use crate::arena::*;
use crate::atom_table::*;
use crate::instructions::*;
use crate::machine::*;
use crate::machine::arithmetic_ops::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_state::*;
use crate::types::*;

use crate::try_numeric_result;

use fxhash::FxBuildHasher;

macro_rules! step_or_fail {
    ($self:expr, $step_e:expr) => {
        if $self.machine_st.fail {
            $self.machine_st.backtrack();
        } else {
            $step_e;
        }
    };
}

macro_rules! try_or_throw {
    ($s:expr, $e:expr) => {{
        match $e {
            Ok(val) => val,
            Err(msg) => {
                $s.throw_exception(msg);
                $s.backtrack();
                continue;
            }
        }
    }};
}

macro_rules! try_or_throw_gen {
    ($s:expr, $e:expr) => {{
        match $e {
            Ok(val) => val,
            Err(msg_fn) => {
                let e = msg_fn($s);
                $s.throw_exception(e);
                $s.backtrack();
                continue;
            }
        }
    }};
}

static INSTRUCTIONS_PER_INTERRUPT_POLL: usize = 256;

impl MachineState {
    #[inline(always)]
    fn compare(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("compare"), 3);

        let a1 = self.store(self.deref(self.registers[1]));
        let a2 = self.registers[2];
        let a3 = self.registers[3];

        let check_atom = |machine_st: &mut MachineState, name: Atom, arity: usize| -> Result<(), MachineStub> {
            match name {
                atom!(">") | atom!("<") | atom!("=") if arity == 0 => {
                    Ok(())
                }
                _ => {
                    let err = machine_st.domain_error(DomainErrorType::Order, a1);
                    Err(machine_st.error_form(err, stub_gen()))
                }
            }
        };

        read_heap_cell!(a1,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                check_atom(self, name, arity)?;
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                check_atom(self, name, arity)?;
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
            }
            _ => {
                let err = self.type_error(ValidType::Atom, a1);
                return Err(self.error_form(err, stub_gen()));
            }
        );

        let atom = match compare_term_test!(self, a2, a3) {
            Some(Ordering::Greater) => {
                atom!(">")
            }
            Some(Ordering::Equal) => {
                atom!("=")
            }
            None | Some(Ordering::Less) => {
                atom!("<")
            }
        };

        self.unify_atom(atom, a1);
        Ok(())
    }

    pub fn copy_term(&mut self, attr_var_policy: AttrVarPolicy) {
        let old_h = self.heap.len();

        let a1 = self.registers[1];
        let a2 = self.registers[2];

        copy_term(CopyTerm::new(self), a1, attr_var_policy);

        unify_fn!(*self, heap_loc_as_cell!(old_h), a2);
    }

    fn sort(&mut self) -> CallResult {
        self.check_sort_errors()?;

        let stub_gen = || functor_stub(atom!("sort"), 2);
        let mut list = self.try_from_list(self.registers[1], stub_gen)?;

        list.sort_unstable_by(|v1, v2| {
            compare_term_test!(self, *v1, *v2).unwrap_or(Ordering::Less)
        });

        list.dedup_by(|v1, v2| {
            compare_term_test!(self, *v1, *v2) == Some(Ordering::Equal)
        });

        let heap_addr = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.heap, list.into_iter())
        );

        let target_addr = self.registers[2];

        unify_fn!(*self, target_addr, heap_addr);
        Ok(())
    }

    fn keysort(&mut self, var_comparison: VarComparison) -> CallResult {
        self.check_keysort_errors()?;

        let stub_gen = || functor_stub(atom!("keysort"), 2);
        let list = self.try_from_list(self.registers[1], stub_gen)?;

        let mut key_pairs = Vec::with_capacity(list.len());

        for val in list {
            let key = self.project_onto_key(val)?;
            key_pairs.push((key, val));
        }

        key_pairs.sort_by(|a1, a2| {
            compare_term_test!(self, a1.0, a2.0, var_comparison).unwrap_or(Ordering::Less)
        });

        let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
        let heap_addr = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.heap, key_pairs)
        );

        let target_addr = self.registers[2];

        unify_fn!(*self, target_addr, heap_addr);
        Ok(())
    }

    fn is(&mut self, r: RegType, at: ArithmeticTerm) -> CallResult {
        let n1 = self.store(self.deref(self[r]));

        match self.get_number(&at)? {
            Number::Fixnum(n) => self.unify_fixnum(n, n1),
            Number::Float(n) => {
                let n = float_alloc!(n.into_inner(), self.arena);
                self.unify_f64(n, n1)
            }
            Number::Integer(n) => self.unify_big_int(n, n1),
            Number::Rational(n) => self.unify_rational(n, n1),
        }

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn select_switch_on_term_index(
        &self,
        addr: HeapCellValue,
        v: IndexingCodePtr,
        c: IndexingCodePtr,
        l: IndexingCodePtr,
        s: IndexingCodePtr,
    ) -> IndexingCodePtr {
        read_heap_cell!(addr,
            (HeapCellValueTag::Var |
             HeapCellValueTag::StackVar |
             HeapCellValueTag::AttrVar) => {
                v
            }
            (HeapCellValueTag::PStrLoc |
             HeapCellValueTag::Lis |
             HeapCellValueTag::CStr) => {
                l
            }
            (HeapCellValueTag::Fixnum |
             HeapCellValueTag::Char |
             HeapCellValueTag::F64) => {
                c
            }
            (HeapCellValueTag::Atom, (_name, arity)) => {
                // if arity == 0 { c } else { s }
                debug_assert!(arity == 0);
                c
            }
            (HeapCellValueTag::Str, st) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[st])
                    .get_name_and_arity();

                match (name, arity) {
                    (atom!("."), 2) => l,
                    (_, 0) => c,
                    _ => s,
                }
            }
            (HeapCellValueTag::Cons, ptr) => {
                match ptr.get_tag() {
                    ArenaHeaderTag::Rational | ArenaHeaderTag::Integer => {
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
        )
    }

    #[inline(always)]
    pub(crate) fn constant_to_literal(&self, addr: HeapCellValue) -> Literal {
        read_heap_cell!(addr,
            (HeapCellValueTag::Char, c) => {
                Literal::Char(c)
            }
            (HeapCellValueTag::Fixnum, n) => {
                Literal::Fixnum(n)
            }
            (HeapCellValueTag::F64, f) => {
                Literal::Float(f.as_offset())
            }
            (HeapCellValueTag::Atom, (atom, arity)) => {
                debug_assert_eq!(arity, 0);
                Literal::Atom(atom)
            }
            (HeapCellValueTag::Str, s) => {
                Literal::Atom(cell_as_atom_cell!(self.heap[s]).get_name())
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::Rational, r) => {
                        Literal::Rational(r)
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
        )
    }

    #[inline(always)]
    pub(crate) fn select_switch_on_structure_index(
        &self,
        addr: HeapCellValue,
        hm: &IndexMap<(Atom, usize), IndexingCodePtr, FxBuildHasher>,
    ) -> IndexingCodePtr {
        read_heap_cell!(addr,
            (HeapCellValueTag::Atom, (name, arity)) => {
                match hm.get(&(name, arity)) {
                    Some(offset) => *offset,
                    None => IndexingCodePtr::Fail,
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                match hm.get(&(name, arity)) {
                    Some(offset) => *offset,
                    None => IndexingCodePtr::Fail,
                }
            }
            _ => {
                IndexingCodePtr::Fail
            }
        )
    }
}

impl Machine {
    fn read(&mut self) -> CallResult {
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices.stream_aliases,
            atom!("read"),
            2,
        )?;

        match self.machine_st.read(stream, &self.indices.op_dir) {
            Ok(offset) => {
                let value = self.machine_st.registers[2];
                unify_fn!(&mut self.machine_st, value, heap_loc_as_cell!(offset.heap_loc));
            }
            Err(CompilationError::ParserError(e)) if e.is_unexpected_eof() => {
                let value = self.machine_st.registers[2];
                self.machine_st.unify_atom(atom!("end_of_file"), value);
            }
            Err(e) => {
                let stub = functor_stub(atom!("read"), 2);
                let err = self.machine_st.syntax_error(e);

                return Err(self.machine_st.error_form(err, stub));
            }
        };

        Ok(())
    }

    pub(super) fn find_living_dynamic_else(&self, mut p: usize) -> Option<(usize, usize)> {
        loop {
            match &self.code[p] {
                &Instruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                ) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, i));
                    } else if i > 0 {
                        p += i;
                    } else {
                        return None;
                    }
                }
                &Instruction::DynamicElse(
                    birth,
                    death,
                    NextOrFail::Fail(_),
                ) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, 0));
                    } else {
                        return None;
                    }
                }
                &Instruction::DynamicInternalElse(
                    birth,
                    death,
                    NextOrFail::Next(i),
                ) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, i));
                    } else if i > 0 {
                        p += i;
                    } else {
                        return None;
                    }
                }
                &Instruction::DynamicInternalElse(
                    birth,
                    death,
                    NextOrFail::Fail(_),
                ) => {
                    if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                        return Some((p, 0));
                    } else {
                        return None;
                    }
                }
                &Instruction::RevJmpBy(i) => {
                    p -= i;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    pub(super) fn find_living_dynamic(&self, oi: u32, mut ii: u32) -> Option<(usize, u32, u32, bool)> {
        let p = self.machine_st.p;

        let indexed_choice_instrs = match &self.code[p] {
            Instruction::IndexingCode(ref indexing_code) => match &indexing_code[oi as usize] {
                IndexingLine::DynamicIndexedChoice(ref indexed_choice_instrs) => {
                    indexed_choice_instrs
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        loop {
            match &indexed_choice_instrs.get(ii as usize) {
                Some(&offset) => match &self.code[p + offset - 1] {
                    &Instruction::DynamicInternalElse(
                        birth,
                        death,
                        next_or_fail,
                    ) => {
                        if birth < self.machine_st.cc && Death::Finite(self.machine_st.cc) <= death {
                            return Some((offset, oi, ii, next_or_fail.is_next()));
                        } else {
                            ii += 1;
                        }
                    }
                    _ => unreachable!(),
                },
                None => return None,
            }
        }
    }

    #[inline(always)]
    fn execute_switch_on_term(&mut self) {
        #[inline(always)]
        fn dynamic_external_of_clause_is_valid(machine: &mut Machine, p: usize) -> bool {
            match &machine.code[p] {
                Instruction::DynamicInternalElse(..) => {
                    machine.machine_st.dynamic_mode = FirstOrNext::First;
                    return true;
                }
                _ => {}
            }

            match &machine.code[p - 1] {
                &Instruction::DynamicInternalElse(birth, death, _) => {
                    if birth < machine.machine_st.cc && Death::Finite(machine.machine_st.cc) <= death {
                        return true;
                    } else {
                        return false;
                    }
                }
                _ => {}
            }

            true
        }

        let indexing_lines = self.code[self.machine_st.p].to_indexing_line_mut().unwrap();

        let mut index = 0;
        let addr = match &indexing_lines[0] {
            &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(arg, ..)) => {
                self.machine_st.store(self.machine_st.deref(self.machine_st.registers[arg]))
            }
            _ => {
                unreachable!()
            }
        };

        loop {
            match &indexing_lines[index] {
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(_, v, c, l, s)) => {
                    let offset = self.machine_st.select_switch_on_term_index(addr, v, c, l, s);

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.machine_st.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            // either points directly to a
                            // DynamicInternalElse, or just ahead of
                            // one. Or neither!
                            let p = self.machine_st.p;

                            if !dynamic_external_of_clause_is_valid(self, p + o) {
                                self.machine_st.fail = true;
                            } else {
                                self.machine_st.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.machine_st.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(hm)) => {
                    let lit = self.machine_st.constant_to_literal(addr);

                    let offset = match hm.get(&lit) {
                        Some(offset) => *offset,
                        _ => IndexingCodePtr::Fail,
                    };

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.machine_st.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            // either points directly to a
                            // DynamicInternalElse, or just ahead of
                            // one. Or neither!
                            let p = self.machine_st.p;

                            if !dynamic_external_of_clause_is_valid(self, p + o) {
                                self.machine_st.fail = true;
                            } else {
                                self.machine_st.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.machine_st.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(hm)) => {
                    let offset = self.machine_st.select_switch_on_structure_index(addr, hm);

                    match offset {
                        IndexingCodePtr::Fail => {
                            self.machine_st.fail = true;
                            break;
                        }
                        IndexingCodePtr::DynamicExternal(o) => {
                            let p = self.machine_st.p;

                            if !dynamic_external_of_clause_is_valid(self, p + o) {
                                self.machine_st.fail = true;
                            } else {
                                self.machine_st.p += o;
                            }

                            break;
                        }
                        IndexingCodePtr::External(o) => {
                            self.machine_st.p += o;
                            break;
                        }
                        IndexingCodePtr::Internal(o) => {
                            index += o;
                        }
                    }
                }
                &IndexingLine::IndexedChoice(_) => {
                    self.machine_st.oip = index as u32;
                    self.machine_st.iip = 0;

                    break;
                }
                &IndexingLine::DynamicIndexedChoice(_) => {
                    self.machine_st.dynamic_mode = FirstOrNext::First;

                    self.machine_st.oip = index as u32;
                    self.machine_st.iip = 0;

                    break;
                }
            }
        }
    }

    #[inline(always)]
    pub(super) fn dispatch_loop(&mut self) {
        'outer: loop {
        for _ in 0 .. INSTRUCTIONS_PER_INTERRUPT_POLL {
            match &self.code[self.machine_st.p] {
                &Instruction::BreakFromDispatchLoop => {
                    break 'outer;
                }
                &Instruction::InstallVerifyAttr => {
                    self.machine_st.p = self.machine_st.attr_var_init.p;

                    if self.code[self.machine_st.p].is_execute() {
                        self.machine_st.p = self.machine_st.attr_var_init.cp;
                    } else {
                        self.machine_st.p += 1;
                        self.machine_st.cp = self.machine_st.attr_var_init.cp;
                    }

                    let mut p = self.machine_st.p;

                    while self.code[p].is_head_instr() {
                        p += 1;
                    }

                    let instr = std::mem::replace(
                        &mut self.code[p],
                        Instruction::VerifyAttrInterrupt,
                    );

                    self.code[VERIFY_ATTR_INTERRUPT_LOC] = instr;
                    self.machine_st.attr_var_init.cp = p;
                }
                &Instruction::VerifyAttrInterrupt => {
                    let (_, arity) = self.code[VERIFY_ATTR_INTERRUPT_LOC].to_name_and_arity();
                    let arity = std::cmp::max(arity, self.machine_st.num_of_args);
                    self.run_verify_attr_interrupt(arity);
                }
                &Instruction::Add(ref a1, ref a2, t) => {
                    let stub_gen = || functor_stub(atom!("is"), 2);

                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        try_numeric_result!(add(n1, n2, &mut self.machine_st.arena), stub_gen)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Sub(ref a1, ref a2, t) => {
                    let stub_gen = || functor_stub(atom!("is"), 2);

                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        try_numeric_result!(sub(n1, n2, &mut self.machine_st.arena), stub_gen)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Mul(ref a1, ref a2, t) => {
                    let stub_gen = || functor_stub(atom!("is"), 2);

                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        try_numeric_result!(mul(n1, n2, &mut self.machine_st.arena), stub_gen)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Max(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        max(n1, n2)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Min(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        min(n1, n2)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::IntPow(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        int_pow(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Gcd(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        gcd(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Pow(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        pow(n1, n2, atom!("**"))
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::RDiv(ref a1, ref a2, t) => {
                    let stub_gen = || functor_stub(atom!("(rdiv)"), 2);

                    let r1 = try_or_throw!(self.machine_st, self.machine_st.get_rational(a1, stub_gen));
                    let r2 = try_or_throw!(self.machine_st, self.machine_st.get_rational(a2, stub_gen));

                    self.machine_st.interms[t - 1] = Number::Rational(arena_alloc!(
                        try_or_throw_gen!(&mut self.machine_st, rdiv(r1, r2)),
                        &mut self.machine_st.arena
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::IntFloorDiv(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        int_floor_div(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::IDiv(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        idiv(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Abs(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = abs(n1, &mut self.machine_st.arena);
                    self.machine_st.p += 1;
                }
                &Instruction::Sign(ref a1, t) => {
                    let n = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = n.sign();
                    self.machine_st.p += 1;
                }
                &Instruction::Neg(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = neg(n1, &mut self.machine_st.arena);
                    self.machine_st.p += 1;
                }
                &Instruction::BitwiseComplement(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        bitwise_complement(n1, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Div(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        div(n1, n2)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Shr(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        shr(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Shl(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        shl(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Xor(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        xor(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::And(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        and(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Or(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        or(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Mod(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        modulus(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Rem(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = try_or_throw_gen!(
                        &mut self.machine_st,
                        remainder(n1, n2, &mut self.machine_st.arena)
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::Cos(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, cos(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Sin(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, sin(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Tan(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, tan(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Sqrt(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, sqrt(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Log(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, log(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Exp(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, exp(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::ACos(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, acos(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::ASin(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, asin(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::ATan(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, atan(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::ATan2(ref a1, ref a2, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(a2));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, atan2(n1, n2))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Float(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                        try_or_throw_gen!(&mut self.machine_st, float(n1))
                    ));

                    self.machine_st.p += 1;
                }
                &Instruction::Truncate(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = truncate(n1, &mut self.machine_st.arena);
                    self.machine_st.p += 1;
                }
                &Instruction::Round(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] =
                        try_or_throw_gen!(&mut self.machine_st, round(n1, &mut self.machine_st.arena));

                    self.machine_st.p += 1;
                }
                &Instruction::Ceiling(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = ceiling(n1, &mut self.machine_st.arena);
                    self.machine_st.p += 1;
                }
                &Instruction::Floor(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = floor(n1, &mut self.machine_st.arena);
                    self.machine_st.p += 1;
                }
                &Instruction::Plus(ref a1, t) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(a1));

                    self.machine_st.interms[t - 1] = n1;
                    self.machine_st.p += 1;
                }
                &Instruction::DynamicElse(..) => {
                    if let FirstOrNext::First = self.machine_st.dynamic_mode {
                        self.machine_st.cc = self.machine_st.global_clock;
                    }

                    let p = self.machine_st.p;

                    match self.find_living_dynamic_else(p) {
                        Some((p, next_i)) => {
                            self.machine_st.p = p;
                            self.machine_st.oip = 0;
                            self.machine_st.iip = 0;

                            match self.machine_st.dynamic_mode {
                                FirstOrNext::First if next_i == 0 => {
                                    self.machine_st.p += 1;
                                }
                                FirstOrNext::First => {
                                    self.machine_st.cc = self.machine_st.global_clock;

                                    match self.find_living_dynamic_else(p + next_i) {
                                        Some(_) => {
                                            self.machine_st.registers[self.machine_st.num_of_args + 1] =
                                                fixnum_as_cell!(Fixnum::build_with(self.machine_st.cc as i64));

                                            self.machine_st.num_of_args += 1;
                                            self.try_me_else(next_i);
                                            self.machine_st.num_of_args -= 1;
                                        }
                                        None => {
                                            self.machine_st.p += 1;
                                        }
                                    }
                                }
                                FirstOrNext::Next => {
                                    let n = self.machine_st
                                        .stack
                                        .index_or_frame(self.machine_st.b)
                                        .prelude
                                        .num_cells;

                                    self.machine_st.cc = cell_as_fixnum!(
                                        self.machine_st.stack[stack_loc!(OrFrame, self.machine_st.b, n-1)]
                                    ).get_num() as usize;

                                    if next_i > 0 {
                                        match self.find_living_dynamic_else(p + next_i) {
                                            Some(_) => {
                                                self.retry_me_else(next_i);
                                            }
                                            None => {
                                                self.trust_me();
                                            }
                                        }
                                    } else {
                                        self.trust_me();
                                    }

                                    try_or_throw!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                        }
                        None => {
                            self.machine_st.fail = true;
                        }
                    }

                    self.machine_st.dynamic_mode = FirstOrNext::Next;

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DynamicInternalElse(..) => {
                    let p = self.machine_st.p;

                    match self.find_living_dynamic_else(p) {
                        Some((p, next_i)) => {
                            self.machine_st.p = p;
                            self.machine_st.oip = 0;
                            self.machine_st.iip = 0;

                            match self.machine_st.dynamic_mode {
                                FirstOrNext::First if next_i == 0 => {
                                    self.machine_st.p += 1;
                                }
                                FirstOrNext::First => {
                                    match self.find_living_dynamic_else(p + next_i) {
                                        Some(_) => {
                                            self.machine_st.registers[self.machine_st.num_of_args + 1] =
                                                fixnum_as_cell!(Fixnum::build_with(self.machine_st.cc as i64));

                                            self.machine_st.num_of_args += 1;
                                            self.try_me_else(next_i);
                                            self.machine_st.num_of_args -= 1;
                                        }
                                        None => {
                                            self.machine_st.p += 1;
                                        }
                                    }
                                }
                                FirstOrNext::Next => {
                                    let n = self.machine_st
                                        .stack
                                        .index_or_frame(self.machine_st.b)
                                        .prelude
                                        .num_cells;

                                    self.machine_st.cc = cell_as_fixnum!(
                                        self.machine_st.stack[stack_loc!(OrFrame, self.machine_st.b, n-1)]
                                    ).get_num() as usize;

                                    if next_i > 0 {
                                        match self.find_living_dynamic_else(p + next_i) {
                                            Some(_) => {
                                                self.retry_me_else(next_i);
                                            }
                                            None => {
                                                self.trust_me();
                                            }
                                        }
                                    } else {
                                        self.trust_me();
                                    }

                                    try_or_throw!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                        }
                        None => {
                            self.machine_st.fail = true;
                        }
                    }

                    self.machine_st.dynamic_mode = FirstOrNext::Next;

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::TryMeElse(offset) => {
                    self.try_me_else(offset);
                }
                &Instruction::DefaultRetryMeElse(offset) => {
                    self.retry_me_else(offset);
                }
                &Instruction::DefaultTrustMe(_) => {
                    self.trust_me();
                }
                &Instruction::RetryMeElse(offset) => {
                    self.retry_me_else(offset);

                    try_or_throw!(
                        self.machine_st,
                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                    );
                }
                &Instruction::TrustMe(_) => {
                    self.trust_me();

                    try_or_throw!(
                        self.machine_st,
                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                    );
                }
                &Instruction::NeckCut => {
                    self.machine_st.neck_cut();
                    self.machine_st.p += 1;
                }
                &Instruction::GetLevel(r) => {
                    let b0 = self.machine_st.b0;

                    self.machine_st[r] = fixnum_as_cell!(Fixnum::as_cutpoint(b0 as i64));
                    self.machine_st.p += 1;
                }
                &Instruction::GetPrevLevel(r) => {
                    let prev_b = self.machine_st.stack.index_or_frame(self.machine_st.b).prelude.b;

                    self.machine_st[r] = fixnum_as_cell!(Fixnum::as_cutpoint(prev_b as i64));
                    self.machine_st.p += 1;
                }
                &Instruction::GetCutPoint(r) => {
                    self.machine_st[r] = fixnum_as_cell!(Fixnum::as_cutpoint(self.machine_st.b as i64));
                    self.machine_st.p += 1;
                }
                &Instruction::Cut(r) => {
                    let value = self.machine_st[r];
                    self.machine_st.cut_body(value);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                        continue;
                    }

                    if (self.machine_st.run_cleaners_fn)(self) {
                       continue;
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::Allocate(num_cells) => {
                    self.machine_st.allocate(num_cells);
                }
                &Instruction::DefaultCallAcyclicTerm => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteAcyclicTerm => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallArg => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteArg => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallCompare => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteCompare => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallTermGreaterThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteTermGreaterThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultCallTermLessThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteTermLessThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultCallTermGreaterThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Greater | Ordering::Equal) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteTermGreaterThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Greater | Ordering::Equal) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallTermLessThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Less | Ordering::Equal) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteTermLessThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Less | Ordering::Equal) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallRead => {
                    try_or_throw!(self.machine_st, self.read());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteRead => {
                    try_or_throw!(self.machine_st, self.read());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallCopyTerm => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteCopyTerm => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallTermEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteTermEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallGround => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteGround => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallFunctor => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteFunctor => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallTermNotEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteTermNotEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallSort => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteSort => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallKeySort => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Distinct));
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteKeySort => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Distinct));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallIs(r, at) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteIs(r, at) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAcyclicTerm => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteAcyclicTerm => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallArg => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteArg => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallCompare => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteCompare => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallTermGreaterThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::ExecuteTermGreaterThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::CallTermLessThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::ExecuteTermLessThan => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::CallTermGreaterThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Greater | Ordering::Equal) => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteTermGreaterThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Greater | Ordering::Equal) => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallTermLessThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Less | Ordering::Equal) => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteTermLessThanOrEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    match compare_term_test!(self.machine_st, a1, a2) {
                        Some(Ordering::Less | Ordering::Equal) => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallRead => {
                    try_or_throw!(self.machine_st, self.read());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteRead => {
                    try_or_throw!(self.machine_st, self.read());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallCopyTerm => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteCopyTerm => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallTermEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteTermEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallGround => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteGround => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallFunctor => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteFunctor => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallTermNotEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteTermNotEqual => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallSort => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteSort => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallKeySort => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Distinct));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteKeySort => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Distinct));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallKeySortWithConstantVarOrdering => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Indistinct));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteKeySortWithConstantVarOrdering => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort(VarComparison::Indistinct));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallIs(r, at) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteIs(r, at) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );

                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallN(arity) => {
                    let pred = self.machine_st.registers[1];

                    for i in 2..arity + 1 {
                        self.machine_st.registers[i - 1] = self.machine_st.registers[i];
                    }

                    self.machine_st.registers[arity] = pred;

                    try_or_throw!(
                        self.machine_st,
                        self.call_n(atom!("user"), arity)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::ExecuteN(arity) => {
                    let pred = self.machine_st.registers[1];

                    for i in 2..arity + 1 {
                        self.machine_st.registers[i - 1] = self.machine_st.registers[i];
                    }

                    self.machine_st.registers[arity] = pred;

                    try_or_throw!(
                        self.machine_st,
                        self.execute_n(atom!("user"), arity)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::DefaultCallN(arity) => {
                    let pred = self.machine_st.registers[1];

                    for i in 2..arity + 1 {
                        self.machine_st.registers[i - 1] = self.machine_st.registers[i];
                    }

                    self.machine_st.registers[arity] = pred;

                    try_or_throw!(
                        self.machine_st,
                        self.call_n(atom!("user"), arity)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteN(arity) => {
                    let pred = self.machine_st.registers[1];

                    for i in 2..arity + 1 {
                        self.machine_st.registers[i - 1] = self.machine_st.registers[i];
                    }

                    self.machine_st.registers[arity] = pred;

                    try_or_throw!(
                        self.machine_st,
                        self.execute_n(atom!("user"), arity)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::CallNumberLessThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less | Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteNumberLessThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less | Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallNumberEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteNumberEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallNumberNotEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                    }
                }
                &Instruction::ExecuteNumberNotEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                    }
                }
                &Instruction::CallNumberGreaterThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater | Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteNumberGreaterThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater | Ordering::Equal => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallNumberGreaterThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteNumberGreaterThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallNumberLessThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteNumberLessThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less => {
                            try_or_throw!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );

                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallNumberLessThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less | Ordering::Equal => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberLessThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less | Ordering::Equal => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallNumberNotEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            self.machine_st.p += 1;
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberNotEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                    }
                }
                &Instruction::DefaultCallNumberEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Equal => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallNumberGreaterThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater | Ordering::Equal => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberGreaterThanOrEqual(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater | Ordering::Equal => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallNumberGreaterThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberGreaterThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Greater => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultCallNumberLessThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::DefaultExecuteNumberLessThan(ref at_1, ref at_2) => {
                    let n1 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_1));
                    let n2 = try_or_throw!(self.machine_st, self.machine_st.get_number(at_2));

                    match n1.cmp(&n2) {
                        Ordering::Less => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                //
                &Instruction::CallIsAtom(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity == 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Char) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::ExecuteIsAtom(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity == 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Char) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::CallIsAtomic(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Char | HeapCellValueTag::Fixnum | HeapCellValueTag::F64 |
                         HeapCellValueTag::Cons) => {
                            self.machine_st.p += 1;
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity == 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::ExecuteIsAtomic(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Char | HeapCellValueTag::Fixnum | HeapCellValueTag::F64 |
                         HeapCellValueTag::Cons) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity == 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::CallIsCompound(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Lis |
                         HeapCellValueTag::PStrLoc |
                         HeapCellValueTag::CStr) => {
                            self.machine_st.p += 1;
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity > 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity > 0 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::ExecuteIsCompound(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Lis |
                         HeapCellValueTag::PStrLoc |
                         HeapCellValueTag::CStr) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        (HeapCellValueTag::Str, s) => {
                            let arity = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_arity();

                            if arity > 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity > 0 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::CallIsInteger(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(Number::Fixnum(_) | Number::Integer(_)) => {
                            self.machine_st.p += 1;
                        }
                        Ok(Number::Rational(n)) => {
                            if n.denom() == &1 {
                                self.machine_st.p += 1;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteIsInteger(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(Number::Fixnum(_) | Number::Integer(_)) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        Ok(Number::Rational(n)) => {
                            if n.denom() == &1 {
                                self.machine_st.p = self.machine_st.cp;
                            } else {
                                self.machine_st.backtrack();
                            }
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallIsNumber(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(_) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteIsNumber(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(_) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallIsRational(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Cons, ptr) => {
                            match_untyped_arena_ptr!(ptr,
                                 (ArenaHeaderTag::Rational | ArenaHeaderTag::Integer, _r) => {
                                     self.machine_st.p += 1;
                                 }
                                 _ => {
                                     self.machine_st.backtrack();
                                 }
                            );
                        }
                        (HeapCellValueTag::Fixnum) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::ExecuteIsRational(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Cons, ptr) => {
                            match_untyped_arena_ptr!(ptr,
                                 (ArenaHeaderTag::Rational | ArenaHeaderTag::Integer, _r) => {
                                     self.machine_st.p = self.machine_st.cp;
                                 }
                                 _ => {
                                     self.machine_st.backtrack();
                                 }
                            );
                        }
                        (HeapCellValueTag::Fixnum) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::CallIsFloat(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(Number::Float(_)) => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteIsFloat(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match Number::try_from(d) {
                        Ok(Number::Float(_)) => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallIsNonVar(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match d.get_tag() {
                        HeapCellValueTag::AttrVar |
                        HeapCellValueTag::Var |
                        HeapCellValueTag::StackVar => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            self.machine_st.p += 1;
                        }
                    }
                }
                &Instruction::ExecuteIsNonVar(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match d.get_tag() {
                        HeapCellValueTag::AttrVar |
                        HeapCellValueTag::Var |
                        HeapCellValueTag::StackVar => {
                            self.machine_st.backtrack();
                        }
                        _ => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                    }
                }
                &Instruction::CallIsVar(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match d.get_tag() {
                        HeapCellValueTag::AttrVar |
                        HeapCellValueTag::Var |
                        HeapCellValueTag::StackVar => {
                            self.machine_st.p += 1;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::ExecuteIsVar(r) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    match d.get_tag() {
                        HeapCellValueTag::AttrVar |
                        HeapCellValueTag::Var |
                        HeapCellValueTag::StackVar => {
                            self.machine_st.p = self.machine_st.cp;
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    }
                }
                &Instruction::CallNamed(arity, name, ref idx) => {
                    let idx = idx.get();

                    try_or_throw!(
                        self.machine_st,
                        self.try_call(name, arity, idx)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::ExecuteNamed(arity, name, ref idx) => {
                    let idx = idx.get();

                    try_or_throw!(
                        self.machine_st,
                        self.try_execute(name, arity, idx)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::DefaultCallNamed(arity, name, ref idx) => {
                    let idx = idx.get();

                    try_or_throw!(
                        self.machine_st,
                        self.try_call(name, arity, idx)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteNamed(arity, name, ref idx) => {
                    let idx = idx.get();

                    try_or_throw!(
                        self.machine_st,
                        self.try_execute(name, arity, idx)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::Deallocate => {
                    self.machine_st.deallocate()
                }
                &Instruction::JmpByCall(offset) => {
                    self.machine_st.p += offset;
                }
                &Instruction::RevJmpBy(offset) => {
                    self.machine_st.p -= offset;
                }
                &Instruction::Proceed => {
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::GetConstant(_, c, reg) => {
                    let value = self.machine_st.deref(self.machine_st[reg]);
                    self.machine_st.write_literal_to_var(value, c);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::GetList(_, reg) => {
                    let deref_v = self.machine_st.deref(self.machine_st[reg]);
                    let store_v = self.machine_st.store(deref_v);

                    read_heap_cell!(store_v,
                        (HeapCellValueTag::PStrLoc, h) => {
                            let (h, n) = pstr_loc_and_offset(&self.machine_st.heap, h);

                            self.machine_st.s = HeapPtr::PStrChar(h, n.get_num() as usize);
                            self.machine_st.s_offset = 0;
                            self.machine_st.mode = MachineMode::Read;
                        }
                        (HeapCellValueTag::CStr) => {
                            let h = self.machine_st.heap.len();
                            self.machine_st.heap.push(store_v);

                            self.machine_st.s = HeapPtr::PStrChar(h, 0);
                            self.machine_st.s_offset = 0;
                            self.machine_st.mode = MachineMode::Read;
                        }
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_name_and_arity();

                            if name == atom!(".") && arity == 2 {
                                self.machine_st.s = HeapPtr::HeapCell(s+1);
                                self.machine_st.s_offset = 0;
                                self.machine_st.mode = MachineMode::Read;
                            } else {
                                self.machine_st.backtrack();
                                continue;
                            }
                        }
                        (HeapCellValueTag::Lis, l) => {
                            self.machine_st.s = HeapPtr::HeapCell(l);
                            self.machine_st.s_offset = 0;
                            self.machine_st.mode = MachineMode::Read;
                        }
                        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                            let h = self.machine_st.heap.len();

                            self.machine_st.heap.push(list_loc_as_cell!(h+1));
                            self.machine_st.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));

                            self.machine_st.mode = MachineMode::Write;
                        }
                        _ => {
                            self.machine_st.backtrack();
                            continue;
                        }
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::GetPartialString(_, string, reg, has_tail) => {
                    let deref_v = self.machine_st.deref(self.machine_st[reg]);
                    let store_v = self.machine_st.store(deref_v);

                    read_heap_cell!(store_v,
                        (HeapCellValueTag::Str |
                         HeapCellValueTag::Lis |
                         HeapCellValueTag::PStrLoc |
                         HeapCellValueTag::CStr) => {
                            self.machine_st.match_partial_string(store_v, string, has_tail);
                        }
                        (HeapCellValueTag::AttrVar |
                         HeapCellValueTag::StackVar |
                         HeapCellValueTag::Var) => {
                            let target_cell = self.machine_st.push_str_to_heap(
                                string.as_str(),
                                has_tail,
                            );

                            self.machine_st.bind(
                                store_v.as_var().unwrap(),
                                target_cell,
                            );
                        }
                        _ => {
                            self.machine_st.backtrack();
                            continue;
                        }
                    );

                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::GetStructure(_lvl, name, arity, reg) => {
                    let deref_v = self.machine_st.deref(self.machine_st[reg]);
                    let store_v = self.machine_st.store(deref_v);

                    read_heap_cell!(store_v,
                        (HeapCellValueTag::Str, a) => {
                            read_heap_cell!(self.machine_st.heap[a],
                                (HeapCellValueTag::Atom, (result_name, result_arity)) => {
                                    if arity == result_arity && name == result_name {
                                        self.machine_st.s = HeapPtr::HeapCell(a + 1);
                                        self.machine_st.s_offset = 0;
                                        self.machine_st.mode = MachineMode::Read;
                                    } else {
                                        self.machine_st.backtrack();
                                        continue;
                                    }
                                }
                                _ => {
                                    unreachable!();
                                }
                            );
                        }
                        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                            let h = self.machine_st.heap.len();

                            self.machine_st.heap.push(str_loc_as_cell!(h+1));
                            self.machine_st.heap.push(atom_as_cell!(name, arity));

                            self.machine_st.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));
                            self.machine_st.mode = MachineMode::Write;
                        }
                        _ => {
                            self.machine_st.backtrack();
                            continue;
                        }
                    );

                    self.machine_st.p += 1;
                }
                &Instruction::GetVariable(norm, arg) => {
                    self.machine_st[norm] = self.machine_st.registers[arg];
                    self.machine_st.p += 1;
                }
                &Instruction::GetValue(norm, arg) => {
                    let norm_addr = self.machine_st[norm];
                    let reg_addr = self.machine_st.registers[arg];

                    unify_fn!(&mut self.machine_st, norm_addr, reg_addr);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                        continue;
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::UnifyConstant(v) => {
                    match self.machine_st.mode {
                        MachineMode::Read => {
                            let addr = self.machine_st.read_s();

                            self.machine_st.write_literal_to_var(addr, v);

                            if self.machine_st.fail {
                                self.machine_st.backtrack();
                                continue;
                            } else {
                                self.machine_st.s_offset += 1;
                            }
                        }
                        MachineMode::Write => {
                            self.machine_st.heap.push(v);
                        }
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::UnifyLocalValue(reg) => {
                    match self.machine_st.mode {
                        MachineMode::Read => {
                            let reg_addr = self.machine_st[reg];
                            let value = self.machine_st.read_s();

                            unify_fn!(&mut self.machine_st, reg_addr, value);

                            if self.machine_st.fail {
                                self.machine_st.backtrack();
                                continue;
                            } else {
                                self.machine_st.s_offset += 1;
                            }
                        }
                        MachineMode::Write => {
                            let value = self.machine_st.store(self.machine_st.deref(self.machine_st[reg]));
                            let h = self.machine_st.heap.len();

                            read_heap_cell!(value,
                                (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, hc) => {
                                    let value = self.machine_st.heap[hc];

                                    self.machine_st.heap.push(value);
                                    self.machine_st.s_offset += 1;
                                }
                                _ => {
                                    self.machine_st.heap.push(heap_loc_as_cell!(h));
                                    (self.machine_st.bind_fn)(
                                        &mut self.machine_st,
                                        Ref::heap_cell(h),
                                        value,
                                    );
                                }
                            );
                        }
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::UnifyVariable(reg) => {
                    match self.machine_st.mode {
                        MachineMode::Read => {
                            self.machine_st[reg] = self.machine_st.read_s();
                            self.machine_st.s_offset += 1;
                        }
                        MachineMode::Write => {
                            let h = self.machine_st.heap.len();

                            self.machine_st.heap.push(heap_loc_as_cell!(h));
                            self.machine_st[reg] = heap_loc_as_cell!(h);
                        }
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::UnifyValue(reg) => {
                    match self.machine_st.mode {
                        MachineMode::Read => {
                            let reg_addr = self.machine_st[reg];
                            let value = self.machine_st.read_s();

                            unify_fn!(&mut self.machine_st, reg_addr, value);

                            if self.machine_st.fail {
                                self.machine_st.backtrack();
                                continue;
                            } else {
                                self.machine_st.s_offset += 1;
                            }
                        }
                        MachineMode::Write => {
                            let h = self.machine_st.heap.len();
                            self.machine_st.heap.push(heap_loc_as_cell!(h));

                            let addr = self.machine_st.store(self.machine_st[reg]);
                            (self.machine_st.bind_fn)(&mut self.machine_st, Ref::heap_cell(h), addr);

                            // the former code of this match arm was:

                            // let addr = self.machine_st.store(self.machine_st[reg]);
                            // self.machine_st.heap.push(HeapCellValue::Addr(addr));

                            // the old code didn't perform the occurs
                            // check when enabled and so it was changed to
                            // the above, which is only slightly less
                            // efficient when the occurs_check is disabled.
                        }
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::UnifyVoid(n) => {
                    match self.machine_st.mode {
                        MachineMode::Read => {
                            self.machine_st.s_offset += n;
                        }
                        MachineMode::Write => {
                            let h = self.machine_st.heap.len();

                            for i in h..h + n {
                                self.machine_st.heap.push(heap_loc_as_cell!(i));
                            }
                        }
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::IndexingCode(ref indexing_lines) => {
                    match &indexing_lines[self.machine_st.oip as usize] {
                        IndexingLine::Indexing(_) => {
                            self.execute_switch_on_term();

                            if self.machine_st.fail {
                                self.machine_st.backtrack();
                            }
                        }
                        IndexingLine::IndexedChoice(ref indexed_choice) => {
                            match &indexed_choice[self.machine_st.iip as usize] {
                                &IndexedChoiceInstruction::Try(offset) => {
                                    self.indexed_try(offset);
                                }
                                &IndexedChoiceInstruction::Retry(l) => {
                                    self.retry(l);

                                    try_or_throw!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                                &IndexedChoiceInstruction::Trust(l) => {
                                    self.trust(l);

                                    try_or_throw!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                        }
                        IndexingLine::DynamicIndexedChoice(_) => {
                            let p = self.machine_st.p;

                            match self.find_living_dynamic(self.machine_st.oip, self.machine_st.iip) {
                                Some((offset, oi, ii, is_next_clause)) => {
                                    self.machine_st.p = p;
                                    self.machine_st.oip = oi;
                                    self.machine_st.iip = ii;

                                    match self.machine_st.dynamic_mode {
                                        FirstOrNext::First if !is_next_clause => {
                                            self.machine_st.p = p + offset;
                                        }
                                        FirstOrNext::First => {
                                            // there's a leading DynamicElse that sets self.machine_st.cc.
                                            // self.machine_st.cc = self.machine_st.global_clock;

                                            // see that there is a following dynamic_else
                                            // clause so we avoid generating a choice
                                            // point in case there isn't.
                                            match self.find_living_dynamic(oi, ii + 1) {
                                                Some(_) => {
                                                    self.machine_st.registers[self.machine_st.num_of_args + 1] =
                                                        fixnum_as_cell!(Fixnum::build_with(self.machine_st.cc as i64));

                                                    self.machine_st.num_of_args += 1;
                                                    self.indexed_try(offset);
                                                    self.machine_st.num_of_args -= 1;
                                                }
                                                None => {
                                                    self.machine_st.p = p + offset;
                                                    self.machine_st.oip = 0;
                                                    self.machine_st.iip = 0;
                                                }
                                            }
                                        }
                                        FirstOrNext::Next => {
                                            let b = self.machine_st.b;
                                            let n = self.machine_st
                                                .stack
                                                .index_or_frame(b)
                                                .prelude
                                                .num_cells;

                                            self.machine_st.cc = cell_as_fixnum!(
                                                self.machine_st.stack[stack_loc!(OrFrame, b, n-1)]
                                            ).get_num() as usize;

                                            if is_next_clause {
                                                match self.find_living_dynamic(self.machine_st.oip, self.machine_st.iip + 1) {
                                                    // if we're executing the last instruction
                                                    // of the internal block pointed to by
                                                    // self.machine_st.iip, we want trust, not retry.
                                                    // this is true iff ii + 1 < len.
                                                    Some(_) => {
                                                        self.retry(offset);

                                                        try_or_throw!(
                                                            self.machine_st,
                                                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                        );
                                                    }
                                                    _ => {
                                                        self.trust(offset);

                                                        try_or_throw!(
                                                            self.machine_st,
                                                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                        );
                                                    }
                                                }
                                            } else {
                                                self.trust(offset);

                                                try_or_throw!(
                                                    self.machine_st,
                                                    (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                );
                                            }
                                        }
                                    }
                                }
                                None => {
                                    self.machine_st.fail = true;
                                }
                            }

                            self.machine_st.dynamic_mode = FirstOrNext::Next;

                            if self.machine_st.fail {
                                self.machine_st.backtrack();
                            }
                        }
                    }
                }
                &Instruction::PutConstant(_, c, reg) => {
                    self.machine_st[reg] = c;
                    self.machine_st.p += 1;
                }
                &Instruction::PutList(_, reg) => {
                    self.machine_st[reg] = list_loc_as_cell!(self.machine_st.heap.len());
                    self.machine_st.p += 1;
                }
                &Instruction::PutPartialString(_, string, reg, has_tail) => {
                    let pstr_addr = if has_tail {
                        if string != atom!("") {
                            let h = self.machine_st.heap.len();
                            self.machine_st.heap.push(string_as_pstr_cell!(string));

                            // the tail will be pushed by the next
                            // instruction, so don't push one here.

                            pstr_loc_as_cell!(h)
                        } else {
                            empty_list_as_cell!()
                        }
                    } else {
                        string_as_cstr_cell!(string)
                    };

                    self.machine_st[reg] = pstr_addr;
                    self.machine_st.p += 1;
                }
                &Instruction::PutStructure(name, arity, reg) => {
                    let h = self.machine_st.heap.len();

                    self.machine_st.heap.push(atom_as_cell!(name, arity));
                    self.machine_st[reg] = str_loc_as_cell!(h);

                    self.machine_st.p += 1;
                }
                &Instruction::PutUnsafeValue(perm_slot, arg) => {
                    let s = stack_loc!(AndFrame, self.machine_st.e, perm_slot);
                    let addr = self.machine_st.store(self.machine_st.deref(stack_loc_as_cell!(s)));

                    if addr.is_protected(self.machine_st.e) {
                        self.machine_st.registers[arg] = addr;
                    } else {
                        let h = self.machine_st.heap.len();

                        self.machine_st.heap.push(heap_loc_as_cell!(h));
                        (self.machine_st.bind_fn)(&mut self.machine_st, Ref::heap_cell(h), addr);

                        self.machine_st.registers[arg] = heap_loc_as_cell!(h);
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::PutValue(norm, arg) => {
                    self.machine_st.registers[arg] = self.machine_st[norm];
                    self.machine_st.p += 1;
                }
                &Instruction::PutVariable(norm, arg) => {
                    match norm {
                        RegType::Perm(n) => {
                            self.machine_st[norm] = stack_loc_as_cell!(AndFrame, self.machine_st.e, n);
                            self.machine_st.registers[arg] = self.machine_st[norm];
                        }
                        RegType::Temp(_) => {
                            let h = self.machine_st.heap.len();
                            self.machine_st.heap.push(heap_loc_as_cell!(h));

                            self.machine_st[norm] = heap_loc_as_cell!(h);
                            self.machine_st.registers[arg] = heap_loc_as_cell!(h);
                        }
                    };

                    self.machine_st.p += 1;
                }
                &Instruction::SetConstant(c) => {
                    self.machine_st.heap.push(c);
                    self.machine_st.p += 1;
                }
                &Instruction::SetLocalValue(reg) => {
                    let addr = self.machine_st.deref(self.machine_st[reg]);
                    let stored_v = self.machine_st.store(addr);

                    if stored_v.is_stack_var() {
                        let h = self.machine_st.heap.len();
                        self.machine_st.heap.push(heap_loc_as_cell!(h));
                        (self.machine_st.bind_fn)(&mut self.machine_st, Ref::heap_cell(h), stored_v);
                    } else {
                        self.machine_st.heap.push(stored_v);
                    }

                    self.machine_st.p += 1;
                }
                &Instruction::SetVariable(reg) => {
                    let h = self.machine_st.heap.len();

                    self.machine_st.heap.push(heap_loc_as_cell!(h));
                    self.machine_st[reg] = heap_loc_as_cell!(h);

                    self.machine_st.p += 1;
                }
                &Instruction::SetValue(reg) => {
                    let heap_val = self.machine_st.store(self.machine_st[reg]);
                    self.machine_st.heap.push(heap_val);
                    self.machine_st.p += 1;
                }
                &Instruction::SetVoid(n) => {
                    let h = self.machine_st.heap.len();

                    for i in h..h + n {
                        self.machine_st.heap.push(heap_loc_as_cell!(i));
                    }

                    self.machine_st.p += 1;
                }
                //
                &Instruction::CallAtomChars => {
                    self.atom_chars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteAtomChars => {
                    self.atom_chars();

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallAtomCodes => {
                    try_or_throw!(self.machine_st, self.atom_codes());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteAtomCodes => {
                    try_or_throw!(self.machine_st, self.atom_codes());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallAtomLength => {
                    self.atom_length();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteAtomLength => {
                    self.atom_length();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallBindFromRegister => {
                    self.bind_from_register();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteBindFromRegister => {
                    self.bind_from_register();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallContinuation => {
                    try_or_throw!(self.machine_st, self.call_continuation(false));
                }
                &Instruction::ExecuteContinuation => {
                    try_or_throw!(self.machine_st, self.call_continuation(true));
                }
                &Instruction::CallCharCode => {
                    try_or_throw!(self.machine_st, self.char_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharCode => {
                    try_or_throw!(self.machine_st, self.char_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharType => {
                    self.char_type();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharType => {
                    self.char_type();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharsToNumber => {
                    try_or_throw!(self.machine_st, self.chars_to_number());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharsToNumber => {
                    try_or_throw!(self.machine_st, self.chars_to_number());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCodesToNumber => {
                    try_or_throw!(self.machine_st, self.codes_to_number());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCodesToNumber => {
                    try_or_throw!(self.machine_st, self.codes_to_number());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCopyTermWithoutAttrVars => {
                    self.copy_term_without_attr_vars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCopyTermWithoutAttrVars => {
                    self.copy_term_without_attr_vars();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCheckCutPoint => {
                    self.check_cut_point();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCheckCutPoint => {
                    self.check_cut_point();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallClose => {
                    try_or_throw!(self.machine_st, self.close());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteClose => {
                    try_or_throw!(self.machine_st, self.close());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallCopyToLiftedHeap => {
                    self.copy_to_lifted_heap();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteCopyToLiftedHeap => {
                    self.copy_to_lifted_heap();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallCreatePartialString => {
                    self.create_partial_string();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCreatePartialString => {
                    self.create_partial_string();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentHostname => {
                    self.current_hostname();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentHostname => {
                    self.current_hostname();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentInput => {
                    try_or_throw!(self.machine_st, self.current_input());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentInput => {
                    try_or_throw!(self.machine_st, self.current_input());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentOutput => {
                    try_or_throw!(self.machine_st, self.current_output());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentOutput => {
                    try_or_throw!(self.machine_st, self.current_output());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectoryFiles => {
                    try_or_throw!(self.machine_st, self.directory_files());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectoryFiles => {
                    try_or_throw!(self.machine_st, self.directory_files());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileSize => {
                    self.file_size();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileSize => {
                    self.file_size();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileExists => {
                    self.file_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileExists => {
                    self.file_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectoryExists => {
                    self.directory_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectoryExists => {
                    self.directory_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectorySeparator => {
                    self.directory_separator();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectorySeparator => {
                    self.directory_separator();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMakeDirectory => {
                    self.make_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMakeDirectory => {
                    self.make_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMakeDirectoryPath => {
                    self.make_directory_path();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMakeDirectoryPath => {
                    self.make_directory_path();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteFile => {
                    self.delete_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteFile => {
                    self.delete_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallRenameFile => {
                    self.rename_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteRenameFile => {
                    self.rename_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
		&Instruction::CallFileCopy => {
		    self.file_copy();
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteFileCopy => {
		    self.file_copy();
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
                &Instruction::CallWorkingDirectory => {
                    try_or_throw!(self.machine_st, self.working_directory());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWorkingDirectory => {
                    try_or_throw!(self.machine_st, self.working_directory());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteDirectory => {
                    self.delete_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteDirectory => {
                    self.delete_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPathCanonical => {
                    try_or_throw!(self.machine_st, self.path_canonical());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePathCanonical => {
                    try_or_throw!(self.machine_st, self.path_canonical());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileTime => {
                    self.file_time();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileTime => {
                    self.file_time();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDynamicModuleResolution(arity) => {
                    let (module_name, key) = try_or_throw!(
                        self.machine_st,
                        self.dynamic_module_resolution(arity - 2)
                    );

                    try_or_throw!(
                        self.machine_st,
                        self.call_clause(module_name, key)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::ExecuteDynamicModuleResolution(arity) => {
                    let (module_name, key) = try_or_throw!(
                        self.machine_st,
                        self.dynamic_module_resolution(arity - 2)
                    );

                    try_or_throw!(
                        self.machine_st,
                        self.execute_clause(module_name, key)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::CallFetchGlobalVar => {
                    self.fetch_global_var();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFetchGlobalVar => {
                    self.fetch_global_var();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFirstStream => {
                    self.first_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFirstStream => {
                    self.first_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFlushOutput => {
                    try_or_throw!(self.machine_st, self.flush_output());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteFlushOutput => {
                    try_or_throw!(self.machine_st, self.flush_output());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallGetByte => {
                    try_or_throw!(self.machine_st, self.get_byte());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetByte => {
                    try_or_throw!(self.machine_st, self.get_byte());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetChar => {
                    try_or_throw!(self.machine_st, self.get_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetChar => {
                    try_or_throw!(self.machine_st, self.get_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetNChars => {
                    try_or_throw!(self.machine_st, self.get_n_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetNChars => {
                    try_or_throw!(self.machine_st, self.get_n_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCode => {
                    try_or_throw!(self.machine_st, self.get_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCode => {
                    try_or_throw!(self.machine_st, self.get_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetSingleChar => {
                    try_or_throw!(self.machine_st, self.get_single_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetSingleChar => {
                    try_or_throw!(self.machine_st, self.get_single_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateIfNoLiftedHeapGrowthDiff => {
                    self.truncate_if_no_lifted_heap_growth_diff();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTruncateIfNoLiftedHeapGrowthDiff => {
                    self.truncate_if_no_lifted_heap_growth_diff();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateIfNoLiftedHeapGrowth => {
                    self.truncate_if_no_lifted_heap_growth();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTruncateIfNoLiftedHeapGrowth => {
                    self.truncate_if_no_lifted_heap_growth();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttributedVariableList => {
                    self.get_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttributedVariableList => {
                    self.get_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttrVarQueueDelimiter => {
                    self.get_attr_var_queue_delimiter();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttrVarQueueDelimiter => {
                    self.get_attr_var_queue_delimiter();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttrVarQueueBeyond => {
                    self.get_attr_var_queue_beyond();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttrVarQueueBeyond => {
                    self.get_attr_var_queue_beyond();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetBValue => {
                    self.get_b_value();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetBValue => {
                    self.get_b_value();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetContinuationChunk => {
                    self.get_continuation_chunk();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetContinuationChunk => {
                    self.get_continuation_chunk();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLookupDBRef => {
                    self.lookup_db_ref();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLookupDBRef => {
                    self.lookup_db_ref();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetNextOpDBRef => {
                    self.get_next_op_db_ref();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetNextOpDBRef => {
                    self.get_next_op_db_ref();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsPartialString => {
                    self.is_partial_string();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsPartialString => {
                    self.is_partial_string();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHalt => {
                    self.halt();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteHalt => {
                    self.halt();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallGetLiftedHeapFromOffset => {
                    self.get_lifted_heap_from_offset();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetLiftedHeapFromOffset => {
                    self.get_lifted_heap_from_offset();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetLiftedHeapFromOffsetDiff => {
                    self.get_lifted_heap_from_offset_diff();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetLiftedHeapFromOffsetDiff => {
                    self.get_lifted_heap_from_offset_diff();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetSCCCleaner => {
                    self.get_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetSCCCleaner => {
                    self.get_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHeadIsDynamic => {
                    self.head_is_dynamic();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHeadIsDynamic => {
                    self.head_is_dynamic();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallSCCCleaner => {
                    self.install_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallSCCCleaner => {
                    self.install_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallInferenceCounter => {
                    try_or_throw!(self.machine_st, self.install_inference_counter());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallInferenceCounter => {
                    try_or_throw!(self.machine_st, self.install_inference_counter());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLiftedHeapLength => {
                    self.lifted_heap_length();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLiftedHeapLength => {
                    self.lifted_heap_length();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadLibraryAsStream => {
                    try_or_throw!(self.machine_st, self.load_library_as_stream());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadLibraryAsStream => {
                    try_or_throw!(self.machine_st, self.load_library_as_stream());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallModuleExists => {
                    self.module_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteModuleExists => {
                    self.module_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNextEP => {
                    self.next_ep();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNextEP => {
                    self.next_ep();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNoSuchPredicate => {
                    try_or_throw!(self.machine_st, self.no_such_predicate());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNoSuchPredicate => {
                    try_or_throw!(self.machine_st, self.no_such_predicate());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNumberToChars => {
                    self.number_to_chars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNumberToChars => {
                    self.number_to_chars();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNumberToCodes => {
                    self.number_to_codes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNumberToCodes => {
                    self.number_to_codes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallOpDeclaration => {
                    try_or_throw!(self.machine_st, self.op_declaration());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteOpDeclaration => {
                    try_or_throw!(self.machine_st, self.op_declaration());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallOpen => {
                    try_or_throw!(self.machine_st, self.open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteOpen => {
                    try_or_throw!(self.machine_st, self.open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetStreamOptions => {
                    try_or_throw!(self.machine_st, self.set_stream_options());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetStreamOptions => {
                    try_or_throw!(self.machine_st, self.set_stream_options());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallNextStream => {
                    self.next_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNextStream => {
                    self.next_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPartialStringTail => {
                    self.partial_string_tail();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePartialStringTail => {
                    self.partial_string_tail();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekByte => {
                    try_or_throw!(self.machine_st, self.peek_byte());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekByte => {
                    try_or_throw!(self.machine_st, self.peek_byte());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekChar => {
                    try_or_throw!(self.machine_st, self.peek_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekChar => {
                    try_or_throw!(self.machine_st, self.peek_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekCode => {
                    try_or_throw!(self.machine_st, self.peek_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekCode => {
                    try_or_throw!(self.machine_st, self.peek_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPointsToContinuationResetMarker => {
                    self.points_to_continuation_reset_marker();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePointsToContinuationResetMarker => {
                    self.points_to_continuation_reset_marker();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutByte => {
                    try_or_throw!(self.machine_st, self.put_byte());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutByte => {
                    try_or_throw!(self.machine_st, self.put_byte());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPutChar => {
                    try_or_throw!(self.machine_st, self.put_char());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutChar => {
                    try_or_throw!(self.machine_st, self.put_char());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPutChars => {
                    try_or_throw!(self.machine_st, self.put_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePutChars => {
                    try_or_throw!(self.machine_st, self.put_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutCode => {
                    try_or_throw!(self.machine_st, self.put_code());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutCode => {
                    try_or_throw!(self.machine_st, self.put_code());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallReadQueryTerm => {
                    try_or_throw!(self.machine_st, self.read_query_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadQueryTerm => {
                    try_or_throw!(self.machine_st, self.read_query_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReadTerm => {
                    try_or_throw!(self.machine_st, self.read_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadTerm => {
                    try_or_throw!(self.machine_st, self.read_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallRedoAttrVarBinding => {
                    self.redo_attr_var_binding();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRedoAttrVarBinding => {
                    self.redo_attr_var_binding();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveCallPolicyCheck => {
                    self.remove_call_policy_check();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRemoveCallPolicyCheck => {
                    self.remove_call_policy_check();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveInferenceCounter => {
                    self.remove_inference_counter();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteRemoveInferenceCounter => {
                    self.remove_inference_counter();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallResetContinuationMarker => {
                    self.reset_continuation_marker();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteResetContinuationMarker => {
                    self.reset_continuation_marker();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRestoreCutPolicy => {
                    self.restore_cut_policy();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRestoreCutPolicy => {
                    self.restore_cut_policy();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetCutPoint(r) => {
                    if !self.set_cut_point(r) {
                        step_or_fail!(self, self.machine_st.p += 1);
                    }
                }
                &Instruction::ExecuteSetCutPoint(r) => {
                    let cp = self.machine_st.cp;

                    if !self.set_cut_point(r) {
                        step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                    } else {
                        // run_cleaners in set_cut_point calls call_by_index.
                        // replace the effect of call_by_index with that
                        // of execute_by_index here.

                        self.machine_st.cp = cp;
                    }
                }
                &Instruction::CallSetInput => {
                    try_or_throw!(self.machine_st, self.set_input());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetInput => {
                    try_or_throw!(self.machine_st, self.set_input());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetOutput => {
                    try_or_throw!(self.machine_st, self.set_output());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetOutput => {
                    try_or_throw!(self.machine_st, self.set_output());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStoreBacktrackableGlobalVar => {
                    self.store_backtrackable_global_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteStoreBacktrackableGlobalVar => {
                    self.store_backtrackable_global_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStoreGlobalVar => {
                    self.store_global_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteStoreGlobalVar => {
                    self.store_global_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStreamProperty => {
                    try_or_throw!(self.machine_st, self.stream_property());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteStreamProperty => {
                    try_or_throw!(self.machine_st, self.stream_property());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetStreamPosition => {
                    try_or_throw!(self.machine_st, self.set_stream_position());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetStreamPosition => {
                    try_or_throw!(self.machine_st, self.set_stream_position());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInferenceLevel => {
                    self.inference_level();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInferenceLevel => {
                    self.inference_level();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCleanUpBlock => {
                    self.clean_up_block();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteCleanUpBlock => {
                    self.clean_up_block();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallFail | &Instruction::ExecuteFail => {
                    self.machine_st.backtrack();
                }
                &Instruction::CallGetBall => {
                    self.get_ball();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetBall => {
                    self.get_ball();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCurrentBlock => {
                    self.get_current_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCurrentBlock => {
                    self.get_current_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCurrentSCCBlock => {
                    self.get_current_scc_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCurrentSCCBlock => {
                    self.get_current_scc_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCutPoint => {
                    self.get_cut_point();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCutPoint => {
                    self.get_cut_point();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetDoubleQuotes => {
                    self.get_double_quotes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetDoubleQuotes => {
                    self.get_double_quotes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallNewBlock => {
                    self.machine_st.install_new_block(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallNewBlock => {
                    self.machine_st.install_new_block(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMaybe => {
                    self.maybe();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMaybe => {
                    self.maybe();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCpuNow => {
                    self.cpu_now();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCpuNow => {
                    self.cpu_now();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeterministicLengthRundown => {
                    try_or_throw!(self.machine_st, self.det_length_rundown());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeterministicLengthRundown => {
                    try_or_throw!(self.machine_st, self.det_length_rundown());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHttpOpen => {
                    try_or_throw!(self.machine_st, self.http_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHttpOpen => {
                    try_or_throw!(self.machine_st, self.http_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
		&Instruction::CallHttpListen => {
		    try_or_throw!(self.machine_st, self.http_listen());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpListen => {
		    try_or_throw!(self.machine_st, self.http_listen());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallHttpAccept => {
		    try_or_throw!(self.machine_st, self.http_accept());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpAccept => {
		    try_or_throw!(self.machine_st, self.http_accept());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallHttpAnswer => {
		    try_or_throw!(self.machine_st, self.http_answer());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpAnswer => {
		    try_or_throw!(self.machine_st, self.http_answer());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallLoadForeignLib => {
		    try_or_throw!(self.machine_st, self.load_foreign_lib());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteLoadForeignLib => {
		    try_or_throw!(self.machine_st, self.load_foreign_lib());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallForeignCall => {
		    try_or_throw!(self.machine_st, self.foreign_call());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteForeignCall => {
		    try_or_throw!(self.machine_st, self.foreign_call());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallDefineForeignStruct => {
		    try_or_throw!(self.machine_st, self.define_foreign_struct());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteDefineForeignStruct => {
		    try_or_throw!(self.machine_st, self.define_foreign_struct());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
                &Instruction::CallCurrentTime => {
                    self.current_time();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentTime => {
                    self.current_time();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallQuotedToken => {
                    self.quoted_token();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteQuotedToken => {
                    self.quoted_token();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReadTermFromChars => {
                    try_or_throw!(self.machine_st, self.read_term_from_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadTermFromChars => {
                    try_or_throw!(self.machine_st, self.read_term_from_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallResetBlock => {
                    self.reset_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteResetBlock => {
                    self.reset_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallResetSCCBlock => {
                    self.reset_scc_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteResetSCCBlock => {
                    self.reset_scc_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReturnFromVerifyAttr |
                &Instruction::ExecuteReturnFromVerifyAttr => {
                    self.return_from_verify_attr();
                }
                &Instruction::CallSetBall => {
                    self.set_ball();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetBall => {
                    self.set_ball();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushBallStack => {
                    self.push_ball_stack();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePushBallStack => {
                    self.push_ball_stack();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPopBallStack => {
                    self.pop_ball_stack();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopBallStack => {
                    self.pop_ball_stack();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopFromBallStack => {
                    self.pop_from_ball_stack();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopFromBallStack => {
                    self.pop_from_ball_stack();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetCutPointByDefault(r) => {
                    self.set_cut_point_by_default(r);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetCutPointByDefault(r) => {
                    self.set_cut_point_by_default(r);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetDoubleQuotes => {
                    self.set_double_quotes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetDoubleQuotes => {
                    self.set_double_quotes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetSeed => {
                    self.set_seed();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetSeed => {
                    self.set_seed();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSkipMaxList => {
                    try_or_throw!(self.machine_st, self.machine_st.skip_max_list());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSkipMaxList => {
                    try_or_throw!(self.machine_st, self.machine_st.skip_max_list());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSleep => {
                    self.sleep();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSleep => {
                    self.sleep();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSocketClientOpen => {
                    try_or_throw!(self.machine_st, self.socket_client_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketClientOpen => {
                    try_or_throw!(self.machine_st, self.socket_client_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerOpen => {
                    try_or_throw!(self.machine_st, self.socket_server_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketServerOpen => {
                    try_or_throw!(self.machine_st, self.socket_server_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerAccept => {
                    try_or_throw!(self.machine_st, self.socket_server_accept());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketServerAccept => {
                    try_or_throw!(self.machine_st, self.socket_server_accept());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerClose => {
                    try_or_throw!(self.machine_st, self.socket_server_close());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSocketServerClose => {
                    try_or_throw!(self.machine_st, self.socket_server_close());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallTLSAcceptClient => {
                    try_or_throw!(self.machine_st, self.tls_accept_client());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTLSAcceptClient => {
                    try_or_throw!(self.machine_st, self.tls_accept_client());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTLSClientConnect => {
                    try_or_throw!(self.machine_st, self.tls_client_connect());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTLSClientConnect => {
                    try_or_throw!(self.machine_st, self.tls_client_connect());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSucceed => {
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSucceed => {
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallTermAttributedVariables => {
                    self.term_attributed_variables();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermAttributedVariables => {
                    self.term_attributed_variables();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTermVariables => {
                    self.term_variables();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermVariables => {
                    self.term_variables();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTermVariablesUnderMaxDepth => {
                    self.term_variables_under_max_depth();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermVariablesUnderMaxDepth => {
                    self.term_variables_under_max_depth();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateLiftedHeapTo => {
                    self.truncate_lifted_heap_to();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteTruncateLiftedHeapTo => {
                    self.truncate_lifted_heap_to();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnifyWithOccursCheck => {
                    self.unify_with_occurs_check();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteUnifyWithOccursCheck => {
                    self.unify_with_occurs_check();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallUnwindEnvironments => {
                    if !self.unwind_environments() {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteUnwindEnvironments => {
                    if !self.unwind_environments() {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallUnwindStack | &Instruction::ExecuteUnwindStack => {
                    self.machine_st.unwind_stack();
                    self.machine_st.backtrack();
                }
                &Instruction::CallWAMInstructions => {
                    try_or_throw!(self.machine_st, self.wam_instructions());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWAMInstructions => {
                    try_or_throw!(self.machine_st, self.wam_instructions());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInlinedInstructions => {
                    self.inlined_instructions();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteInlinedInstructions => {
                    self.inlined_instructions();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallWriteTerm => {
                    try_or_throw!(self.machine_st, self.write_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWriteTerm => {
                    try_or_throw!(self.machine_st, self.write_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallWriteTermToChars => {
                    try_or_throw!(self.machine_st, self.write_term_to_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWriteTermToChars => {
                    try_or_throw!(self.machine_st, self.write_term_to_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallScryerPrologVersion => {
                    self.scryer_prolog_version();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteScryerPrologVersion => {
                    self.scryer_prolog_version();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoRandomByte => {
                    self.crypto_random_byte();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoRandomByte => {
                    self.crypto_random_byte();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataHash => {
                    self.crypto_data_hash();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataHash => {
                    self.crypto_data_hash();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataHKDF => {
                    self.crypto_data_hkdf();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataHKDF => {
                    self.crypto_data_hkdf();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoPasswordHash => {
                    self.crypto_password_hash();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoPasswordHash => {
                    self.crypto_password_hash();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataEncrypt => {
                    self.crypto_data_encrypt();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataEncrypt => {
                    self.crypto_data_encrypt();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataDecrypt => {
                    self.crypto_data_decrypt();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataDecrypt => {
                    self.crypto_data_decrypt();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoCurveScalarMult => {
                    self.crypto_curve_scalar_mult();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoCurveScalarMult => {
                    self.crypto_curve_scalar_mult();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519Sign => {
                    self.ed25519_sign();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519Sign => {
                    self.ed25519_sign();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519Verify => {
                    self.ed25519_verify();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519Verify => {
                    self.ed25519_verify();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519NewKeyPair => {
                    self.ed25519_new_key_pair();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519NewKeyPair => {
                    self.ed25519_new_key_pair();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519KeyPairPublicKey => {
                    self.ed25519_key_pair_public_key();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519KeyPairPublicKey => {
                    self.ed25519_key_pair_public_key();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurve25519ScalarMult => {
                    self.curve25519_scalar_mult();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurve25519ScalarMult => {
                    self.curve25519_scalar_mult();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFirstNonOctet => {
                    self.first_non_octet();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFirstNonOctet => {
                    self.first_non_octet();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadHTML => {
                    self.load_html();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadHTML => {
                    self.load_html();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadXML => {
                    self.load_xml();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadXML => {
                    self.load_xml();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetEnv => {
                    self.get_env();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetEnv => {
                    self.get_env();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetEnv => {
                    self.set_env();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetEnv => {
                    self.set_env();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnsetEnv => {
                    self.unset_env();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteUnsetEnv => {
                    self.unset_env();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallShell => {
                    self.shell();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteShell => {
                    self.shell();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPID => {
                    self.pid();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePID => {
                    self.pid();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharsBase64 => {
                    try_or_throw!(self.machine_st, self.chars_base64());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharsBase64 => {
                    try_or_throw!(self.machine_st, self.chars_base64());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDevourWhitespace => {
                    try_or_throw!(self.machine_st, self.devour_whitespace());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDevourWhitespace => {
                    try_or_throw!(self.machine_st, self.devour_whitespace());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsSTOEnabled => {
                    self.is_sto_enabled();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsSTOEnabled => {
                    self.is_sto_enabled();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetSTOAsUnify => {
                    self.set_sto_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetSTOAsUnify => {
                    self.set_sto_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetNSTOAsUnify => {
                    self.set_nsto_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetNSTOAsUnify => {
                    self.set_nsto_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetSTOWithErrorAsUnify => {
                    self.set_sto_with_error_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetSTOWithErrorAsUnify => {
                    self.set_sto_with_error_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallHomeDirectory => {
                    self.home_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHomeDirectory => {
                    self.home_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDebugHook => {
                    self.debug_hook();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDebugHook => {
                    self.debug_hook();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopCount => {
                    self.pop_count();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePopCount => {
                    self.pop_count();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAddDiscontiguousPredicate => {
                    try_or_throw!(self.machine_st, self.add_discontiguous_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddDiscontiguousPredicate => {
                    try_or_throw!(self.machine_st, self.add_discontiguous_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddDynamicPredicate => {
                    try_or_throw!(self.machine_st, self.add_dynamic_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddDynamicPredicate => {
                    try_or_throw!(self.machine_st, self.add_dynamic_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddMultifilePredicate => {
                    try_or_throw!(self.machine_st, self.add_multifile_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddMultifilePredicate => {
                    try_or_throw!(self.machine_st, self.add_multifile_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddGoalExpansionClause => {
                    try_or_throw!(self.machine_st, self.add_goal_expansion_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddGoalExpansionClause => {
                    try_or_throw!(self.machine_st, self.add_goal_expansion_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddTermExpansionClause => {
                    try_or_throw!(self.machine_st, self.add_term_expansion_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddTermExpansionClause => {
                    try_or_throw!(self.machine_st, self.add_term_expansion_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddInSituFilenameModule => {
                    try_or_throw!(self.machine_st, self.add_in_situ_filename_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddInSituFilenameModule => {
                    try_or_throw!(self.machine_st, self.add_in_situ_filename_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallClauseToEvacuable => {
                    try_or_throw!(self.machine_st, self.clause_to_evacuable());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteClauseToEvacuable => {
                    try_or_throw!(self.machine_st, self.clause_to_evacuable());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallScopedClauseToEvacuable => {
                    try_or_throw!(self.machine_st, self.scoped_clause_to_evacuable());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteScopedClauseToEvacuable => {
                    try_or_throw!(self.machine_st, self.scoped_clause_to_evacuable());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallConcludeLoad => {
                    try_or_throw!(self.machine_st, self.conclude_load());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteConcludeLoad => {
                    try_or_throw!(self.machine_st, self.conclude_load());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallDeclareModule => {
                    try_or_throw!(self.machine_st, self.declare_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDeclareModule => {
                    try_or_throw!(self.machine_st, self.declare_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallLoadCompiledLibrary => {
                    try_or_throw!(self.machine_st, self.load_compiled_library());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadCompiledLibrary => {
                    try_or_throw!(self.machine_st, self.load_compiled_library());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextSource => {
                    self.load_context_source();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextSource => {
                    self.load_context_source();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextFile => {
                    self.load_context_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextFile => {
                    self.load_context_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextDirectory => {
                    self.load_context_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextDirectory => {
                    self.load_context_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextModule => {
                    self.load_context_module(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextModule => {
                    self.load_context_module(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextStream => {
                    self.load_context_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextStream => {
                    self.load_context_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPopLoadContext => {
                    self.pop_load_context();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopLoadContext => {
                    self.pop_load_context();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopLoadStatePayload => {
                    self.pop_load_state_payload();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopLoadStatePayload => {
                    self.pop_load_state_payload();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushLoadContext => {
                    try_or_throw!(self.machine_st, self.push_load_context());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePushLoadContext => {
                    try_or_throw!(self.machine_st, self.push_load_context());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushLoadStatePayload => {
                    self.push_load_state_payload();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePushLoadStatePayload => {
                    self.push_load_state_payload();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallUseModule => {
                    try_or_throw!(self.machine_st, self.use_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteUseModule => {
                    try_or_throw!(self.machine_st, self.use_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallBuiltInProperty => {
                    let key = self
                        .machine_st
                        .read_predicate_key(self.machine_st.registers[1], self.machine_st.registers[2]);

                    self.machine_st.fail = !self.indices.builtin_property(key);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteBuiltInProperty => {
                    let key = self
                        .machine_st
                        .read_predicate_key(self.machine_st.registers[1], self.machine_st.registers[2]);

                    self.machine_st.fail = !self.indices.builtin_property(key);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMetaPredicateProperty => {
                    self.meta_predicate_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMetaPredicateProperty => {
                    self.meta_predicate_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMultifileProperty => {
                    self.multifile_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMultifileProperty => {
                    self.multifile_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDiscontiguousProperty => {
                    self.discontiguous_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDiscontiguousProperty => {
                    self.discontiguous_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDynamicProperty => {
                    self.dynamic_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDynamicProperty => {
                    self.dynamic_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAbolishClause => {
                    try_or_throw!(self.machine_st, self.abolish_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAbolishClause => {
                    try_or_throw!(self.machine_st, self.abolish_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAsserta => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Prepend));
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAsserta => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Prepend));
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAssertz => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Append));
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAssertz => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Append));
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRetract => {
                    try_or_throw!(self.machine_st, self.retract_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRetract => {
                    try_or_throw!(self.machine_st, self.retract_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallIsConsistentWithTermQueue => {
                    try_or_throw!(self.machine_st, self.is_consistent_with_term_queue());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsConsistentWithTermQueue => {
                    try_or_throw!(self.machine_st, self.is_consistent_with_term_queue());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::CallFlushTermQueue => {
                    try_or_throw!(self.machine_st, self.flush_term_queue());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteFlushTermQueue => {
                    try_or_throw!(self.machine_st, self.flush_term_queue());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveModuleExports => {
                    try_or_throw!(self.machine_st, self.remove_module_exports());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRemoveModuleExports => {
                    try_or_throw!(self.machine_st, self.remove_module_exports());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddNonCountedBacktracking => {
                    try_or_throw!(self.machine_st, self.add_non_counted_backtracking());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddNonCountedBacktracking => {
                    try_or_throw!(self.machine_st, self.add_non_counted_backtracking());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPredicateDefined => {
                    self.machine_st.fail = !self.predicate_defined();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePredicateDefined => {
                    self.machine_st.fail = !self.predicate_defined();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallStripModule => {
                    self.strip_module();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteStripModule => {
                    self.strip_module();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPrepareCallClause(arity) => {
                    try_or_throw!(self.machine_st, self.prepare_call_clause(arity));
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePrepareCallClause(arity) => {
                    try_or_throw!(self.machine_st, self.prepare_call_clause(arity));
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCompileInlineOrExpandedGoal => {
                    try_or_throw!(self.machine_st, self.compile_inline_or_expanded_goal());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCompileInlineOrExpandedGoal => {
                    try_or_throw!(self.machine_st, self.compile_inline_or_expanded_goal());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsExpandedOrInlined => {
                    self.machine_st.fail = !self.is_expanded_or_inlined();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsExpandedOrInlined => {
                    self.machine_st.fail = !self.is_expanded_or_inlined();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFastCallN(arity) => {
                    let call_at_index = |wam: &mut Machine, name, arity, ptr| {
                        wam.try_call(name, arity, ptr)
                    };

                    try_or_throw!(self.machine_st, self.fast_call(arity, call_at_index));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::ExecuteFastCallN(arity) => {
                    let call_at_index = |wam: &mut Machine, name, arity, ptr| {
                        wam.try_execute(name, arity, ptr)
                    };

                    try_or_throw!(self.machine_st, self.fast_call(arity, call_at_index));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::CallGetClauseP => {
                    let module_name = cell_as_atom!(self.deref_register(3));

                    let (n, p) = self.get_clause_p(module_name);

                    let r = self.machine_st.registers[2];
                    let r = self.machine_st.store(self.machine_st.deref(r));

                    let h = self.machine_st.heap.len();
                    self.machine_st.heap.extend(functor!(atom!("-"), [fixnum(n), fixnum(p)]));

                    let r = r.as_var().unwrap();
                    self.machine_st.bind(r, str_loc_as_cell!(h));

                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetClauseP => {
                    let module_name = cell_as_atom!(self.deref_register(3));

                    let (n, p) = self.get_clause_p(module_name);

                    let r = self.machine_st.registers[2];
                    let r = self.machine_st.store(self.machine_st.deref(r));

                    let h = self.machine_st.heap.len();
                    self.machine_st.heap.extend(functor!(atom!("-"), [fixnum(n), fixnum(p)]));

                    let r = r.as_var().unwrap();
                    self.machine_st.bind(r, str_loc_as_cell!(h));

                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInvokeClauseAtP => {
                    let key_cell = self.machine_st.registers[1];
                    let key = self.machine_st.name_and_arity_from_heap(key_cell).unwrap();

                    let l = self.machine_st.registers[3];
                    let l = self.machine_st.store(self.machine_st.deref(l));

                    let l = match Number::try_from(l) {
                        Ok(Number::Fixnum(l)) => l.get_num() as usize,
                        _ => unreachable!(),
                    };

                    let p = self.machine_st.registers[4];
                    let p = self.machine_st.store(self.machine_st.deref(p));

                    let p = match Number::try_from(p) {
                        Ok(Number::Fixnum(p)) => p.get_num() as usize,
                        _ => unreachable!(),
                    };

                    let module_name = cell_as_atom!(self.deref_register(6));

                    let compilation_target = match module_name {
                        atom!("user") => CompilationTarget::User,
                        _ => CompilationTarget::Module(module_name),
                    };

                    let skeleton = self.indices.get_predicate_skeleton_mut(
                        &compilation_target,
                        &key,
                    ).unwrap();

                    match skeleton.target_pos_of_clause_clause_loc(l) {
                        Some(n) => {
                            let r = self.machine_st.store(self.machine_st.deref(
                                self.machine_st.registers[5],
                            ));

                            self.machine_st.unify_fixnum(Fixnum::build_with(n as i64), r);
                        }
                        None => {}
                    }

                    self.machine_st.call_at_index(2, p);
                }
                &Instruction::ExecuteInvokeClauseAtP => {
                    let key_cell = self.machine_st.registers[1];
                    let key = self.machine_st.name_and_arity_from_heap(key_cell).unwrap();

                    let l = self.machine_st.registers[3];
                    let l = self.machine_st.store(self.machine_st.deref(l));

                    let l = match Number::try_from(l) {
                        Ok(Number::Fixnum(l)) => l.get_num() as usize,
                        _ => unreachable!(),
                    };

                    let p = self.machine_st.registers[4];
                    let p = self.machine_st.store(self.machine_st.deref(p));

                    let p = match Number::try_from(p) {
                        Ok(Number::Fixnum(p)) => p.get_num() as usize,
                        _ => unreachable!(),
                    };

                    let module_name = cell_as_atom!(self.deref_register(6));

                    let compilation_target = match module_name {
                        atom!("user") => CompilationTarget::User,
                        _ => CompilationTarget::Module(module_name),
                    };

                    let skeleton = self.indices.get_predicate_skeleton_mut(
                        &compilation_target,
                        &key,
                    ).unwrap();

                    match skeleton.target_pos_of_clause_clause_loc(l) {
                        Some(n) => {
                            let r = self.machine_st.store(self.machine_st.deref(
                                self.machine_st.registers[5],
                            ));

                            self.machine_st.unify_fixnum(Fixnum::build_with(n as i64), r);
                        }
                        None => {}
                    }

                    self.machine_st.execute_at_index(2, p);
                }
                &Instruction::CallGetFromAttributedVarList => {
                    self.get_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetFromAttributedVarList => {
                    self.get_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutToAttributedVarList => {
                    self.put_to_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePutToAttributedVarList => {
                    self.put_to_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteFromAttributedVarList => {
                    self.delete_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteFromAttributedVarList => {
                    self.delete_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteAllAttributesFromVar => {
                    self.delete_all_attributes_from_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDeleteAllAttributesFromVar => {
                    self.delete_all_attributes_from_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnattributedVar => {
                    self.machine_st.unattributed_var();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteUnattributedVar => {
                    self.machine_st.unattributed_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallGetDBRefs => {
                    self.get_db_refs();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetDBRefs => {
                    self.get_db_refs();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
            }
        }

        let interrupted = INTERRUPT.load(std::sync::atomic::Ordering::Relaxed);

        match INTERRUPT.compare_exchange(
            interrupted,
            false,
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
        ) {
            Ok(interruption) => {
                if interruption {
                    self.machine_st.throw_interrupt_exception();
                    self.machine_st.backtrack();
                }
            }
            Err(_) => unreachable!(),
        }
        }
    }
}
