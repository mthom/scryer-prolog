use crate::arena::*;
use crate::atom_table::*;
use crate::instructions::*;
use crate::machine::*;
use crate::machine::arithmetic_ops::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_state::*;
use crate::types::*;

use crate::try_numeric_result;

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

    fn keysort(&mut self) -> CallResult {
        self.check_keysort_errors()?;

        let stub_gen = || functor_stub(atom!("keysort"), 2);
        let list = self.try_from_list(self.registers[1], stub_gen)?;

        let mut key_pairs = Vec::with_capacity(list.len());

        for val in list {
            let key = self.project_onto_key(val)?;
            key_pairs.push((key, val));
        }

        key_pairs.sort_by(|a1, a2| {
            compare_term_test!(self, a1.0, a2.0).unwrap_or(Ordering::Less)
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
            Err(CompilationError::ParserError(ParserError::UnexpectedEOF)) => {
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
                    let offset = read_heap_cell!(addr,
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
                            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[st])
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
                    );

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
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(ref hm)) => {
                    let lit = read_heap_cell!(addr,
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
                            Literal::Atom(cell_as_atom_cell!(self.machine_st.heap[s]).get_name())
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
                    );

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
                &IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(ref hm)) => {
                    let offset = read_heap_cell!(addr,
                        (HeapCellValueTag::Atom, (name, arity)) => {
                            match hm.get(&(name, arity)) {
                                Some(offset) => *offset,
                                None => IndexingCodePtr::Fail,
                            }
                        }
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                                .get_name_and_arity();

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
                                            self.machine_st.try_me_else(next_i);
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
                                            self.machine_st.try_me_else(next_i);
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
                    self.machine_st.try_me_else(offset);
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

                    self.machine_st[r] = fixnum_as_cell!(Fixnum::build_with(b0 as i64));
                    self.machine_st.p += 1;
                }
                &Instruction::GetLevelAndUnify(r) => {
                    // let b0 = self.machine_st[perm_v!(1)];
                    let b0 = cell_as_fixnum!(
                        self.machine_st.stack[stack_loc!(AndFrame, self.machine_st.e, 1)]
                    );
                    let a = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    // unify_fn!(&mut self.machine_st, a, b0);
                    self.machine_st.unify_fixnum(b0, a);
                    step_or_fail!(self, self.machine_st.p += 1);
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
                &Instruction::DefaultCallAcyclicTerm(_) => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteAcyclicTerm(_) => {
                    let addr = self.machine_st.registers[1];

                    if self.machine_st.is_cyclic_term(addr) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallArg(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteArg(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.try_arg());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallCompare(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteCompare(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.compare());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallTermGreaterThan(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteTermGreaterThan(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Greater) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultCallTermLessThan(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p += 1;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteTermLessThan(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Less) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.p = self.machine_st.cp;
                    } else {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultCallTermGreaterThanOrEqual(_) => {
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
                &Instruction::DefaultExecuteTermGreaterThanOrEqual(_) => {
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
                &Instruction::DefaultCallTermLessThanOrEqual(_) => {
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
                &Instruction::DefaultExecuteTermLessThanOrEqual(_) => {
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
                &Instruction::DefaultCallRead(_) => {
                    try_or_throw!(self.machine_st, self.read());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteRead(_) => {
                    try_or_throw!(self.machine_st, self.read());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallCopyTerm(_) => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteCopyTerm(_) => {
                    self.machine_st.copy_term(AttrVarPolicy::DeepCopy);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallTermEqual(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteTermEqual(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if self.machine_st.eq_test(a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallGround(_) => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteGround(_) => {
                    if self.machine_st.ground_test() {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallFunctor(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteFunctor(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.try_functor());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallTermNotEqual(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::DefaultExecuteTermNotEqual(_) => {
                    let a1 = self.machine_st.registers[1];
                    let a2 = self.machine_st.registers[2];

                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallSort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteSort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.sort());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::DefaultCallKeySort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteKeySort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::DefaultCallIs(r, at, _) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::DefaultExecuteIs(r, at, _) => {
                    try_or_throw!(self.machine_st, self.machine_st.is(r, at));
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAcyclicTerm(_) => {
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
                &Instruction::ExecuteAcyclicTerm(_) => {
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
                &Instruction::CallArg(_) => {
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
                &Instruction::ExecuteArg(_) => {
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
                &Instruction::CallCompare(_) => {
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
                &Instruction::ExecuteCompare(_) => {
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
                &Instruction::CallTermGreaterThan(_) => {
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
                &Instruction::ExecuteTermGreaterThan(_) => {
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
                &Instruction::CallTermLessThan(_) => {
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
                &Instruction::ExecuteTermLessThan(_) => {
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
                &Instruction::CallTermGreaterThanOrEqual(_) => {
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
                &Instruction::ExecuteTermGreaterThanOrEqual(_) => {
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
                &Instruction::CallTermLessThanOrEqual(_) => {
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
                &Instruction::ExecuteTermLessThanOrEqual(_) => {
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
                &Instruction::CallRead(_) => {
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
                &Instruction::ExecuteRead(_) => {
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
                &Instruction::CallCopyTerm(_) => {
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
                &Instruction::ExecuteCopyTerm(_) => {
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
                &Instruction::CallTermEqual(_) => {
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
                &Instruction::ExecuteTermEqual(_) => {
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
                &Instruction::CallGround(_) => {
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
                &Instruction::ExecuteGround(_) => {
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
                &Instruction::CallFunctor(_) => {
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
                &Instruction::ExecuteFunctor(_) => {
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
                &Instruction::CallTermNotEqual(_) => {
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
                &Instruction::ExecuteTermNotEqual(_) => {
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
                &Instruction::CallSort(_) => {
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
                &Instruction::ExecuteSort(_) => {
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
                &Instruction::CallKeySort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort());

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
                &Instruction::ExecuteKeySort(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.keysort());

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
                &Instruction::CallIs(r, at, _) => {
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
                &Instruction::ExecuteIs(r, at, _) => {
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
                &Instruction::CallN(arity, _) => {
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
                &Instruction::ExecuteN(arity, _) => {
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
                &Instruction::DefaultCallN(arity, _) => {
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
                &Instruction::DefaultExecuteN(arity, _) => {
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
                &Instruction::CallNumberLessThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberLessThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::CallNumberEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::CallNumberNotEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberNotEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::CallNumberGreaterThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberGreaterThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::CallNumberGreaterThan(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberGreaterThan(ref at_1, ref at_2, _) => {
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
                &Instruction::CallNumberLessThan(ref at_1, ref at_2, _) => {
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
                &Instruction::ExecuteNumberLessThan(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberLessThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberLessThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberNotEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberNotEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberGreaterThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberGreaterThanOrEqual(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberGreaterThan(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberGreaterThan(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultCallNumberLessThan(ref at_1, ref at_2, _) => {
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
                &Instruction::DefaultExecuteNumberLessThan(ref at_1, ref at_2, _) => {
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
                &Instruction::CallIsAtom(r, _) => {
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
                &Instruction::ExecuteIsAtom(r, _) => {
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
                &Instruction::CallIsAtomic(r, _) => {
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
                &Instruction::ExecuteIsAtomic(r, _) => {
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
                &Instruction::CallIsCompound(r, _) => {
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
                &Instruction::ExecuteIsCompound(r, _) => {
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
                &Instruction::CallIsInteger(r, _) => {
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
                &Instruction::ExecuteIsInteger(r, _) => {
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
                &Instruction::CallIsNumber(r, _) => {
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
                &Instruction::ExecuteIsNumber(r, _) => {
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
                &Instruction::CallIsRational(r, _) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Cons, ptr) => {
                            match_untyped_arena_ptr!(ptr,
                                 (ArenaHeaderTag::Rational, _r) => {
                                     self.machine_st.p += 1;
                                 }
                                 _ => {
                                     self.machine_st.backtrack();
                                 }
                            );
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::ExecuteIsRational(r, _) => {
                    let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));

                    read_heap_cell!(d,
                        (HeapCellValueTag::Cons, ptr) => {
                            match_untyped_arena_ptr!(ptr,
                                 (ArenaHeaderTag::Rational, _r) => {
                                     self.machine_st.p = self.machine_st.cp;
                                 }
                                 _ => {
                                     self.machine_st.backtrack();
                                 }
                            );
                        }
                        _ => {
                            self.machine_st.backtrack();
                        }
                    );
                }
                &Instruction::CallIsFloat(r, _) => {
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
                &Instruction::ExecuteIsFloat(r, _) => {
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
                &Instruction::CallIsNonVar(r, _) => {
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
                &Instruction::ExecuteIsNonVar(r, _) => {
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
                &Instruction::CallIsVar(r, _) => {
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
                &Instruction::ExecuteIsVar(r, _) => {
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
                &Instruction::CallNamed(arity, name, ref idx, _) => {
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
                &Instruction::ExecuteNamed(arity, name, ref idx, _) => {
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
                &Instruction::DefaultCallNamed(arity, name, ref idx, _) => {
                    let idx = idx.get();

                    try_or_throw!(
                        self.machine_st,
                        self.try_call(name, arity, idx)
                    );

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                &Instruction::DefaultExecuteNamed(arity, name, ref idx, _) => {
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
                &Instruction::JmpByCall(arity, offset, _) => {
                    self.machine_st.num_of_args = arity;
                    self.machine_st.b0 = self.machine_st.b;
                    self.machine_st.cp = self.machine_st.p + 1;
                    self.machine_st.p += offset;
                }
                &Instruction::JmpByExecute(arity, offset, _) => {
                    self.machine_st.num_of_args = arity;
                    self.machine_st.b0 = self.machine_st.b;
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
                &Instruction::GetStructure(name, arity, reg) => {
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
                                    self.machine_st.indexed_try(offset);
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
                                                    self.machine_st.indexed_try(offset);
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
                &Instruction::PutUnsafeValue(n, arg) => {
                    let s = stack_loc!(AndFrame, self.machine_st.e, n);
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
                &Instruction::CallAtomChars(_) => {
                    self.atom_chars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteAtomChars(_) => {
                    self.atom_chars();

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallAtomCodes(_) => {
                    try_or_throw!(self.machine_st, self.atom_codes());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteAtomCodes(_) => {
                    try_or_throw!(self.machine_st, self.atom_codes());

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallAtomLength(_) => {
                    self.atom_length();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteAtomLength(_) => {
                    self.atom_length();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallBindFromRegister(_) => {
                    self.bind_from_register();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteBindFromRegister(_) => {
                    self.bind_from_register();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallContinuation(_) => {
                    try_or_throw!(self.machine_st, self.call_continuation(false));
                }
                &Instruction::ExecuteContinuation(_) => {
                    try_or_throw!(self.machine_st, self.call_continuation(true));
                }
                &Instruction::CallCharCode(_) => {
                    try_or_throw!(self.machine_st, self.char_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharCode(_) => {
                    try_or_throw!(self.machine_st, self.char_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharType(_) => {
                    self.char_type();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharType(_) => {
                    self.char_type();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharsToNumber(_) => {
                    try_or_throw!(self.machine_st, self.chars_to_number());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharsToNumber(_) => {
                    try_or_throw!(self.machine_st, self.chars_to_number());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCodesToNumber(_) => {
                    try_or_throw!(self.machine_st, self.codes_to_number());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCodesToNumber(_) => {
                    try_or_throw!(self.machine_st, self.codes_to_number());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCopyTermWithoutAttrVars(_) => {
                    self.copy_term_without_attr_vars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCopyTermWithoutAttrVars(_) => {
                    self.copy_term_without_attr_vars();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCheckCutPoint(_) => {
                    self.check_cut_point();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCheckCutPoint(_) => {
                    self.check_cut_point();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallClose(_) => {
                    try_or_throw!(self.machine_st, self.close());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteClose(_) => {
                    try_or_throw!(self.machine_st, self.close());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallCopyToLiftedHeap(_) => {
                    self.copy_to_lifted_heap();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteCopyToLiftedHeap(_) => {
                    self.copy_to_lifted_heap();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallCreatePartialString(_) => {
                    self.create_partial_string();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCreatePartialString(_) => {
                    self.create_partial_string();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentHostname(_) => {
                    self.current_hostname();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentHostname(_) => {
                    self.current_hostname();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentInput(_) => {
                    try_or_throw!(self.machine_st, self.current_input());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentInput(_) => {
                    try_or_throw!(self.machine_st, self.current_input());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurrentOutput(_) => {
                    try_or_throw!(self.machine_st, self.current_output());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentOutput(_) => {
                    try_or_throw!(self.machine_st, self.current_output());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectoryFiles(_) => {
                    try_or_throw!(self.machine_st, self.directory_files());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectoryFiles(_) => {
                    try_or_throw!(self.machine_st, self.directory_files());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileSize(_) => {
                    self.file_size();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileSize(_) => {
                    self.file_size();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileExists(_) => {
                    self.file_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileExists(_) => {
                    self.file_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectoryExists(_) => {
                    self.directory_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectoryExists(_) => {
                    self.directory_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDirectorySeparator(_) => {
                    self.directory_separator();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDirectorySeparator(_) => {
                    self.directory_separator();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMakeDirectory(_) => {
                    self.make_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMakeDirectory(_) => {
                    self.make_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMakeDirectoryPath(_) => {
                    self.make_directory_path();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMakeDirectoryPath(_) => {
                    self.make_directory_path();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteFile(_) => {
                    self.delete_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteFile(_) => {
                    self.delete_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallRenameFile(_) => {
                    self.rename_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteRenameFile(_) => {
                    self.rename_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
		&Instruction::CallFileCopy(_) => {
		    self.file_copy();
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteFileCopy(_) => {
		    self.file_copy();
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
                &Instruction::CallWorkingDirectory(_) => {
                    try_or_throw!(self.machine_st, self.working_directory());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWorkingDirectory(_) => {
                    try_or_throw!(self.machine_st, self.working_directory());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteDirectory(_) => {
                    self.delete_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteDirectory(_) => {
                    self.delete_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPathCanonical(_) => {
                    try_or_throw!(self.machine_st, self.path_canonical());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePathCanonical(_) => {
                    try_or_throw!(self.machine_st, self.path_canonical());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFileTime(_) => {
                    self.file_time();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFileTime(_) => {
                    self.file_time();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDynamicModuleResolution(arity, _) => {
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
                &Instruction::ExecuteDynamicModuleResolution(arity, _) => {
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
                &Instruction::CallFetchGlobalVar(_) => {
                    self.fetch_global_var();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFetchGlobalVar(_) => {
                    self.fetch_global_var();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFirstStream(_) => {
                    self.first_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFirstStream(_) => {
                    self.first_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFlushOutput(_) => {
                    try_or_throw!(self.machine_st, self.flush_output());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteFlushOutput(_) => {
                    try_or_throw!(self.machine_st, self.flush_output());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallGetByte(_) => {
                    try_or_throw!(self.machine_st, self.get_byte());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetByte(_) => {
                    try_or_throw!(self.machine_st, self.get_byte());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetChar(_) => {
                    try_or_throw!(self.machine_st, self.get_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetChar(_) => {
                    try_or_throw!(self.machine_st, self.get_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetNChars(_) => {
                    try_or_throw!(self.machine_st, self.get_n_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetNChars(_) => {
                    try_or_throw!(self.machine_st, self.get_n_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCode(_) => {
                    try_or_throw!(self.machine_st, self.get_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCode(_) => {
                    try_or_throw!(self.machine_st, self.get_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetSingleChar(_) => {
                    try_or_throw!(self.machine_st, self.get_single_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetSingleChar(_) => {
                    try_or_throw!(self.machine_st, self.get_single_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateIfNoLiftedHeapGrowthDiff(_) => {
                    self.truncate_if_no_lifted_heap_growth_diff();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTruncateIfNoLiftedHeapGrowthDiff(_) => {
                    self.truncate_if_no_lifted_heap_growth_diff();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateIfNoLiftedHeapGrowth(_) => {
                    self.truncate_if_no_lifted_heap_growth();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTruncateIfNoLiftedHeapGrowth(_) => {
                    self.truncate_if_no_lifted_heap_growth();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttributedVariableList(_) => {
                    self.get_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttributedVariableList(_) => {
                    self.get_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttrVarQueueDelimiter(_) => {
                    self.get_attr_var_queue_delimiter();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttrVarQueueDelimiter(_) => {
                    self.get_attr_var_queue_delimiter();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetAttrVarQueueBeyond(_) => {
                    self.get_attr_var_queue_beyond();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetAttrVarQueueBeyond(_) => {
                    self.get_attr_var_queue_beyond();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetBValue(_) => {
                    self.get_b_value();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetBValue(_) => {
                    self.get_b_value();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetContinuationChunk(_) => {
                    self.get_continuation_chunk();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetContinuationChunk(_) => {
                    self.get_continuation_chunk();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetNextDBRef(_) => {
                    self.get_next_db_ref();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetNextDBRef(_) => {
                    self.get_next_db_ref();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetNextOpDBRef(_) => {
                    self.get_next_op_db_ref();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetNextOpDBRef(_) => {
                    self.get_next_op_db_ref();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsPartialString(_) => {
                    self.is_partial_string();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsPartialString(_) => {
                    self.is_partial_string();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHalt(_) => {
                    self.halt();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteHalt(_) => {
                    self.halt();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallGetLiftedHeapFromOffset(_) => {
                    self.get_lifted_heap_from_offset();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetLiftedHeapFromOffset(_) => {
                    self.get_lifted_heap_from_offset();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetLiftedHeapFromOffsetDiff(_) => {
                    self.get_lifted_heap_from_offset_diff();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetLiftedHeapFromOffsetDiff(_) => {
                    self.get_lifted_heap_from_offset_diff();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetSCCCleaner(_) => {
                    self.get_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetSCCCleaner(_) => {
                    self.get_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHeadIsDynamic(_) => {
                    self.head_is_dynamic();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHeadIsDynamic(_) => {
                    self.head_is_dynamic();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallSCCCleaner(_) => {
                    self.install_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallSCCCleaner(_) => {
                    self.install_scc_cleaner();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallInferenceCounter(_) => {
                    try_or_throw!(self.machine_st, self.install_inference_counter());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallInferenceCounter(_) => {
                    try_or_throw!(self.machine_st, self.install_inference_counter());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLiftedHeapLength(_) => {
                    self.lifted_heap_length();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLiftedHeapLength(_) => {
                    self.lifted_heap_length();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadLibraryAsStream(_) => {
                    try_or_throw!(self.machine_st, self.load_library_as_stream());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadLibraryAsStream(_) => {
                    try_or_throw!(self.machine_st, self.load_library_as_stream());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallModuleExists(_) => {
                    self.module_exists();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteModuleExists(_) => {
                    self.module_exists();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNextEP(_) => {
                    self.next_ep();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNextEP(_) => {
                    self.next_ep();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNoSuchPredicate(_) => {
                    try_or_throw!(self.machine_st, self.no_such_predicate());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNoSuchPredicate(_) => {
                    try_or_throw!(self.machine_st, self.no_such_predicate());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNumberToChars(_) => {
                    self.number_to_chars();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNumberToChars(_) => {
                    self.number_to_chars();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallNumberToCodes(_) => {
                    self.number_to_codes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNumberToCodes(_) => {
                    self.number_to_codes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallOpDeclaration(_) => {
                    try_or_throw!(self.machine_st, self.op_declaration());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteOpDeclaration(_) => {
                    try_or_throw!(self.machine_st, self.op_declaration());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallOpen(_) => {
                    try_or_throw!(self.machine_st, self.open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteOpen(_) => {
                    try_or_throw!(self.machine_st, self.open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetStreamOptions(_) => {
                    try_or_throw!(self.machine_st, self.set_stream_options());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetStreamOptions(_) => {
                    try_or_throw!(self.machine_st, self.set_stream_options());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallNextStream(_) => {
                    self.next_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteNextStream(_) => {
                    self.next_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPartialStringTail(_) => {
                    self.partial_string_tail();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePartialStringTail(_) => {
                    self.partial_string_tail();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekByte(_) => {
                    try_or_throw!(self.machine_st, self.peek_byte());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekByte(_) => {
                    try_or_throw!(self.machine_st, self.peek_byte());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekChar(_) => {
                    try_or_throw!(self.machine_st, self.peek_char());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekChar(_) => {
                    try_or_throw!(self.machine_st, self.peek_char());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPeekCode(_) => {
                    try_or_throw!(self.machine_st, self.peek_code());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePeekCode(_) => {
                    try_or_throw!(self.machine_st, self.peek_code());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPointsToContinuationResetMarker(_) => {
                    self.points_to_continuation_reset_marker();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePointsToContinuationResetMarker(_) => {
                    self.points_to_continuation_reset_marker();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutByte(_) => {
                    try_or_throw!(self.machine_st, self.put_byte());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutByte(_) => {
                    try_or_throw!(self.machine_st, self.put_byte());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPutChar(_) => {
                    try_or_throw!(self.machine_st, self.put_char());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutChar(_) => {
                    try_or_throw!(self.machine_st, self.put_char());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPutChars(_) => {
                    try_or_throw!(self.machine_st, self.put_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePutChars(_) => {
                    try_or_throw!(self.machine_st, self.put_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutCode(_) => {
                    try_or_throw!(self.machine_st, self.put_code());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePutCode(_) => {
                    try_or_throw!(self.machine_st, self.put_code());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallReadQueryTerm(_) => {
                    try_or_throw!(self.machine_st, self.read_query_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadQueryTerm(_) => {
                    try_or_throw!(self.machine_st, self.read_query_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReadTerm(_) => {
                    try_or_throw!(self.machine_st, self.read_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadTerm(_) => {
                    try_or_throw!(self.machine_st, self.read_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallRedoAttrVarBinding(_) => {
                    self.redo_attr_var_binding();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRedoAttrVarBinding(_) => {
                    self.redo_attr_var_binding();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveCallPolicyCheck(_) => {
                    self.remove_call_policy_check();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRemoveCallPolicyCheck(_) => {
                    self.remove_call_policy_check();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveInferenceCounter(_) => {
                    self.remove_inference_counter();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteRemoveInferenceCounter(_) => {
                    self.remove_inference_counter();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallResetContinuationMarker(_) => {
                    self.reset_continuation_marker();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteResetContinuationMarker(_) => {
                    self.reset_continuation_marker();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRestoreCutPolicy(_) => {
                    self.restore_cut_policy();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRestoreCutPolicy(_) => {
                    self.restore_cut_policy();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetCutPoint(r, _) => {
                    if !self.set_cut_point(r) {
                        step_or_fail!(self, self.machine_st.p += 1);
                    }
                }
                &Instruction::ExecuteSetCutPoint(r, _) => {
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
                &Instruction::CallSetInput(_) => {
                    try_or_throw!(self.machine_st, self.set_input());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetInput(_) => {
                    try_or_throw!(self.machine_st, self.set_input());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetOutput(_) => {
                    try_or_throw!(self.machine_st, self.set_output());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetOutput(_) => {
                    try_or_throw!(self.machine_st, self.set_output());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStoreBacktrackableGlobalVar(_) => {
                    self.store_backtrackable_global_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteStoreBacktrackableGlobalVar(_) => {
                    self.store_backtrackable_global_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStoreGlobalVar(_) => {
                    self.store_global_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteStoreGlobalVar(_) => {
                    self.store_global_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallStreamProperty(_) => {
                    try_or_throw!(self.machine_st, self.stream_property());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteStreamProperty(_) => {
                    try_or_throw!(self.machine_st, self.stream_property());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetStreamPosition(_) => {
                    try_or_throw!(self.machine_st, self.set_stream_position());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetStreamPosition(_) => {
                    try_or_throw!(self.machine_st, self.set_stream_position());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInferenceLevel(_) => {
                    self.inference_level();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInferenceLevel(_) => {
                    self.inference_level();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCleanUpBlock(_) => {
                    self.clean_up_block();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteCleanUpBlock(_) => {
                    self.clean_up_block();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallFail(_) | &Instruction::ExecuteFail(_) => {
                    self.machine_st.backtrack();
                }
                &Instruction::CallGetBall(_) => {
                    self.get_ball();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetBall(_) => {
                    self.get_ball();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCurrentBlock(_) => {
                    self.get_current_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCurrentBlock(_) => {
                    self.get_current_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetCutPoint(_) => {
                    self.get_cut_point();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetCutPoint(_) => {
                    self.get_cut_point();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetDoubleQuotes(_) => {
                    self.get_double_quotes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetDoubleQuotes(_) => {
                    self.get_double_quotes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInstallNewBlock(_) => {
                    self.machine_st.install_new_block(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteInstallNewBlock(_) => {
                    self.machine_st.install_new_block(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMaybe(_) => {
                    self.maybe();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMaybe(_) => {
                    self.maybe();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCpuNow(_) => {
                    self.cpu_now();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCpuNow(_) => {
                    self.cpu_now();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeterministicLengthRundown(_) => {
                    try_or_throw!(self.machine_st, self.det_length_rundown());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeterministicLengthRundown(_) => {
                    try_or_throw!(self.machine_st, self.det_length_rundown());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallHttpOpen(_) => {
                    try_or_throw!(self.machine_st, self.http_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHttpOpen(_) => {
                    try_or_throw!(self.machine_st, self.http_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
		&Instruction::CallHttpListen(_) => {
		    try_or_throw!(self.machine_st, self.http_listen());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpListen(_) => {
		    try_or_throw!(self.machine_st, self.http_listen());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallHttpAccept(_) => {
		    try_or_throw!(self.machine_st, self.http_accept());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpAccept(_) => {
		    try_or_throw!(self.machine_st, self.http_accept());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallHttpAnswer(_) => {
		    try_or_throw!(self.machine_st, self.http_answer());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteHttpAnswer(_) => {
		    try_or_throw!(self.machine_st, self.http_answer());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallLoadForeignLib(_) => {
		    try_or_throw!(self.machine_st, self.load_foreign_lib());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteLoadForeignLib(_) => {
		    try_or_throw!(self.machine_st, self.load_foreign_lib());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallForeignCall(_) => {
		    try_or_throw!(self.machine_st, self.foreign_call());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteForeignCall(_) => {
		    try_or_throw!(self.machine_st, self.foreign_call());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
		&Instruction::CallDefineForeignStruct(_) => {
		    try_or_throw!(self.machine_st, self.define_foreign_struct());
		    step_or_fail!(self, self.machine_st.p += 1);
		}
		&Instruction::ExecuteDefineForeignStruct(_) => {
		    try_or_throw!(self.machine_st, self.define_foreign_struct());
		    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
		}
                &Instruction::CallCurrentTime(_) => {
                    self.current_time();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurrentTime(_) => {
                    self.current_time();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallQuotedToken(_) => {
                    self.quoted_token();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteQuotedToken(_) => {
                    self.quoted_token();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReadTermFromChars(_) => {
                    try_or_throw!(self.machine_st, self.read_term_from_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteReadTermFromChars(_) => {
                    try_or_throw!(self.machine_st, self.read_term_from_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallResetBlock(_) => {
                    self.reset_block();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteResetBlock(_) => {
                    self.reset_block();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallReturnFromVerifyAttr(_) |
                &Instruction::ExecuteReturnFromVerifyAttr(_) => {
                    self.return_from_verify_attr();
                }
                &Instruction::CallSetBall(_) => {
                    self.set_ball();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetBall(_) => {
                    self.set_ball();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushBallStack(_) => {
                    self.push_ball_stack();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePushBallStack(_) => {
                    self.push_ball_stack();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPopBallStack(_) => {
                    self.pop_ball_stack();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopBallStack(_) => {
                    self.pop_ball_stack();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopFromBallStack(_) => {
                    self.pop_from_ball_stack();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopFromBallStack(_) => {
                    self.pop_from_ball_stack();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetCutPointByDefault(r, _) => {
                    self.set_cut_point_by_default(r);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetCutPointByDefault(r, _) => {
                    self.set_cut_point_by_default(r);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetDoubleQuotes(_) => {
                    self.set_double_quotes();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetDoubleQuotes(_) => {
                    self.set_double_quotes();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetSeed(_) => {
                    self.set_seed();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSetSeed(_) => {
                    self.set_seed();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSkipMaxList(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.skip_max_list());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSkipMaxList(_) => {
                    try_or_throw!(self.machine_st, self.machine_st.skip_max_list());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSleep(_) => {
                    self.sleep();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSleep(_) => {
                    self.sleep();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSocketClientOpen(_) => {
                    try_or_throw!(self.machine_st, self.socket_client_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketClientOpen(_) => {
                    try_or_throw!(self.machine_st, self.socket_client_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerOpen(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_open());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketServerOpen(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_open());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerAccept(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_accept());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteSocketServerAccept(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_accept());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSocketServerClose(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_close());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSocketServerClose(_) => {
                    try_or_throw!(self.machine_st, self.socket_server_close());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallTLSAcceptClient(_) => {
                    try_or_throw!(self.machine_st, self.tls_accept_client());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTLSAcceptClient(_) => {
                    try_or_throw!(self.machine_st, self.tls_accept_client());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTLSClientConnect(_) => {
                    try_or_throw!(self.machine_st, self.tls_client_connect());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTLSClientConnect(_) => {
                    try_or_throw!(self.machine_st, self.tls_client_connect());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSucceed(_) => {
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSucceed(_) => {
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallTermAttributedVariables(_) => {
                    self.term_attributed_variables();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermAttributedVariables(_) => {
                    self.term_attributed_variables();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTermVariables(_) => {
                    self.term_variables();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermVariables(_) => {
                    self.term_variables();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTermVariablesUnderMaxDepth(_) => {
                    self.term_variables_under_max_depth();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteTermVariablesUnderMaxDepth(_) => {
                    self.term_variables_under_max_depth();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallTruncateLiftedHeapTo(_) => {
                    self.truncate_lifted_heap_to();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteTruncateLiftedHeapTo(_) => {
                    self.truncate_lifted_heap_to();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnifyWithOccursCheck(_) => {
                    self.unify_with_occurs_check();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteUnifyWithOccursCheck(_) => {
                    self.unify_with_occurs_check();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallUnwindEnvironments(_) => {
                    if !self.unwind_environments() {
                        self.machine_st.p += 1;
                    }
                }
                &Instruction::ExecuteUnwindEnvironments(_) => {
                    if !self.unwind_environments() {
                        self.machine_st.p = self.machine_st.cp;
                    }
                }
                &Instruction::CallUnwindStack(_) | &Instruction::ExecuteUnwindStack(_) => {
                    self.machine_st.unwind_stack();
                    self.machine_st.backtrack();
                }
                &Instruction::CallWAMInstructions(_) => {
                    try_or_throw!(self.machine_st, self.wam_instructions());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWAMInstructions(_) => {
                    try_or_throw!(self.machine_st, self.wam_instructions());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallWriteTerm(_) => {
                    try_or_throw!(self.machine_st, self.write_term());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWriteTerm(_) => {
                    try_or_throw!(self.machine_st, self.write_term());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallWriteTermToChars(_) => {
                    try_or_throw!(self.machine_st, self.write_term_to_chars());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteWriteTermToChars(_) => {
                    try_or_throw!(self.machine_st, self.write_term_to_chars());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallScryerPrologVersion(_) => {
                    self.scryer_prolog_version();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteScryerPrologVersion(_) => {
                    self.scryer_prolog_version();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoRandomByte(_) => {
                    self.crypto_random_byte();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoRandomByte(_) => {
                    self.crypto_random_byte();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataHash(_) => {
                    self.crypto_data_hash();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataHash(_) => {
                    self.crypto_data_hash();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataHKDF(_) => {
                    self.crypto_data_hkdf();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataHKDF(_) => {
                    self.crypto_data_hkdf();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoPasswordHash(_) => {
                    self.crypto_password_hash();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoPasswordHash(_) => {
                    self.crypto_password_hash();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataEncrypt(_) => {
                    self.crypto_data_encrypt();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataEncrypt(_) => {
                    self.crypto_data_encrypt();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoDataDecrypt(_) => {
                    self.crypto_data_decrypt();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoDataDecrypt(_) => {
                    self.crypto_data_decrypt();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCryptoCurveScalarMult(_) => {
                    self.crypto_curve_scalar_mult();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCryptoCurveScalarMult(_) => {
                    self.crypto_curve_scalar_mult();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519Sign(_) => {
                    self.ed25519_sign();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519Sign(_) => {
                    self.ed25519_sign();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519Verify(_) => {
                    self.ed25519_verify();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519Verify(_) => {
                    self.ed25519_verify();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519NewKeyPair(_) => {
                    self.ed25519_new_key_pair();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519NewKeyPair(_) => {
                    self.ed25519_new_key_pair();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallEd25519KeyPairPublicKey(_) => {
                    self.ed25519_key_pair_public_key();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteEd25519KeyPairPublicKey(_) => {
                    self.ed25519_key_pair_public_key();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCurve25519ScalarMult(_) => {
                    self.curve25519_scalar_mult();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCurve25519ScalarMult(_) => {
                    self.curve25519_scalar_mult();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallFirstNonOctet(_) => {
                    self.first_non_octet();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteFirstNonOctet(_) => {
                    self.first_non_octet();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadHTML(_) => {
                    self.load_html();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadHTML(_) => {
                    self.load_html();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadXML(_) => {
                    self.load_xml();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadXML(_) => {
                    self.load_xml();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallGetEnv(_) => {
                    self.get_env();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetEnv(_) => {
                    self.get_env();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetEnv(_) => {
                    self.set_env();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetEnv(_) => {
                    self.set_env();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnsetEnv(_) => {
                    self.unset_env();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteUnsetEnv(_) => {
                    self.unset_env();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallShell(_) => {
                    self.shell();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteShell(_) => {
                    self.shell();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPID(_) => {
                    self.pid();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePID(_) => {
                    self.pid();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCharsBase64(_) => {
                    try_or_throw!(self.machine_st, self.chars_base64());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCharsBase64(_) => {
                    try_or_throw!(self.machine_st, self.chars_base64());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDevourWhitespace(_) => {
                    try_or_throw!(self.machine_st, self.devour_whitespace());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDevourWhitespace(_) => {
                    try_or_throw!(self.machine_st, self.devour_whitespace());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsSTOEnabled(_) => {
                    self.is_sto_enabled();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsSTOEnabled(_) => {
                    self.is_sto_enabled();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallSetSTOAsUnify(_) => {
                    self.set_sto_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetSTOAsUnify(_) => {
                    self.set_sto_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetNSTOAsUnify(_) => {
                    self.set_nsto_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetNSTOAsUnify(_) => {
                    self.set_nsto_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallSetSTOWithErrorAsUnify(_) => {
                    self.set_sto_with_error_as_unify();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteSetSTOWithErrorAsUnify(_) => {
                    self.set_sto_with_error_as_unify();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallHomeDirectory(_) => {
                    self.home_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteHomeDirectory(_) => {
                    self.home_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDebugHook(_) => {
                    self.debug_hook();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDebugHook(_) => {
                    self.debug_hook();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopCount(_) => {
                    self.pop_count();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePopCount(_) => {
                    self.pop_count();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAddDiscontiguousPredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_discontiguous_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddDiscontiguousPredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_discontiguous_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddDynamicPredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_dynamic_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddDynamicPredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_dynamic_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddMultifilePredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_multifile_predicate());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddMultifilePredicate(_) => {
                    try_or_throw!(self.machine_st, self.add_multifile_predicate());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddGoalExpansionClause(_) => {
                    try_or_throw!(self.machine_st, self.add_goal_expansion_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddGoalExpansionClause(_) => {
                    try_or_throw!(self.machine_st, self.add_goal_expansion_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddTermExpansionClause(_) => {
                    try_or_throw!(self.machine_st, self.add_term_expansion_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddTermExpansionClause(_) => {
                    try_or_throw!(self.machine_st, self.add_term_expansion_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddInSituFilenameModule(_) => {
                    try_or_throw!(self.machine_st, self.add_in_situ_filename_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddInSituFilenameModule(_) => {
                    try_or_throw!(self.machine_st, self.add_in_situ_filename_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallClauseToEvacuable(_) => {
                    try_or_throw!(self.machine_st, self.clause_to_evacuable());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteClauseToEvacuable(_) => {
                    try_or_throw!(self.machine_st, self.clause_to_evacuable());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallScopedClauseToEvacuable(_) => {
                    try_or_throw!(self.machine_st, self.scoped_clause_to_evacuable());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteScopedClauseToEvacuable(_) => {
                    try_or_throw!(self.machine_st, self.scoped_clause_to_evacuable());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallConcludeLoad(_) => {
                    try_or_throw!(self.machine_st, self.conclude_load());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteConcludeLoad(_) => {
                    try_or_throw!(self.machine_st, self.conclude_load());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallDeclareModule(_) => {
                    try_or_throw!(self.machine_st, self.declare_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDeclareModule(_) => {
                    try_or_throw!(self.machine_st, self.declare_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallLoadCompiledLibrary(_) => {
                    try_or_throw!(self.machine_st, self.load_compiled_library());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadCompiledLibrary(_) => {
                    try_or_throw!(self.machine_st, self.load_compiled_library());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextSource(_) => {
                    self.load_context_source();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextSource(_) => {
                    self.load_context_source();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextFile(_) => {
                    self.load_context_file();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextFile(_) => {
                    self.load_context_file();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextDirectory(_) => {
                    self.load_context_directory();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextDirectory(_) => {
                    self.load_context_directory();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextModule(_) => {
                    self.load_context_module(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextModule(_) => {
                    self.load_context_module(self.machine_st.registers[1]);
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallLoadContextStream(_) => {
                    self.load_context_stream();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteLoadContextStream(_) => {
                    self.load_context_stream();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPopLoadContext(_) => {
                    self.pop_load_context();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopLoadContext(_) => {
                    self.pop_load_context();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPopLoadStatePayload(_) => {
                    self.pop_load_state_payload();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePopLoadStatePayload(_) => {
                    self.pop_load_state_payload();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushLoadContext(_) => {
                    try_or_throw!(self.machine_st, self.push_load_context());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecutePushLoadContext(_) => {
                    try_or_throw!(self.machine_st, self.push_load_context());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPushLoadStatePayload(_) => {
                    self.push_load_state_payload();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePushLoadStatePayload(_) => {
                    self.push_load_state_payload();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallUseModule(_) => {
                    try_or_throw!(self.machine_st, self.use_module());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteUseModule(_) => {
                    try_or_throw!(self.machine_st, self.use_module());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallBuiltInProperty(_) => {
                    self.builtin_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteBuiltInProperty(_) => {
                    self.builtin_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMetaPredicateProperty(_) => {
                    self.meta_predicate_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMetaPredicateProperty(_) => {
                    self.meta_predicate_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallMultifileProperty(_) => {
                    self.multifile_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteMultifileProperty(_) => {
                    self.multifile_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDiscontiguousProperty(_) => {
                    self.discontiguous_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDiscontiguousProperty(_) => {
                    self.discontiguous_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDynamicProperty(_) => {
                    self.dynamic_property();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDynamicProperty(_) => {
                    self.dynamic_property();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallAbolishClause(_) => {
                    try_or_throw!(self.machine_st, self.abolish_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAbolishClause(_) => {
                    try_or_throw!(self.machine_st, self.abolish_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAsserta(_) => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Prepend));
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAsserta(_) => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Prepend));
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAssertz(_) => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Append));
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAssertz(_) => {
                    try_or_throw!(self.machine_st, self.compile_assert(AppendOrPrepend::Append));
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRetract(_) => {
                    try_or_throw!(self.machine_st, self.retract_clause());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRetract(_) => {
                    try_or_throw!(self.machine_st, self.retract_clause());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallIsConsistentWithTermQueue(_) => {
                    try_or_throw!(self.machine_st, self.is_consistent_with_term_queue());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsConsistentWithTermQueue(_) => {
                    try_or_throw!(self.machine_st, self.is_consistent_with_term_queue());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::CallFlushTermQueue(_) => {
                    try_or_throw!(self.machine_st, self.flush_term_queue());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteFlushTermQueue(_) => {
                    try_or_throw!(self.machine_st, self.flush_term_queue());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallRemoveModuleExports(_) => {
                    try_or_throw!(self.machine_st, self.remove_module_exports());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteRemoveModuleExports(_) => {
                    try_or_throw!(self.machine_st, self.remove_module_exports());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallAddNonCountedBacktracking(_) => {
                    try_or_throw!(self.machine_st, self.add_non_counted_backtracking());
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteAddNonCountedBacktracking(_) => {
                    try_or_throw!(self.machine_st, self.add_non_counted_backtracking());
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallPredicateDefined(_) => {
                    self.machine_st.fail = !self.predicate_defined();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePredicateDefined(_) => {
                    self.machine_st.fail = !self.predicate_defined();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallStripModule(_) => {
                    let (module_loc, qualified_goal) = self.machine_st.strip_module(
                        self.machine_st.registers[1],
                        self.machine_st.registers[2],
                    );

                    let target_module_loc = self.machine_st.registers[2];

                    unify_fn!(
                        &mut self.machine_st,
                        module_loc,
                        target_module_loc
                    );

                    let target_qualified_goal = self.machine_st.registers[3];

                    unify_fn!(
                        &mut self.machine_st,
                        qualified_goal,
                        target_qualified_goal
                    );

                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteStripModule(_) => {
                    let (module_loc, qualified_goal) = self.machine_st.strip_module(
                        self.machine_st.registers[1],
                        self.machine_st.registers[2],
                    );

                    let target_module_loc = self.machine_st.registers[2];

                    unify_fn!(
                        &mut self.machine_st,
                        module_loc,
                        target_module_loc
                    );

                    let target_qualified_goal = self.machine_st.registers[3];

                    unify_fn!(
                        &mut self.machine_st,
                        qualified_goal,
                        target_qualified_goal
                    );

                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPrepareCallClause(arity, _) => {
                    try_or_throw!(self.machine_st, self.prepare_call_clause(arity));
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePrepareCallClause(arity, _) => {
                    try_or_throw!(self.machine_st, self.prepare_call_clause(arity));
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallCompileInlineOrExpandedGoal(_) => {
                    try_or_throw!(self.machine_st, self.compile_inline_or_expanded_goal());
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteCompileInlineOrExpandedGoal(_) => {
                    try_or_throw!(self.machine_st, self.compile_inline_or_expanded_goal());
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallIsExpandedOrInlined(_) => {
                    self.machine_st.fail = !self.is_expanded_or_inlined();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteIsExpandedOrInlined(_) => {
                    self.machine_st.fail = !self.is_expanded_or_inlined();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallInlineCallN(arity, _) => {
                    let call_at_index = |wam: &mut Machine, name, arity, ptr| {
                        wam.try_call(name, arity, ptr)
                    };

                    try_or_throw!(self.machine_st, self.call_inline(arity, call_at_index));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::ExecuteInlineCallN(arity, _) => {
                    let call_at_index = |wam: &mut Machine, name, arity, ptr| {
                        wam.try_execute(name, arity, ptr)
                    };

                    try_or_throw!(self.machine_st, self.call_inline(arity, call_at_index));

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    } else {
                        try_or_throw!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
                &Instruction::CallGetClauseP(_) => {
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
                &Instruction::ExecuteGetClauseP(_) => {
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
                &Instruction::CallInvokeClauseAtP(_) => {
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
                &Instruction::ExecuteInvokeClauseAtP(_) => {
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
                &Instruction::CallGetFromAttributedVarList(_) => {
                    self.get_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteGetFromAttributedVarList(_) => {
                    self.get_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallPutToAttributedVarList(_) => {
                    self.put_to_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecutePutToAttributedVarList(_) => {
                    self.put_to_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteFromAttributedVarList(_) => {
                    self.delete_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteDeleteFromAttributedVarList(_) => {
                    self.delete_from_attributed_variable_list();
                    step_or_fail!(self, self.machine_st.p = self.machine_st.cp);
                }
                &Instruction::CallDeleteAllAttributesFromVar(_) => {
                    self.delete_all_attributes_from_var();
                    self.machine_st.p += 1;
                }
                &Instruction::ExecuteDeleteAllAttributesFromVar(_) => {
                    self.delete_all_attributes_from_var();
                    self.machine_st.p = self.machine_st.cp;
                }
                &Instruction::CallUnattributedVar(_) => {
                    self.machine_st.unattributed_var();
                    step_or_fail!(self, self.machine_st.p += 1);
                }
                &Instruction::ExecuteUnattributedVar(_) => {
                    self.machine_st.unattributed_var();
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
