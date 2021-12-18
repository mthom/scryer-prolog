use crate::arena::*;
use crate::atom_table::*;
use crate::instructions::*;
use crate::machine::*;
use crate::machine::arithmetic_ops::*;
use crate::machine::code_repo::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_state::*;
use crate::types::*;

use crate::try_numeric_result;

impl Machine {
    #[inline(always)]
    pub(super) fn dispatch_instr(&mut self, instr: OwnedOrIndexed) {
        match instr.as_ref(&self.code_repo.code) {
            &Line::Arithmetic(ref arith_instr) => {
                let stub_gen = || functor_stub(atom!("is"), 2);

                match arith_instr {
                    &ArithmeticInstruction::Add(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            try_numeric_result!(add(n1, n2, &mut self.machine_st.arena), stub_gen)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Sub(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            try_numeric_result!(sub(n1, n2, &mut self.machine_st.arena), stub_gen)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Mul(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            try_numeric_result!(mul(n1, n2, &mut self.machine_st.arena), stub_gen)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Max(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            max(n1, n2)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Min(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            min(n1, n2)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::IntPow(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            int_pow(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Gcd(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            gcd(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Pow(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            pow(n1, n2, atom!("**"))
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                        let stub_gen = || functor_stub(atom!("(rdiv)"), 2);

                        let r1 = try_or_fail!(self.machine_st, self.machine_st.get_rational(a1, stub_gen));
                        let r2 = try_or_fail!(self.machine_st, self.machine_st.get_rational(a2, stub_gen));

                        self.machine_st.interms[t - 1] = Number::Rational(arena_alloc!(
                            try_or_fail_gen!(&mut self.machine_st, rdiv(r1, r2)),
                            self.machine_st.arena
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::IntFloorDiv(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            int_floor_div(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::IDiv(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            idiv(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Abs(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = abs(n1, &mut self.machine_st.arena);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Sign(ref a1, t) => {
                        let n = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = sign(n);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Neg(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = neg(n1, &mut self.machine_st.arena);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::BitwiseComplement(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            bitwise_complement(n1, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Div(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            div(n1, n2)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Shr(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            shr(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Shl(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            shl(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Xor(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            xor(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::And(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            and(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Or(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            or(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Mod(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            modulus(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Rem(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = try_or_fail_gen!(
                            &mut self.machine_st,
                            remainder(n1, n2, &mut self.machine_st.arena)
                        );
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Cos(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, cos(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Sin(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, sin(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Tan(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, tan(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Sqrt(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, sqrt(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Log(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, log(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Exp(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, exp(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::ACos(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, acos(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::ASin(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, asin(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::ATan(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, atan(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::ATan2(ref a1, ref a2, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));
                        let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(a2));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, atan2(n1, n2))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Float(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = Number::Float(OrderedFloat(
                            try_or_fail_gen!(&mut self.machine_st, float(n1))
                        ));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Truncate(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = truncate(n1, &mut self.machine_st.arena);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Round(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] =
                            try_or_fail_gen!(&mut self.machine_st, round(n1, &mut self.machine_st.arena));
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Ceiling(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = ceiling(n1, &mut self.machine_st.arena);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Floor(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = floor(n1, &mut self.machine_st.arena);
                        self.machine_st.p += 1;
                    }
                    &ArithmeticInstruction::Plus(ref a1, t) => {
                        let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(a1));

                        self.machine_st.interms[t - 1] = n1;
                        self.machine_st.p += 1;
                    }
                }
            }
            &Line::Choice(ref choice_instr) => {
                match choice_instr {
                    &ChoiceInstruction::DynamicElse(..) => {
                        if let FirstOrNext::First = self.machine_st.dynamic_mode {
                            self.machine_st.cc = self.machine_st.global_clock;
                        }

                        let p = self.machine_st.p.local().abs_loc();

                        match self.find_living_dynamic_else(p) {
                            Some((p, next_i)) => {
                                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p));

                                match self.machine_st.dynamic_mode {
                                    FirstOrNext::First if next_i == 0 => {
                                        self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p + 1));
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
                                            .univ_prelude
                                            .num_cells;

                                        self.machine_st.cc = cell_as_fixnum!(
                                            self.machine_st.stack[stack_loc!(OrFrame, self.machine_st.b, n-1)]
                                        ).get_num() as usize;

                                        if next_i > 0 {
                                            match self.find_living_dynamic_else(p + next_i) {
                                                Some(_) => {
                                                    self.retry_me_else(next_i);

                                                    try_or_fail!(
                                                        self.machine_st,
                                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                    );
                                                }
                                                None => {
                                                    self.trust_me();

                                                    try_or_fail!(
                                                        self.machine_st,
                                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                    );
                                                }
                                            }
                                        } else {
                                            self.trust_me();

                                            try_or_fail!(
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
                    }
                    &ChoiceInstruction::DynamicInternalElse(..) => {
                        let p = self.machine_st.p.local().abs_loc();

                        match self.find_living_dynamic_else(p) {
                            Some((p, next_i)) => {
                                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p));

                                match self.machine_st.dynamic_mode {
                                    FirstOrNext::First if next_i == 0 => {
                                        self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p + 1));
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
                                            .univ_prelude
                                            .num_cells;

                                        self.machine_st.cc = cell_as_fixnum!(
                                            self.machine_st.stack[stack_loc!(OrFrame, self.machine_st.b, n-1)]
                                        ).get_num() as usize;

                                        if next_i > 0 {
                                            match self.find_living_dynamic_else(p + next_i) {
                                                Some(_) => {
                                                    self.retry_me_else(next_i);

                                                    try_or_fail!(
                                                        self.machine_st,
                                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                    );
                                                }
                                                None => {
                                                    self.trust_me();

                                                    try_or_fail!(
                                                        self.machine_st,
                                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                                    );
                                                }
                                            }
                                        } else {
                                            self.trust_me();

                                            try_or_fail!(
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
                    }
                    &ChoiceInstruction::TryMeElse(offset) => {
                        self.machine_st.try_me_else(offset);
                    }
                    &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                        self.retry_me_else(offset);
                    }
                    &ChoiceInstruction::DefaultTrustMe(_) => {
                        self.trust_me();
                    }
                    &ChoiceInstruction::RetryMeElse(offset) => {
                        self.retry_me_else(offset);

                        try_or_fail!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                    &ChoiceInstruction::TrustMe(_) => {
                        self.trust_me();

                        try_or_fail!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
            }
            &Line::Cut(ref cut_instr) => {
                match cut_instr {
                    &CutInstruction::NeckCut => {
                        let b = self.machine_st.b;
                        let b0 = self.machine_st.b0;

                        if b > b0 {
                            self.machine_st.b = b0;

                            if b > self.machine_st.e {
                                self.machine_st.stack.truncate(b);
                            }
                        }

                        self.machine_st.p += 1;
                    }
                    &CutInstruction::GetLevel(r) => {
                        let b0 = self.machine_st.b0;

                        self.machine_st[r] = fixnum_as_cell!(Fixnum::build_with(b0 as i64));
                        self.machine_st.p += 1;
                    }
                    &CutInstruction::GetLevelAndUnify(r) => {
                        let b0 = self.machine_st[perm_v!(1)];
                        let a = self.machine_st[r];

                        unify_fn!(&mut self.machine_st, a, b0);
                        self.machine_st.p += 1;
                    }
                    &CutInstruction::Cut(r) => {
                        let value = self.machine_st[r];
                        self.machine_st.cut_body(value);

                        if !self.machine_st.fail && !(self.machine_st.run_cleaners_fn)(self) {
                            self.machine_st.p += 1;
                        }
                    }
                }
            }
            &Line::Control(ref ctrl_instr) => {
                match ctrl_instr {
                    &ControlInstruction::Allocate(num_cells) =>
                        self.machine_st.allocate(num_cells),
                    &ControlInstruction::CallClause(ref ct, arity, _, lco, use_default_cp) => {
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
                                    return;
                                }
                            }
                            Err(_) => unreachable!(),
                        }

                        self.machine_st.last_call = lco;

                        match ct {
                            &ClauseType::BuiltIn(ref ct) => {
                                let ct = ct.clone();

                                try_or_fail!(
                                    self.machine_st,
                                    self.call_builtin(&ct)
                                );

                                if !use_default_cp {
                                    try_or_fail!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                            &ClauseType::CallN => {
                                try_or_fail!(
                                    self.machine_st,
                                    self.call_n(atom!("user"), arity)
                                );

                                if !use_default_cp {
                                    try_or_fail!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                            &ClauseType::Inlined(ref ct) => {
                                let ct = ct.clone();
                                self.execute_inlined(&ct);

                                if lco {
                                    self.machine_st.p = CodePtr::Local(self.machine_st.cp);
                                }
                            }
                            &ClauseType::Named(name, _, ref idx) => {
                                let idx = idx.clone();

                                try_or_fail!(
                                    self.machine_st,
                                    self.context_call(name, arity, idx) // TODO: change to idx.get() ???
                                );

                                if !use_default_cp {
                                    try_or_fail!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                            &ClauseType::System(ref ct) => {
                                let ct = ct.clone();

                                try_or_fail!(
                                    self.machine_st,
                                    self.system_call(&ct)
                                );
                            }
                        };

                        self.machine_st.last_call = false;
                    }
                    &ControlInstruction::Deallocate =>
                        self.machine_st.deallocate(),
                    &ControlInstruction::JmpBy(arity, offset, _, lco) => {
                        if !lco {
                            self.machine_st.cp.assign_if_local(self.machine_st.p.clone() + 1);
                        }

                        self.machine_st.num_of_args = arity;
                        self.machine_st.b0 = self.machine_st.b;
                        self.machine_st.p += offset;
                    }
                    &ControlInstruction::RevJmpBy(offset) => {
                        self.machine_st.p -= offset;
                    }
                    &ControlInstruction::Proceed => {
                        self.machine_st.p = CodePtr::Local(self.machine_st.cp);
                    }
                }
            }
            &Line::Fact(ref fact_instr) => {
                match fact_instr {
                    &FactInstruction::GetConstant(_, c, reg) => {
                        let value = self.machine_st.deref(self.machine_st[reg]);
                        self.machine_st.write_literal_to_var(value, c);
                    }
                    &FactInstruction::GetList(_, reg) => {
                        let deref_v = self.machine_st.deref(self.machine_st[reg]);
                        let store_v = self.machine_st.store(deref_v);

                        read_heap_cell!(store_v,
                            (HeapCellValueTag::PStrLoc, h) => {
                                let (h, n) = pstr_loc_and_offset(&self.machine_st.heap, h);

                                self.machine_st.s = HeapPtr::PStrChar(h, n.get_num() as usize);
                                self.machine_st.mode = MachineMode::Read;
                            }
                            (HeapCellValueTag::CStr) => {
                                let h = self.machine_st.heap.len();
                                self.machine_st.heap.push(store_v);

                                self.machine_st.s = HeapPtr::PStrChar(h, 0);
                                self.machine_st.mode = MachineMode::Read;
                            }
                            (HeapCellValueTag::Lis, l) => {
                                self.machine_st.s = HeapPtr::HeapCell(l);
                                self.machine_st.mode = MachineMode::Read;
                            }
                            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                                let h = self.machine_st.heap.len();

                                self.machine_st.heap.push(list_loc_as_cell!(h+1));
                                self.machine_st.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));

                                self.machine_st.mode = MachineMode::Write;
                            }
                            _ => {
                                self.machine_st.fail = true;
                            }
                        );
                    }
                    &FactInstruction::GetPartialString(_, string, reg, has_tail) => {
                        let deref_v = self.machine_st.deref(self.machine_st[reg]);
                        let store_v = self.machine_st.store(deref_v);

                        read_heap_cell!(store_v,
                            (HeapCellValueTag::Str | HeapCellValueTag::Lis |
                             HeapCellValueTag::PStrLoc | HeapCellValueTag::AttrVar |
                             HeapCellValueTag::StackVar | HeapCellValueTag::Var |
                             HeapCellValueTag::CStr) => {
                                self.machine_st.match_partial_string(store_v, string, has_tail);
                            }
                            _ => {
                                self.machine_st.fail = true;
                            }
                        );
                    }
                    &FactInstruction::GetStructure(ref ct, arity, reg) => {
                        let deref_v = self.machine_st.deref(self.machine_st[reg]);
                        let store_v = self.machine_st.store(deref_v);

                        read_heap_cell!(store_v,
                            (HeapCellValueTag::Str, a) => {
                                let result = self.machine_st.heap[a];

                                read_heap_cell!(result,
                                    (HeapCellValueTag::Atom, (name, narity)) => {
                                        if narity == arity && ct.name() == name {
                                            self.machine_st.s = HeapPtr::HeapCell(a + 1);
                                            self.machine_st.mode = MachineMode::Read;
                                        } else {
                                            self.machine_st.fail = true;
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
                                self.machine_st.heap.push(atom_as_cell!(ct.name(), arity));

                                self.machine_st.bind(store_v.as_var().unwrap(), heap_loc_as_cell!(h));

                                self.machine_st.mode = MachineMode::Write;
                            }
                            _ => {
                                self.machine_st.fail = true;
                            }
                        );
                    }
                    &FactInstruction::GetVariable(norm, arg) => {
                        self.machine_st[norm] = self.machine_st.registers[arg];
                    }
                    &FactInstruction::GetValue(norm, arg) => {
                        let norm_addr = self.machine_st[norm];
                        let reg_addr = self.machine_st.registers[arg];

                        unify_fn!(&mut self.machine_st, norm_addr, reg_addr);
                    }
                    &FactInstruction::UnifyConstant(v) => {
                        match self.machine_st.mode {
                            MachineMode::Read => {
                                let addr = self.machine_st.read_s();

                                self.machine_st.write_literal_to_var(addr, v);
                                self.machine_st.increment_s_ptr(1);
                            }
                            MachineMode::Write => {
                                self.machine_st.heap.push(v);
                            }
                        };
                    }
                    &FactInstruction::UnifyVariable(reg) => {
                        match self.machine_st.mode {
                            MachineMode::Read => {
                                self.machine_st[reg] = self.machine_st.read_s();
                                self.machine_st.increment_s_ptr(1);
                            }
                            MachineMode::Write => {
                                let h = self.machine_st.heap.len();

                                self.machine_st.heap.push(heap_loc_as_cell!(h));
                                self.machine_st[reg] = heap_loc_as_cell!(h);
                            }
                        };
                    }
                    &FactInstruction::UnifyLocalValue(reg) => {
                        match self.machine_st.mode {
                            MachineMode::Read => {
                                let reg_addr = self.machine_st[reg];
                                let value = self.machine_st.read_s();

                                unify_fn!(&mut self.machine_st, reg_addr, value);
                                self.machine_st.increment_s_ptr(1);
                            }
                            MachineMode::Write => {
                                let value = self.machine_st.store(self.machine_st.deref(self.machine_st[reg]));
                                let h = self.machine_st.heap.len();

                                read_heap_cell!(value,
                                    (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, hc) => {
                                        let value = self.machine_st.heap[hc];

                                        self.machine_st.heap.push(value);
                                        self.machine_st.increment_s_ptr(1);
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
                        };
                    }
                    &FactInstruction::UnifyValue(reg) => {
                        match self.machine_st.mode {
                            MachineMode::Read => {
                                let reg_addr = self.machine_st[reg];
                                let value = self.machine_st.read_s();

                                unify_fn!(&mut self.machine_st, reg_addr, value);
                                self.machine_st.increment_s_ptr(1);
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
                        };
                    }
                    &FactInstruction::UnifyVoid(n) => {
                        match self.machine_st.mode {
                            MachineMode::Read => {
                                self.machine_st.increment_s_ptr(n);
                            }
                            MachineMode::Write => {
                                let h = self.machine_st.heap.len();

                                for i in h..h + n {
                                    self.machine_st.heap.push(heap_loc_as_cell!(i));
                                }
                            }
                        };
                    }
                }
                self.machine_st.p += 1;
            }
            &Line::IndexingCode(ref indexing_lines) => {
                #[inline(always)]
                fn dynamic_external_of_clause_is_valid(machine: &mut Machine, p: usize) -> bool {
                    match &machine.code_repo.code[p] {
                        Line::Choice(ChoiceInstruction::DynamicInternalElse(..)) => {
                            machine.machine_st.dynamic_mode = FirstOrNext::First;
                            return true;
                        }
                        _ => {}
                    }

                    match &machine.code_repo.code[p - 1] {
                        &Line::Choice(ChoiceInstruction::DynamicInternalElse(birth, death, _)) => {
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
                                    self.machine_st.fail = true;
                                    break;
                                }
                                IndexingCodePtr::DynamicExternal(o) => {
                                    // either points directly to a
                                    // DynamicInternalElse, or just ahead of
                                    // one. Or neither!
                                    let p = self.machine_st.p.local().abs_loc();

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
                                    self.machine_st.fail = true;
                                    break;
                                }
                                IndexingCodePtr::DynamicExternal(o) => {
                                    // either points directly to a
                                    // DynamicInternalElse, or just ahead of
                                    // one. Or neither!
                                    let p = self.machine_st.p.local().abs_loc();

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
                                    let p = self.machine_st.p.local().abs_loc();

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
                            if let LocalCodePtr::DirEntry(p) = self.machine_st.p.local() {
                                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p));
                                self.machine_st.oip = index as u32;
                                self.machine_st.iip = 0;
                            } else {
                                unreachable!()
                            }

                            break;
                        }
                        &IndexingLine::DynamicIndexedChoice(_) => {
                            self.machine_st.dynamic_mode = FirstOrNext::First;

                            if let LocalCodePtr::DirEntry(p) = self.machine_st.p.local() {
                                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p));
                                self.machine_st.oip = index as u32;
                                self.machine_st.iip = 0;
                            } else {
                                unreachable!()
                            }

                            break;
                        }
                    }
                }
            }
            &Line::IndexedChoice(ref choice_instr) => {
                match choice_instr {
                    &IndexedChoiceInstruction::Try(offset) => {
                        self.machine_st.indexed_try(offset);
                    }
                    &IndexedChoiceInstruction::Retry(l) => {
                        self.retry(l);

                        try_or_fail!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                    &IndexedChoiceInstruction::Trust(l) => {
                        self.trust(l);

                        try_or_fail!(
                            self.machine_st,
                            (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                        );
                    }
                }
            }
            &Line::DynamicIndexedChoice(_) => self.execute_dynamic_indexed_choice_instr(),
            &Line::Query(ref query_instr) => {
                match query_instr {
                    &QueryInstruction::GetVariable(norm, arg) => {
                        self.machine_st[norm] = self.machine_st.registers[arg];
                    }
                    &QueryInstruction::PutConstant(_, c, reg) => {
                        self.machine_st[reg] = c;
                    }
                    &QueryInstruction::PutList(_, reg) => {
                        self.machine_st[reg] = list_loc_as_cell!(self.machine_st.heap.len());
                    }
                    &QueryInstruction::PutPartialString(_, string, reg, has_tail) => {
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
                    }
                    &QueryInstruction::PutStructure(ref ct, arity, reg) => {
                        let h = self.machine_st.heap.len();

                        self.machine_st.heap.push(atom_as_cell!(ct.name(), arity));
                        self.machine_st[reg] = str_loc_as_cell!(h);
                    }
                    &QueryInstruction::PutUnsafeValue(n, arg) => {
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
                    }
                    &QueryInstruction::PutValue(norm, arg) => {
                        self.machine_st.registers[arg] = self.machine_st[norm];
                    }
                    &QueryInstruction::PutVariable(norm, arg) => {
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
                    }
                    &QueryInstruction::SetConstant(c) => {
                        self.machine_st.heap.push(c);
                    }
                    &QueryInstruction::SetLocalValue(reg) => {
                        let addr = self.machine_st.deref(self.machine_st[reg]);
                        let stored_v = self.machine_st.store(addr);

                        if stored_v.is_stack_var() {
                            let h = self.machine_st.heap.len();
                            self.machine_st.heap.push(heap_loc_as_cell!(h));
                            (self.machine_st.bind_fn)(&mut self.machine_st, Ref::heap_cell(h), stored_v);
                        } else {
                            self.machine_st.heap.push(stored_v);
                        }
                    }
                    &QueryInstruction::SetVariable(reg) => {
                        let h = self.machine_st.heap.len();
                        self.machine_st.heap.push(heap_loc_as_cell!(h));
                        self.machine_st[reg] = heap_loc_as_cell!(h);
                    }
                    &QueryInstruction::SetValue(reg) => {
                        let heap_val = self.machine_st.store(self.machine_st[reg]);
                        self.machine_st.heap.push(heap_val);
                    }
                    &QueryInstruction::SetVoid(n) => {
                        let h = self.machine_st.heap.len();

                        for i in h..h + n {
                            self.machine_st.heap.push(heap_loc_as_cell!(i));
                        }
                    }
                }

                self.machine_st.p += 1;
            }
        }
    }
}
