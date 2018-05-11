use prolog::ast::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_state::*;
use prolog::num::{ToPrimitive, Zero};
use prolog::num::bigint::BigInt;
use prolog::tabled_rc::*;

use std::rc::Rc;

struct BrentAlgState {
    hare: usize,
    tortoise: usize,
    power: usize,
    steps: usize
}

impl BrentAlgState {
    fn new(hare: usize) -> Self {
        BrentAlgState { hare, tortoise: hare, power: 2, steps: 1 }
    }
}

impl MachineState {
    // a step in Brent's algorithm.
    fn brents_alg_step(&self, brent_st: &mut BrentAlgState) -> Option<CycleSearchResult>
    {
        match self.heap[brent_st.hare].clone() {
            HeapCellValue::Addr(Addr::Lis(l)) => {
                brent_st.hare = l + 1;
                brent_st.steps += 1;

                if brent_st.tortoise == brent_st.hare {
                    return Some(CycleSearchResult::NotList);
                } else if brent_st.steps == brent_st.power {
                    brent_st.tortoise = brent_st.hare;
                    brent_st.power <<= 1;
                }

                None
            },
            HeapCellValue::NamedStr(..) =>
                Some(CycleSearchResult::NotList),
            HeapCellValue::Addr(addr) =>
                match self.store(self.deref(addr)) {
                    Addr::Con(Constant::EmptyList) =>
                        Some(CycleSearchResult::ProperList(brent_st.steps)),
                    Addr::HeapCell(_) | Addr::StackCell(..) =>
                        Some(CycleSearchResult::PartialList(brent_st.steps, brent_st.hare)),
                    _ =>
                        Some(CycleSearchResult::NotList)
                }
        }
    }

    pub(super) fn detect_cycles_with_max(&self, max_steps: usize, addr: Addr) -> CycleSearchResult
    {
        let addr = self.store(self.deref(addr));
        let hare = match addr {
            Addr::Lis(offset) if max_steps > 0 => offset + 1,
            Addr::Lis(offset) => return CycleSearchResult::UntouchedList(offset),
            Addr::Con(Constant::EmptyList) => return CycleSearchResult::EmptyList,
            _ => return CycleSearchResult::NotList
        };

        let mut brent_st = BrentAlgState::new(hare);

        loop {
            if brent_st.steps == max_steps {
                return CycleSearchResult::PartialList(brent_st.steps, brent_st.hare);
            }

            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    pub(super) fn detect_cycles(&self, addr: Addr) -> CycleSearchResult
    {
        let addr = self.store(self.deref(addr));
        let hare = match addr {
            Addr::Lis(offset) => offset + 1,
            Addr::Con(Constant::EmptyList) => return CycleSearchResult::EmptyList,
            _ => return CycleSearchResult::NotList
        };

        let mut brent_st = BrentAlgState::new(hare);

        loop {
            if let Some(result) = self.brents_alg_step(&mut brent_st) {
                return result;
            }
        }
    }

    fn finalize_skip_max_list(&mut self, n: usize, addr: Addr) {
        let target_n = self[temp_v!(1)].clone();
        self.unify(Addr::Con(integer!(n)), target_n);

        if !self.fail {
            let xs = self[temp_v!(4)].clone();
            self.unify(addr, xs);
        }
    }

    pub(super) fn skip_max_list(&mut self) -> Result<(), MachineError> {
        let max_steps = self.arith_eval_by_metacall(temp_v!(2))?;

        match max_steps {
            Number::Integer(ref max_steps)
                if max_steps.to_isize().map(|i| i >= -1).unwrap_or(false) => {
                    let n = self.store(self.deref(self[temp_v!(1)].clone()));

                    match n {
                        Addr::Con(Constant::Number(Number::Integer(ref n))) if n.is_zero() => {
                            let xs0 = self[temp_v!(3)].clone();
                            let xs  = self[temp_v!(4)].clone();

                            self.unify(xs0, xs);
                        },
                        _ => {
                            let search_result = if let Some(max_steps) = max_steps.to_isize() {
                                if max_steps == -1 {
                                    self.detect_cycles(self[temp_v!(3)].clone())
                                } else {
                                    self.detect_cycles_with_max(max_steps as usize,
                                                                self[temp_v!(3)].clone())
                                }
                            } else {
                                self.detect_cycles(self[temp_v!(3)].clone())
                            };

                            match search_result {
                                CycleSearchResult::UntouchedList(l) =>
                                    self.finalize_skip_max_list(0, Addr::Lis(l)),
                                CycleSearchResult::EmptyList =>
                                    self.finalize_skip_max_list(0, Addr::Con(Constant::EmptyList)),
                                CycleSearchResult::PartialList(n, hc) =>
                                    self.finalize_skip_max_list(n, Addr::HeapCell(hc)),
                                CycleSearchResult::ProperList(n) =>
                                    self.finalize_skip_max_list(n, Addr::Con(Constant::EmptyList)),
                                CycleSearchResult::NotList => {
                                    let xs0 = self[temp_v!(3)].clone();
                                    self.finalize_skip_max_list(0, xs0);
                                }
                            }
                        }
                    }
                },
            _ => self.fail = true
        };

        Ok(())
    }
            
    pub(super) fn system_call(&mut self, ct: &SystemClauseType) -> CallResult
    {
        match ct {
            &SystemClauseType::GetArg =>
                self.try_get_arg(),
            &SystemClauseType::InferenceLevel(r1, r2) => {
                let a1 = self[r1].clone();
                let a2 = self.store(self.deref(self[r2].clone()));

                match a2 {
                    Addr::Con(Constant::Usize(bp)) =>
                        if self.b <= bp + 1 {
                            let a2 = Addr::Con(atom!("!", self.atom_tbl));
                            self.unify(a1, a2);
                        } else {
                            let a2 = Addr::Con(atom!("true", self.atom_tbl));
                            self.unify(a1, a2);
                        },
                    _ => self.fail = true
                };

                Ok(())
            },            
            &SystemClauseType::CleanUpBlock => {
                let nb = self.store(self.deref(self[temp_v!(1)].clone()));

                match nb {
                    Addr::Con(Constant::Usize(nb)) => {
                        let b = self.b - 1;

                        if nb > 0 && self.or_stack[b].b == nb {
                            self.b = self.or_stack[nb - 1].b;
                            self.or_stack.truncate(self.b);
                        }
                    },
                    _ => self.fail = true
                };

                Ok(())
            },
            &SystemClauseType::EraseBall => {
                self.ball.reset();
                Ok(())
            },
            &SystemClauseType::Fail => {
                self.fail = true;
                Ok(())
            },
            &SystemClauseType::GetBall => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));
                let h = self.heap.h;

                if self.ball.stub.len() > 0 {
                    self.copy_and_align_ball_to_heap();
                } else {
                    self.fail = true;
                    return Ok(());
                }

                let ball = self.heap[h].as_addr(h);

                match addr.as_var() {
                    Some(r) => self.bind(r, ball),
                    _ => self.fail = true
                };

                Ok(())
            },
            &SystemClauseType::GetCurrentBlock => {
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, c);
                Ok(())
            },
            &SystemClauseType::GetCutPoint(r) => {
                let c = Constant::Usize(self.b);
                self[r] = Addr::Con(c);
                Ok(())
            },
            &SystemClauseType::InstallNewBlock => {
                self.block = self.b;

                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, c);
                Ok(())
            },
            &SystemClauseType::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)].clone());
                self.reset_block(addr);
                Ok(())
            },
            &SystemClauseType::SetBall => {
                self.set_ball();
                Ok(())
            },            
            &SystemClauseType::SkipMaxList => {
                self.skip_max_list()?;
                Ok(())
            },
            &SystemClauseType::Succeed => {
                Ok(())
            },
            &SystemClauseType::UnwindStack => {
                self.unwind_stack();
                Ok(())
            }
        }
    }
}
