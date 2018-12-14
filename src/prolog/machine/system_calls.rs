use prolog_parser::ast::*;

use prolog::heap_iter::*;
use prolog::heap_print::*;
use prolog::instructions::*;
use prolog::machine::IndexStore;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_state::*;
use prolog::num::{ToPrimitive, Zero};
use prolog::num::bigint::{BigInt};

use std::collections::HashSet;
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

    pub(super) fn skip_max_list(&mut self) -> CallResult {
        let max_steps = self.store(self.deref(self[temp_v!(2)].clone()));

        match max_steps {
            Addr::Con(Constant::Number(Number::Integer(ref max_steps))) =>
                if max_steps.to_isize().map(|i| i >= -1).unwrap_or(false) {
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
                } else {
                    self.fail = true;
                },
            Addr::HeapCell(_) | Addr::StackCell(..) => {
                let stub = MachineError::functor_stub(clause_name!("$skip_max_list"), 4);
                return Err(self.error_form(MachineError::instantiation_error(), stub));
            },
            addr => {
                let stub = MachineError::functor_stub(clause_name!("$skip_max_list"), 4);
                return Err(self.error_form(MachineError::type_error(ValidType::Integer, addr),
                                           stub));
            }
        };

        Ok(())
    }

    #[inline]
    fn install_new_block(&mut self, r: RegType) -> usize {
        self.block = self.b;

        let c = Constant::Usize(self.block);
        let addr = self[r].clone();

        self.write_constant_to_var(addr, c);
        self.block
    }

    #[inline]
    fn set_p(&mut self) {
        if self.last_call {
            self.p = CodePtr::Local(self.cp.clone());
        } else {
            self.p += 1;
        }
    }

    pub(super) fn system_call(&mut self, ct: &SystemClauseType,
                              indices: &IndexStore,
                              call_policy: &mut Box<CallPolicy>,
                              cut_policy:  &mut Box<CutPolicy>)
                              -> CallResult
    {
        match ct {
            &SystemClauseType::CheckCutPoint => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));

                match addr {
                    Addr::Con(Constant::Usize(old_b)) if self.b <= old_b + 2 => {},
                    _ => self.fail = true
                };
            },
            &SystemClauseType::ExpandGoal => {
                self.p = CodePtr::Local(LocalCodePtr::UserGoalExpansion(0));
                return Ok(());
            },
            &SystemClauseType::ExpandTerm => {
                self.p = CodePtr::Local(LocalCodePtr::UserTermExpansion(0));
                return Ok(());
            },
            &SystemClauseType::GetDoubleQuotes => {
                let a1 = self[temp_v!(1)].clone();

                match self.flags.double_quotes {
                    DoubleQuotes::Chars =>
                        self.unify(a1, Addr::Con(atom!("chars"))),
                    DoubleQuotes::Atom =>
                        self.unify(a1, Addr::Con(atom!("atom")))
                }
            },
            &SystemClauseType::GetSCCCleaner => {
                let dest = self[temp_v!(1)].clone();

                match cut_policy.downcast_mut::<SCCCutPolicy>().ok() {
                    Some(sgc_policy) =>
                        if let Some((addr, b_cutoff, prev_b)) = sgc_policy.pop_cont_pt() {
                            if self.b <= b_cutoff + 1 {
                                self.block = prev_b;

                                if let Some(r) = dest.as_var() {
                                    self.bind(r, addr.clone());
                                    self.set_p();

                                    return Ok(());
                                }
                            } else {
                                sgc_policy.push_cont_pt(addr, b_cutoff, prev_b);
                            }
                        },
                    None => panic!("expected SCCCutPolicy trait object.")
                };

                self.fail = true;
            },
            &SystemClauseType::InstallSCCCleaner => {
                let addr = self[temp_v!(1)].clone();
                let b = self.b;
                let prev_block = self.block;

                if cut_policy.downcast_ref::<SCCCutPolicy>().is_err() {
                    let (r_c_w_h, r_c_wo_h) = indices.get_cleaner_sites();
                    *cut_policy = Box::new(SCCCutPolicy::new(r_c_w_h, r_c_wo_h));
                }

                match cut_policy.downcast_mut::<SCCCutPolicy>().ok()
                {
                    Some(cut_policy) => {
                        self.install_new_block(temp_v!(2));
                        cut_policy.push_cont_pt(addr, b, prev_block);
                    },
                    None => panic!("install_cleaner: should have installed \\
                                    SCCCutPolicy.")
                };
            },
            &SystemClauseType::InstallInferenceCounter => { // A1 = B, A2 = L
                let a1 = self.store(self.deref(self[temp_v!(1)].clone()));
                let a2 = self.store(self.deref(self[temp_v!(2)].clone()));

                if call_policy.downcast_ref::<CWILCallPolicy>().is_err() {
                    CWILCallPolicy::new_in_place(call_policy);
                }

                match (a1, a2.clone()) {
                    (Addr::Con(Constant::Usize(bp)),
                     Addr::Con(Constant::Number(Number::Integer(n)))) =>
                        match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                            Some(call_policy) => {
                                let count = call_policy.add_limit(n, bp);
                                let count = Addr::Con(Constant::Number(Number::Integer(count)));

                                let a3 = self[temp_v!(3)].clone();

                                self.unify(a3, count);
                            },
                            None => panic!("install_inference_counter: should have installed \\
                                            CWILCallPolicy.")
                        },
                    _ => {
                        let stub = MachineError::functor_stub(clause_name!("call_with_inference_limit"), 3);
                        let type_error = self.error_form(MachineError::type_error(ValidType::Integer, a2),
                                                         stub);
                        self.throw_exception(type_error)
                    }
                };
            },
            &SystemClauseType::RemoveCallPolicyCheck => {
                let restore_default =
                    match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                        Some(call_policy) => {
                            let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

                            if let Addr::Con(Constant::Usize(bp)) = a1 {
                                if call_policy.is_empty() && bp == self.b {
                                    Some(call_policy.into_inner())
                                } else {
                                    None
                                }
                            } else {
                                panic!("remove_call_policy_check: expected Usize in A1.");
                            }
                        },
                        None => panic!("remove_call_policy_check: requires \\
                                        CWILCallPolicy.")
                    };

                if let Some(new_policy) = restore_default {
                    *call_policy = new_policy;
                }
            },
            &SystemClauseType::RemoveInferenceCounter =>
                match call_policy.downcast_mut::<CWILCallPolicy>().ok() {
                    Some(call_policy) => {
                        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

                        if let Addr::Con(Constant::Usize(bp)) = a1 {
                            let count = call_policy.remove_limit(bp);
                            let count = Addr::Con(Constant::Number(Number::Integer(count)));

                            let a2 = self[temp_v!(2)].clone();

                            self.unify(a2, count);
                        } else {
                            panic!("remove_inference_counter: expected Usize in A1.");
                        }
                    },
                    None => panic!("remove_inference_counter: requires \\
                                    CWILCallPolicy.")
                },
            &SystemClauseType::RestoreCutPolicy => {
                let restore_default =
                    if let Ok(cut_policy) = cut_policy.downcast_ref::<SCCCutPolicy>() {
                        cut_policy.out_of_cont_pts()
                    } else {
                        false
                    };

                if restore_default {
                    *cut_policy = Box::new(DefaultCutPolicy {});
                }
            },
            &SystemClauseType::SetCutPoint(r) => if cut_policy.cut(self, r) {
                return Ok(());
            },
            &SystemClauseType::SetCutPointByDefault(r) =>
                deref_cut(self, r),
            &SystemClauseType::SetDoubleQuotes =>
                match self[temp_v!(1)].clone() {
                    Addr::Con(Constant::Atom(ref atom, _)) if atom.as_str() == "chars" =>
                        self.flags.double_quotes = DoubleQuotes::Chars,
                    Addr::Con(Constant::Atom(ref atom, _)) if atom.as_str() == "atom" =>
                        self.flags.double_quotes = DoubleQuotes::Atom,
                    _ => self.fail = true
                },
            &SystemClauseType::InferenceLevel => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = self.store(self.deref(self[temp_v!(2)].clone()));

                match a2 {
                    Addr::Con(Constant::Usize(bp)) =>
                        if self.b <= bp + 1 {
                            let a2 = Addr::Con(atom!("!"));
                            self.unify(a1, a2);
                        } else {
                            let a2 = Addr::Con(atom!("true"));
                            self.unify(a1, a2);
                        },
                    _ => self.fail = true
                };
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
            },
            &SystemClauseType::EraseBall => self.ball.reset(),
            &SystemClauseType::Fail => self.fail = true,
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
            },
            &SystemClauseType::GetCurrentBlock => {
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, c);
            },
            &SystemClauseType::GetBValue => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = Addr::Con(Constant::Usize(self.b));

                self.unify(a1, a2);
            },
            &SystemClauseType::GetCutPoint => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = Addr::Con(Constant::Usize(self.b0));

                self.unify(a1, a2);
            },
            &SystemClauseType::InstallNewBlock => {
                self.install_new_block(temp_v!(1));
            },
            &SystemClauseType::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)].clone());
                self.reset_block(addr);
            },
            &SystemClauseType::SetBall => self.set_ball(),
            &SystemClauseType::SkipMaxList => if let Err(err) = self.skip_max_list() {
                return Err(err);
            },
            &SystemClauseType::Succeed => {},
            &SystemClauseType::TermVariables => {
                let a1 = self[temp_v!(1)].clone();
                let mut vars = Vec::new();

                {
                    let iter = HCPreOrderIterator::new(self, a1);

                    for item in iter {
                        match item {
                            HeapCellValue::Addr(Addr::HeapCell(h)) =>
                                vars.push(Ref::HeapCell(h)),
                            HeapCellValue::Addr(Addr::StackCell(fr, sc)) =>
                                vars.push(Ref::StackCell(fr, sc)),
                            _ => {}
                        }
                    }
                }

                let mut h = self.heap.h;
                let outcome = Addr::HeapCell(h);

                let mut seen_vars = HashSet::new();

                for r in vars {
                    if seen_vars.contains(&r) {
                        continue;
                    }

                    self.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));
                    self.heap.push(HeapCellValue::Addr(r.as_addr()));

                    h += 2;

                    seen_vars.insert(r);
                }

                self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::EmptyList)));

                let a2 = self[temp_v!(2)].clone();
                self.unify(a2, outcome);
            },
            &SystemClauseType::UnwindStack => self.unwind_stack(),
            &SystemClauseType::WriteTerm => {
                let addr = self[temp_v!(1)].clone();

                let ignore_ops = self[temp_v!(2)].clone();
                let numbervars = self[temp_v!(3)].clone();
                let quoted = self[temp_v!(4)].clone();

                let mut printer = HCPrinter::new(&self, PrinterOutputter::new());

                if let &Addr::Con(Constant::Atom(ref name, ..)) = &ignore_ops {
                    printer.ignore_ops = name.as_str() == "true";
                }

                if let &Addr::Con(Constant::Atom(ref name, ..)) = &numbervars {
                    printer.numbervars = name.as_str() == "true";
                }

                if let &Addr::Con(Constant::Atom(ref name, ..)) = &quoted {
                    printer.quoted = name.as_str() == "true";
                }

                let mut output  = printer.print(addr);
                println!("{}", output.result());
            }
        };

        self.set_p();

        Ok(())
    }
}
