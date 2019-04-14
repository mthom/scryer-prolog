use prolog_parser::ast::*;
use prolog_parser::parser::{get_desc, get_clause_spec};
use prolog_parser::tabled_rc::*;

use prolog::clause_types::*;
use prolog::heap_print::*;
use prolog::machine::copier::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::machine::toplevel::to_op_decl;
use prolog::num::{FromPrimitive, ToPrimitive, Zero};
use prolog::num::bigint::{BigInt};
use prolog::read::{PrologStream, readline};

use ref_thread_local::RefThreadLocal;

use std::collections::HashSet;
use std::io::{stdout, Write};
use std::iter::once;
use std::mem;
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
            HeapCellValue::NamedStr(..) =>
                Some(CycleSearchResult::NotList),
            HeapCellValue::Addr(addr) =>
                match self.store(self.deref(addr)) {
                    Addr::Con(Constant::EmptyList) =>
                        Some(CycleSearchResult::ProperList(brent_st.steps)),
                    Addr::HeapCell(_) | Addr::StackCell(..) =>
                        Some(CycleSearchResult::PartialList(brent_st.steps, brent_st.hare)),
                    Addr::Lis(l) => {
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

    fn copy_findall_solution(&mut self, lh_offset: usize, copy_target: Addr) -> usize
    {
        let threshold = self.lifted_heap.len() - lh_offset;
        let mut copy_ball_term = CopyBallTerm::new(&mut self.and_stack, &mut self.heap,
                                                   &mut self.lifted_heap);

        copy_ball_term.push(HeapCellValue::Addr(Addr::Lis(threshold + 1)));
        copy_ball_term.push(HeapCellValue::Addr(Addr::HeapCell(threshold + 3)));
        copy_ball_term.push(HeapCellValue::Addr(Addr::HeapCell(threshold + 2)));

        copy_term(copy_ball_term, copy_target);
        threshold + lh_offset + 2
    }

    fn repl_redirect(&mut self, repl_code_ptr: REPLCodePtr) -> CallResult {
        let p = if self.last_call {
            self.cp
        } else {
            self.p.local() + 1
        };

        self.p = CodePtr::REPL(repl_code_ptr, p);
        return Ok(());
    }

    fn truncate_if_no_lifted_heap_diff<AddrConstr>(&mut self, addr_constr: AddrConstr)
       where AddrConstr: Fn(usize) -> Addr
    {
        match self.store(self.deref(self[temp_v!(1)].clone())) {
            Addr::Con(Constant::Usize(lh_offset)) => {
                if lh_offset >= self.lifted_heap.len() {
                    self.lifted_heap.truncate(lh_offset);
                } else {
                    let threshold = self.lifted_heap.len() - lh_offset;
                    self.lifted_heap.push(HeapCellValue::Addr(addr_constr(threshold)));
                }
            },
            _ =>
                self.fail = true
        }
    }

    fn get_next_db_ref(&mut self, indices: &IndexStore, db_ref: &DBRef) {
        match db_ref {
            &DBRef::BuiltInPred(ref name, arity, _) => {
                let key = (name.as_str(), arity);

                match CLAUSE_TYPE_FORMS.borrow().range(&key ..).skip(1).next() {
                    Some(((_, arity), ct)) => {
                        let a2 = self[temp_v!(2)].clone();

                        if let Some(r) = a2.as_var() {
                            self.bind(r, Addr::DBRef(DBRef::BuiltInPred(ct.name(), *arity, ct.spec())));
                        } else {
                            self.fail = true;
                        }
                    },
                    None =>
                        match indices.code_dir.iter().next() {
                            Some(((ref name, arity), _)) => {
                                let a2 = self[temp_v!(2)].clone();

                                if let Some(r) = a2.as_var() {
                                    let spec = get_clause_spec(name.clone(), *arity,
                                                               composite_op!(&indices.op_dir));
                                    self.bind(r, Addr::DBRef(DBRef::NamedPred(name.clone(), *arity, spec)));
                                } else {
                                    self.fail = true;
                                }
                            },
                            None => {
                                self.fail = true;
                            }
                        }
                }
            },
            &DBRef::NamedPred(ref name, arity, _) => {
                let key = (name.clone(), arity);

                match indices.code_dir.range(key ..).skip(1).next() {
                    Some(((name, arity), _)) => {
                        let a2 = self[temp_v!(2)].clone();

                        if let Some(r) = a2.as_var() {
                            let spec = get_clause_spec(name.clone(), *arity,
                                                       composite_op!(&indices.op_dir));
                            self.bind(r, Addr::DBRef(DBRef::NamedPred(name.clone(), *arity, spec)));
                        } else {
                            self.fail = true;
                        }
                    },
                    None => self.fail = true
                }
            },
            &DBRef::Op(_, spec, ref name, ref op_dir, _) => {
                let fixity = match spec {
                    XF | YF => Fixity::Post,
                    FX | FY => Fixity::Pre,
                    _ => Fixity::In
                };

                let key = OrderedOpDirKey(name.clone(), fixity);

                match op_dir.range(key ..).skip(1).next() {
                    Some((OrderedOpDirKey(name, _), (priority, spec))) => {
                        let a2 = self[temp_v!(2)].clone();

                        if let Some(r) = a2.as_var() {
                            self.bind(r, Addr::DBRef(DBRef::Op(*priority, *spec, name.clone(),
                                                               op_dir.clone(),
                                                               SharedOpDesc::new(*priority, *spec))));
                        } else {
                            self.fail = true;
                        }
                    },
                    None => self.fail = true
                }
            }
        }
    }

    pub(super) fn system_call(&mut self,
                              ct: &SystemClauseType,
                              indices: &mut IndexStore,
                              call_policy: &mut Box<CallPolicy>,
                              cut_policy:  &mut Box<CutPolicy>,
                              parsing_stream: &mut PrologStream)
                              -> CallResult
    {
        match ct {
            &SystemClauseType::AbolishClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Abolish;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::AbolishModuleClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAbolish;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::AssertDynamicPredicateToFront => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Assert(DynamicAssertPlace::Front);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::AssertDynamicPredicateToBack => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Assert(DynamicAssertPlace::Back);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::AtomChars => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    Addr::Con(Constant::Char(c)) => {
                        let iter = once(Addr::Con(Constant::Char(c)));
                        let list_of_chars = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)].clone();
                        self.unify(a2, list_of_chars);
                    },
                    Addr::Con(Constant::Atom(name, _)) => {
                        let iter = name.as_str().chars().map(|c| Addr::Con(Constant::Char(c)));
                        let list_of_chars = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)].clone();
                        self.unify(a2, list_of_chars);
                    },
                    Addr::Con(Constant::EmptyList) => {
                        let a2 = self[temp_v!(2)].clone();
                        let chars = vec![Addr::Con(Constant::Char('[')),
                                         Addr::Con(Constant::Char(']'))];

                        let list_of_chars = Addr::HeapCell(self.heap.to_list(chars.into_iter()));

                        self.unify(a2, list_of_chars);
                    },
                    ref addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("atom_chars"), 2);

                        match self.try_from_list(temp_v!(2), stub.clone()) {
                            Err(e) => return Err(e),
                            Ok(addrs) => {
                                let mut chars = String::new();

                                for addr in addrs.iter() {
                                    match addr {
                                        &Addr::Con(Constant::Char(c)) =>
                                            chars.push(c),
                                        &Addr::Con(Constant::Atom(ref name, _))
                                            if name.as_str().len() == 1 => {
                                                chars += name.as_str();
                                            },
                                        _ => {
                                            let err = MachineError::type_error(ValidType::Character,
                                                                               addr.clone());
                                            return Err(self.error_form(err, stub));
                                        }
                                    }
                                }

                                let chars = clause_name!(chars, indices.atom_tbl);
                                self.unify(addr.clone(), Addr::Con(Constant::Atom(chars, None)));
                            }
                        }
                    },
                    _ => unreachable!()
                };
            },
            &SystemClauseType::AtomCodes => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    Addr::Con(Constant::Char(c)) => {
                        let iter = once(Addr::Con(Constant::CharCode(c as u8)));
                        let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)].clone();
                        self.unify(a2, list_of_codes);
                    },
                    Addr::Con(Constant::Atom(name, _)) => {
                        let iter = name.as_str().chars().map(|c| Addr::Con(Constant::CharCode(c as u8)));
                        let list_of_codes = Addr::HeapCell(self.heap.to_list(iter));

                        let a2 = self[temp_v!(2)].clone();

                        self.unify(a2, list_of_codes);
                    },
                    Addr::Con(Constant::EmptyList) => {
                        let a2 = self[temp_v!(2)].clone();
                        let chars = vec![Addr::Con(Constant::CharCode('[' as u8)),
                                         Addr::Con(Constant::CharCode(']' as u8))];

                        let list_of_codes = Addr::HeapCell(self.heap.to_list(chars.into_iter()));

                        self.unify(a2, list_of_codes);
                    },
                    ref addr if addr.is_ref() => {
                        let stub = MachineError::functor_stub(clause_name!("atom_codes"), 2);

                        match self.try_from_list(temp_v!(2), stub.clone()) {
                            Err(e) => return Err(e),
                            Ok(addrs) => {
                                let mut chars = String::new();

                                for addr in addrs.iter() {
                                    match addr {
                                        &Addr::Con(Constant::CharCode(c)) =>
                                            chars.push(c as char),
                                        _ => {
                                            let err = MachineError::representation_error(RepFlag::CharacterCode);
                                            return Err(self.error_form(err, stub));
                                        }
                                    }
                                }

                                let chars = clause_name!(chars, indices.atom_tbl);
                                self.unify(addr.clone(), Addr::Con(Constant::Atom(chars, None)));
                            }
                        }
                    },
                    _ => unreachable!()
                };
            },
            &SystemClauseType::AtomLength => {
                let a1 = self[temp_v!(1)].clone();

                let atom = match self.store(self.deref(a1)) {
                    Addr::Con(Constant::Atom(name, _)) => name,
                    Addr::Con(Constant::EmptyList) => clause_name!("[]"),
                    Addr::Con(Constant::Char(c)) => clause_name!(c.to_string(), indices.atom_tbl),
                    _ => unreachable!()
                };

                let len = Number::Integer(Rc::new(BigInt::from_usize(atom.as_str().len()).unwrap()));
                let a2  = self[temp_v!(2)].clone();

                self.unify(a2, Addr::Con(Constant::Number(len)));
            },
            &SystemClauseType::ModuleAssertDynamicPredicateToFront => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAssert(DynamicAssertPlace::Front);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::ModuleAssertDynamicPredicateToBack => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleAssert(DynamicAssertPlace::Back);

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::LiftedHeapLength => {
                let a1 = self[temp_v!(1)].clone();
                let lh_len = Addr::Con(Constant::Usize(self.lifted_heap.len()));

                self.unify(a1, lh_len);
            },
            &SystemClauseType::CharCode => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    Addr::Con(Constant::Atom(name, _)) => {
                        let c = name.as_str().chars().next().unwrap();
                        let a2 = self[temp_v!(2)].clone();

                        self.unify(Addr::Con(Constant::CharCode(c as u8)), a2);
                    },
                    Addr::Con(Constant::Char(c)) => {
                        let a2 = self[temp_v!(2)].clone();
                        self.unify(Addr::Con(Constant::CharCode(c as u8)), a2);
                    },
                    ref addr if addr.is_ref() => {
                        let a2 = self[temp_v!(2)].clone();

                        match self.store(self.deref(a2)) {
                            Addr::Con(Constant::CharCode(code)) =>
                                self.unify(Addr::Con(Constant::Char(code as char)), addr.clone()),
                            Addr::Con(Constant::Number(Number::Integer(n))) =>
                                if let Some(c) = n.to_u8() {
                                    self.unify(Addr::Con(Constant::Char(c as char)), addr.clone());
                                } else {
                                    let stub = MachineError::functor_stub(clause_name!("char_code"), 2);
                                    let err = MachineError::representation_error(RepFlag::CharacterCode);
                                    let err = self.error_form(err, stub);

                                    return Err(err);
                                },
                            _ => self.fail = true
                        };
                    },
                    _ => unreachable!()
                };
            },
            &SystemClauseType::CheckCutPoint => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));

                match addr {
                    Addr::Con(Constant::Usize(old_b)) if self.b <= old_b + 2 => {},
                    _ => self.fail = true
                };
            },
            &SystemClauseType::FetchGlobalVar => {
                let key = self[temp_v!(1)].clone();

                let key = match self.store(self.deref(key)) {
                    Addr::Con(Constant::Atom(atom, _)) => atom,
                    _ => unreachable!()
                };

                let addr = self[temp_v!(2)].clone();

                match indices.global_variables.get(&key).cloned() {
                    Some(sought_addr) => self.unify(addr, sought_addr),
                    None => self.fail = true
                };
            },
            &SystemClauseType::GetChar => {
                readline::toggle_prompt(false);

                let result = parsing_stream.next();
                let a1 = self[temp_v!(1)].clone();

                match result {
                    Some(Ok(b)) => self.unify(Addr::Con(Constant::Char(b as char)), a1),
                    _ => {
                        let stub = MachineError::functor_stub(clause_name!("get_char"), 1);
                        let err = MachineError::representation_error(RepFlag::Character);
                        let err = self.error_form(err, stub);

                        return Err(err);
                    }
                }
            },
            &SystemClauseType::GetModuleClause => {
                let module = self[temp_v!(3)].clone();
                let head = self[temp_v!(1)].clone();

                let module = match self.store(self.deref(module)) {
                    Addr::Con(Constant::Atom(module, _)) =>
                        module,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let subsection = match self.store(self.deref(head)) {
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(arity, name, ..) =>
                                indices.get_clause_subsection(module, name, arity),
                            _ => unreachable!()
                        },
                    Addr::Con(Constant::Atom(name, _)) =>
                        indices.get_clause_subsection(module, name, 0),
                    _ => unreachable!()
                };

                match subsection {
                    Some(dynamic_predicate_info) => {
                        self.execute_at_index(2, dynamic_predicate_info.clauses_subsection_p);
                        return Ok(());
                    },
                    None => self.fail = true
                }
            },
            &SystemClauseType::ModuleHeadIsDynamic => {
                let module = self[temp_v!(2)].clone();
                let head = self[temp_v!(1)].clone();

                let module = match self.store(self.deref(module)) {
                    Addr::Con(Constant::Atom(module, _)) =>
                        module,
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                self.fail = !match self.store(self.deref(head)) {
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(arity, name, ..) =>
                                indices.get_clause_subsection(module, name, arity).is_some(),
                            _ => unreachable!()
                        },
                    Addr::Con(Constant::Atom(name, _)) =>
                        indices.get_clause_subsection(module, name, 0).is_some(),
                    _ => unreachable!()
                };
            },
            &SystemClauseType::HeadIsDynamic => {
                let head = self[temp_v!(1)].clone();

                self.fail = !match self.store(self.deref(head)) {
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(arity, name, ..) =>
                                indices.get_clause_subsection(name.owning_module(), name, arity).is_some(),
                            _ => unreachable!()
                        },
                    Addr::Con(Constant::Atom(name, _)) =>
                        indices.get_clause_subsection(name.owning_module(), name, 0).is_some(),
                    _ => unreachable!()
                };
            },
            &SystemClauseType::CopyToLiftedHeap =>
                match self.store(self.deref(self[temp_v!(1)].clone())) {
                    Addr::Con(Constant::Usize(lh_offset)) => {
                        let copy_target = self[temp_v!(2)].clone();

                        let old_threshold = self.copy_findall_solution(lh_offset, copy_target);
                        let new_threshold = self.lifted_heap.len() - lh_offset;

                        self.lifted_heap[old_threshold] = HeapCellValue::Addr(Addr::HeapCell(new_threshold));

                        for index in old_threshold + 1 .. self.lifted_heap.len() {
                            match &mut self.lifted_heap[index] {
                                &mut HeapCellValue::Addr(ref mut addr) =>
                                    *addr -= self.heap.len() + lh_offset,
                                _ => {}
                            }
                        }
                    },
                    _ => self.fail = true
                },
            &SystemClauseType::DeleteAttribute => {
                let ls0 = self.store(self.deref(self[temp_v!(1)].clone()));

                if let Addr::Lis(l1) = ls0 {
                    if let Addr::Lis(l2) = self.store(self.deref(Addr::HeapCell(l1 + 1))) {
                        let addr = self.heap[l1 + 1].as_addr(l1 + 1);
                        self.heap[l1 + 1] = HeapCellValue::Addr(Addr::HeapCell(l2 + 1));
                        self.trail(TrailRef::AttrVarLink(l1 + 1, addr));
                    }
                }
            },
            &SystemClauseType::DeleteHeadAttribute => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));

                match addr {
                    Addr::AttrVar(h) => {
                        let addr = self.heap[h+1].as_addr(h+1).clone();
                        let addr = self.store(self.deref(addr));

                        match addr {
                            Addr::Lis(l) => {
                                self.heap[h+1] = HeapCellValue::Addr(Addr::HeapCell(l+1));
                                self.trail(TrailRef::AttrVarLink(h+1, Addr::Lis(l)));
                            },
                            _ => unreachable!()
                        }
                    },
                    _ => unreachable!()
                }
            },
            &SystemClauseType::DynamicModuleResolution => {
                let module_name = self.store(self.deref(self[temp_v!(1)].clone()));

                if let Addr::Con(Constant::Atom(module_name, _)) = module_name {
                    match self.store(self.deref(self[temp_v!(2)].clone())) {
                        Addr::Str(a) =>
                            if let HeapCellValue::NamedStr(arity, name, _) = self.heap[a].clone() {
                                for i in 1 .. arity + 1 {
                                    self.registers[i] = self.heap[a+i].as_addr(a+i);
                                }

                                return self.module_lookup(indices, (name, arity), module_name, true);
                            },
                        Addr::Con(Constant::Atom(name, _)) =>
                            return self.module_lookup(indices, (name, 0), module_name, true),
                        addr => {
                            let stub = MachineError::functor_stub(clause_name!("(:)"), 2);

                            let type_error = MachineError::type_error(ValidType::Callable, addr);
                            let type_error = self.error_form(type_error, stub);

                            return Err(type_error);
                        }
                    }
                };
            },
            &SystemClauseType::EnqueueAttributeGoal => {
                let addr = self[temp_v!(1)].clone();
                self.attr_var_init.attribute_goals.push(addr);
            },
            &SystemClauseType::EnqueueAttributedVar => {
                let addr = self[temp_v!(1)].clone();

                match self.store(self.deref(addr)) {
                    Addr::AttrVar(h) =>
                        self.attr_var_init.attr_var_queue.push(h),
                    _ => {}
                }
            },
            &SystemClauseType::ExpandGoal => {
                self.p = CodePtr::Local(LocalCodePtr::UserGoalExpansion(0));
                return Ok(());
            },
            &SystemClauseType::ExpandTerm => {
                self.p = CodePtr::Local(LocalCodePtr::UserTermExpansion(0));
                return Ok(());
            },
            &SystemClauseType::GetNextDBRef => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    addr @ Addr::HeapCell(_)
                  | addr @ Addr::StackCell(..)
                  | addr @ Addr::AttrVar(_) =>
                      match CLAUSE_TYPE_FORMS.borrow().iter().next() {
                          Some(((_, arity), ct)) => {
                              let db_ref = DBRef::BuiltInPred(ct.name(), *arity, ct.spec());
                              let r = addr.as_var().unwrap();

                              self.bind(r, Addr::DBRef(db_ref));
                          },
                          None => {
                              self.fail = true;
                              return Ok(());
                          }
                      },
                    Addr::DBRef(DBRef::Op(..)) => self.fail = true,
                    Addr::DBRef(ref db_ref) =>
                      self.get_next_db_ref(&indices, db_ref),
                    _ => {
                      self.fail = true;
                    }
                };
            },
            &SystemClauseType::GetNextOpDBRef => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    addr @ Addr::HeapCell(_)
                  | addr @ Addr::StackCell(..)
                  | addr @ Addr::AttrVar(_) =>  {
                      let mut unossified_op_dir = OssifiedOpDir::new();

                      unossified_op_dir.extend(indices.op_dir.iter().filter_map(|(key, op_dir_val)| {
                          let (name, fixity) = key.clone();

                          let prec  = op_dir_val.shared_op_desc().prec();

                          if prec == 0 {
                              return None;
                          }

                          let assoc = op_dir_val.shared_op_desc().assoc();

                          Some((OrderedOpDirKey(name, fixity), (prec, assoc)))
                      }));

                      let ossified_op_dir = Rc::new(unossified_op_dir);

                      match ossified_op_dir.iter().next() {
                          Some((OrderedOpDirKey(name, _), (priority, spec))) => {
                              let db_ref = DBRef::Op(*priority, *spec, name.clone(),
                                                     ossified_op_dir.clone(),
                                                     SharedOpDesc::new(*priority, *spec));
                              let r = addr.as_var().unwrap();

                              self.bind(r, Addr::DBRef(db_ref));
                          },
                          None => {
                              self.fail = true;
                              return Ok(());
                          }
                      }
                    },
                    Addr::DBRef(DBRef::BuiltInPred(..)) | Addr::DBRef(DBRef::NamedPred(..)) =>
                        self.fail = true,
                    Addr::DBRef(ref db_ref) =>
                        self.get_next_db_ref(&indices, db_ref),
                    _ => {
                        self.fail = true;
                    }
                }
            },
            &SystemClauseType::LookupDBRef => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    Addr::DBRef(db_ref) =>
                        match db_ref {
                            DBRef::BuiltInPred(name, arity, spec) | DBRef::NamedPred(name, arity, spec) => {
                                let a2 = self[temp_v!(2)].clone();
                                let a3 = self[temp_v!(3)].clone();

                                let arity = Number::Integer(Rc::new(BigInt::from_usize(arity).unwrap()));

                                self.unify(a2, Addr::Con(Constant::Atom(name, spec)));

                                if !self.fail {
                                    self.unify(a3, Addr::Con(Constant::Number(arity)));
                                }
                            },
                            _ => self.fail = true
                        },
                    _ => self.fail = true
                }
            },
            &SystemClauseType::LookupOpDBRef => {
                let a1 = self[temp_v!(1)].clone();

                match self.store(self.deref(a1)) {
                    Addr::DBRef(db_ref) =>
                        match db_ref {
                            DBRef::Op(priority, spec, name, _, shared_op_desc) => {


                                let prec = self[temp_v!(2)].clone();
                                let specifier = self[temp_v!(3)].clone();
                                let op = self[temp_v!(4)].clone();

                                let spec = match spec {
                                    FX => "fx",
                                    FY => "fy",
                                    XF => "xf",
                                    YF => "yf",
                                    XFX => "xfx",
                                    XFY => "xfy",
                                    YFX => "yfx",
                                    _ => {
                                        self.fail = true;
                                        return Ok(());
                                    }
                                };

                                let a2 = Number::Integer(Rc::new(BigInt::from_usize(priority).unwrap()));
                                let a3 = Addr::Con(Constant::Atom(clause_name!(spec), None));
                                let a4 = Addr::Con(Constant::Atom(name, Some(shared_op_desc)));

                                self.unify(Addr::Con(Constant::Number(a2)), prec);

                                if !self.fail {
                                    self.unify(a3, specifier);
                                }

                                if !self.fail {
                                    self.unify(a4, op);
                                }
                            },
                            _ => self.fail = true
                        },
                    _ => self.fail = true
                }
            },
            &SystemClauseType::OpDeclaration => {
                let priority  = self[temp_v!(1)].clone();
                let specifier = self[temp_v!(2)].clone();
                let op = self[temp_v!(3)].clone();

                let priority = match self.store(self.deref(priority)) {
                    Addr::Con(Constant::Number(Number::Integer(n))) => n.to_usize().unwrap(),
                    _ => unreachable!()
                };

                let specifier = match self.store(self.deref(specifier)) {
                    Addr::Con(Constant::Atom(name, _)) => name,
                    _ => unreachable!()
                };

                let op = match self.store(self.deref(op)) {
                    Addr::Con(Constant::Atom(name, _)) => name,
                    Addr::Con(Constant::Char(c)) =>
                        clause_name!(c.to_string(), indices.atom_tbl),
                    _ => unreachable!()
                };

                let module  = op.owning_module();

                let result = to_op_decl(priority, specifier.as_str(), op)
                    .map_err(SessionError::from)
                    .and_then(|op_decl| {
                        if op_decl.0 == 0 {
                            Ok(op_decl.remove(&mut indices.op_dir))
                        } else {
                            let spec = get_desc(op_decl.name(), composite_op!(&indices.op_dir));
                            op_decl.submit(module, spec, &mut indices.op_dir)
                        }
                    });

                match result {
                    Ok(()) => {},
                    Err(e) => {
                        // 8.14.3.3 l)
                        let e = MachineError::session_error(self.heap.h, e);
                        let stub = MachineError::functor_stub(clause_name!("op"), 3);
                        let permission_error = self.error_form(e, stub);

                        return Err(permission_error);
                    }
                };
            },
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff =>
                self.truncate_if_no_lifted_heap_diff(|h| Addr::HeapCell(h)),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth =>
                self.truncate_if_no_lifted_heap_diff(|_| Addr::Con(Constant::EmptyList)),
            &SystemClauseType::GetAttributedVariableList => {
                let attr_var = self.store(self.deref(self[temp_v!(1)].clone()));
                let mut attr_var_list = match attr_var {
                    Addr::AttrVar(h) => h + 1,
                    attr_var @ Addr::HeapCell(_) | attr_var @ Addr::StackCell(..) => {
                        // create an AttrVar in the heap.
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::AttrVar(h)));
                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h + 1)));

                        self.bind(Ref::AttrVar(h), attr_var);
                        h + 1
                    },
                    _ => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let list_addr = self[temp_v!(2)].clone();
                self.unify(Addr::HeapCell(attr_var_list), list_addr);
            },
            &SystemClauseType::GetAttrVarQueueDelimiter => {
                let addr  = self[temp_v!(1)].clone();
                let value = Addr::Con(Constant::Usize(self.attr_var_init.attr_var_queue.len()));

                self.unify(addr, value);
            },
            &SystemClauseType::GetAttrVarQueueBeyond => {
                let addr = self[temp_v!(1)].clone();

                match self.store(self.deref(addr)) {
                    Addr::Con(Constant::Usize(b)) => {
                        let iter = self.gather_attr_vars_created_since(b);

                        let var_list_addr = Addr::HeapCell(self.heap.to_list(iter));
                        let list_addr = self[temp_v!(2)].clone();

                        self.unify(var_list_addr, list_addr);
                    },
                    _ => self.fail = true
                }
            },
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => {
                let lh_offset = self[temp_v!(1)].clone();

                match self.store(self.deref(lh_offset)) {
                    Addr::Con(Constant::Usize(lh_offset)) =>
                        if lh_offset >= self.lifted_heap.len() {
                            let solutions = self[temp_v!(2)].clone();
                            let diff = self[temp_v!(3)].clone();

                            self.unify(solutions, Addr::Con(Constant::EmptyList));
                            self.unify(diff, Addr::Con(Constant::EmptyList));
                        } else {
                            let h = self.heap.h;

                            for index in lh_offset .. self.lifted_heap.len() {
                                match self.lifted_heap[index].clone() {
                                    HeapCellValue::Addr(addr) =>
                                        self.heap.push(HeapCellValue::Addr(addr + h)),
                                    value =>
                                        self.heap.push(value)
                                }
                            }

                            if let Some(HeapCellValue::Addr(addr)) = self.heap.last().cloned() {
                                let diff = self[temp_v!(3)].clone();
                                self.unify(diff, addr);
                            }

                            self.lifted_heap.truncate(lh_offset);

                            let solutions = self[temp_v!(2)].clone();
                            self.unify(Addr::HeapCell(h), solutions);
                        },
                    _ => self.fail = true
                }
            },
            &SystemClauseType::GetLiftedHeapFromOffset => {
                let lh_offset = self[temp_v!(1)].clone();

                match self.store(self.deref(lh_offset)) {
                    Addr::Con(Constant::Usize(lh_offset)) =>
                        if lh_offset >= self.lifted_heap.len() {
                            let solutions = self[temp_v!(2)].clone();
                            self.unify(solutions, Addr::Con(Constant::EmptyList));
                        } else {
                            let h = self.heap.h;

                            for index in lh_offset .. self.lifted_heap.len() {
                                match self.lifted_heap[index].clone() {
                                    HeapCellValue::Addr(addr) =>
                                        self.heap.push(HeapCellValue::Addr(addr + h)),
                                    value =>
                                        self.heap.push(value)
                                }
                            }

                            self.lifted_heap.truncate(lh_offset);

                            let solutions = self[temp_v!(2)].clone();
                            self.unify(Addr::HeapCell(h), solutions);
                        },
                    _ => self.fail = true
                }
            },
            &SystemClauseType::GetDoubleQuotes => {
                let a1 = self[temp_v!(1)].clone();

                match self.flags.double_quotes {
                    DoubleQuotes::Chars =>
                        self.unify(a1, Addr::Con(atom!("chars"))),
                    DoubleQuotes::Atom =>
                        self.unify(a1, Addr::Con(atom!("atom"))),
                    DoubleQuotes::Codes =>
                        self.unify(a1, Addr::Con(atom!("codes")))
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
                                    return return_from_clause!(self.last_call, self);
                                }
                            } else {
                                sgc_policy.push_cont_pt(addr, b_cutoff, prev_b);
                            }
                        },
                    None => panic!("expected SCCCutPolicy trait object.")
                };

                self.fail = true;
            },
            &SystemClauseType::Halt =>
                std::process::exit(0),
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
            &SystemClauseType::ModuleOf => {
                let module = self.store(self.deref(self[temp_v!(2)].clone()));

                match module {
                    Addr::Con(Constant::Atom(name, _)) => {
                        let module = Addr::Con(Constant::Atom(name.owning_module(), None));
                        let target = self[temp_v!(1)].clone();

                        self.unify(target, module);
                    },
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(_, name, ..) => {
                                let module = Addr::Con(Constant::Atom(name.owning_module(), None));
                                let target = self[temp_v!(1)].clone();

                                self.unify(target, module);
                            },
                            _ => self.fail = true
                        },
                    _ => self.fail = true
                };
            },
            &SystemClauseType::NoSuchPredicate => {
                let head = self[temp_v!(1)].clone();

                self.fail = match self.store(self.deref(head)) {
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(arity, name, op_spec) => {
                                let module = name.owning_module();
                                indices.predicate_exists(name, module, arity, op_spec)
                            },
                            _ => unreachable!()
                        },
                    Addr::Con(Constant::Atom(name, op_spec)) => {
                        let module = name.owning_module();
                        indices.predicate_exists(name, module, 0, op_spec)
                    },
                    head => {
                        let err = MachineError::type_error(ValidType::Callable, head);
                        let stub = MachineError::functor_stub(clause_name!("clause"), 2);

                        return Err(self.error_form(err, stub));
                    }
                };
            },
            &SystemClauseType::RedoAttrVarBindings => {
                let mut bindings = mem::replace(&mut self.attr_var_init.bindings, vec![]);

                for (h, addr) in bindings {
                    self.heap[h] = HeapCellValue::Addr(addr);
                }
            },
            &SystemClauseType::ResetGlobalVarAtKey => {
                let key = self[temp_v!(1)].clone();

                let key = match self.store(self.deref(key)) {
                    Addr::Con(Constant::Atom(atom, _)) => atom,
                    _ => unreachable!()
                };

                indices.global_variables.remove(&key);
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
            &SystemClauseType::REPL(repl_code_ptr) =>
                return self.repl_redirect(repl_code_ptr),
            &SystemClauseType::ModuleRetractClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::ModuleRetract;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::RetractClause => {
                let p = self.cp;
                let trans_type = DynamicTransactionType::Retract;

                self.p = CodePtr::DynamicTransaction(trans_type, p);
                return Ok(());
            },
            &SystemClauseType::ReturnFromAttributeGoals => {
                self.deallocate();
                self.p = CodePtr::Local(LocalCodePtr::TopLevel(0, 0));
                return Ok(());
            },
            &SystemClauseType::ReturnFromVerifyAttr => {
                let e = self.e;
                let frame_len = self.and_stack[e].len();

                for i in 1 .. frame_len - 1 {
                    self[RegType::Temp(i)] = self.and_stack[e][i].clone();
                }

                if let &Addr::Con(Constant::Usize(b0)) = &self.and_stack[e][frame_len - 1] {
                    self.b0 = b0;
                }

                if let &Addr::Con(Constant::Usize(num_of_args)) = &self.and_stack[e][frame_len] {
                    self.num_of_args = num_of_args;
                }

                self.p = CodePtr::Local(self.and_stack[e].interrupt_cp);
                self.deallocate();

                return Ok(());
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
                    Addr::Con(Constant::Atom(ref atom, _)) if atom.as_str() == "codes" =>
                        self.flags.double_quotes = DoubleQuotes::Codes,
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
                    let stub = self.copy_and_align_ball();
                    self.heap.append(stub);
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
            &SystemClauseType::GetClause => {
                let head = self[temp_v!(1)].clone();

                let subsection = match self.store(self.deref(head)) {
                    Addr::Str(s) =>
                        match self.heap[s].clone() {
                            HeapCellValue::NamedStr(arity, name, ..) =>
                                indices.get_clause_subsection(name.owning_module(), name, arity),
                            _ => unreachable!()
                        },
                    Addr::Con(Constant::Atom(name, _)) =>
                        indices.get_clause_subsection(name.owning_module(), name, 0),
                    _ => unreachable!()
                };

                match subsection {
                    Some(dynamic_predicate_info) => {
                        self.execute_at_index(2, dynamic_predicate_info.clauses_subsection_p);
                        return Ok(());
                    },
                    _ => unreachable!()
                }
            },
            &SystemClauseType::GetCutPoint => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = Addr::Con(Constant::Usize(self.b0));

                self.unify(a1, a2);
            },
            &SystemClauseType::InstallNewBlock => {
                self.install_new_block(temp_v!(1));
            },
            &SystemClauseType::ReadTerm => {
                readline::toggle_prompt(true);

                match self.read(parsing_stream, indices.atom_tbl.clone(), &indices.op_dir) {
                    Ok(term_write_result) => {
                        let a1 = self[temp_v!(1)].clone();
                        self.unify(Addr::HeapCell(term_write_result.heap_loc), a1);

                        if self.fail {
                            return Ok(());
                        }

                        let mut list_of_var_eqs = vec![];

                        for (var, binding) in term_write_result.var_dict {
                            let var_atom = clause_name!(var.to_string(), indices.atom_tbl);
                            let var_atom = Constant::Atom(var_atom, None);

                            let h = self.heap.h;
                            let op_desc = Some(SharedOpDesc::new(700, XFX));

                            self.heap.push(HeapCellValue::NamedStr(2, clause_name!("="), op_desc));
                            self.heap.push(HeapCellValue::Addr(Addr::Con(var_atom)));
                            self.heap.push(HeapCellValue::Addr(binding));

                            list_of_var_eqs.push(Addr::Str(h));
                        }

                        let a2 = self[temp_v!(2)].clone();
                        let list_offset = Addr::HeapCell(self.heap.to_list(list_of_var_eqs.into_iter()));

                        self.unify(list_offset, a2);
                    },
                    Err(err) => {
                        // reset the input stream after an input failure.
                        *parsing_stream = readline::input_stream();

                        let h = self.heap.h;
                        let syntax_error = MachineError::syntax_error(h, err);
                        let stub = MachineError::functor_stub(clause_name!("read_term"), 2);

                        return Err(self.error_form(syntax_error, stub));
                    }
                }
            },
            &SystemClauseType::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)].clone());
                self.reset_block(addr);
            },
            &SystemClauseType::SetBall => self.set_ball(),
            &SystemClauseType::SkipMaxList => if let Err(err) = self.skip_max_list() {
                return Err(err);
            },
            &SystemClauseType::StoreGlobalVar => {
                let key = self[temp_v!(1)].clone();

                let key = match self.store(self.deref(key)) {
                    Addr::Con(Constant::Atom(atom, _)) => atom,
                    _ => unreachable!()
                };

                let value = self[temp_v!(2)].clone();

                indices.global_variables.insert(key, value);
            }
            &SystemClauseType::Succeed => {},
            &SystemClauseType::TermVariables => {
                let a1 = self[temp_v!(1)].clone();
                let mut seen_vars = HashSet::new();

                for item in self.acyclic_pre_order_iter(a1) {
                    match item {
                        HeapCellValue::Addr(addr) =>
                            if addr.is_ref() {
                                seen_vars.insert(addr);
                            },
                        _ => {}
                    }
                }

                let outcome = Addr::HeapCell(self.heap.to_list(seen_vars.into_iter()));

                let a2 = self[temp_v!(2)].clone();
                self.unify(a2, outcome);
            },
            &SystemClauseType::TruncateLiftedHeapTo =>
                match self.store(self.deref(self[temp_v!(1)].clone())) {
                    Addr::Con(Constant::Usize(lh_offset)) =>
                        self.lifted_heap.truncate(lh_offset),
                    _ => self.fail = true
                },
            &SystemClauseType::UnwindStack => self.unwind_stack(),
            &SystemClauseType::WriteTerm => {
                let addr = self[temp_v!(1)].clone();

                let ignore_ops = self.store(self.deref(self[temp_v!(2)].clone()));
                let numbervars = self.store(self.deref(self[temp_v!(3)].clone()));
                let quoted = self.store(self.deref(self[temp_v!(4)].clone()));

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
                print!("{}", output.result());
                stdout().flush().unwrap();
            }
        };

        return_from_clause!(self.last_call, self)
    }
}
