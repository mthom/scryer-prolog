use prolog::and_stack::*;
use prolog::ast::*;
use prolog::copier::*;
use prolog::machine::machine_errors::MachineStub;
use prolog::num::{BigInt, BigUint, Zero, One};
use prolog::or_stack::*;
use prolog::heap_print::*;
use prolog::tabled_rc::*;

use downcast::Any;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::mem::swap;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

pub(super) struct Ball {
    pub(super) boundary: usize, // ball.0
    pub(super) stub: MachineStub, // ball.1    
}

impl Ball {
    pub(super) fn new() -> Self {
        Ball { boundary: 0, stub: MachineStub::new() }
    }
    
    pub(super) fn reset(&mut self) {
        self.boundary = 0;
        self.stub.clear();
    }
}

pub(crate) struct CodeDirs<'a> {
    code_dir: &'a CodeDir,
    modules: &'a HashMap<ClauseName, Module>
}

impl<'a> CodeDirs<'a> {
    pub(super) fn new(code_dir: &'a CodeDir, modules: &'a HashMap<ClauseName, Module>) -> Self {
        CodeDirs { code_dir, modules }
    }

    pub(super) fn get(&self, name: ClauseName, arity: usize, in_mod: ClauseName) -> Option<CodeIndex>
    {
        match in_mod.as_str() {
            "user" | "builtin" => self.code_dir.get(&(name, arity)).cloned(),
            _ =>
                match self.modules.get(&in_mod) {
                    Some(&Module { ref code_dir, .. }) =>
                        code_dir.get(&(name, arity)).cloned().map(CodeIndex::from),
                    None => None
                }
        }
    }
}

pub(super) struct DuplicateTerm<'a> {
    state: &'a mut MachineState
}

impl<'a> DuplicateTerm<'a> {
    pub(super) fn new(state: &'a mut MachineState) -> Self {
        DuplicateTerm { state: state }
    }
}

impl<'a> Index<usize> for DuplicateTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.state.heap[index]
    }
}

impl<'a> IndexMut<usize> for DuplicateTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.state.heap[index]
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for DuplicateTerm<'a> {
    fn source(&self) -> usize {
        self.state.heap.h
    }

    fn threshold(&self) -> usize {
        self.state.heap.h
    }

    fn push(&mut self, hcv: HeapCellValue) {
        self.state.heap.push(hcv);
    }

    fn store(&self, a: Addr) -> Addr {
        self.state.store(a)
    }

    fn deref(&self, a: Addr) -> Addr {
        self.state.deref(a)
    }

    fn stack(&mut self) -> &mut AndStack {
        &mut self.state.and_stack
    }
}

pub(super) struct DuplicateBallTerm<'a> {
    state: &'a mut MachineState,
    heap_boundary: usize
}

impl<'a> DuplicateBallTerm<'a> {
    pub(super) fn new(state: &'a mut MachineState) -> Self {
        let hb = state.heap.len();
        DuplicateBallTerm { state, heap_boundary: hb }
    }
}

impl<'a> Index<usize> for DuplicateBallTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.heap_boundary {
            &self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &self.state.ball.stub[index]
        }
    }
}

impl<'a> IndexMut<usize> for DuplicateBallTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.heap_boundary {
            &mut self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &mut self.state.ball.stub[index]
        }
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for DuplicateBallTerm<'a> {
    fn source(&self) -> usize {
        self.heap_boundary
    }

    fn threshold(&self) -> usize {
        self.heap_boundary + self.state.ball.stub.len()
    }

    fn push(&mut self, hcv: HeapCellValue) {
        self.state.ball.stub.push(hcv);
    }

    fn store(&self, a: Addr) -> Addr {
        self.state.store(a)
    }

    fn deref(&self, a: Addr) -> Addr {
        self.state.deref(a)
    }

    fn stack(&mut self) -> &mut AndStack {
        &mut self.state.and_stack
    }
}

impl Index<RegType> for MachineState {
    type Output = Addr;

    fn index(&self, reg: RegType) -> &Self::Output {
        match reg {
            RegType::Temp(temp) => &self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &self.and_stack[e][perm]
            }
        }
    }
}

impl IndexMut<RegType> for MachineState {
    fn index_mut(&mut self, reg: RegType) -> &mut Self::Output {
        match reg {
            RegType::Temp(temp) => &mut self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &mut self.and_stack[e][perm]
            }
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum MachineMode {
    Read,
    Write
}

pub struct MachineState {
    pub(super) atom_tbl: TabledData<Atom>,
    pub(super) s: usize,
    pub(super) p: CodePtr,
    pub(super) b: usize,
    pub(super) b0: usize,
    pub(super) e: usize,
    pub(super) num_of_args: usize,
    pub(super) cp: CodePtr,
    pub(super) fail: bool,
    pub(crate) heap: Heap,
    pub(super) mode: MachineMode,
    pub(crate) and_stack: AndStack,
    pub(super) or_stack: OrStack,
    pub(super) registers: Registers,
    pub(super) trail: Vec<Ref>,
    pub(super) tr: usize,
    pub(super) hb: usize,
    pub(super) block: usize, // an offset into the OR stack.
    pub(super) ball: Ball,
    pub(super) interms: Vec<Number>, // intermediate numbers.
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any {
    fn context_call(&mut self, machine_st: &mut MachineState, name: ClauseName,
                    arity: usize, idx: CodeIndex, lco: bool)
                    -> CallResult
    {
        if lco {
            self.try_execute(machine_st, name, arity, idx)
        } else {
            self.try_call(machine_st, name, arity, idx)
        }
    }

    fn try_call(&mut self, machine_st: &mut MachineState, name: ClauseName,
                arity: usize, idx: CodeIndex)
                -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Undefined =>
                return Err(machine_st.existence_error(name, arity)),
            IndexPtr::Index(compiled_tl_index) => {
                let module_name = idx.0.borrow().1.clone();

                machine_st.cp = machine_st.p.clone() + 1;
                machine_st.num_of_args = arity;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(compiled_tl_index, module_name);
            }
        }

        Ok(())
    }

    fn try_execute<'a>(&mut self, machine_st: &mut MachineState, name: ClauseName,
                       arity: usize, idx: CodeIndex)
                       -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Undefined =>
                return Err(machine_st.existence_error(name, arity)),
            IndexPtr::Index(compiled_tl_index) => {
                let module_name = idx.0.borrow().1.clone();

                machine_st.num_of_args = arity;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(compiled_tl_index, module_name);
            }
        }

        Ok(())
    }

    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        let b = machine_st.b - 1;
        let n = machine_st.or_stack[b].num_args();

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.or_stack[b][i].clone();
        }

        machine_st.e  = machine_st.or_stack[b].e;
        machine_st.cp = machine_st.or_stack[b].cp.clone();

        machine_st.or_stack[b].bp = machine_st.p.clone() + offset;

        let old_tr  = machine_st.or_stack[b].tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.or_stack[b].tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.or_stack[b].h);

        machine_st.hb = machine_st.heap.h;

        machine_st.p += 1;

        Ok(())
    }

    fn retry(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        let b = machine_st.b - 1;
        let n = machine_st.or_stack[b].num_args();

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.or_stack[b][i].clone();
        }

        machine_st.e  = machine_st.or_stack[b].e;
        machine_st.cp = machine_st.or_stack[b].cp.clone();

        machine_st.or_stack[b].bp = machine_st.p.clone() + 1;

        let old_tr  = machine_st.or_stack[b].tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.or_stack[b].tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.or_stack[b].h);

        machine_st.hb = machine_st.heap.h;

        machine_st.p += offset;

        Ok(())
    }

    fn trust(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        let b = machine_st.b - 1;
        let n = machine_st.or_stack[b].num_args();

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.or_stack[b][i].clone();
        }

        machine_st.e  = machine_st.or_stack[b].e;
        machine_st.cp = machine_st.or_stack[b].cp.clone();

        let old_tr  = machine_st.or_stack[b].tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);

        machine_st.tr = machine_st.or_stack[b].tr;
        machine_st.trail.truncate(machine_st.tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);
        machine_st.b = machine_st.or_stack[b].b;

        machine_st.or_stack.truncate(machine_st.b);

        machine_st.hb = machine_st.heap.h;
        machine_st.p += offset;

        Ok(())
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult
    {
        let b = machine_st.b - 1;
        let n = machine_st.or_stack[b].num_args();

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.or_stack[b][i].clone();
        }

        machine_st.e  = machine_st.or_stack[b].e;
        machine_st.cp = machine_st.or_stack[b].cp.clone();

        let old_tr  = machine_st.or_stack[b].tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);

        machine_st.tr = machine_st.or_stack[b].tr;
        machine_st.trail.truncate(machine_st.tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);

        machine_st.b = machine_st.or_stack[b].b;

        machine_st.or_stack.truncate(machine_st.b);

        machine_st.hb = machine_st.heap.h;
        machine_st.p += 1;

        Ok(())
    }

    fn try_call_clause<'a>(&mut self, machine_st: &mut MachineState, code_dirs: CodeDirs<'a>,
                           ct: &ClauseType, arity: usize, lco: bool)
                           -> CallResult
    {
        match ct {
            &ClauseType::AcyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = machine_st.is_cyclic_term(addr);
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Arg => {
                if !lco {
                    machine_st.cp = machine_st.p.clone() + 1;
                }

                machine_st.num_of_args = 3;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(166, clause_name!("builtin"));

                Ok(())
            },
            &ClauseType::Catch => {
                if !lco {
                    machine_st.cp = machine_st.p.clone() + 1;
                }

                machine_st.num_of_args = 3;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(5, clause_name!("builtin"));

                Ok(())
            },
            &ClauseType::CallN =>
                if let Some((name, arity)) = machine_st.setup_call_n(arity) {
                    if let Some(idx) = code_dirs.get(name.clone(), arity, clause_name!("user")) {
                        self.context_call(machine_st, name, arity, idx, lco)
                    } else {
                        Err(machine_st.existence_error(name, arity))
                    }
                } else {
                    Ok(())
                },
            &ClauseType::Compare => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();
                let a3 = machine_st[temp_v!(3)].clone();

                let c = Addr::Con(match machine_st.compare_term_test(&a2, &a3) {
                    Ordering::Greater => atom!(">"),
                    Ordering::Equal   => atom!("="),
                    Ordering::Less    => atom!("<")
                });

                machine_st.unify(a1, c);
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::CompareTerm(qt) => {
                match qt {
                    CompareTermQT::Equal =>
                        machine_st.fail = machine_st.structural_eq_test(),
                    CompareTermQT::NotEqual =>
                        machine_st.fail = !machine_st.structural_eq_test(),
                    _ => machine_st.compare_term(qt)
                };

                return_from_clause!(lco, machine_st)
            },
            &ClauseType::CyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = !machine_st.is_cyclic_term(addr);
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Display => {
                let output = machine_st.print_term(machine_st[temp_v!(1)].clone(),
                                                   DisplayFormatter {},
                                                   PrinterOutputter::new());

                println!("{}", output.result());
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::DuplicateTerm => {
                machine_st.duplicate_term();
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Eq => {
                machine_st.fail = machine_st.eq_test();
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Ground => {
                machine_st.fail = machine_st.ground_test();
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Functor => {
                machine_st.try_functor()?;
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::NotEq => {
                machine_st.fail = !machine_st.eq_test();
                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Sort => {
                machine_st.check_sort_errors()?;
                
                let stub = machine_st.functor_stub(clause_name!("sort"), 2);
                let mut list = machine_st.try_from_list(temp_v!(1), stub)?;                                
                
                list.sort_unstable_by(|a1, a2| machine_st.compare_term_test(a1, a2));
                machine_st.term_dedup(&mut list);

                let heap_addr = Addr::HeapCell(machine_st.to_list(list.into_iter()));

                let r2 = machine_st[temp_v!(2)].clone();
                machine_st.unify(r2, heap_addr);

                return_from_clause!(lco, machine_st)
            },
            &ClauseType::KeySort => {
                machine_st.check_keysort_errors()?;
                
                let stub = machine_st.functor_stub(clause_name!("keysort"), 2);
                let mut list = machine_st.try_from_list(temp_v!(1), stub)?;
                let mut key_pairs = Vec::new();                
                
                for val in list {
                    let key = machine_st.project_onto_key(val.clone())?;
                    key_pairs.push((key, val.clone()));
                }

                key_pairs.sort_by(|a1, a2| machine_st.compare_term_test(&a1.0, &a2.0));

                let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
                let heap_addr = Addr::HeapCell(machine_st.to_list(key_pairs));

                let r2 = machine_st[temp_v!(2)].clone();
                machine_st.unify(r2, heap_addr);

                return_from_clause!(lco, machine_st)
            },
            &ClauseType::Throw => {
                if !lco {
                    machine_st.cp = machine_st.p.clone() + 1;
                }

                machine_st.goto_throw();
                Ok(())
            },
            &ClauseType::Named(ref name, ref idx) | &ClauseType::Op(ref name, _, ref idx) =>
                self.context_call(machine_st, name.clone(), arity, idx.clone(), lco),
            &ClauseType::CallWithInferenceLimit => {
                machine_st.goto_ptr(CodePtr::DirEntry(409, clause_name!("builtin")), 3, lco);
                Ok(())
            },
            &ClauseType::SetupCallCleanup => {
                machine_st.goto_ptr(CodePtr::DirEntry(310, clause_name!("builtin")), 3, lco);
                Ok(())
            },
            &ClauseType::Is => {
                let a = machine_st[temp_v!(1)].clone();
                let result = machine_st.arith_eval_by_metacall(temp_v!(2))?;

                machine_st.unify(a, Addr::Con(Constant::Number(result)));
                machine_st.p += 1;

                Ok(())
            },
            &ClauseType::Inlined(ref inlined) => {
                machine_st.execute_inlined(inlined, &vec![temp_v!(1), temp_v!(2)]);
                Ok(())
            },
            &ClauseType::SkipMaxList => {
                machine_st.skip_max_list()?;
                machine_st.p += 1;
                
                Ok(())
            }
        }
    }
}

downcast!(CallPolicy);

pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

pub(crate) struct CallWithInferenceLimitCallPolicy {
    pub(crate) prev_policy: Box<CallPolicy>,
    count:  BigUint,
    limits: Vec<(BigUint, usize)>
}

impl CallWithInferenceLimitCallPolicy {
    pub(crate) fn new_in_place(policy: &mut Box<CallPolicy>)
    {
        let mut prev_policy: Box<CallPolicy> = Box::new(DefaultCallPolicy {});
        swap(&mut prev_policy, policy);

        let new_policy = CallWithInferenceLimitCallPolicy { prev_policy,
                                                            count:  BigUint::zero(),
                                                            limits: vec![] };
        *policy = Box::new(new_policy);
    }

    fn increment(&mut self) -> CallResult {
        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == *limit {
                return Err(functor!("inference_limit_exceeded", 1,
                                    [HeapCellValue::Addr(Addr::Con(Constant::Usize(bp)))]));
            } else {
                self.count += BigUint::one();
            }
        }

        Ok(())
    }

    pub(crate) fn add_limit(&mut self, limit: Rc<BigInt>, b: usize) -> Rc<BigInt> {
        let limit = match limit.to_biguint() {
            Some(limit) => limit + &self.count,
            None => panic!("install_inference_counter: limit must be positive")
        };

        match self.limits.last().cloned() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {},
            _ => self.limits.push((limit, b))
        };

        Rc::new(BigInt::from(self.count.clone()))
    }

    pub(crate) fn remove_limit(&mut self, b: usize) -> Rc<BigInt> {
        if let Some((_, bp)) = self.limits.last().cloned() {
            if bp == b {
                self.limits.pop();
            }
        }

        Rc::new(BigInt::from(self.count.clone()))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.limits.is_empty()
    }

    pub(crate) fn into_inner(&mut self) -> Box<CallPolicy> {
        let mut new_inner: Box<CallPolicy> = Box::new(DefaultCallPolicy {});
        swap(&mut self.prev_policy, &mut new_inner);
        new_inner
    }
}

impl CallPolicy for CallWithInferenceLimitCallPolicy {
    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.retry_me_else(machine_st, offset)?;
        self.increment()
    }

    fn retry(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.retry(machine_st, offset)?;
        self.increment()
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult
    {
        self.prev_policy.trust_me(machine_st)?;
        self.increment()
    }

    fn trust(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.trust(machine_st, offset)?;
        self.increment()
    }

    fn try_call_clause<'a>(&mut self, machine_st: &mut MachineState, code_dirs: CodeDirs<'a>,
                           ct: &ClauseType, arity: usize, lco: bool)
                           -> CallResult
    {
        self.prev_policy.try_call_clause(machine_st, code_dirs, ct, arity, lco)?;
        self.increment()
    }
}

pub(crate) trait CutPolicy: Any {
    fn cut(&mut self, &mut MachineState, RegType);
}

downcast!(CutPolicy);

pub(crate) struct DefaultCutPolicy {}

impl CutPolicy for DefaultCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) {
        let b = machine_st.b;

        if let Addr::Con(Constant::Usize(b0)) = machine_st[r].clone() {
            if b > b0 {
                machine_st.b = b0;
                machine_st.tidy_trail();
                machine_st.or_stack.truncate(machine_st.b);
            }
        } else {
            machine_st.fail = true;
            return;
        }

        machine_st.p += 1;
    }
}

pub(crate) struct SetupCallCleanupCutPolicy {
    // locations of cleaners, cut points, the previous block
    cont_pts: Vec<(Addr, usize, usize)>
}

impl SetupCallCleanupCutPolicy {
    pub(crate) fn new() -> Self {
        SetupCallCleanupCutPolicy { cont_pts: vec![] }
    }

    pub(crate) fn out_of_cont_pts(&self) -> bool {
        self.cont_pts.is_empty()
    }

    pub(crate) fn push_cont_pt(&mut self, addr: Addr, b: usize, block: usize) {
        self.cont_pts.push((addr, b, block));
    }

    pub(crate) fn pop_cont_pt(&mut self) -> Option<(Addr, usize, usize)> {
        self.cont_pts.pop()
    }
}

impl CutPolicy for SetupCallCleanupCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) {
        let b = machine_st.b;

        if let Addr::Con(Constant::Usize(b0)) = machine_st[r].clone() {
            if b > b0 {
                machine_st.b = b0;
                machine_st.tidy_trail();
                machine_st.or_stack.truncate(machine_st.b);
            }
        } else {
            machine_st.fail = true;
            return;
        }

        machine_st.p += 1;

        if !self.out_of_cont_pts() {
            machine_st.cp = machine_st.p.clone();
            machine_st.num_of_args = 0;
            machine_st.b0 = machine_st.b;
            // goto_call run_cleaners_without_handling/0, 370.
            machine_st.p = CodePtr::DirEntry(370, clause_name!("builtin"));
        }
    }
}
