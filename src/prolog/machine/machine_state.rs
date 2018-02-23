use prolog::and_stack::*;
use prolog::builtins::CodeDir;
use prolog::ast::*;
use prolog::copier::*;
use prolog::num::{BigInt, Zero, One};
use prolog::or_stack::*;
use prolog::tabled_rc::*;

use downcast::Any;

use std::mem::swap;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

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
        DuplicateBallTerm { state: state, heap_boundary: hb }
    }
}

impl<'a> Index<usize> for DuplicateBallTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.heap_boundary {
            &self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &self.state.ball.1[index]
        }
    }
}

impl<'a> IndexMut<usize> for DuplicateBallTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.heap_boundary {
            &mut self.state.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &mut self.state.ball.1[index]
        }
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for DuplicateBallTerm<'a> {
    fn source(&self) -> usize {
        self.heap_boundary
    }

    fn threshold(&self) -> usize {
        self.heap_boundary + self.state.ball.1.len()
    }

    fn push(&mut self, hcv: HeapCellValue) {
        self.state.ball.1.push(hcv);
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
    pub(super) ball: (usize, Vec<HeapCellValue>), // heap boundary, and a term copy
    pub(super) interms: Vec<Number>, // intermediate numbers.
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any {
    fn try_call(&mut self, machine_st: &mut MachineState, code_dir: &CodeDir,
                name: TabledRc<Atom>, arity: usize)
                -> CallResult
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                machine_st.cp = machine_st.p + 1;
                machine_st.num_of_args = arity;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => machine_st.fail = true
        };

        Ok(())
    }

    fn try_execute(&mut self, machine_st: &mut MachineState, code_dir: &CodeDir,
                   name: TabledRc<Atom>, arity: usize)
                   -> CallResult
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                machine_st.num_of_args = arity;
                machine_st.b0 = machine_st.b;
                machine_st.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => machine_st.fail = true
        };

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
        machine_st.cp = machine_st.or_stack[b].cp;

        machine_st.or_stack[b].bp = machine_st.p + offset;

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
        machine_st.cp = machine_st.or_stack[b].cp;

        machine_st.or_stack[b].bp = machine_st.p + 1;

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
        machine_st.cp = machine_st.or_stack[b].cp;

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
        machine_st.cp = machine_st.or_stack[b].cp;

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
}

downcast!(CallPolicy);

pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

pub(crate) struct CallWithInferenceLimitCallPolicy {
    atom_tbl: TabledData<Atom>,
    pub(crate) prev_policy: Box<CallPolicy>,
    count:  BigInt,
    limits: Vec<(Rc<BigInt>, usize)>
}

impl CallWithInferenceLimitCallPolicy {
    pub(crate) fn new_in_place(atom_tbl: TabledData<Atom>, policy: &mut Box<CallPolicy>)
    {
        let mut prev_policy: Box<CallPolicy> = Box::new(DefaultCallPolicy {});
        swap(&mut prev_policy, policy);

        let new_policy = CallWithInferenceLimitCallPolicy { atom_tbl, prev_policy,
                                                            count:  BigInt::zero(),
                                                            limits: vec![] };
        *policy = Box::new(new_policy);
    }

    fn increment(&mut self) -> CallResult {
        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == **limit {
                return Err(functor!(self.atom_tbl,
                                    "inference_limit_exceeded",
                                    1,
                                    [HeapCellValue::Addr(Addr::Con(Constant::Usize(bp)))]));
            } else {
                self.count = BigInt::one() + &self.count;
            }
        }

        Ok(())
    }

    pub(crate) fn add_limit(&mut self, limit: Rc<BigInt>, b: usize) -> Rc<BigInt> {
        let limit = Rc::new(&*limit + &self.count);
        
        match self.limits.last().cloned() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {},
            _ => self.limits.push((limit, b))
        };

        Rc::new(self.count.clone())
    }

    pub(crate) fn remove_limit(&mut self, b: usize) -> Rc<BigInt> {
        if let Some((_, bp)) = self.limits.last().cloned() {
            if bp == b {
                self.limits.pop();
            }
        }

        Rc::new(self.count.clone())
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
    fn try_call(&mut self, machine_st: &mut MachineState, code_dir: &CodeDir,
                name: TabledRc<Atom>, arity: usize)
                -> CallResult
    {
        self.prev_policy.try_call(machine_st, code_dir, name, arity)?;
        self.increment()
    }

    fn try_execute(&mut self, machine_st: &mut MachineState, code_dir: &CodeDir,
                   name: TabledRc<Atom>, arity: usize)
                   -> CallResult
    {
        self.prev_policy.try_execute(machine_st, code_dir, name, arity)?;
        self.increment()
    }

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
}

pub(crate) trait CutPolicy: Any {
    fn cut(&mut self, &mut MachineState, RegType);
}

// from the downcast crate.
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
            machine_st.cp = machine_st.p;
            machine_st.num_of_args = 0;
            machine_st.b0 = machine_st.b;
            machine_st.p  = CodePtr::DirEntry(354); // goto_call run_cleaners_without_handling/0, 354.
        }
    }
}
