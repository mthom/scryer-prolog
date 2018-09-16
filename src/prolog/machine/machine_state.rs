use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::instructions::*;
use prolog::and_stack::*;
use prolog::copier::*;
use prolog::heap_print::*;
use prolog::machine::MachineCodeIndices;
use prolog::machine::machine_errors::*;
use prolog::num::{BigInt, BigUint, Zero, One};
use prolog::or_stack::*;

use downcast::Any;

use std::cmp::Ordering;
use std::io::stdin;
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

#[derive(Clone, Copy)]
pub(crate) struct CodeDirs<'a> {
    pub code_dir: &'a CodeDir,
    pub op_dir: &'a OpDir,
    pub modules: &'a ModuleDir
}

impl<'a> CodeDirs<'a> {
    fn get_internal(&self, name: ClauseName, arity: usize, in_mod: ClauseName) -> Option<ModuleCodeIndex> {
        self.modules.get(&in_mod)
            .and_then(|ref module| module.code_dir.get(&(name, arity)))
            .cloned()
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h  = clause_name!("run_cleaners_with_handling");
        let r_wo_h = clause_name!("run_cleaners_without_handling");

        let builtins = clause_name!("builtins");

        let r_w_h  = self.get_internal(r_w_h, 0, builtins.clone()).and_then(|item| item.local());
        let r_wo_h = self.get_internal(r_wo_h, 1, builtins).and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
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

    fn store(&self, addr: Addr) -> Addr {
        match addr {
            Addr::HeapCell(hc) if hc < self.heap_boundary =>
                self.state.heap[hc].as_addr(hc),
            Addr::HeapCell(hc) => {
                let index = hc - self.heap_boundary;
                self.state.ball.stub[index].as_addr(hc)
            },
            Addr::StackCell(fr, sc) =>
                self.state.and_stack[fr][sc].clone(),
            addr => addr
        }
    }

    fn deref(&self, mut addr: Addr) -> Addr {
        loop {
            let value = self.store(addr.clone());

            if value.is_ref() && value != addr {
                addr = value;
                continue;
            }

            return addr;
        };
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
    pub(crate) atom_tbl: TabledData<Atom>,
    pub(super) s: usize,
    pub(super) p: CodePtr,
    pub(super) b: usize,
    pub(super) b0: usize,
    pub(super) e: usize,
    pub(super) num_of_args: usize,
    pub(super) cp: LocalCodePtr,
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
    pub(super) last_call: bool,
    pub(crate) flags: MachineFlags
}

fn call_at_index(machine_st: &mut MachineState, module_name: ClauseName, arity: usize, idx: usize)
{
    machine_st.cp.assign_if_local(machine_st.p.clone() + 1);
    machine_st.num_of_args = arity;
    machine_st.b0 = machine_st.b;
    machine_st.p  = dir_entry!(idx, module_name);
}

fn execute_at_index(machine_st: &mut MachineState, module_name: ClauseName, arity: usize, idx: usize)
{
    machine_st.num_of_args = arity;
    machine_st.b0 = machine_st.b;
    machine_st.p  = dir_entry!(idx, module_name);
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any {
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

    fn context_call(&mut self, machine_st: &mut MachineState, name: ClauseName, arity: usize,
                    idx: CodeIndex, indices: MachineCodeIndices)
                    -> CallResult
    {
        if machine_st.last_call {
            self.try_execute(machine_st, name, arity, idx, indices)
        } else {
            self.try_call(machine_st, name, arity, idx, indices)
        }
    }

    fn try_call<'a>(&mut self, machine_st: &mut MachineState, name: ClauseName, arity: usize,
                    idx: CodeIndex, indices: MachineCodeIndices<'a>)
                    -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Module => {
                let stub = MachineError::functor_stub(name.clone(), arity);
                let module_name = idx.0.borrow().1.clone();
                let h = machine_st.heap.h;

                if let Some(ref idx) = indices.get_code_index((name.clone(), arity), module_name.clone())
                {
                    if let IndexPtr::Index(compiled_tl_index) = idx.0.borrow().0 {
                        call_at_index(machine_st, module_name, arity, compiled_tl_index);
                        return Ok(());
                    }
                }

                let err = MachineError::module_resolution_error(h, module_name, name, arity);
                return Err(machine_st.error_form(err, stub));
            },
            IndexPtr::Undefined => {
                let stub = MachineError::functor_stub(name.clone(), arity);
                let h = machine_st.heap.h;

                return Err(machine_st.error_form(MachineError::existence_error(h, name, arity),
                                                 stub));
            },
            IndexPtr::Index(compiled_tl_index) => {
                let module_name = idx.0.borrow().1.clone();
                call_at_index(machine_st, module_name, arity, compiled_tl_index)
            }
        }

        Ok(())
    }

    fn try_execute<'a>(&mut self, machine_st: &mut MachineState, name: ClauseName,
                       arity: usize, idx: CodeIndex, indices: MachineCodeIndices<'a>)
                       -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Module => {
                let stub = MachineError::functor_stub(name.clone(), arity);
                let module_name = idx.0.borrow().1.clone();
                let h = machine_st.heap.h;

                if let Some(ref idx) = indices.get_code_index((name.clone(), arity), module_name.clone())
                {
                    if let IndexPtr::Index(compiled_tl_index) = idx.0.borrow().0 {
                        execute_at_index(machine_st, module_name, arity, compiled_tl_index);
                        return Ok(());
                    }
                }

                let err = MachineError::module_resolution_error(h, module_name, name, arity);
                return Err(machine_st.error_form(err, stub));
            },
            IndexPtr::Undefined => {
                let stub = MachineError::functor_stub(name.clone(), arity);
                let h = machine_st.heap.h;

                return Err(machine_st.error_form(MachineError::existence_error(h, name, arity),
                                                 stub));
            },
            IndexPtr::Index(compiled_tl_index) => {
                let module_name = idx.0.borrow().1.clone();
                execute_at_index(machine_st, module_name, arity, compiled_tl_index);
            }
        }

        Ok(())
    }

    fn call_builtin<'a>(&mut self, machine_st: &mut MachineState, ct: &BuiltInClauseType,
                        indices: MachineCodeIndices<'a>) //code_dirs: CodeDirs)
                        -> CallResult
    {
        match ct {
            &BuiltInClauseType::AcyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Arg => {
                machine_st.try_arg()?;
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Compare => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();
                let a3 = machine_st[temp_v!(3)].clone();

                let c = Addr::Con(match machine_st.compare_term_test(&a2, &a3) {
                    Ordering::Greater => atom!(">"),
                    Ordering::Equal   => atom!("="),
                    Ordering::Less    => atom!("<")
                });

                machine_st.unify(a1, c);
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::CompareTerm(qt) => {
                match qt {
                    CompareTermQT::Equal =>
                        machine_st.fail = machine_st.structural_eq_test(),
                    CompareTermQT::NotEqual =>
                        machine_st.fail = !machine_st.structural_eq_test(),
                    _ => machine_st.compare_term(qt)
                };

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::CyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = !machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Read => {                
                match machine_st.read(stdin(), &indices.op_dir) {
                    Ok(offset) => {
                        let addr = machine_st[temp_v!(1)].clone();
                        machine_st.unify(addr, Addr::HeapCell(offset));
                    },
                    Err(e) => {
                        let h    = machine_st.heap.h;
                        let stub = MachineError::functor_stub(clause_name!("read"), 1);
                        let err  = MachineError::syntax_error(h, e);
                        let err  = machine_st.error_form(err, stub);

                        return Err(err);
                    }
                };

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Writeq => {
                let output = machine_st.print_term(machine_st[temp_v!(1)].clone(),
                                                   WriteqFormatter {},
                                                   PrinterOutputter::new());

                println!("{}", output.result());
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::DuplicateTerm => {
                machine_st.duplicate_term();
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Eq => {
                machine_st.fail = machine_st.eq_test();
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Ground => {
                machine_st.fail = machine_st.ground_test();
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Functor => {
                machine_st.try_functor()?;
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::NotEq => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();

                machine_st.fail = if let Ordering::Equal = machine_st.compare_term_test(&a1, &a2) {
                    true
                } else {
                    false
                };

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::PartialString => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();

                if let Addr::Con(Constant::String(s)) = a1 {
                    s.set_expandable();
                    machine_st.write_constant_to_var(a2, Constant::String(s));
                } else {
                    machine_st.fail = true;
                }

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Sort => {
                machine_st.check_sort_errors()?;

                let stub = MachineError::functor_stub(clause_name!("sort"), 2);
                let mut list = machine_st.try_from_list(temp_v!(1), stub)?;

                list.sort_unstable_by(|a1, a2| machine_st.compare_term_test(a1, a2));
                machine_st.term_dedup(&mut list);

                let heap_addr = Addr::HeapCell(machine_st.to_list(list.into_iter()));

                let r2 = machine_st[temp_v!(2)].clone();
                machine_st.unify(r2, heap_addr);

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::KeySort => {
                machine_st.check_keysort_errors()?;

                let stub = MachineError::functor_stub(clause_name!("keysort"), 2);
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

                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Is(r, ref at) => {
                let a1 = machine_st[r].clone();
                let a2 = machine_st.get_number(at)?;

                machine_st.unify(a1, Addr::Con(Constant::Number(a2)));
                return_from_clause!(machine_st.last_call, machine_st)
            },
        }
    }

    fn call_n<'a>(&mut self, machine_st: &mut MachineState, arity: usize,
                  indices: MachineCodeIndices<'a>) //code_dirs: CodeDirs)
                  -> CallResult
    {
        if let Some((name, arity)) = machine_st.setup_call_n(arity) {
            let user = clause_name!("user");

            match ClauseType::from(name.clone(), arity, None) {
                ClauseType::CallN => {
                    machine_st.handle_internal_call_n(arity);

                    if machine_st.fail {
                        return Ok(());
                    }

                    machine_st.p = CodePtr::CallN(arity, machine_st.p.local());
                },
                ClauseType::BuiltIn(built_in) => {
                    machine_st.setup_built_in_call(built_in.clone());
                    self.call_builtin(machine_st, &built_in, indices)?;
                },
                ClauseType::Inlined(inlined) =>
                    machine_st.execute_inlined(&inlined),
                ClauseType::Op(..) | ClauseType::Named(..) =>
                    if let Some(idx) = indices.get_code_index((name.clone(), arity), user) {
                        self.context_call(machine_st, name, arity, idx, indices)?;
                    } else {
                        let h = machine_st.heap.h;
                        let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
                        return Err(machine_st.error_form(MachineError::existence_error(h, name, arity),
                                                         stub));
                    },
                ClauseType::System(_) => {
                    let name = Addr::Con(Constant::Atom(name));
                    let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);

                    return Err(machine_st.error_form(MachineError::type_error(ValidType::Callable,
                                                                              name),
                                                     stub));
                }
            };
        }

        Ok(())
    }
}

impl CallPolicy for CWILCallPolicy {
    fn context_call<'a>(&mut self, machine_st: &mut MachineState, name: ClauseName,
                        arity: usize, idx: CodeIndex, indices: MachineCodeIndices<'a>)
                        -> CallResult
    {
        self.prev_policy.context_call(machine_st, name, arity, idx, indices)?;
        self.increment(machine_st)
    }

    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.retry_me_else(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn retry(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.retry(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult
    {
        self.prev_policy.trust_me(machine_st)?;
        self.increment(machine_st)
    }

    fn trust(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult
    {
        self.prev_policy.trust(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn call_builtin<'a>(&mut self, machine_st: &mut MachineState, ct: &BuiltInClauseType,
                        indices: MachineCodeIndices<'a>)
                        -> CallResult
    {
        self.prev_policy.call_builtin(machine_st, ct, indices)?;
        self.increment(machine_st)
    }

    fn call_n<'a>(&mut self, machine_st: &mut MachineState, arity: usize, indices: MachineCodeIndices<'a>)
                  -> CallResult
    {
        self.prev_policy.call_n(machine_st, arity, indices)?;
        self.increment(machine_st)
    }
}

downcast!(CallPolicy);

pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

pub(crate) struct CWILCallPolicy {
    pub(crate) prev_policy: Box<CallPolicy>,
    count:  BigUint,
    limits: Vec<(BigUint, usize)>,
    inference_limit_exceeded: bool
}

impl CWILCallPolicy {
    pub(crate) fn new_in_place(policy: &mut Box<CallPolicy>)
    {
        let mut prev_policy: Box<CallPolicy> = Box::new(DefaultCallPolicy {});
        swap(&mut prev_policy, policy);

        let new_policy = CWILCallPolicy { prev_policy,
                                          count:  BigUint::zero(),
                                          limits: vec![],
                                          inference_limit_exceeded: false };
        *policy = Box::new(new_policy);
    }

    fn increment(&mut self, machine_st: &MachineState) -> CallResult {
        if self.inference_limit_exceeded || machine_st.ball.stub.len() > 0 {
            return Ok(());
        }

        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == *limit {
                self.inference_limit_exceeded = true;
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

pub(crate) trait CutPolicy: Any {
    // returns true iff we fail or cut redirected the MachineState's p itself
    fn cut(&mut self, &mut MachineState, RegType) -> bool;
}

downcast!(CutPolicy);

fn cut_body(machine_st: &mut MachineState, addr: Addr) -> bool {
    let b = machine_st.b;

    if let Addr::Con(Constant::Usize(b0)) = addr {
        if b > b0 {
            machine_st.b = b0;
            machine_st.tidy_trail();
            machine_st.or_stack.truncate(machine_st.b);
        }
    } else {
        machine_st.fail = true;
        return true;
    }

    false
}

pub(crate) struct DefaultCutPolicy {}

pub(super) fn deref_cut(machine_st: &mut MachineState, r: RegType) {
    let addr = machine_st.store(machine_st.deref(machine_st[r].clone()));
    cut_body(machine_st, addr);
}

impl CutPolicy for DefaultCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool {
        let addr = machine_st[r].clone();
        cut_body(machine_st, addr)
    }
}

pub(crate) struct SCCCutPolicy {
    // locations of cleaners, cut points, the previous block
    cont_pts: Vec<(Addr, usize, usize)>,
    r_c_w_h:  usize,
    r_c_wo_h: usize
}

impl SCCCutPolicy {
    pub(crate) fn new(r_c_w_h: usize, r_c_wo_h: usize) -> Self {
        SCCCutPolicy { cont_pts: vec![], r_c_w_h, r_c_wo_h }
    }

    pub(crate) fn out_of_cont_pts(&self) -> bool {
        self.cont_pts.is_empty()
    }

    pub(crate) fn push_cont_pt(&mut self, addr: Addr, b: usize, prev_b: usize) {
        self.cont_pts.push((addr, b, prev_b));
    }

    pub(crate) fn pop_cont_pt(&mut self) -> Option<(Addr, usize, usize)> {
        self.cont_pts.pop()
    }

    fn run_cleaners(&self, machine_st: &mut MachineState) -> bool {
        if let Some(&(_, b_cutoff, prev_block)) = self.cont_pts.last() {
            if machine_st.b < b_cutoff {
                let builtins = clause_name!("builtins");
                let (idx, arity) = if machine_st.block < prev_block {
                    (self.r_c_w_h, 0)
                } else {
                    machine_st[temp_v!(1)] = Addr::Con(Constant::Usize(b_cutoff));
                    (self.r_c_wo_h, 1)
                };

                if machine_st.last_call {
                    execute_at_index(machine_st, builtins, arity, idx);
                } else {
                    call_at_index(machine_st, builtins, arity, idx);
                }

                return true;
            }
        }

        false
    }
}

impl CutPolicy for SCCCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool {
        let b = machine_st.b;

        if let Addr::Con(Constant::Usize(b0)) = machine_st[r].clone() {
            if b > b0 {
                machine_st.b = b0;
                machine_st.tidy_trail();
                machine_st.or_stack.truncate(machine_st.b);
            }
        } else {
            machine_st.fail = true;
            return true;
        }

        self.run_cleaners(machine_st)
    }
}
