use prolog_parser::ast::*;
use prolog_parser::string_list::*;

use prolog::clause_types::*;
use prolog::forms::*;
use prolog::machine::and_stack::*;
use prolog::machine::attributed_variables::*;
use prolog::machine::copier::*;
use prolog::machine::heap::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::modules::*;
use prolog::machine::or_stack::*;
use prolog::num::{BigInt, BigUint, Zero, One};
use prolog::read::{PrologStream, readline};

use downcast::Any;

use std::cmp::Ordering;
use std::io::{Write, stdout};
use std::mem;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

pub(super) struct Ball {
    pub(super) boundary: usize,   // ball.0
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

    pub(super) fn take(&mut self) -> Ball {
        let boundary = self.boundary;
        self.boundary = 0;
        
        Ball {
            boundary,
            stub: mem::replace(&mut self.stub, vec![])
        }
    }
}

pub(super) struct CopyTerm<'a> {
    state: &'a mut MachineState
}

impl<'a> CopyTerm<'a> {
    pub(super) fn new(state: &'a mut MachineState) -> Self {
        CopyTerm { state: state }
    }
}

impl<'a> Index<usize> for CopyTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        &self.state.heap[index]
    }
}

impl<'a> IndexMut<usize> for CopyTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.state.heap[index]
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for CopyTerm<'a> {
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

pub(super) struct CopyBallTerm<'a> {
    and_stack: &'a mut AndStack,
    heap: &'a mut Heap,
    heap_boundary: usize,
    stub: &'a mut MachineStub,
}

impl<'a> CopyBallTerm<'a> {
    pub(super) fn new(and_stack: &'a mut AndStack, heap: &'a mut Heap, stub: &'a mut MachineStub) -> Self
    {
        let hb = heap.len();
        CopyBallTerm { and_stack, heap, heap_boundary: hb, stub }
    }
}

impl<'a> Index<usize> for CopyBallTerm<'a> {
    type Output = HeapCellValue;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.heap_boundary {
            &self.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &self.stub[index]
        }
    }
}

impl<'a> IndexMut<usize> for CopyBallTerm<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.heap_boundary {
            &mut self.heap[index]
        } else {
            let index = index - self.heap_boundary;
            &mut self.stub[index]
        }
    }
}

// the ordinary, heap term copier, used by duplicate_term.
impl<'a> CopierTarget for CopyBallTerm<'a> {
    fn threshold(&self) -> usize {
        self.heap_boundary + self.stub.len()
    }

    fn push(&mut self, value: HeapCellValue) {
        self.stub.push(value);
    }

    fn store(&self, addr: Addr) -> Addr {
        match addr {
            Addr::HeapCell(h) | Addr::AttrVar(h) if h < self.heap_boundary =>
                self.heap[h].as_addr(h),
            Addr::HeapCell(h) | Addr::AttrVar(h) => {
                let index = h - self.heap_boundary;
                self.stub[index].as_addr(h)
            },
            Addr::StackCell(fr, sc) =>
                self.and_stack[fr][sc].clone(),
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
        self.and_stack
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

pub type Registers = Vec<Addr>;

#[derive(Clone, Copy)]
pub(super) enum MachineMode {
    Read,
    Write
}

pub struct MachineState {
    pub(super) s: usize,
    pub(super) p: CodePtr,
    pub(super) b: usize,
    pub(super) b0: usize,
    pub(super) e: usize,
    pub(super) num_of_args: usize,
    pub(super) cp: LocalCodePtr,
    pub(super) attr_var_init: AttrVarInitializer,
    pub(super) fail: bool,
    pub(crate) heap: Heap,
    pub(super) mode: MachineMode,
    pub(crate) and_stack: AndStack,
    pub(super) or_stack: OrStack,
    pub(super) registers: Registers,
    pub(super) trail: Vec<TrailRef>,
    pub(super) pstr_trail: Vec<(usize, StringList, usize)>, // b, String, trunc_pt
    pub(super) pstr_tr: usize,
    pub(super) tr: usize,
    pub(super) hb: usize,
    pub(super) block: usize, // an offset into the OR stack.
    pub(super) ball: Ball,
    pub(super) lifted_heap: Vec<HeapCellValue>,
    pub(super) interms: Vec<Number>, // intermediate numbers.
    pub(super) last_call: bool,
    pub(crate) flags: MachineFlags
}

impl MachineState {    
    fn call_at_index(&mut self, arity: usize, p: usize)
    {
        self.cp.assign_if_local(self.p.clone() + 1);
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = dir_entry!(p);
    }

    pub(super)
    fn execute_at_index(&mut self, arity: usize, p: usize)
    {
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = dir_entry!(p);
    }

    pub(super)
    fn module_lookup(&mut self, indices: &IndexStore, key: PredicateKey, module_name: ClauseName,
                     last_call: bool)
                     -> CallResult
    {
        let (name, arity) = key;

        if let Some(ref idx) = indices.get_code_index((name.clone(), arity), module_name.clone())
        {
            if let IndexPtr::Index(compiled_tl_index) = idx.0.borrow().0 {
                if last_call {
                    self.execute_at_index(arity, compiled_tl_index);
                } else {
                    self.call_at_index(arity, compiled_tl_index);
                }

                return Ok(());
            }
        }

        let h = self.heap.h;
        let stub = MachineError::functor_stub(name.clone(), arity);
        let err = MachineError::module_resolution_error(h, module_name, name, arity);

        return Err(self.error_form(err, stub));
    }
}

fn try_in_situ_lookup(name: ClauseName, arity: usize, indices: &IndexStore) -> Option<usize>
{
    match indices.in_situ_code_dir.get(&(name.clone(), arity)) {
        Some(p) => Some(*p),
        None => match indices.code_dir.get(&(name, arity)) {
            Some(ref idx) => if let &IndexPtr::Index(p) = &idx.0.borrow().0 {
                Some(p)
            } else {
                None
            },
            _ => None
        }
    }
}

fn try_in_situ(machine_st: &mut MachineState, name: ClauseName, arity: usize,
               indices: &IndexStore, last_call: bool)
               -> CallResult
{
    if let Some(p) = try_in_situ_lookup(name.clone(), arity, indices) {
        if last_call {
            machine_st.execute_at_index(arity, p);
        } else {
            machine_st.call_at_index(arity, p);
        }

        machine_st.p = in_situ_dir_entry!(p);
        Ok(())
    } else {
        let stub = MachineError::functor_stub(name.clone(), arity);
        let h = machine_st.heap.h;

        Err(machine_st.error_form(MachineError::existence_error(h, name, arity),
                                  stub))
    }
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

        let old_pstr_tr  = machine_st.or_stack[b].pstr_tr;
        let curr_pstr_tr = machine_st.pstr_tr;

        machine_st.unwind_pstr_trail(old_pstr_tr, curr_pstr_tr);
        machine_st.pstr_tr = machine_st.or_stack[b].pstr_tr;

        machine_st.pstr_trail.truncate(machine_st.pstr_tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);

        let attr_var_init_b = machine_st.or_stack[b].attr_var_init_b;
        machine_st.attr_var_init.attr_var_queue.truncate(attr_var_init_b);

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

        let old_pstr_tr  = machine_st.or_stack[b].pstr_tr;
        let curr_pstr_tr = machine_st.pstr_tr;

        machine_st.unwind_pstr_trail(old_pstr_tr, curr_pstr_tr);
        machine_st.pstr_tr = machine_st.or_stack[b].pstr_tr;

        machine_st.pstr_trail.truncate(machine_st.pstr_tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);

        let attr_var_init_b = machine_st.or_stack[b].attr_var_init_b;
        machine_st.attr_var_init.attr_var_queue.truncate(attr_var_init_b);

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

        let old_pstr_tr  = machine_st.or_stack[b].pstr_tr;
        let curr_pstr_tr = machine_st.pstr_tr;

        machine_st.unwind_pstr_trail(old_pstr_tr, curr_pstr_tr);
        machine_st.pstr_tr = machine_st.or_stack[b].pstr_tr;

        machine_st.pstr_trail.truncate(machine_st.pstr_tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);

        let attr_var_init_b = machine_st.or_stack[b].attr_var_init_b;
        machine_st.attr_var_init.attr_var_queue.truncate(attr_var_init_b);

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

        let old_pstr_tr  = machine_st.or_stack[b].pstr_tr;
        let curr_pstr_tr = machine_st.pstr_tr;

        machine_st.unwind_pstr_trail(old_pstr_tr, curr_pstr_tr);
        machine_st.pstr_tr = machine_st.or_stack[b].pstr_tr;

        machine_st.pstr_trail.truncate(machine_st.pstr_tr);

        machine_st.heap.truncate(machine_st.or_stack[b].h);

        let attr_var_init_b = machine_st.or_stack[b].attr_var_init_b;
        machine_st.attr_var_init.attr_var_queue.truncate(attr_var_init_b);

        machine_st.b = machine_st.or_stack[b].b;
        machine_st.or_stack.truncate(machine_st.b);

        machine_st.hb = machine_st.heap.h;
        machine_st.p += 1;

        Ok(())
    }

    fn context_call(&mut self, machine_st: &mut MachineState, name: ClauseName,
                    arity: usize, idx: CodeIndex, indices: &mut IndexStore)
                    -> CallResult
    {
        if machine_st.last_call {
            self.try_execute(machine_st, name, arity, idx, indices)
        } else {
            self.try_call(machine_st, name, arity, idx, indices)
        }
    }

    fn try_call(&mut self, machine_st: &mut MachineState, name: ClauseName, arity: usize,
                idx: CodeIndex, indices: &IndexStore)
                -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Undefined =>
                return try_in_situ(machine_st, name, arity, indices, false),
            IndexPtr::Index(compiled_tl_index) =>
                machine_st.call_at_index(arity, compiled_tl_index)
        }

        Ok(())
    }

    fn try_execute(&mut self, machine_st: &mut MachineState, name: ClauseName,
                   arity: usize, idx: CodeIndex, indices: &IndexStore)
                   -> CallResult
    {
        match idx.0.borrow().0 {
            IndexPtr::Undefined =>
                return try_in_situ(machine_st, name, arity, indices, true),
            IndexPtr::Index(compiled_tl_index) =>
                machine_st.execute_at_index(arity, compiled_tl_index)
        }

        Ok(())
    }

    fn call_builtin(&mut self, machine_st: &mut MachineState, ct: &BuiltInClauseType,
                    indices: &mut IndexStore, parsing_stream: &mut PrologStream)
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

                let c = match machine_st.compare_term_test(&a2, &a3) {
                    Ordering::Greater => Addr::Con(Constant::Atom(clause_name!(">"),
                                                                  Some(SharedOpDesc::new(700, XFX)))),
                    Ordering::Equal   => Addr::Con(Constant::Atom(clause_name!("="),
                                                                  Some(SharedOpDesc::new(700, XFX)))),
                    Ordering::Less    => Addr::Con(Constant::Atom(clause_name!("<"),
                                                                  Some(SharedOpDesc::new(700, XFX))))
                };

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
            &BuiltInClauseType::Nl => {
                let mut stdout = stdout();

                write!(stdout, "\n\r").unwrap();
                stdout.flush().unwrap();
                return_from_clause!(machine_st.last_call, machine_st)
            },
            &BuiltInClauseType::Read => {
                readline::toggle_prompt(false);
                
                match machine_st.read(parsing_stream, indices.atom_tbl.clone(), &indices.op_dir) {
                    Ok(offset) => {
                        let addr = machine_st[temp_v!(1)].clone();
                        machine_st.unify(addr, Addr::HeapCell(offset.heap_loc));
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
            &BuiltInClauseType::CopyTerm => {
                machine_st.copy_term();
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
                    s.set_expandable(true);
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

                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(list.into_iter()));

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
                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(key_pairs));

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

    fn compile_hook(&mut self, machine_st: &mut MachineState, hook: &CompileTimeHook) -> CallResult
    {
        machine_st.cp = LocalCodePtr::TopLevel(0, 0);

        machine_st.num_of_args = hook.arity();
        machine_st.b0 = machine_st.b;

        machine_st.p = match hook {
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion =>
                CodePtr::Local(LocalCodePtr::UserTermExpansion(0)),
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion =>
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(0))
        };

        Ok(())
    }

    fn call_n(&mut self, machine_st: &mut MachineState, arity: usize, indices: &mut IndexStore,
              parsing_stream: &mut PrologStream)
              -> CallResult
    {
        if let Some((name, arity)) = machine_st.setup_call_n(arity) {
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
                    self.call_builtin(machine_st, &built_in, indices, parsing_stream)?;
                },
                ClauseType::Inlined(inlined) => {
                    machine_st.execute_inlined(&inlined);

                    if machine_st.last_call {
                        machine_st.p = CodePtr::Local(machine_st.cp);
                    }
                },
                ClauseType::Op(..) | ClauseType::Named(..) => {
                    let module = name.owning_module();

                    if let Some(idx) = indices.get_code_index((name.clone(), arity), module) {
                        self.context_call(machine_st, name, arity, idx, indices)?;
                    } else {
                        let h = machine_st.heap.h;
                        let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
                        return Err(machine_st.error_form(MachineError::existence_error(h, name, arity),
                                                         stub));
                    }
                },
                ClauseType::Hook(_) | ClauseType::System(_) => {
                    let name = Addr::Con(Constant::Atom(name, None));
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
    fn context_call(&mut self, machine_st: &mut MachineState, name: ClauseName,
                    arity: usize, idx: CodeIndex, indices: &mut IndexStore)
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

    fn call_builtin(&mut self, machine_st: &mut MachineState, ct: &BuiltInClauseType,
                    indices: &mut IndexStore, parsing_stream: &mut PrologStream)
                    -> CallResult
    {
        self.prev_policy.call_builtin(machine_st, ct, indices, parsing_stream)?;
        self.increment(machine_st)
    }

    fn call_n(&mut self, machine_st: &mut MachineState, arity: usize, indices: &mut IndexStore,
              parsing_stream: &mut PrologStream)
              -> CallResult
    {
        self.prev_policy.call_n(machine_st, arity, indices, parsing_stream)?;
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
        mem::swap(&mut prev_policy, policy);

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
        mem::swap(&mut self.prev_policy, &mut new_inner);
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
            machine_st.tidy_pstr_trail();
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
                let (idx, arity) = if machine_st.block < prev_block {
                    (self.r_c_w_h, 0)
                } else {
                    machine_st[temp_v!(1)] = Addr::Con(Constant::Usize(b_cutoff));
                    (self.r_c_wo_h, 1)
                };

                if machine_st.last_call {
                    machine_st.execute_at_index(arity, idx);
                } else {
                    machine_st.call_at_index(arity, idx);
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
                machine_st.tidy_pstr_trail();
                machine_st.or_stack.truncate(machine_st.b);
            }
        } else {
            machine_st.fail = true;
            return true;
        }

        self.run_cleaners(machine_st)
    }
}
