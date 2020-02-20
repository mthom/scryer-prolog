use prolog_parser::ast::*;

use crate::prolog::clause_types::*;
use crate::prolog::forms::*;
use crate::prolog::machine::attributed_variables::*;
use crate::prolog::machine::copier::*;
use crate::prolog::machine::heap::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::modules::*;
use crate::prolog::machine::stack::*;
use crate::prolog::read::PrologStream;
use crate::prolog::rug::Integer;

use downcast::Any;

use std::cmp::Ordering;
use std::io::{stdout, Write};
use std::mem;
use std::ops::{Index, IndexMut};

pub struct Ball {
    pub(super) boundary: usize,
    pub(super) stub: Heap,
}

impl Ball {
    pub(super)
    fn new() -> Self {
        Ball {
            boundary: 0,
            stub: Heap::new(),
        }
    }

    pub(super)
    fn reset(&mut self) {
        self.boundary = 0;
        self.stub.clear();
    }

    pub(super)
    fn take(&mut self) -> Ball {
        let boundary = self.boundary;
        self.boundary = 0;

        Ball {
            boundary,
            stub: self.stub.take(),
        }
    }

    pub(super)
    fn copy_and_align(&self, h: usize) -> Heap {
        let diff = self.boundary as i64 - h as i64;
        let mut stub = Heap::new();

        for heap_value in self.stub.iter_from(0) {
            stub.push(match heap_value {
                HeapCellValue::Addr(ref addr) => HeapCellValue::Addr(addr.clone() - diff),
                HeapCellValue::PartialString(ref pstr) => {
                    let mut new_pstr = pstr.clone();
                    new_pstr.tail = pstr.tail.clone() - diff;
                    HeapCellValue::PartialString(new_pstr)
                }
                heap_value => heap_value.clone(),
            });
        }

        stub
    }
}

pub(super) struct CopyTerm<'a> {
    state: &'a mut MachineState,
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
        self.state.heap.h()
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

    fn stack(&mut self) -> &mut Stack {
        &mut self.state.stack
    }
}

pub(super) struct CopyBallTerm<'a> {
    stack: &'a mut Stack,
    heap: &'a mut Heap,
    heap_boundary: usize,
    stub: &'a mut Heap,
}

impl<'a> CopyBallTerm<'a> {
    pub(super) fn new(
        stack: &'a mut Stack,
        heap: &'a mut Heap,
        stub: &'a mut Heap,
    ) -> Self {
        let hb = heap.h();

        CopyBallTerm {
            stack,
            heap,
            heap_boundary: hb,
            stub,
        }
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
        self.heap_boundary + self.stub.h()
    }

    fn push(&mut self, value: HeapCellValue) {
        self.stub.push(value);
    }

    fn store(&self, addr: Addr) -> Addr {
        match addr {
            Addr::HeapCell(h) | Addr::AttrVar(h) if h < self.heap_boundary => {
                self.heap[h].as_addr(h)
            }
            Addr::HeapCell(h) | Addr::AttrVar(h) => {
                let index = h - self.heap_boundary;
                self.stub[index].as_addr(h)
            }
            Addr::StackCell(fr, sc) => self.stack.index_and_frame(fr)[sc].clone(),
            addr => addr,
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
        }
    }

    fn stack(&mut self) -> &mut Stack {
        self.stack
    }
}

impl Index<RegType> for MachineState {
    type Output = Addr;

    fn index(&self, reg: RegType) -> &Self::Output {
        match reg {
            RegType::Temp(temp) => &self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &self.stack.index_and_frame(e)[perm]
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
                &mut self.stack.index_and_frame_mut(e)[perm]
            }
        }
    }
}

pub type Registers = Vec<Addr>;

#[derive(Clone, Copy)]
pub(super) enum MachineMode {
    Read,
    Write,
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
    pub(crate) stack: Stack,
    pub(super) registers: Registers,
    pub(super) trail: Vec<TrailRef>,
    pub(super) tr: usize,
    pub(super) hb: usize,
    pub(super) block: usize, // an offset into the OR stack.
    pub(super) ball: Ball,
    pub(super) lifted_heap: Heap,
    pub(super) interms: Vec<Number>, // intermediate numbers.
    pub(super) last_call: bool,
    pub(crate) heap_locs: HeapVarDict,
    pub(crate) flags: MachineFlags,
    pub(crate) at_end_of_expansion: bool
}

impl MachineState {
    pub(super)
    fn try_char_list(&self, addrs: Vec<Addr>) -> Result<String, MachineError> {
        let mut chars = String::new();
        let mut iter = addrs.iter();

        while let Some(addr) = iter.next() {
            match addr {
                &Addr::Con(Constant::String(n, ref s))
                    if self.flags.double_quotes.is_chars() => {
                        if s.len() < n {
                            chars += &s[n ..];
                        }

                        if iter.next().is_some() {
                            return Err(MachineError::type_error(ValidType::Character, addr.clone()));
                        }
                    }
                &Addr::Con(Constant::Char(c)) => {
                    chars.push(c);
                }
                &Addr::Con(Constant::Atom(ref name, _))
                    if name.as_str().len() == 1 => {
                        chars += name.as_str();
                    }
                _ => {
                    return Err(
                        MachineError::type_error(ValidType::Character, addr.clone())
                    );
                }
            }
        }

        Ok(chars)
    }

    pub(super)
    fn call_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.cp.assign_if_local(self.p.clone() + 1);
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub(super)
    fn execute_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub(super)
    fn module_lookup(
        &mut self,
        indices: &IndexStore,
        key: PredicateKey,
        module_name: ClauseName,
        last_call: bool,
    ) -> CallResult {
        let (name, arity) = key;

        if let Some(ref idx) = indices.get_code_index((name.clone(), arity), module_name.clone()) {
            match idx.0.borrow().0 {
                IndexPtr::Index(compiled_tl_index) => {
                    if last_call {
                        self.execute_at_index(arity, dir_entry!(compiled_tl_index));
                    } else {
                        self.call_at_index(arity, dir_entry!(compiled_tl_index));
                    }

                    return Ok(());
                }
                IndexPtr::DynamicUndefined => {
                    self.fail = true;
                    return Ok(());
                }
                IndexPtr::UserTermExpansion => {
                    if last_call {
                        self.execute_at_index(arity, LocalCodePtr::UserTermExpansion(0));
                    } else {
                        self.call_at_index(arity, LocalCodePtr::UserTermExpansion(0));
                    }

                    return Ok(());
                }
                IndexPtr::UserGoalExpansion => {
                    if last_call {
                        self.execute_at_index(arity, LocalCodePtr::UserGoalExpansion(0));
                    } else {
                        self.call_at_index(arity, LocalCodePtr::UserGoalExpansion(0));
                    }

                    return Ok(());
                }
                IndexPtr::InSituDirEntry(p) => {
                    if last_call {
                        self.execute_at_index(arity, LocalCodePtr::InSituDirEntry(p));
                    } else {
                        self.call_at_index(arity, LocalCodePtr::InSituDirEntry(p));
                    }

                    return Ok(());
                }
                _ => {}
            }
        }

        let h = self.heap.h();
        let stub = MachineError::functor_stub(name.clone(), arity);
        let err = MachineError::module_resolution_error(h, module_name, name, arity);

        return Err(self.error_form(err, stub));
    }
}

fn try_in_situ_lookup(name: ClauseName, arity: usize, indices: &IndexStore) -> Option<usize>
{
    match indices.in_situ_code_dir.get(&(name.clone(), arity)) {
        Some(p) => Some(*p),
        None =>
            match indices.code_dir.get(&(name, arity)) {
                Some(ref idx) => {
                    if let IndexPtr::Index(p) = idx.0.borrow().0 {
                        Some(p)
                    } else {
                        None
                    }
                }
                _ => None,
            },
    }
}

fn try_in_situ(
    machine_st: &mut MachineState,
    name: ClauseName,
    arity: usize,
    indices: &IndexStore,
    last_call: bool,
) -> CallResult {
    if let Some(p) = try_in_situ_lookup(name.clone(), arity, indices) {
        if last_call {
            machine_st.execute_at_index(arity, LocalCodePtr::DirEntry(p));
        } else {
            machine_st.call_at_index(arity, LocalCodePtr::DirEntry(p));
        }

        machine_st.p = in_situ_dir_entry!(p);
        Ok(())
    } else {
        let stub = MachineError::functor_stub(name.clone(), arity);
        let h = machine_st.heap.h();
        let key = ExistenceError::Procedure(name, arity);

        Err(machine_st.error_form(MachineError::existence_error(h, key), stub))
    }
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any {
    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1].clone();
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        machine_st.stack.index_or_frame_mut(b).prelude.bp = machine_st.p.local() + offset;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_queue_b;
        let attr_var_init_bindings_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_bindings_b;

        machine_st.attr_var_init.backtrack(
            attr_var_init_queue_b,
            attr_var_init_bindings_b,
        );

        machine_st.hb = machine_st.heap.h();
        machine_st.p += 1;

        Ok(())
    }

    fn retry(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1].clone();
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        machine_st.stack.index_or_frame_mut(b).prelude.bp = machine_st.p.local() + 1;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_queue_b;
        let attr_var_init_bindings_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_bindings_b;

        machine_st.attr_var_init.backtrack(attr_var_init_queue_b, attr_var_init_bindings_b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p += offset;

        Ok(())
    }

    fn trust(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1].clone();
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_queue_b;
        let attr_var_init_bindings_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_bindings_b;

        machine_st.attr_var_init.backtrack(
            attr_var_init_queue_b,
            attr_var_init_bindings_b,
        );

        machine_st.stack.truncate(machine_st.b);
        machine_st.b = machine_st.stack.index_or_frame(b).prelude.b;

        machine_st.hb = machine_st.heap.h();
        machine_st.p += offset;

        Ok(())
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1].clone();
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_queue_b;
        let attr_var_init_bindings_b =
            machine_st.stack.index_or_frame(b).prelude.attr_var_init_bindings_b;

        machine_st.attr_var_init.backtrack(
            attr_var_init_queue_b,
            attr_var_init_bindings_b,
        );

        machine_st.stack.truncate(machine_st.b);
        machine_st.b = machine_st.stack.index_or_frame(b).prelude.b;

        machine_st.hb = machine_st.heap.h();
        machine_st.p += 1;

        Ok(())
    }

    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
        arity: usize,
        idx: CodeIndex,
        indices: &mut IndexStore,
    ) -> CallResult {
        if machine_st.last_call {
            self.try_execute(machine_st, name, arity, idx, indices)
        } else {
            self.try_call(machine_st, name, arity, idx, indices)
        }
    }

    fn try_call(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
        arity: usize,
        idx: CodeIndex,
        indices: &IndexStore,
    ) -> CallResult {
        match idx.0.borrow().0 {
            IndexPtr::DynamicUndefined => {
                machine_st.fail = true;
            }
            IndexPtr::Undefined => {
                return try_in_situ(machine_st, name, arity, indices, false);
            }
            IndexPtr::Index(compiled_tl_index) => {
                machine_st.call_at_index(arity, LocalCodePtr::DirEntry(compiled_tl_index))
            }
            IndexPtr::UserTermExpansion => {
                machine_st.call_at_index(arity, LocalCodePtr::UserTermExpansion(0));
            }
            IndexPtr::UserGoalExpansion => {
                machine_st.call_at_index(arity, LocalCodePtr::UserGoalExpansion(0));
            }
            IndexPtr::InSituDirEntry(p) => {
                machine_st.call_at_index(arity, LocalCodePtr::InSituDirEntry(p));
            }
        }

        Ok(())
    }

    fn try_execute(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
        arity: usize,
        idx: CodeIndex,
        indices: &IndexStore,
    ) -> CallResult {
        match idx.0.borrow().0 {
            IndexPtr::DynamicUndefined =>
                machine_st.fail = true,
            IndexPtr::Undefined =>
                return try_in_situ(machine_st, name, arity, indices, true),
            IndexPtr::Index(compiled_tl_index) => {
                machine_st.execute_at_index(arity, dir_entry!(compiled_tl_index))
            }
            IndexPtr::UserTermExpansion => {
                machine_st.execute_at_index(arity, LocalCodePtr::UserTermExpansion(0));
            }
            IndexPtr::UserGoalExpansion => {
                machine_st.execute_at_index(arity, LocalCodePtr::UserGoalExpansion(0));
            }
            IndexPtr::InSituDirEntry(p) => {
                machine_st.execute_at_index(arity, LocalCodePtr::InSituDirEntry(p));
            }
        }

        Ok(())
    }

    fn call_builtin(
        &mut self,
        machine_st: &mut MachineState,
        ct: &BuiltInClauseType,
        indices: &mut IndexStore,
        parsing_stream: &mut PrologStream,
    ) -> CallResult {
        match ct {
            &BuiltInClauseType::AcyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Arg => {
                machine_st.try_arg()?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Compare => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();
                let a3 = machine_st[temp_v!(3)].clone();

                let c = match machine_st.compare_term_test(&a2, &a3) {
                    Ordering::Greater => {
                        let spec = fetch_atom_op_spec(clause_name!(">"), None, &indices.op_dir);
                        Addr::Con(Constant::Atom(clause_name!(">"), spec))
                    }
                    Ordering::Equal => {
                        let spec = fetch_atom_op_spec(clause_name!("="), None, &indices.op_dir);
                        Addr::Con(Constant::Atom(clause_name!("="), spec))
                    }
                    Ordering::Less => {
                        let spec = fetch_atom_op_spec(clause_name!("<"), None, &indices.op_dir);
                        Addr::Con(Constant::Atom(clause_name!("<"), spec))
                    }
                };

                machine_st.unify(a1, c);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CompareTerm(qt) => {
                machine_st.compare_term(qt);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CyclicTerm => {
                let addr = machine_st[temp_v!(1)].clone();
                machine_st.fail = !machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Nl => {
                let mut stdout = stdout();

                write!(stdout, "\n").unwrap();
                stdout.flush().unwrap();
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Read => {
                match machine_st.read(parsing_stream, indices.atom_tbl.clone(), &indices.op_dir) {
                    Ok(offset) => {
                        let addr = machine_st[temp_v!(1)].clone();
                        machine_st.unify(addr, Addr::HeapCell(offset.heap_loc));
                    }
                    Err(e) => {
                        let h = machine_st.heap.h();
                        let stub = MachineError::functor_stub(clause_name!("read"), 1);
                        let err = MachineError::syntax_error(h, e);
                        let err = machine_st.error_form(err, stub);

                        return Err(err);
                    }
                };

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CopyTerm => {
                machine_st.copy_term(AttrVarPolicy::DeepCopy);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Eq => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();

                machine_st.fail = machine_st.eq_test(a1, a2);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Ground => {
                machine_st.fail = machine_st.ground_test();
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Functor => {
                machine_st.try_functor(&indices)?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::NotEq => {
                let a1 = machine_st[temp_v!(1)].clone();
                let a2 = machine_st[temp_v!(2)].clone();

                machine_st.fail = if let Ordering::Equal = machine_st.compare_term_test(&a1, &a2) {
                    true
                } else {
                    false
                };

                return_from_clause!(machine_st.last_call, machine_st)
            }
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
            }
            &BuiltInClauseType::KeySort => {
                machine_st.check_keysort_errors()?;

                let stub = MachineError::functor_stub(clause_name!("keysort"), 2);
                let list = machine_st.try_from_list(temp_v!(1), stub)?;
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
            }
            &BuiltInClauseType::Is(r, ref at) => {
                let a1 = machine_st[r].clone();
                let a2 = machine_st.get_number(at)?;

                machine_st.unify(a1, Addr::Con(a2.to_constant()));
                return_from_clause!(machine_st.last_call, machine_st)
            }
        }
    }

    fn compile_hook(
        &mut self,
        machine_st: &mut MachineState,
        hook: &CompileTimeHook,
    ) -> CallResult {
        machine_st.cp = LocalCodePtr::TopLevel(0, 0);

        machine_st.num_of_args = hook.arity();
        machine_st.b0 = machine_st.b;

        machine_st.p = match hook {
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                CodePtr::Local(LocalCodePtr::UserTermExpansion(0))
            }
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(0))
            }
        };

        Ok(())
    }

    fn call_n(
        &mut self,
        machine_st: &mut MachineState,
        arity: usize,
        indices: &mut IndexStore,
        parsing_stream: &mut PrologStream,
    ) -> CallResult {
        if let Some((name, arity)) = machine_st.setup_call_n(arity) {
            match ClauseType::from(name.clone(), arity, None) {
                ClauseType::BuiltIn(built_in) => {
                    machine_st.setup_built_in_call(built_in.clone());
                    self.call_builtin(machine_st, &built_in, indices, parsing_stream)?;
                }
                ClauseType::CallN => {
                    machine_st.handle_internal_call_n(arity);

                    if machine_st.fail {
                        return Ok(());
                    }

                    machine_st.p = CodePtr::CallN(arity, machine_st.p.local(), machine_st.last_call);
                }
                ClauseType::Inlined(inlined) => {
                    machine_st.execute_inlined(&inlined);

                    if machine_st.last_call {
                        machine_st.p = CodePtr::Local(machine_st.cp);
                    }
                }
                ClauseType::Op(..) | ClauseType::Named(..) => {
                    let module = name.owning_module();

                    if let Some(idx) = indices.get_code_index((name.clone(), arity), module) {
                        self.context_call(machine_st, name, arity, idx, indices)?;
                    } else {
                        try_in_situ(machine_st, name, arity, indices, machine_st.last_call)?;
                    }
                }
                ClauseType::Hook(_) | ClauseType::System(_) => {
                    let name = Addr::Con(Constant::Atom(name, None));
                    let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);

                    return Err(machine_st
                               .error_form(MachineError::type_error(ValidType::Callable, name), stub));
                }
            };
        }

        Ok(())
    }
}

impl CallPolicy for CWILCallPolicy {
    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
        arity: usize,
        idx: CodeIndex,
        indices: &mut IndexStore,
    ) -> CallResult {
        self.prev_policy
            .context_call(machine_st, name, arity, idx, indices)?;
        self.increment(machine_st)
    }

    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        self.prev_policy.retry_me_else(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn retry(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        self.prev_policy.retry(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult {
        self.prev_policy.trust_me(machine_st)?;
        self.increment(machine_st)
    }

    fn trust(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        self.prev_policy.trust(machine_st, offset)?;
        self.increment(machine_st)
    }

    fn call_builtin(
        &mut self,
        machine_st: &mut MachineState,
        ct: &BuiltInClauseType,
        indices: &mut IndexStore,
        parsing_stream: &mut PrologStream,
    ) -> CallResult {
        self.prev_policy
            .call_builtin(machine_st, ct, indices, parsing_stream)?;
        self.increment(machine_st)
    }

    fn call_n(
        &mut self,
        machine_st: &mut MachineState,
        arity: usize,
        indices: &mut IndexStore,
        parsing_stream: &mut PrologStream,
    ) -> CallResult {
        self.prev_policy
            .call_n(machine_st, arity, indices, parsing_stream)?;
        self.increment(machine_st)
    }
}

downcast!(dyn CallPolicy);

pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

pub(crate) struct CWILCallPolicy {
    pub(crate) prev_policy: Box<dyn CallPolicy>,
    count: Integer,
    limits: Vec<(Integer, usize)>,
    inference_limit_exceeded: bool,
}

impl CWILCallPolicy {
    pub(crate) fn new_in_place(policy: &mut Box<dyn CallPolicy>) {
        let mut prev_policy: Box<dyn CallPolicy> = Box::new(DefaultCallPolicy {});
        mem::swap(&mut prev_policy, policy);

        let new_policy = CWILCallPolicy {
            prev_policy,
            count: Integer::from(0),
            limits: vec![],
            inference_limit_exceeded: false,
        };
        *policy = Box::new(new_policy);
    }

    fn increment(&mut self, machine_st: &MachineState) -> CallResult {
        if self.inference_limit_exceeded || machine_st.ball.stub.h() > 0 {
            return Ok(());
        }

        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == *limit {
                self.inference_limit_exceeded = true;
                return Err(functor!(
                    "inference_limit_exceeded",
                    1,
                    [HeapCellValue::Addr(Addr::Con(Constant::Usize(bp)))]
                ));
            } else {
                self.count += 1;
            }
        }

        Ok(())
    }

    pub(crate) fn add_limit(&mut self, mut limit: Integer, b: usize) -> &Integer {
        limit += &self.count;

        match self.limits.last().cloned() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {}
            _ => self.limits.push((limit, b)),
        };

        &self.count
    }

    pub(crate) fn remove_limit(&mut self, b: usize) -> &Integer {
        if let Some((_, bp)) = self.limits.last().cloned() {
            if bp == b {
                self.limits.pop();
            }
        }

        &self.count
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.limits.is_empty()
    }

    pub(crate) fn into_inner(&mut self) -> Box<dyn CallPolicy> {
        let mut new_inner: Box<dyn CallPolicy> = Box::new(DefaultCallPolicy {});
        mem::swap(&mut self.prev_policy, &mut new_inner);
        new_inner
    }
}

pub(crate) trait CutPolicy: Any {
    // returns true iff we fail or cut redirected the MachineState's p itself
    fn cut(&mut self, _: &mut MachineState, _: RegType) -> bool;
}

downcast!(dyn CutPolicy);

fn cut_body(machine_st: &mut MachineState, addr: Addr) -> bool {
    let b = machine_st.b;

    match addr {
        Addr::Con(Constant::CutPoint(b0)) | Addr::Con(Constant::Usize(b0)) => {
            if b > b0 {
                machine_st.b = b0;
                machine_st.tidy_trail();
            }
        }
        _ => {
            machine_st.fail = true;
            return true;
        }
    };

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
    r_c_w_h: usize,
    r_c_wo_h: usize,
}

impl SCCCutPolicy {
    pub(crate) fn new(r_c_w_h: usize, r_c_wo_h: usize) -> Self {
        SCCCutPolicy {
            cont_pts: vec![],
            r_c_w_h,
            r_c_wo_h,
        }
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
                    (dir_entry!(self.r_c_w_h), 0)
                } else {
                    machine_st[temp_v!(1)] = Addr::Con(Constant::Usize(b_cutoff));
                    (dir_entry!(self.r_c_wo_h), 1)
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

        match machine_st[r].clone() {
            Addr::Con(Constant::Usize(b0)) | Addr::Con(Constant::CutPoint(b0)) => {
                if b > b0 {
                    machine_st.b = b0;
                    machine_st.tidy_trail();
                }
            }
            _ => {
                machine_st.fail = true;
                return true;
            }
        }

        self.run_cleaners(machine_st)
    }
}
