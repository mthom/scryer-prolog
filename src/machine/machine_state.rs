use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::heap_print::*;
use crate::machine::attributed_variables::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::types::*;

use crate::parser::rug::Integer;

use downcast::{
    downcast, downcast_methods, downcast_methods_core, downcast_methods_std, impl_downcast, Any,
};

use indexmap::IndexMap;

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

pub(crate) type Registers = [HeapCellValue; MAX_ARITY + 1];

#[derive(Debug, Clone, Copy)]
pub(super) enum MachineMode {
    Read,
    Write,
}

#[derive(Debug, Clone)]
pub(super) enum HeapPtr {
    HeapCell(usize),
    PStrChar(usize, usize),
    PStrLocation(usize, usize),
}

impl Default for HeapPtr {
    fn default() -> Self {
        HeapPtr::HeapCell(0)
    }
}

#[derive(Debug)]
pub enum FirstOrNext {
    First,
    Next,
}

pub struct MachineState {
    pub atom_tbl: AtomTable,
    pub arena: Arena,
    pub(super) pdl: Vec<HeapCellValue>,
    pub(super) s: HeapPtr,
    pub(super) p: CodePtr,
    pub(super) oip: u32, // first internal code ptr
    pub(super) iip : u32, // second internal code ptr
    pub(super) b: usize,
    pub(super) b0: usize,
    pub(super) e: usize,
    pub(super) num_of_args: usize,
    pub(super) cp: LocalCodePtr,
    pub(super) attr_var_init: AttrVarInitializer,
    pub(super) fail: bool,
    pub heap: Heap,
    pub(super) mode: MachineMode,
    pub(crate) stack: Stack,
    pub(super) registers: Registers,
    pub(super) trail: Vec<TrailEntry>,
    pub(super) tr: usize,
    pub(super) hb: usize,
    pub(super) block: usize, // an offset into the OR stack.
    pub(super) ball: Ball,
    pub(super) lifted_heap: Heap,
    pub(super) interms: Vec<Number>, // intermediate numbers.
    pub(super) last_call: bool, // TODO: REMOVE THIS.
    pub(crate) flags: MachineFlags,
    pub(crate) cc: usize,
    pub(crate) global_clock: usize,
    pub(crate) dynamic_mode: FirstOrNext,
    pub(crate) unify_fn: fn(&mut MachineState),
    pub(crate) bind_fn: fn(&mut MachineState, Ref, HeapCellValue),
}

impl fmt::Debug for MachineState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("MachineState")
            .field("atom_tbl", &self.atom_tbl)
            .field("arena", &self.arena)
            .field("s", &self.s)
            .field("p", &self.p)
            .field("b", &self.b)
            .field("b0", &self.b0)
            .field("e", &self.e)
            .field("num_of_args", &self.num_of_args)
            .field("cp", &self.cp)
            .field("attr_var_init", &self.attr_var_init)
            .field("fail", &self.fail)
            .field("heap", &self.heap)
            .field("mode", &self.mode)
            .field("stack", &self.stack)
            .field("registers", &self.registers)
            .field("trail", &self.trail)
            .field("tr", &self.tr)
            .field("hb", &self.hb)
            .field("block", &self.block)
            .field("ball", &self.ball)
            .field("lifted_heap", &self.lifted_heap)
            .field("interms", &self.interms)
            .field("last_call", &self.last_call)
            .field("flags", &self.flags)
            .field("cc", &self.cc)
            .field("global_clock", &self.global_clock)
            .field("dynamic_mode", &self.dynamic_mode)
            .field(
                "unify_fn",
                if self.unify_fn as usize == MachineState::unify as usize {
                    &"MachineState::unify"
                } else if self.unify_fn as usize == MachineState::unify_with_occurs_check as usize {
                    &"MachineState::unify_with_occurs_check"
                } else {
                    &"MachineState::unify_with_occurs_check_with_error"
                },
            )
            .field(
                "bind_fn",
                if self.bind_fn as usize == MachineState::bind as usize {
                    &"MachineState::bind"
                } else if self.bind_fn as usize
                    == MachineState::bind_with_occurs_check_wrapper as usize
                {
                    &"MachineState::bind_with_occurs_check"
                } else {
                    &"MachineState::bind_with_occurs_check_with_error_wrapper"
                },
            )
            .finish()
    }
}

impl Index<RegType> for MachineState {
    type Output = HeapCellValue;

    #[inline(always)]
    fn index(&self, reg: RegType) -> &Self::Output {
        match reg {
            RegType::Temp(temp) => &self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &self.stack[stack_loc!(AndFrame, e, perm)]
            }
        }
    }
}

impl IndexMut<RegType> for MachineState {
    #[inline(always)]
    fn index_mut(&mut self, reg: RegType) -> &mut Self::Output {
        match reg {
            RegType::Temp(temp) => &mut self.registers[temp],
            RegType::Perm(perm) => {
                let e = self.e;
                &mut self.stack[stack_loc!(AndFrame, e, perm)]
            }
        }
    }
}

pub type CallResult = Result<(), Vec<HeapCellValue>>;

pub trait CutPolicy: Any + fmt::Debug {
    // returns true iff we fail or cut redirected the MachineState's p itself
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool;
}

downcast!(dyn CutPolicy);

pub trait CallPolicy: Any + fmt::Debug {
    fn retry_me_else(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let or_frame = machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            machine_st.registers[i + 1] = or_frame[i];
        }

        machine_st.num_of_args = n;
        machine_st.e = or_frame.prelude.e;
        machine_st.cp = or_frame.prelude.cp;

        or_frame.prelude.bp = machine_st.p.local() + offset;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = machine_st.tr;
        let target_h = or_frame.prelude.h;

        machine_st.tr = or_frame.prelude.tr;

        machine_st.attr_var_init.reset();
        machine_st.hb = machine_st.heap.len();
        machine_st.p += 1;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(target_h);

        Ok(())
    }

    fn retry(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let or_frame = machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            machine_st.registers[i+1] = or_frame[i];
        }

        machine_st.num_of_args = n;
        machine_st.e = or_frame.prelude.e;
        machine_st.cp = or_frame.prelude.cp;

        // WAS: or_frame.prelude.bp = machine_st.p.local() + 1;
        or_frame.prelude.biip += 1;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = machine_st.tr;
        let target_h = or_frame.prelude.h;

        machine_st.tr = or_frame.prelude.tr;
        machine_st.attr_var_init.reset();

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);

        machine_st.trail.truncate(machine_st.tr);
        machine_st.heap.truncate(target_h);

        machine_st.hb = machine_st.heap.len();
        machine_st.p = CodePtr::Local(dir_entry!(machine_st.p.local().abs_loc() + offset));

        machine_st.oip = 0;
        machine_st.iip = 0;

        Ok(())
    }

    fn trust(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let or_frame = machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            machine_st.registers[i+1] = or_frame[i];
        }

        machine_st.num_of_args = n;
        machine_st.e = or_frame.prelude.e;
        machine_st.cp = or_frame.prelude.cp;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = machine_st.tr;
        let target_h = or_frame.prelude.h;

        machine_st.tr = or_frame.prelude.tr;

        machine_st.attr_var_init.reset();
        machine_st.b = or_frame.prelude.b;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);

        machine_st.trail.truncate(machine_st.tr);
        machine_st.stack.truncate(b);
        machine_st.heap.truncate(target_h);

        machine_st.hb = machine_st.heap.len();
        machine_st.p = CodePtr::Local(dir_entry!(machine_st.p.local().abs_loc() + offset));

        machine_st.oip = 0;
        machine_st.iip = 0;

        Ok(())
    }

    fn trust_me(
        &mut self,
        machine_st: &mut MachineState,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let or_frame = machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            machine_st.registers[i+1] = or_frame[i];
        }

        machine_st.num_of_args = n;
        machine_st.e = or_frame.prelude.e;
        machine_st.cp = or_frame.prelude.cp;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = machine_st.tr;
        let target_h = or_frame.prelude.h;

        machine_st.tr = or_frame.prelude.tr;

        machine_st.attr_var_init.reset();
        machine_st.b = or_frame.prelude.b;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);

        machine_st.trail.truncate(machine_st.tr);
        machine_st.stack.truncate(b);
        machine_st.heap.truncate(target_h);

        machine_st.hb = machine_st.heap.len();
        machine_st.p += 1;

        Ok(())
    }

    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: Atom,
        arity: usize,
        idx: &CodeIndex,
    ) -> CallResult {
        if machine_st.last_call {
            self.try_execute(machine_st, name, arity, idx)
        } else {
            self.try_call(machine_st, name, arity, idx)
        }
    }

    fn try_call(
        &mut self,
        machine_st: &mut MachineState,
        name: Atom,
        arity: usize,
        idx: &CodeIndex,
    ) -> CallResult {
        match idx.get() {
            IndexPtr::DynamicUndefined => {
                machine_st.fail = true;
                return Ok(());
            }
            IndexPtr::Undefined => {
                return Err(machine_st.throw_undefined_error(name, arity));
            }
            IndexPtr::DynamicIndex(compiled_tl_index) => {
                machine_st.dynamic_mode = FirstOrNext::First;
                machine_st.call_at_index(arity, dir_entry!(compiled_tl_index));
            }
            IndexPtr::Index(compiled_tl_index) => {
                machine_st.call_at_index(arity, dir_entry!(compiled_tl_index));
            }
        }

        Ok(())
    }

    fn try_execute(
        &mut self,
        machine_st: &mut MachineState,
        name: Atom,
        arity: usize,
        idx: &CodeIndex,
    ) -> CallResult {
        match idx.get() {
            IndexPtr::DynamicUndefined => {
                machine_st.fail = true;
                return Ok(());
            }
            IndexPtr::Undefined => {
                return Err(machine_st.throw_undefined_error(name, arity));
            }
            IndexPtr::DynamicIndex(compiled_tl_index) => {
                machine_st.dynamic_mode = FirstOrNext::First;
                machine_st.execute_at_index(arity, dir_entry!(compiled_tl_index));
            }
            IndexPtr::Index(compiled_tl_index) => {
                machine_st.execute_at_index(arity, dir_entry!(compiled_tl_index))
            }
        }

        Ok(())
    }

    fn call_builtin(
        &mut self,
        machine_st: &mut MachineState,
        ct: &BuiltInClauseType,
        _code_dir: &CodeDir,
        op_dir: &OpDir,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        match ct {
            &BuiltInClauseType::AcyclicTerm => {
                let addr = machine_st.registers[1];
                machine_st.fail = machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Arg => {
                machine_st.try_arg()?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Compare => {
                let stub_gen = || functor_stub(atom!("compare"), 3);

                let a1 = machine_st.store(machine_st.deref(machine_st.registers[1]));
                let a2 = machine_st.registers[2];
                let a3 = machine_st.registers[3];

                read_heap_cell!(a1,
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(machine_st.heap[s])
                            .get_name_and_arity();

                        match name {
                            atom!(">") | atom!("<") | atom!("=") if arity == 2 => {
                            }
                            _ => {
                                let err = machine_st.domain_error(DomainErrorType::Order, a1);
                                return Err(machine_st.error_form(err, stub_gen()));
                            }
                        }
                    }
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                    }
                    _ => {
                        let err = machine_st.type_error(ValidType::Atom, a1);
                        return Err(machine_st.error_form(err, stub_gen()));
                    }
                );

                let atom = match compare_term_test!(machine_st, a2, a3) {
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

                machine_st.unify_atom(atom, a1);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CompareTerm(qt) => {
                machine_st.compare_term(qt);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Read => {
                let stream = machine_st.get_stream_or_alias(
                    machine_st.registers[1],
                    stream_aliases,
                    atom!("read"),
                    2,
                )?;

                match machine_st.read(stream, op_dir) {
                    Ok(offset) => {
                        let value = machine_st.registers[2];
                        unify_fn!(machine_st, value, heap_loc_as_cell!(offset.heap_loc));
                    }
                    Err(ParserError::UnexpectedEOF) => {
                        let value = machine_st.registers[2];
                        machine_st.unify_atom(atom!("end_of_file"), value);
                    }
                    Err(e) => {
                        let stub = functor_stub(atom!("read"), 2);
                        let err = machine_st.syntax_error(e);

                        return Err(machine_st.error_form(err, stub));
                    }
                };

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CopyTerm => {
                machine_st.copy_term(AttrVarPolicy::DeepCopy);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Eq => {
                let a1 = machine_st.registers[1];
                let a2 = machine_st.registers[2];

                machine_st.fail = machine_st.eq_test(a1, a2);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Ground => {
                machine_st.fail = machine_st.ground_test();
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Functor => {
                machine_st.try_functor()?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::NotEq => {
                let a1 = machine_st.registers[1];
                let a2 = machine_st.registers[2];

                machine_st.fail =
                    if let Some(Ordering::Equal) = compare_term_test!(machine_st, a1, a2) {
                        true
                    } else {
                        false
                    };

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Sort => {
                machine_st.check_sort_errors()?;

                let stub_gen = || functor_stub(atom!("sort"), 2);
                let mut list = machine_st.try_from_list(machine_st.registers[1], stub_gen)?;

                list.sort_unstable_by(|v1, v2| {
                    compare_term_test!(machine_st, *v1, *v2).unwrap_or(Ordering::Less)
                });

                list.dedup_by(|v1, v2| {
                    compare_term_test!(machine_st, *v1, *v2) == Some(Ordering::Equal)
                });

                let heap_addr = heap_loc_as_cell!(
                    iter_to_heap_list(&mut machine_st.heap, list.into_iter())
                );

                let r2 = machine_st.registers[2];
                unify_fn!(machine_st, r2, heap_addr);

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::KeySort => {
                machine_st.check_keysort_errors()?;

                let stub_gen = || functor_stub(atom!("keysort"), 2);
                let list = machine_st.try_from_list(machine_st.registers[1], stub_gen)?;

                let mut key_pairs = Vec::with_capacity(list.len());

                for val in list {
                    let key = machine_st.project_onto_key(val)?;
                    key_pairs.push((key, val));
                }

                key_pairs.sort_by(|a1, a2| {
                    compare_term_test!(machine_st, a1.0, a2.0).unwrap_or(Ordering::Less)
                });

                let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
                let heap_addr = heap_loc_as_cell!(
                    iter_to_heap_list(&mut machine_st.heap, key_pairs)
                );

                let r2 = machine_st.registers[2];
                unify_fn!(machine_st, r2, heap_addr);

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Is(r, ref at) => {
                let n1 = machine_st.store(machine_st.deref(machine_st[r]));
                let n2 = machine_st.get_number(at)?;

                match n2 {
                    Number::Fixnum(n) => machine_st.unify_fixnum(n, n1),
                    Number::Float(n) => {
                        // TODO: argghh.. deal with it.
                        let n = arena_alloc!(n, &mut machine_st.arena);
                        machine_st.unify_f64(n, n1)
                    }
                    Number::Integer(n) => machine_st.unify_big_int(n, n1),
                    Number::Rational(n) => machine_st.unify_rational(n, n1),
                }

                return_from_clause!(machine_st.last_call, machine_st)
            }
        }
    }

    fn call_clause_type(
        &mut self,
        machine_st: &mut MachineState,
        key: PredicateKey,
        code_dir: &CodeDir,
        op_dir: &OpDir,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        let (name, arity) = key;

        match ClauseType::from(name, arity) {
            ClauseType::BuiltIn(built_in) => {
                machine_st.setup_built_in_call(built_in);
                self.call_builtin(machine_st, &built_in, code_dir, op_dir, stream_aliases)?;
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
            ClauseType::Named(..) => {
                if let Some(idx) = code_dir.get(&(name, arity)) {
                    self.context_call(machine_st, name, arity, idx)?;
                } else {
                    return Err(machine_st.throw_undefined_error(name, arity));
                }
            }
            ClauseType::System(_) => {
                let (name, arity) = key;
                let name = functor!(name);

                let stub = functor_stub(atom!("call"), arity + 1);
                let err = machine_st.type_error(ValidType::Callable, name);

                return Err(machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    fn call_n(
        &mut self,
        machine_st: &mut MachineState,
        arity: usize,
        code_dir: &CodeDir,
        op_dir: &OpDir,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        if let Some(key) = machine_st.setup_call_n(arity) {
            self.call_clause_type(machine_st, key, code_dir, op_dir, stream_aliases)?;
        }

        Ok(())
    }
}

#[inline(always)]
pub fn pstr_loc_and_offset(heap: &[HeapCellValue], index: usize) -> (usize, Fixnum) {
    read_heap_cell!(heap[index],
        (HeapCellValueTag::PStr | HeapCellValueTag::CStr) => {
            (index, Fixnum::build_with(0))
        }
        (HeapCellValueTag::PStrOffset, h) => {
            (h, cell_as_fixnum!(heap[index+1]))
        }
        _ => {
            unreachable!()
        }
    )
}

#[derive(Debug)]
pub struct Ball {
    pub(super) boundary: usize,
    pub(super) stub: Heap,
}

impl Ball {
    pub(super) fn new() -> Self {
        Ball {
            boundary: 0,
            stub: Heap::new(),
        }
    }

    pub(super) fn reset(&mut self) {
        self.boundary = 0;
        self.stub.clear();
    }

    pub(super) fn copy_and_align(&self, h: usize) -> Heap {
        let diff = self.boundary as i64 - h as i64;

        self.stub.iter().cloned().map(|heap_value| {
            heap_value - diff
        }).collect()
    }
}

#[derive(Debug)]
pub(super) struct CopyTerm<'a> {
    state: &'a mut MachineState,
}

impl<'a> CopyTerm<'a> {
    pub(super) fn new(state: &'a mut MachineState) -> Self {
        CopyTerm { state }
    }
}

impl<'a> Index<usize> for CopyTerm<'a> {
    type Output = HeapCellValue;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.state.heap[index]
    }
}

impl<'a> IndexMut<usize> for CopyTerm<'a> {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.state.heap[index]
    }
}

impl<'a> CopierTarget for CopyTerm<'a> {
    #[inline(always)]
    fn threshold(&self) -> usize {
        self.state.heap.len()
    }

    #[inline(always)]
    fn push(&mut self, hcv: HeapCellValue) {
        self.state.heap.push(hcv);
    }

    #[inline(always)]
    fn store(&self, value: HeapCellValue) -> HeapCellValue {
        self.state.store(value)
    }

    #[inline(always)]
    fn deref(&self, value: HeapCellValue) -> HeapCellValue {
        self.state.deref(value)
    }

    #[inline(always)]
    fn stack(&mut self) -> &mut Stack {
        &mut self.state.stack
    }
}

#[derive(Debug)]
pub(super) struct CopyBallTerm<'a> {
    stack: &'a mut Stack,
    heap: &'a mut Heap,
    heap_boundary: usize,
    stub: &'a mut Heap,
}

impl<'a> CopyBallTerm<'a> {
    pub(super) fn new(stack: &'a mut Stack, heap: &'a mut Heap, stub: &'a mut Heap) -> Self {
        let hb = heap.len();

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

impl<'a> CopierTarget for CopyBallTerm<'a> {
    fn threshold(&self) -> usize {
        self.heap_boundary + self.stub.len()
    }

    fn push(&mut self, value: HeapCellValue) {
        self.stub.push(value);
    }

    fn store(&self, value: HeapCellValue) -> HeapCellValue {
        read_heap_cell!(value,
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, h) => {
                if h < self.heap_boundary {
                    self.heap[h]
                } else {
                    let index = h - self.heap_boundary;
                    self.stub[index]
                }
            }
            (HeapCellValueTag::StackVar, s) => {
                self.stack[s]
            }
            _ => {
                value
            }
        )
    }

    fn deref(&self, mut addr: HeapCellValue) -> HeapCellValue {
        loop {
            let value = self.store(addr);

            if value.is_var() && value != addr {
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

impl MachineState {
    #[allow(dead_code)]
    pub(super) fn try_char_list(&mut self, addrs: Vec<HeapCellValue>) -> Result<String, MachineError> {
        let mut chars = String::new();

        for addr in addrs {
            let addr = self.store(self.deref(addr));

            read_heap_cell!(addr,
                (HeapCellValueTag::Char, c) => {
                    chars.push(c);
                    continue;
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    if arity == 0 {
                        if let Some(c) = name.as_char() {
                            chars.push(c);
                            continue;
                        }
                    }
                }
                _ => {
                }
            );

            return Err(self.type_error(ValidType::Character, addr));
        }

        Ok(chars)
    }

    pub(super) fn throw_undefined_error(&mut self, name: Atom, arity: usize) -> MachineStub {
        let stub = functor_stub(name, arity);
        let err = self.existence_error(ExistenceError::Procedure(name, arity));

        self.error_form(err, stub)
    }

    pub(super) fn call_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.cp.assign_if_local(self.p + 1);
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub(super) fn execute_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub fn read_term(&mut self, stream: Stream, indices: &mut IndexStore) -> CallResult {
        fn push_var_eq_functors<'a>(
            heap: &mut Heap,
            iter: impl Iterator<Item = (&'a Rc<String>, &'a HeapCellValue)>,
            atom_tbl: &mut AtomTable,
        ) -> Vec<HeapCellValue> {
            let mut list_of_var_eqs = vec![];

            for (var, binding) in iter {
                let var_atom = atom_tbl.build_with(&var);
                let h = heap.len();

                heap.push(atom_as_cell!(atom!("="), 2));
                heap.push(atom_as_cell!(var_atom));
                heap.push(*binding);

                list_of_var_eqs.push(str_loc_as_cell!(h));
            }

            list_of_var_eqs
        }

        self.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.registers[2]),
            atom!("read_term"),
            3,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return return_from_clause!(self.last_call, self);
            } else if self.fail {
                return Ok(());
            }
        }

        loop {
            match self.read(stream, &indices.op_dir) {
                Ok(term_write_result) => {
                    let term = self.registers[2];
                    unify_fn!(self, heap_loc_as_cell!(term_write_result.heap_loc), term);
                    let term = heap_loc_as_cell!(term_write_result.heap_loc);

                    if self.fail {
                        return Ok(());
                    }

                    let mut singleton_var_set: IndexMap<Ref, bool> = IndexMap::new();
                    let mut var_list = vec![];

                    let list_of_var_eqs = push_var_eq_functors(
                        &mut self.heap,
                        term_write_result.var_dict.iter(),
                        &mut self.atom_tbl,
                    );

                    for addr in stackful_preorder_iter(&mut self.heap, term) {
                        let addr = unmark_cell_bits!(addr);

                        if let Some(var) = addr.as_var() {
                            if !singleton_var_set.contains_key(&var) {
                                singleton_var_set.insert(var, true);
                                var_list.push(addr);
                            } else {
                                singleton_var_set.insert(var, false);
                            }
                        }
                    }

                    let singleton_var_list = push_var_eq_functors(
                        &mut self.heap,
                        term_write_result.var_dict.iter().filter(|(_, binding)| {
                            if let Some(r) = binding.as_var() {
                                *singleton_var_set.get(&r).unwrap_or(&false)
                            } else {
                                false
                            }
                        }),
                        &mut self.atom_tbl,
                    );

                    let singleton_addr = self.registers[3];
                    let singletons_offset = heap_loc_as_cell!(
                        iter_to_heap_list(&mut self.heap, singleton_var_list.into_iter())
                    );

                    unify_fn!(self, singletons_offset, singleton_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let vars_addr = self.registers[4];
                    let vars_offset = heap_loc_as_cell!(
                        iter_to_heap_list(&mut self.heap, var_list.into_iter())
                    );

                    unify_fn!(self, vars_offset, vars_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let var_names_addr = self.registers[5];
                    let var_names_offset = heap_loc_as_cell!(
                        iter_to_heap_list(&mut self.heap, list_of_var_eqs.into_iter())
                    );

                    return Ok(unify_fn!(self, var_names_offset, var_names_addr));
                }
                Err(err) => {
                    if let ParserError::UnexpectedEOF = err {
                        self.eof_action(
                            self.registers[2],
                            stream,
                            atom!("read_term"),
                            3,
                        )?;

                        if stream.options().eof_action() == EOFAction::Reset {
                            if self.fail == false {
                                continue;
                            }
                        }

                        return Ok(());
                    }

                    let stub = functor_stub(atom!("read_term"), 3);
                    let err = self.syntax_error(err);

                    return Err(self.error_form(err, stub));
                }
            }
        }
    }

    pub(crate) fn write_term<'a>(
        &'a mut self,
        op_dir: &'a OpDir,
    ) -> Result<Option<HCPrinter<'a, PrinterOutputter>>, MachineStub> {
        let ignore_ops = self.store(self.deref(self.registers[3]));
        let numbervars = self.store(self.deref(self.registers[4]));
        let quoted = self.store(self.deref(self.registers[5]));
        let max_depth = self.store(self.deref(self.registers[7]));

        let term_to_be_printed = self.store(self.deref(self.registers[2]));
        let stub_gen = || functor_stub(atom!("write_term"), 2);

        let printer = match self.try_from_list(self.registers[6], stub_gen) {
            Ok(addrs) => {
                let mut var_names: IndexMap<HeapCellValue, Rc<String>> = IndexMap::new();

                for addr in addrs {
                    read_heap_cell!(addr,
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.heap[s])
                                .get_name_and_arity();

                            if name == atom!("=") && arity == 2 {
                                let atom = self.store(self.deref(self.heap[s+1]));
                                let var = self.store(self.deref(self.heap[s+2]));

                                if var_names.contains_key(&var) {
                                    continue;
                                }

                                var_names.insert(var, Rc::new(cell_as_atom!(atom).as_str().to_owned()));
                            }
                        }
                        _ => {
                        }
                    );
                }

                let mut printer = HCPrinter::new(
                    &mut self.heap,
                    &mut self.arena,
                    op_dir,
                    PrinterOutputter::new(),
                    term_to_be_printed,
                );

                if let HeapCellValueTag::Atom = ignore_ops.get_tag() {
                    let name = cell_as_atom!(ignore_ops);
                    printer.ignore_ops = name == atom!("true");
                } else {
                    unreachable!();
                }

                if let HeapCellValueTag::Atom = numbervars.get_tag() {
                    let name = cell_as_atom!(numbervars);
                    printer.numbervars = name == atom!("true");
                } else {
                    unreachable!();
                }

                if let HeapCellValueTag::Atom = quoted.get_tag() {
                    let name = cell_as_atom!(quoted);
                    printer.quoted = name == atom!("true");
                } else {
                    unreachable!();
                }

                match Number::try_from(max_depth) {
                    Ok(Number::Fixnum(n)) => {
                        if let Ok(n) = usize::try_from(n.get_num()) {
                            printer.max_depth = n;
                        } else {
                            self.fail = true;
                            return Ok(None);
                        }
                    }
                    Ok(Number::Integer(n)) => {
                        if let Some(n) = n.to_usize() {
                            printer.max_depth = n;
                        } else {
                            self.fail = true;
                            return Ok(None);
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                }

                printer.var_names = var_names;

                printer
            }
            Err(err) => {
                return Err(err);
            }
        };

        Ok(Some(printer))
    }

    pub(super) fn read_predicate_key(&self, name: HeapCellValue, arity: HeapCellValue) -> (Atom, usize) {
        let name = cell_as_atom!(self.store(self.deref(name)));
        let arity = cell_as_fixnum!(self.store(self.deref(arity)));

        (name, usize::try_from(arity.get_num()).unwrap())
    }

    pub(super) fn module_lookup(
        &mut self,
        indices: &IndexStore,
        call_policy: &mut Box<dyn CallPolicy>,
        key: PredicateKey,
        module_name: Atom,
        _last_call: bool,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        if module_name == atom!("user") {
            return call_policy.call_clause_type(
                self,
                key,
                &indices.code_dir,
                &indices.op_dir,
                stream_aliases,
            );
        } else if let Some(module) = indices.modules.get(&module_name) {
            return call_policy.call_clause_type(
                self,
                key,
                &module.code_dir,
                &module.op_dir,
                stream_aliases,
            );
        }

        let (name, arity) = key;

        let stub = functor_stub(name, arity);
        let err = self.module_resolution_error(module_name, name, arity);

        return Err(self.error_form(err, stub));
    }
}

#[derive(Debug)]
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
        if self.inference_limit_exceeded || machine_st.ball.stub.len() > 0 {
            return Ok(());
        }

        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == *limit {
                self.inference_limit_exceeded = true;

                return Err(
                    functor!(atom!("inference_limit_exceeded"), [fixnum(bp)])
                );
            } else {
                self.count += 1;
            }
        }

        Ok(())
    }

    pub(crate) fn add_limit(&mut self, limit: usize, b: usize) -> &Integer {
        let mut limit = Integer::from(limit);
        limit += &self.count;

        match self.limits.last() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {}
            _ => self.limits.push((limit, b)),
        };

        &self.count
    }

    pub(crate) fn remove_limit(&mut self, b: usize) -> &Integer {
        if let Some((_, bp)) = self.limits.last() {
            if bp == &b {
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

impl CallPolicy for CWILCallPolicy {
    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: Atom,
        arity: usize,
        idx: &CodeIndex,
    ) -> CallResult {
        self.prev_policy.context_call(machine_st, name, arity, idx)?;
        self.increment(machine_st)
    }

    fn retry_me_else(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy.retry_me_else(machine_st, offset, global_variables)?;
        self.increment(machine_st)
    }

    fn retry(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy.retry(machine_st, offset, global_variables)?;
        self.increment(machine_st)
    }

    fn trust_me(
        &mut self,
        machine_st: &mut MachineState,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy.trust_me(machine_st, global_variables)?;
        self.increment(machine_st)
    }

    fn trust(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy.trust(machine_st, offset, global_variables)?;
        self.increment(machine_st)
    }

    fn call_builtin(
        &mut self,
        machine_st: &mut MachineState,
        ct: &BuiltInClauseType,
        code_dir: &CodeDir,
        op_dir: &OpDir,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        self.prev_policy.call_builtin(machine_st, ct, code_dir, op_dir, stream_aliases)?;
        self.increment(machine_st)
    }

    fn call_n(
        &mut self,
        machine_st: &mut MachineState,
        arity: usize,
        code_dir: &CodeDir,
        op_dir: &OpDir,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        self.prev_policy.call_n(machine_st, arity, code_dir, op_dir, stream_aliases)?;
        self.increment(machine_st)
    }
}

downcast!(dyn CallPolicy);

#[derive(Debug)]
pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

fn cut_body(machine_st: &mut MachineState, addr: HeapCellValue) -> bool {
    let b = machine_st.b;

    read_heap_cell!(addr,
        (HeapCellValueTag::Fixnum, b0) => {
            let b0 = b0.get_num() as usize;

            if b > b0 {
                machine_st.b = b0;
            }
        }
        _ => {
            machine_st.fail = true;
            return true;
        }
    );

    false
}

#[derive(Debug)]
pub(crate) struct DefaultCutPolicy {}

pub(super) fn deref_cut(machine_st: &mut MachineState, r: RegType) {
    let addr = machine_st.store(machine_st.deref(machine_st[r]));
    cut_body(machine_st, addr);
}

impl CutPolicy for DefaultCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool {
        let addr = machine_st[r];
        cut_body(machine_st, addr)
    }
}

#[derive(Debug)]
pub(crate) struct SCCCutPolicy {
    // locations of cleaners, cut points, the previous block
    cont_pts: Vec<(HeapCellValue, usize, usize)>,
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

    pub(crate) fn push_cont_pt(&mut self, addr: HeapCellValue, b: usize, prev_b: usize) {
        self.cont_pts.push((addr, b, prev_b));
    }

    pub(crate) fn pop_cont_pt(&mut self) -> Option<(HeapCellValue, usize, usize)> {
        self.cont_pts.pop()
    }

    fn run_cleaners(&self, machine_st: &mut MachineState) -> bool {
        if let Some(&(_, b_cutoff, prev_block)) = self.cont_pts.last() {
            if machine_st.b < b_cutoff {
                let (idx, arity) = if machine_st.block > prev_block {
                    (dir_entry!(self.r_c_w_h), 0)
                } else {
                    machine_st.registers[1] = fixnum_as_cell!(Fixnum::build_with(b_cutoff as i64));
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

        read_heap_cell!(machine_st[r],
            (HeapCellValueTag::Fixnum, b0) => {
                let b0 = b0.get_num() as usize;

                if b > b0 {
                    machine_st.b = b0;
                }
            }
            _ => {
                machine_st.fail = true;
                return true;
            }
        );

        self.run_cleaners(machine_st)
    }
}

