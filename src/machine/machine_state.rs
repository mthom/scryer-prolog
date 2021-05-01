use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;
use prolog_parser::{clause_name, temp_v};

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_print::*;
use crate::machine::attributed_variables::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::partial_string::HeapPStrIter;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::rug::Integer;

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

#[derive(Debug)]
pub(crate) struct Ball {
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
        let mut stub = Heap::new();

        for heap_value in self.stub.iter_from(0) {
            stub.push(match heap_value {
                &HeapCellValue::Addr(addr) => HeapCellValue::Addr(addr - diff),
                heap_value => heap_value.context_free_clone(),
            });
        }

        stub
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
pub(super) struct CopyBallTerm<'a> {
    stack: &'a mut Stack,
    heap: &'a mut Heap,
    heap_boundary: usize,
    stub: &'a mut Heap,
}

impl<'a> CopyBallTerm<'a> {
    pub(super) fn new(stack: &'a mut Stack, heap: &'a mut Heap, stub: &'a mut Heap) -> Self {
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
            Addr::StackCell(fr, sc) => self.stack.index_and_frame(fr)[sc],
            addr => addr,
        }
    }

    fn deref(&self, mut addr: Addr) -> Addr {
        loop {
            let value = self.store(addr);

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

pub(crate) type Registers = Vec<Addr>;

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

impl HeapPtr {
    #[inline]
    pub(super) fn read(&self, heap: &Heap) -> Addr {
        match self {
            &HeapPtr::HeapCell(h) => Addr::HeapCell(h),
            &HeapPtr::PStrChar(h, n) => {
                if let &HeapCellValue::PartialString(ref pstr, has_tail) = &heap[h] {
                    if let Some(c) = pstr.range_from(n..).next() {
                        Addr::Char(c)
                    } else if has_tail {
                        Addr::HeapCell(h + 1)
                    } else {
                        Addr::EmptyList
                    }
                } else {
                    unreachable!()
                }
            }
            &HeapPtr::PStrLocation(h, n) => Addr::PStrLocation(h, n),
        }
    }
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

// #[derive(Debug)]
pub(crate) struct MachineState {
    pub(crate) atom_tbl: TabledData<Atom>,
    pub(super) s: HeapPtr,
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
    pub(crate) flags: MachineFlags,
    pub(crate) cc: usize,
    pub(crate) global_clock: usize,
    pub(crate) dynamic_mode: FirstOrNext,
    pub(crate) unify_fn: fn(&mut MachineState, Addr, Addr),
    pub(crate) bind_fn: fn(&mut MachineState, Ref, Addr),
}

impl fmt::Debug for MachineState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("MachineState")
            .field("atom_tbl", &self.atom_tbl)
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

impl MachineState {
    pub(crate) fn read_term(&mut self, mut stream: Stream, indices: &mut IndexStore) -> CallResult {
        fn push_var_eq_functors<'a>(
            heap: &mut Heap,
            iter: impl Iterator<Item = (&'a Rc<Var>, &'a Addr)>,
            op_dir: &OpDir,
            atom_tbl: TabledData<Atom>,
        ) -> Vec<Addr> {
            let mut list_of_var_eqs = vec![];

            for (var, binding) in iter {
                let var_atom = clause_name!(var.to_string(), atom_tbl);

                let h = heap.h();
                let spec = fetch_atom_op_spec(clause_name!("="), None, op_dir);

                heap.push(HeapCellValue::NamedStr(2, clause_name!("="), spec));
                heap.push(HeapCellValue::Atom(var_atom, None));
                heap.push(HeapCellValue::Addr(*binding));

                list_of_var_eqs.push(Addr::Str(h));
            }

            list_of_var_eqs
        }

        self.check_stream_properties(
            &mut stream,
            StreamType::Text,
            Some(self[temp_v!(2)]),
            clause_name!("read_term"),
            3,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action {
                return return_from_clause!(self.last_call, self);
            } else if self.fail {
                return Ok(());
            }
        }

        let mut orig_stream = stream.clone();

        loop {
            match self.read(stream.clone(), self.atom_tbl.clone(), &indices.op_dir) {
                Ok(term_write_result) => {
                    let term = self[temp_v!(2)];
                    (self.unify_fn)(self, Addr::HeapCell(term_write_result.heap_loc), term);

                    if self.fail {
                        return Ok(());
                    }

                    let list_of_var_eqs = push_var_eq_functors(
                        &mut self.heap,
                        term_write_result.var_dict.iter(),
                        &indices.op_dir,
                        self.atom_tbl.clone(),
                    );

                    let mut singleton_var_set: IndexMap<Ref, bool> = IndexMap::new();
                    let mut var_list = vec![];

                    for addr in self.acyclic_pre_order_iter(term) {
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
                        &indices.op_dir,
                        self.atom_tbl.clone(),
                    );

                    let singleton_addr = self[temp_v!(3)];
                    let singletons_offset =
                        Addr::HeapCell(self.heap.to_list(singleton_var_list.into_iter()));

                    (self.unify_fn)(self, singletons_offset, singleton_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let vars_addr = self[temp_v!(4)];
                    let vars_offset = Addr::HeapCell(self.heap.to_list(var_list.into_iter()));

                    (self.unify_fn)(self, vars_offset, vars_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let var_names_addr = self[temp_v!(5)];
                    let var_names_offset =
                        Addr::HeapCell(self.heap.to_list(list_of_var_eqs.into_iter()));

                    return Ok((self.unify_fn)(self, var_names_offset, var_names_addr));
                }
                Err(err) => {
                    if let ParserError::UnexpectedEOF = err {
                        self.eof_action(
                            self[temp_v!(2)],
                            &mut orig_stream,
                            clause_name!("read_term"),
                            3,
                        )?;

                        if orig_stream.options().eof_action == EOFAction::Reset {
                            if self.fail == false {
                                continue;
                            }
                        }

                        return Ok(());
                    }

                    let stub = MachineError::functor_stub(clause_name!("read_term"), 3);
                    let err = MachineError::syntax_error(self.heap.h(), err);

                    return Err(self.error_form(err, stub));
                }
            }
        }
    }

    pub(crate) fn write_term<'a>(
        &'a self,
        op_dir: &'a OpDir,
    ) -> Result<Option<HCPrinter<'a, PrinterOutputter>>, MachineStub> {
        let ignore_ops = self.store(self.deref(self[temp_v!(3)]));
        let numbervars = self.store(self.deref(self[temp_v!(4)]));
        let quoted = self.store(self.deref(self[temp_v!(5)]));
        let max_depth = self.store(self.deref(self[temp_v!(7)]));

        let mut printer = HCPrinter::new(&self, op_dir, PrinterOutputter::new());

        if let &Addr::Con(h) = &ignore_ops {
            if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                printer.ignore_ops = name.as_str() == "true";
            } else {
                unreachable!()
            }
        }

        if let &Addr::Con(h) = &numbervars {
            if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                printer.numbervars = name.as_str() == "true";
            } else {
                unreachable!()
            }
        }

        if let &Addr::Con(h) = &quoted {
            if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                printer.quoted = name.as_str() == "true";
            } else {
                unreachable!()
            }
        }

        match Number::try_from((max_depth, &self.heap)) {
            Ok(Number::Fixnum(n)) => {
                if let Ok(n) = usize::try_from(n) {
                    printer.max_depth = n;
                } else {
                    return Ok(None);
                }
            }
            Ok(Number::Integer(n)) => {
                if let Some(n) = n.to_usize() {
                    printer.max_depth = n;
                } else {
                    return Ok(None);
                }
            }
            _ => {
                unreachable!();
            }
        }

        let stub = MachineError::functor_stub(clause_name!("write_term"), 2);

        match self.try_from_list(temp_v!(6), stub) {
            Ok(addrs) => {
                let mut var_names: IndexMap<Addr, String> = IndexMap::new();

                for addr in addrs {
                    match addr {
                        Addr::Str(s) => match &self.heap[s] {
                            &HeapCellValue::NamedStr(2, ref name, _) if name.as_str() == "=" => {
                                let atom = self.heap[s + 1].as_addr(s + 1);
                                let var = self.heap[s + 2].as_addr(s + 2);

                                let atom = match self.store(self.deref(atom)) {
                                    Addr::Con(h) => {
                                        if let HeapCellValue::Atom(ref atom, _) = &self.heap[h] {
                                            atom.to_string()
                                        } else {
                                            unreachable!()
                                        }
                                    }
                                    Addr::Char(c) => c.to_string(),
                                    _ => unreachable!(),
                                };

                                let var = self.store(self.deref(var));

                                if var_names.contains_key(&var) {
                                    continue;
                                }

                                var_names.insert(var, atom);
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }

                printer.var_names = var_names;
            }
            Err(err) => {
                return Err(err);
            }
        }

        Ok(Some(printer))
    }

    pub(super) fn throw_undefined_error(&mut self, name: ClauseName, arity: usize) -> MachineStub {
        let stub = MachineError::functor_stub(name.clone(), arity);
        let h = self.heap.h();
        let key = ExistenceError::Procedure(name, arity);

        self.error_form(MachineError::existence_error(h, key), stub)
    }

    #[inline]
    pub(crate) fn heap_pstr_iter<'a>(&'a self, focus: Addr) -> HeapPStrIter<'a> {
        HeapPStrIter::new(self, focus)
    }

    pub(super) fn try_char_list(&self, addrs: Vec<Addr>) -> Result<String, MachineError> {
        let mut chars = String::new();
        let mut iter = addrs.iter();

        while let Some(addr) = iter.next() {
            let addr = self.store(self.deref(*addr));

            match addr {
                Addr::Char(c) => {
                    chars.push(c);
                    continue;
                }
                Addr::Con(h) => {
                    if let HeapCellValue::Atom(ref name, _) = &self.heap[h] {
                        if name.is_char() {
                            chars += name.as_str();
                            continue;
                        }
                    }
                }
                _ => {}
            };

            let h = self.heap.h();

            return Err(MachineError::type_error(h, ValidType::Character, addr));
        }

        Ok(chars)
    }

    pub(super) fn read_predicate_key(&self, name: Addr, arity: Addr) -> (ClauseName, usize) {
        let predicate_name = atom_from!(self, self.store(self.deref(name)));
        let arity = self.store(self.deref(arity));

        let arity = match Number::try_from((arity, &self.heap)) {
            Ok(Number::Integer(n)) if &*n >= &0 && &*n <= &MAX_ARITY => n.to_usize().unwrap(),
            Ok(Number::Fixnum(n)) if n >= 0 && n <= MAX_ARITY as isize => {
                usize::try_from(n).unwrap()
            }
            _ => unreachable!(),
        };

        (predicate_name, arity)
    }

    pub(super) fn call_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.cp.assign_if_local(self.p.clone() + 1);
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub(super) fn execute_at_index(&mut self, arity: usize, p: LocalCodePtr) {
        self.num_of_args = arity;
        self.b0 = self.b;
        self.p = CodePtr::Local(p);
    }

    pub(super) fn module_lookup(
        &mut self,
        indices: &IndexStore,
        call_policy: &mut Box<dyn CallPolicy>,
        key: PredicateKey,
        module_name: ClauseName,
        _last_call: bool,
        stream_aliases: &StreamAliasDir,
    ) -> CallResult {
        if module_name.as_str() == "user" {
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

        let h = self.heap.h();
        let stub = MachineError::functor_stub(name.clone(), arity);
        let err = MachineError::module_resolution_error(h, module_name, name, arity);

        return Err(self.error_form(err, stub));
    }
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any + fmt::Debug {
    fn retry_me_else(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let n = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .univ_prelude
            .num_cells;

        for i in 1..n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i - 1];
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        machine_st.stack.index_or_frame_mut(b).prelude.bp = machine_st.p.local() + offset;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st
            .heap
            .truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_queue_b;
        let attr_var_init_bindings_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_bindings_b;

        machine_st
            .attr_var_init
            .backtrack(attr_var_init_queue_b, attr_var_init_bindings_b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p += 1;

        Ok(())
    }

    fn retry(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let n = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .univ_prelude
            .num_cells;

        for i in 1..n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i - 1];
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        machine_st.stack.index_or_frame_mut(b).prelude.bp = machine_st.p.local() + 1;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st
            .heap
            .truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_queue_b;
        let attr_var_init_bindings_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_bindings_b;

        machine_st
            .attr_var_init
            .backtrack(attr_var_init_queue_b, attr_var_init_bindings_b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p = CodePtr::Local(dir_entry!(machine_st.p.local().abs_loc() + offset));

        Ok(())
    }

    fn trust(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let n = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .univ_prelude
            .num_cells;

        for i in 1..n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i - 1];
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st
            .heap
            .truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_queue_b;
        let attr_var_init_bindings_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_bindings_b;

        machine_st
            .attr_var_init
            .backtrack(attr_var_init_queue_b, attr_var_init_bindings_b);

        machine_st.b = machine_st.stack.index_or_frame(b).prelude.b;
        machine_st.stack.truncate(b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p = CodePtr::Local(dir_entry!(machine_st.p.local().abs_loc() + offset));

        Ok(())
    }

    fn trust_me(
        &mut self,
        machine_st: &mut MachineState,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        let b = machine_st.b;
        let n = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .univ_prelude
            .num_cells;

        for i in 1..n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i - 1];
        }

        machine_st.num_of_args = n;
        machine_st.e = machine_st.stack.index_or_frame(b).prelude.e;
        machine_st.cp = machine_st.stack.index_or_frame(b).prelude.cp;

        let old_tr = machine_st.stack.index_or_frame(b).prelude.tr;
        let curr_tr = machine_st.tr;

        machine_st.unwind_trail(old_tr, curr_tr, global_variables);
        machine_st.tr = machine_st.stack.index_or_frame(b).prelude.tr;

        machine_st.trail.truncate(machine_st.tr);
        machine_st
            .heap
            .truncate(machine_st.stack.index_or_frame(b).prelude.h);

        let attr_var_init_queue_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_queue_b;
        let attr_var_init_bindings_b = machine_st
            .stack
            .index_or_frame(b)
            .prelude
            .attr_var_init_bindings_b;

        machine_st
            .attr_var_init
            .backtrack(attr_var_init_queue_b, attr_var_init_bindings_b);

        machine_st.b = machine_st.stack.index_or_frame(b).prelude.b;
        machine_st.stack.truncate(b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p += 1;

        Ok(())
    }

    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
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
        name: ClauseName,
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
        name: ClauseName,
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
                let addr = machine_st[temp_v!(1)];
                machine_st.fail = machine_st.is_cyclic_term(addr);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Arg => {
                machine_st.try_arg()?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Compare => {
                let a1 = machine_st.store(machine_st.deref(machine_st[temp_v!(1)]));
                let a2 = machine_st[temp_v!(2)];
                let a3 = machine_st[temp_v!(3)];

                match a1 {
                    Addr::Con(h) if machine_st.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &machine_st.heap[h] {
                            match atom.as_str() {
                                ">" | "<" | "=" => {}
                                _ => {
                                    let stub =
                                        MachineError::functor_stub(clause_name!("compare"), 3);

                                    let err =
                                        MachineError::domain_error(DomainErrorType::Order, a1);
                                    return Err(machine_st.error_form(err, stub));
                                }
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    addr if !addr.is_ref() => {
                        let h = machine_st.heap.h();
                        let stub = MachineError::functor_stub(clause_name!("compare"), 3);
                        let err = MachineError::type_error(h, ValidType::Atom, a1);
                        return Err(machine_st.error_form(err, stub));
                    }
                    _ => {}
                }

                let atom = match machine_st.compare_term_test(&a2, &a3) {
                    Some(Ordering::Greater) => {
                        let spec = fetch_atom_op_spec(clause_name!(">"), None, op_dir);
                        HeapCellValue::Atom(clause_name!(">"), spec)
                    }
                    Some(Ordering::Equal) => {
                        let spec = fetch_atom_op_spec(clause_name!("="), None, op_dir);
                        HeapCellValue::Atom(clause_name!("="), spec)
                    }
                    None | Some(Ordering::Less) => {
                        let spec = fetch_atom_op_spec(clause_name!("<"), None, op_dir);
                        HeapCellValue::Atom(clause_name!("<"), spec)
                    }
                };

                let h = machine_st.heap.h();

                machine_st.heap.push(atom);
                (machine_st.unify_fn)(machine_st, a1, Addr::Con(h));

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CompareTerm(qt) => {
                machine_st.compare_term(qt);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Read => {
                let stream = machine_st.get_stream_or_alias(
                    machine_st[temp_v!(1)],
                    stream_aliases,
                    "read",
                    2,
                )?;

                match machine_st.read(stream, machine_st.atom_tbl.clone(), op_dir) {
                    Ok(offset) => {
                        let addr = machine_st[temp_v!(2)];
                        (machine_st.unify_fn)(machine_st, addr, Addr::HeapCell(offset.heap_loc));
                    }
                    Err(ParserError::UnexpectedEOF) => {
                        let addr = machine_st[temp_v!(2)];
                        let eof = clause_name!("end_of_file".to_string(), machine_st.atom_tbl);

                        let atom = machine_st.heap.to_unifiable(HeapCellValue::Atom(eof, None));

                        (machine_st.unify_fn)(machine_st, addr, atom);
                    }
                    Err(e) => {
                        let h = machine_st.heap.h();
                        let stub = MachineError::functor_stub(clause_name!("read"), 2);

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
                let a1 = machine_st[temp_v!(1)];
                let a2 = machine_st[temp_v!(2)];

                machine_st.fail = machine_st.eq_test(a1, a2);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Ground => {
                machine_st.fail = machine_st.ground_test();
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Functor => {
                machine_st.try_functor(op_dir)?;
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::NotEq => {
                let a1 = machine_st[temp_v!(1)];
                let a2 = machine_st[temp_v!(2)];

                machine_st.fail =
                    if let Some(Ordering::Equal) = machine_st.compare_term_test(&a1, &a2) {
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

                list.sort_unstable_by(|a1, a2| {
                    machine_st
                        .compare_term_test(a1, a2)
                        .unwrap_or(Ordering::Less)
                });

                machine_st.term_dedup(&mut list);

                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(list.into_iter()));

                let r2 = machine_st[temp_v!(2)];
                (machine_st.unify_fn)(machine_st, r2, heap_addr);

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

                key_pairs.sort_by(|a1, a2| {
                    machine_st
                        .compare_term_test(&a1.0, &a2.0)
                        .unwrap_or(Ordering::Less)
                });

                let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(key_pairs));

                let r2 = machine_st[temp_v!(2)];
                (machine_st.unify_fn)(machine_st, r2, heap_addr);

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Is(r, ref at) => {
                let a1 = machine_st[r];
                let n2 = machine_st.get_number(at)?;

                let n2 = machine_st.heap.put_constant(n2.into());
                (machine_st.unify_fn)(machine_st, a1, n2);

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

        match ClauseType::from(name.clone(), arity, None) {
            ClauseType::BuiltIn(built_in) => {
                machine_st.setup_built_in_call(built_in.clone());
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
            ClauseType::Op(..) | ClauseType::Named(..) => {
                if let Some(idx) = code_dir.get(&(name.clone(), arity)) {
                    self.context_call(machine_st, name, arity, idx)?;
                } else {
                    return Err(machine_st.throw_undefined_error(name, arity));
                }
            }
            ClauseType::System(_) => {
                let name = functor!(clause_name(name));
                let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);

                return Err(machine_st.error_form(
                    MachineError::type_error(machine_st.heap.h(), ValidType::Callable, name),
                    stub,
                ));
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

impl CallPolicy for CWILCallPolicy {
    fn context_call(
        &mut self,
        machine_st: &mut MachineState,
        name: ClauseName,
        arity: usize,
        idx: &CodeIndex,
    ) -> CallResult {
        self.prev_policy
            .context_call(machine_st, name, arity, idx)?; //, indices)?;
        self.increment(machine_st)
    }

    fn retry_me_else(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy
            .retry_me_else(machine_st, offset, global_variables)?;
        self.increment(machine_st)
    }

    fn retry(
        &mut self,
        machine_st: &mut MachineState,
        offset: usize,
        global_variables: &mut GlobalVarDir,
    ) -> CallResult {
        self.prev_policy
            .retry(machine_st, offset, global_variables)?;
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
        self.prev_policy
            .trust(machine_st, offset, global_variables)?;
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
        self.prev_policy
            .call_builtin(machine_st, ct, code_dir, op_dir, stream_aliases)?;

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
        self.prev_policy
            .call_n(machine_st, arity, code_dir, op_dir, stream_aliases)?;

        self.increment(machine_st)
    }
}

downcast!(dyn CallPolicy);

#[derive(Debug)]
pub(crate) struct DefaultCallPolicy {}

impl CallPolicy for DefaultCallPolicy {}

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
        if self.inference_limit_exceeded || machine_st.ball.stub.h() > 0 {
            return Ok(());
        }

        if let Some(&(ref limit, bp)) = self.limits.last() {
            if self.count == *limit {
                self.inference_limit_exceeded = true;

                return Err(functor!(
                    "inference_limit_exceeded",
                    [addr(Addr::Usize(bp))]
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

pub(crate) trait CutPolicy: Any + fmt::Debug {
    // returns true iff we fail or cut redirected the MachineState's p itself
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool;
}

downcast!(dyn CutPolicy);

fn cut_body(machine_st: &mut MachineState, addr: &Addr) -> bool {
    let b = machine_st.b;

    match addr {
        &Addr::CutPoint(b0) | &Addr::Usize(b0) => {
            if b > b0 {
                machine_st.b = b0;
            }
        }
        _ => {
            machine_st.fail = true;
            return true;
        }
    };

    false
}

#[derive(Debug)]
pub(crate) struct DefaultCutPolicy {}

pub(super) fn deref_cut(machine_st: &mut MachineState, r: RegType) {
    let addr = machine_st.store(machine_st.deref(machine_st[r]));
    cut_body(machine_st, &addr);
}

impl CutPolicy for DefaultCutPolicy {
    fn cut(&mut self, machine_st: &mut MachineState, r: RegType) -> bool {
        let addr = machine_st[r];
        cut_body(machine_st, &addr)
    }
}

#[derive(Debug)]
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
                    machine_st[temp_v!(1)] = Addr::Usize(b_cutoff);
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

        match machine_st[r] {
            Addr::Usize(b0) | Addr::CutPoint(b0) => {
                if b > b0 {
                    machine_st.b = b0;
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
