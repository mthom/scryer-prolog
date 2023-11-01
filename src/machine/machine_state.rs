use crate::arena::*;
use crate::atom_table::*;
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
use crate::machine::Machine;
use crate::parser::ast::*;
use crate::read::TermWriteResult;
use crate::types::*;

use crate::parser::dashu::Integer;

use indexmap::IndexMap;

use std::convert::TryFrom;
use std::fmt;
use std::ops::{Index, IndexMut};
use std::sync::Arc;

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

#[derive(Debug)]
pub enum OnEOF {
    Return,
    Continue,
}

pub struct MachineState {
    pub atom_tbl: Arc<AtomTable>,
    pub arena: Arena,
    pub(super) pdl: Vec<HeapCellValue>,
    pub(super) s: HeapPtr,
    pub(super) s_offset: usize,
    pub(super) p: usize,
    pub(super) oip: u32, // first internal code ptr
    pub(super) iip: u32, // second internal code ptr
    pub(super) b: usize,
    pub(super) b0: usize,
    pub(super) e: usize,
    pub(super) num_of_args: usize,
    pub(super) cp: usize,
    pub(super) attr_var_init: AttrVarInitializer,
    pub(super) fail: bool,
    pub heap: Heap,
    pub(super) mode: MachineMode,
    pub(crate) stack: Stack,
    pub(super) registers: Registers,
    pub(super) trail: Vec<TrailEntry>,
    pub(super) tr: usize,
    pub(super) hb: usize,
    pub(super) block: usize,     // an offset into the OR stack.
    pub(super) scc_block: usize, // an offset into the OR stack for setup_call_cleanup/3.
    pub(super) ball: Ball,
    pub(super) ball_stack: Vec<Ball>, // save current ball before jumping via, e.g., verify_attr interrupt.
    pub(super) lifted_heap: Heap,
    pub(super) interms: Vec<Number>, // intermediate numbers.
    // locations of cleaners, cut points, the previous scc_block. for setup_call_cleanup/3.
    pub(super) cont_pts: Vec<(HeapCellValue, usize, usize)>,
    pub(super) cwil: CWIL,
    pub(crate) flags: MachineFlags,
    pub(crate) cc: usize,
    pub(crate) global_clock: usize,
    pub(crate) dynamic_mode: FirstOrNext,
    pub(crate) unify_fn: fn(&mut MachineState),
    pub(crate) bind_fn: fn(&mut MachineState, Ref, HeapCellValue),
    pub(crate) run_cleaners_fn: fn(&mut Machine) -> bool,
    pub(crate) increment_call_count_fn: fn(&mut MachineState) -> bool,
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
            .field("scc_block", &self.scc_block)
            .field("ball", &self.ball)
            .field("ball_stack", &self.ball_stack)
            .field("lifted_heap", &self.lifted_heap)
            .field("interms", &self.interms)
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

fn push_var_eq_functors<'a>(
    heap: &mut Heap,
    iter: impl Iterator<Item = (&'a VarKey, &'a HeapCellValue)>,
    atom_tbl: &AtomTable,
) -> Vec<HeapCellValue> {
    let mut list_of_var_eqs = vec![];

    for (var, binding) in iter {
        let var_atom = AtomTable::build_with(atom_tbl, &var.to_string());
        let h = heap.len();

        heap.push(atom_as_cell!(atom!("="), 2));
        heap.push(atom_as_cell!(var_atom));
        heap.push(*binding);

        list_of_var_eqs.push(str_loc_as_cell!(h));
    }

    list_of_var_eqs
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

        self.stub
            .iter()
            .cloned()
            .map(|heap_value| heap_value - diff)
            .collect()
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
    pub(crate) fn backtrack(&mut self) {
        let b = self.b;
        let or_frame = self.stack.index_or_frame(b);

        self.b0 = or_frame.prelude.b0;
        self.p = or_frame.prelude.bp;

        self.oip = or_frame.prelude.boip;
        self.iip = or_frame.prelude.biip;

        self.pdl.clear();
        self.fail = false;
    }

    pub(crate) fn increment_call_count(&mut self) -> bool {
        if self.cwil.inference_limit_exceeded || self.ball.stub.len() > 0 {
            return true;
        }

        if let Some(&(ref limit, block)) = self.cwil.limits.last() {
            if self.cwil.count == *limit {
                self.cwil.inference_limit_exceeded = true;
                self.block = block;
                self.unwind_stack();

                return false;
            } else {
                self.cwil.count += 1;
            }
        }

        true
    }

    #[allow(dead_code)]
    pub(super) fn try_char_list(
        &mut self,
        addrs: Vec<HeapCellValue>,
    ) -> Result<String, MachineError> {
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
                (HeapCellValueTag::Str, s) => {
                    let (name, arity) = cell_as_atom_cell!(self.heap[s])
                        .get_name_and_arity();

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

    #[inline(always)]
    pub(super) fn call_at_index(&mut self, arity: usize, p: usize) {
        self.cp = self.p + 1;
        self.p = p;
        self.oip = 0;
        self.iip = 0;
        self.num_of_args = arity;
        self.b0 = self.b;
    }

    #[inline(always)]
    pub(super) fn execute_at_index(&mut self, arity: usize, p: usize) {
        self.p = p;
        self.oip = 0;
        self.iip = 0;
        self.num_of_args = arity;
        self.b0 = self.b;
    }

    #[inline(always)]
    pub fn neck_cut(&mut self) {
        let b = self.b;
        let b0 = self.b0;

        if b > b0 {
            self.b = b0;

            if b > self.e {
                self.stack.truncate(b);
            }
        }
    }

    pub fn write_read_term_options(
        &mut self,
        mut var_list: Vec<(VarKey, HeapCellValue, usize)>,
        singleton_var_list: Vec<HeapCellValue>,
    ) -> CallResult {
        var_list.sort_by(|(_, _, idx_1), (_, _, idx_2)| idx_1.cmp(idx_2));

        let list_of_var_eqs = push_var_eq_functors(
            &mut self.heap,
            var_list.iter().filter_map(|(var_name, var, _)| {
                if var_name.is_anon() {
                    None
                } else {
                    Some((var_name, var))
                }
            }),
            &self.atom_tbl,
        );

        let singleton_addr = self.registers[3];
        let singletons_offset = heap_loc_as_cell!(iter_to_heap_list(
            &mut self.heap,
            singleton_var_list.into_iter()
        ));

        unify_fn!(*self, singletons_offset, singleton_addr);

        if self.fail {
            return Ok(());
        }

        let vars_addr = self.registers[4];
        let vars_offset = heap_loc_as_cell!(iter_to_heap_list(
            &mut self.heap,
            var_list.into_iter().map(|(_, cell, _)| cell)
        ));

        unify_fn!(*self, vars_offset, vars_addr);

        if self.fail {
            return Ok(());
        }

        let var_names_addr = self.registers[5];
        let var_names_offset = heap_loc_as_cell!(iter_to_heap_list(
            &mut self.heap,
            list_of_var_eqs.into_iter()
        ));

        Ok(unify_fn!(*self, var_names_offset, var_names_addr))
    }

    pub fn read_term_body(&mut self, mut term_write_result: TermWriteResult) -> CallResult {
        let heap_loc = read_heap_cell!(self.heap[term_write_result.heap_loc],
            (HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset) => {
                pstr_loc_as_cell!(term_write_result.heap_loc)
            }
            _ => {
                heap_loc_as_cell!(term_write_result.heap_loc)
            }
        );

        unify_fn!(*self, heap_loc, self.registers[2]);

        if self.fail {
            return Ok(());
        }

        for var in term_write_result.var_dict.values_mut() {
            *var = heap_bound_deref(&self.heap, *var);
        }

        let mut singleton_var_set: IndexMap<Ref, bool> = IndexMap::new();

        for cell in stackful_preorder_iter::<NonListElider>(&mut self.heap, &mut self.stack, heap_loc) {
            let cell = unmark_cell_bits!(cell);

            if let Some(var) = cell.as_var() {
                if !singleton_var_set.contains_key(&var) {
                    singleton_var_set.insert(var, true);
                } else {
                    singleton_var_set.insert(var, false);
                }
            }
        }

        let singleton_var_list = push_var_eq_functors(
            &mut self.heap,
            term_write_result
                .var_dict
                .iter()
                .filter(|(var_name, binding)| {
                    if var_name.is_anon() {
                        return false;
                    }

                    if let Some(r) = binding.as_var() {
                        *singleton_var_set.get(&r).unwrap_or(&false)
                    } else {
                        false
                    }
                }),
            &self.atom_tbl,
        );

        for var in term_write_result.var_dict.values_mut() {
            *var = heap_bound_deref(&self.heap, *var);
        }

        let mut var_list = Vec::with_capacity(singleton_var_set.len());

        for (var_name, addr) in term_write_result.var_dict {
            if let Some(var) = addr.as_var() {
                if let Some(idx) = singleton_var_set.get_index_of(&var) {
                    var_list.push((var_name, addr, idx));
                }
            }
        }

        self.write_read_term_options(var_list, singleton_var_list)
    }

    pub fn read_term_from_user_input_eof_handler(
        &mut self,
        stream: Stream,
    ) -> Result<OnEOF, MachineStub> {
        self.eof_action(self.registers[2], stream, atom!("read_term"), 3)?;

        if stream.options().eof_action() == EOFAction::Reset {
            if self.fail == false {
                return Ok(OnEOF::Continue);
            }
        }

        Ok(OnEOF::Return)
    }

    // Safety: the atom_tbl lives for the lifetime of the machine, as does the helper, so the ptr
    // will always be valid.
    pub fn read_term_from_user_input(
        &mut self,
        stream: Stream,
        indices: &mut IndexStore,
    ) -> CallResult {
        if let Stream::Readline(ptr) = stream {
            unsafe {
                let readline = ptr.as_ptr().as_mut().unwrap();
                readline.set_atoms_for_completion(&self.atom_tbl);
                return self.read_term(
                    stream,
                    indices,
                    MachineState::read_term_from_user_input_eof_handler,
                );
            }
        }

        unreachable!("Stream must be a Stream::Readline(_)")
    }

    pub fn read_term_eof_handler(&mut self, mut stream: Stream) -> Result<OnEOF, MachineStub> {
        if stream.at_end_of_stream() {
            unify!(self, self.registers[2], atom_as_cell!(atom!("end_of_file")));
            stream.set_past_end_of_stream(true);
            return Ok(OnEOF::Return);
        } else if stream.past_end_of_stream() {
            self.eof_action(self.registers[2], stream, atom!("read_term"), 3)?;

            if stream.options().eof_action() == EOFAction::Reset {
                if self.fail == false {
                    return Ok(OnEOF::Continue);
                }
            }
        }

        Ok(OnEOF::Return)
    }

    pub fn read_term(
        &mut self,
        stream: Stream,
        indices: &mut IndexStore,
        eof_handler: impl Fn(&mut Self, Stream) -> Result<OnEOF, MachineStub>,
    ) -> CallResult {
        self.check_stream_properties(
            stream,
            StreamType::Text,
            Some(self.registers[2]),
            atom!("read_term"),
            3,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options().eof_action() {
                return Ok(());
            } else if self.fail {
                return Ok(());
            }
        }

        loop {
            match self.read(stream, &indices.op_dir) {
                Ok(term_write_result) => return self.read_term_body(term_write_result),
                Err(err) => {
                    match &err {
                        CompilationError::ParserError(e) if e.is_unexpected_eof() => {
                            match eof_handler(self, stream)? {
                                OnEOF::Return => {
                                    return self.write_read_term_options(vec![], vec![])
                                }
                                OnEOF::Continue => continue,
                            }
                        }
                        _ => {}
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
        let double_quotes = self.store(self.deref(self.registers[8]));

        let term_to_be_printed = self.store(self.deref(self.registers[2]));
        let stub_gen = || functor_stub(atom!("write_term"), 2);

        let printer = match self.try_from_list(self.registers[6], stub_gen) {
            Ok(addrs) => {
                let mut var_names: IndexMap<HeapCellValue, VarPtr> = IndexMap::new();

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

                                read_heap_cell!(atom,
                                    (HeapCellValueTag::Char, c) => {
                                        var_names.insert(var, VarPtr::from(c.to_string()));
                                    }
                                    (HeapCellValueTag::Atom, (name, _arity)) => {
                                        debug_assert_eq!(_arity, 0);
                                        var_names.insert(var, VarPtr::from(&*name.as_str()));
                                    }
                                    (HeapCellValueTag::Str, s) => {
                                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                                            .get_name_and_arity();

                                        debug_assert_eq!(arity, 0);
                                        var_names.insert(var, VarPtr::from(&*name.as_str()));
                                    }
                                    _ => {
                                        unreachable!();
                                    }
                                );
                            }
                        }
                        _ => {
                        }
                    );
                }

                let ignore_ops = read_heap_cell!(ignore_ops,
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name == atom!("true")
                    }
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let numbervars = read_heap_cell!(numbervars,
                    (HeapCellValueTag::Atom, (name, _arity)) => {
                        name == atom!("true")
                    }
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let quoted = read_heap_cell!(quoted,
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let double_quotes = read_heap_cell!(double_quotes,
                    (HeapCellValueTag::Atom, (name, arity)) => {
                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.heap[s])
                            .get_name_and_arity();

                        debug_assert_eq!(arity, 0);
                        name == atom!("true")
                    }
                    _ => {
                        unreachable!()
                    }
                );

                let mut printer = HCPrinter::new(
                    &mut self.heap,
                    Arc::clone(&self.atom_tbl),
                    &mut self.stack,
                    op_dir,
                    PrinterOutputter::new(),
                    term_to_be_printed,
                );

                printer.ignore_ops = ignore_ops;
                printer.numbervars = numbervars;
                printer.quoted = quoted;
                printer.double_quotes = double_quotes;

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
                        let result = (&*n).try_into();

                        if let Ok(value) = result {
                            printer.max_depth = value;
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

    pub(super) fn read_predicate_key(
        &self,
        name: HeapCellValue,
        arity: HeapCellValue,
    ) -> (Atom, usize) {
        let name = cell_as_atom!(self.store(self.deref(name)));
        let arity = cell_as_fixnum!(self.store(self.deref(arity)));

        (name, usize::try_from(arity.get_num()).unwrap())
    }

    #[inline(always)]
    pub(super) fn cut_body(&mut self, value: HeapCellValue) {
        let b = self.b;

        read_heap_cell!(value,
            (HeapCellValueTag::CutPoint, b0) => {
                let b0 = b0.get_num() as usize;

                if b > b0 {
                    self.b = b0;
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }

    #[inline(always)]
    pub(super) fn cut_prev_body(&mut self, value: HeapCellValue) {
        let b = self.b;

        read_heap_cell!(value,
            (HeapCellValueTag::CutPoint, b0) => {
                let b0 = b0.get_num() as usize;
                let b0 = self.stack.index_or_frame(b0).prelude.b;

                if b > b0 {
                    self.b = b0;
                }
            }
            _ => {
                self.fail = true;
            }
        );
    }
}

#[derive(Debug)]
pub(crate) struct CWIL {
    count: Integer,
    limits: Vec<(Integer, usize)>,
    pub(crate) inference_limit_exceeded: bool,
}

impl CWIL {
    pub(crate) fn new() -> Self {
        CWIL {
            count: Integer::from(0),
            limits: vec![],
            inference_limit_exceeded: false,
        }
    }

    pub(crate) fn add_limit(&mut self, limit: usize, block: usize) -> &Integer {
        let mut limit = Integer::from(limit);
        limit += &self.count;

        match self.limits.last() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {}
            _ => self.limits.push((limit, block)),
        };

        &self.count
    }

    #[inline(always)]
    pub(crate) fn remove_limit(&mut self, block: usize) -> &Integer {
        if let Some((_, bl)) = self.limits.last() {
            if bl == &block {
                self.limits.pop();
            }
        }

        &self.count
    }

    #[inline(always)]
    pub(crate) fn reset(&mut self) {
        self.count = Integer::from(0);
        self.limits.clear();
        self.inference_limit_exceeded = false;
    }

    #[inline(always)]
    pub(crate) fn is_empty(&self) -> bool {
        self.limits.is_empty()
    }
}
