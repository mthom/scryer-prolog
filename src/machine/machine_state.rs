use crate::prolog_parser::ast::*;
use crate::prolog_parser::tabled_rc::*;

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_print::*;
use crate::machine::attributed_variables::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::modules::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::rug::Integer;

use crate::downcast::Any;

use crate::indexmap::{IndexMap, IndexSet};

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::io::Write;
use std::mem;
use std::ops::{Index, IndexMut};

#[derive(Debug)]
pub(crate) struct HeapPStrIter<'a> {
    focus: Addr,
    machine_st: &'a MachineState,
    seen: IndexSet<Addr>,
}

impl<'a> HeapPStrIter<'a> {
    #[inline]
    fn new(machine_st: &'a MachineState, focus: Addr) -> Self {
        HeapPStrIter {
            focus,
            machine_st,
            seen: IndexSet::new(),
        }
    }

    #[inline]
    pub(crate)
    fn focus(&self) -> Addr {
        self.machine_st.store(self.machine_st.deref(self.focus))
    }

    #[inline]
    pub(crate)
    fn to_string(&mut self) -> String {
        let mut buf = String::new();

        while let Some(iteratee) = self.next() {
            match iteratee {
                PStrIteratee::Char(c) => {
                    buf.push(c);
                }
                PStrIteratee::PStrSegment(h, n) => {
                    match &self.machine_st.heap[h] {
                        HeapCellValue::PartialString(ref pstr, _) => {
                            buf += pstr.as_str_from(n);
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }
            }
        }

        buf
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PStrIteratee {
    Char(char),
    PStrSegment(usize, usize),
}

impl<'a> Iterator for HeapPStrIter<'a> {
    type Item = PStrIteratee;

    fn next(&mut self) -> Option<Self::Item> {
        let addr = self.machine_st.store(self.machine_st.deref(self.focus));

        if !self.seen.contains(&addr) {
            self.seen.insert(addr);
        } else {
            return None;
        }

        match addr {
            Addr::PStrLocation(h, n) => {
                if let &HeapCellValue::PartialString(_, has_tail) = &self.machine_st.heap[h] {
                    self.focus = if has_tail {
                        Addr::HeapCell(h + 1)
                    } else {
                        Addr::EmptyList
                    };

                    return Some(PStrIteratee::PStrSegment(h, n));
                } else {
                    unreachable!()
                }
            }
            Addr::Lis(l) => {
                let addr = self.machine_st.store(self.machine_st.deref(Addr::HeapCell(l)));

                let opt_c = match addr {
                    Addr::Con(h) if self.machine_st.heap.atom_at(h) => {
                        if let HeapCellValue::Atom(ref atom, _) = &self.machine_st.heap[h] {
                            if atom.is_char() {
                                Some(atom.as_str().chars().next().unwrap())
                            } else {
                                None
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    Addr::Char(c) => {
                        Some(c)
                    }
                    _ => {
                        None
                    }
                };

                if let Some(c) = opt_c {
                    self.focus = Addr::HeapCell(l + 1);
                    return Some(PStrIteratee::Char(c));
                } else {
                    return None;
                }
            }
            Addr::EmptyList => {
                self.focus = Addr::EmptyList;
                return None;
            }
            _ => {
                return None;
            }
        }
    }
}

#[inline]
pub(super)
fn compare_pstr_prefixes<'a>(
    i1: &mut HeapPStrIter<'a>,
    i2: &mut HeapPStrIter<'a>,
) -> Option<Ordering> {
    let mut r1 = i1.next();
    let mut r2 = i2.next();

    loop {
        if let Some(r1i) = r1 {
            if let Some(r2i) = r2 {
                match (r1i, r2i) {
                    (PStrIteratee::Char(c1), PStrIteratee::Char(c2)) => {
                        if c1 != c2 {
                            return c1.partial_cmp(&c2);
                        }
                    }
                    (PStrIteratee::Char(c1), PStrIteratee::PStrSegment(h, n)) => {
                        if let &HeapCellValue::PartialString(ref pstr, _) = &i2.machine_st.heap[h] {
                            if let Some(c2) = pstr.as_str_from(n).chars().next() {
                                if c1 != c2 {
                                    return c1.partial_cmp(&c2);
                                } else {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h, n + c2.len_utf8()));

                                    continue;
                                }
                            } else {
                                r2 = i2.next();
                                continue;
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (PStrIteratee::PStrSegment(h, n), PStrIteratee::Char(c2)) => {
                        if let &HeapCellValue::PartialString(ref pstr, _) = &i1.machine_st.heap[h] {
                            if let Some(c1) = pstr.as_str_from(n).chars().next() {
                                if c1 != c2 {
                                    return c2.partial_cmp(&c1);
                                } else {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h, n + c1.len_utf8()));

                                    continue;
                                }
                            } else {
                                r1 = i1.next();
                                continue;
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    (PStrIteratee::PStrSegment(h1, n1), PStrIteratee::PStrSegment(h2, n2)) => {
                        match (&i1.machine_st.heap[h1], &i2.machine_st.heap[h2]) {
                            (
                                &HeapCellValue::PartialString(ref pstr1, _),
                                &HeapCellValue::PartialString(ref pstr2, _),
                            ) => {
                                let str1 = pstr1.as_str_from(n1);
                                let str2 = pstr2.as_str_from(n2);

                                if str1.starts_with(str2) {
                                    r1 = Some(PStrIteratee::PStrSegment(h1, n1 + str2.len()));
                                    r2 = i2.next();

                                    continue;
                                } else if str2.starts_with(str1) {
                                    r1 = i1.next();
                                    r2 = Some(PStrIteratee::PStrSegment(h2, n2 + str1.len()));

                                    continue;
                                } else {
                                    return str1.partial_cmp(str2);
                                }
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                }

                r1 = i1.next();
                r2 = i2.next();

                continue;
            }
        }

        return match (i1.focus(), i2.focus()) {
            (Addr::EmptyList, Addr::EmptyList) => {
                Some(Ordering::Equal)
            }
            (Addr::EmptyList, _) => {
                Some(Ordering::Less)
            }
            (_, Addr::EmptyList) => {
                Some(Ordering::Greater)
            }
            _ => {
                None
            }
        };
    }
}

#[inline]
pub(super)
fn compare_pstr_to_string<'a>(
    heap_pstr_iter: &mut HeapPStrIter<'a>,
    s: &String,
) -> Option<usize> {
    let mut s_offset = 0;

    while let Some(iteratee) = heap_pstr_iter.next() {
        match iteratee {
            PStrIteratee::Char(c1) => {
                if let Some(c2) = s[s_offset ..].chars().next() {
                    if c1 != c2 {
                        return None;
                    } else {
                        s_offset += c1.len_utf8();
                    }
                } else {
                    return Some(s_offset);
                }
            }
            PStrIteratee::PStrSegment(h, n) => {
                match heap_pstr_iter.machine_st.heap[h] {
                    HeapCellValue::PartialString(ref pstr, _) => {
                        let t = pstr.as_str_from(n);

                        if s[s_offset ..].starts_with(t) {
                            s_offset += t.len();
                        } else if t.starts_with(&s[s_offset ..]) {
                            heap_pstr_iter.focus =
                                Addr::PStrLocation(h, n + s[s_offset ..].len());

                            s_offset += s[s_offset ..].len();
                            return Some(s_offset);
                        } else {
                            return None;
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
        }

        if s[s_offset ..].is_empty() {
            return Some(s_offset);
        }
    }

    Some(s_offset)
}

#[derive(Debug)]
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
                &HeapCellValue::Addr(addr) => {
                    HeapCellValue::Addr(addr - diff)
                }
                heap_value => {
                    heap_value.context_free_clone()
                }
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
            Addr::StackCell(fr, sc) => {
                self.stack.index_and_frame(fr)[sc]
            }
            addr => {
                addr
            }
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
            RegType::Temp(temp) => {
                &mut self.registers[temp]
            }
            RegType::Perm(perm) => {
                let e = self.e;

                &mut self.stack.index_and_frame_mut(e)[perm]
            }
        }
    }
}

pub type Registers = Vec<Addr>;

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
    pub(super)
    fn read(&self, heap: &Heap) -> Addr {
        match self {
            &HeapPtr::HeapCell(h) => {
                Addr::HeapCell(h)
            }
            &HeapPtr::PStrChar(h, n) => {
                if let &HeapCellValue::PartialString(ref pstr, has_tail) = &heap[h] {
                    if let Some(c) = pstr.range_from(n ..).next() {
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
            &HeapPtr::PStrLocation(h, n) => {
                Addr::PStrLocation(h, n)
            }
        }
    }
}

impl Default for HeapPtr {
    fn default() -> Self {
        HeapPtr::HeapCell(0)
    }
}

#[derive(Debug)]
pub struct MachineState {
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
    pub(crate) heap_locs: HeapVarDict,
    pub(crate) flags: MachineFlags,
    pub(crate) at_end_of_expansion: bool,
    pub(crate) inferences: Integer,
}

impl MachineState {
    pub(crate)
    fn read_term(
        &mut self,
        mut stream: Stream,
        indices: &mut IndexStore,
    ) -> CallResult {
        self.check_stream_properties(
            &mut stream,
            StreamType::Text,
            Some(self[temp_v!(2)]),
            clause_name!("read_term"),
            3,
        )?;

        if stream.past_end_of_stream() {
            if EOFAction::Reset != stream.options.eof_action {
                return return_from_clause!(self.last_call, self);
            } else if self.fail {
                return Ok(());
            }
        }

        let mut orig_stream = stream.clone();

        loop {
            match self.read(
                stream.clone(),
                indices.atom_tbl.clone(),
                &indices.op_dir,
            ) {
                Ok(term_write_result) => {
                    let term = self[temp_v!(2)];
                    self.unify(Addr::HeapCell(term_write_result.heap_loc), term);

                    if self.fail {
                        return Ok(());
                    }

                    let mut list_of_var_eqs = vec![];

                    for (var, binding) in term_write_result.var_dict.into_iter() {
                        let var_atom = clause_name!(var.to_string(), indices.atom_tbl);

                        let h = self.heap.h();
                        let spec = fetch_atom_op_spec(clause_name!("="), None, &indices.op_dir);

                        self.heap.push(HeapCellValue::NamedStr(2, clause_name!("="), spec));
                        self.heap.push(HeapCellValue::Atom(var_atom, None));
                        self.heap.push(HeapCellValue::Addr(binding));

                        list_of_var_eqs.push(Addr::Str(h));
                    }

                    let mut var_set: IndexMap<Ref, bool> = IndexMap::new();

                    for addr in self.acyclic_pre_order_iter(term) {
                        if let Some(var) = addr.as_var() {
                            if !var_set.contains_key(&var) {
                                var_set.insert(var, true);
                            } else {
                                var_set.insert(var, false);
                            }
                        }
                    }

                    let mut var_list = vec![];
                    let mut singleton_var_list = vec![];

                    for addr in self.acyclic_pre_order_iter(term) {
                        if let Some(var) = addr.as_var() {
                            if var_set.get(&var) == Some(&true) {
                                singleton_var_list.push(var.as_addr());
                            }

                            var_list.push(var.as_addr());
                        }
                    }

                    let singleton_addr = self[temp_v!(3)];
                    let singletons_offset =
                        Addr::HeapCell(self.heap.to_list(singleton_var_list.into_iter()));

                    self.unify(singletons_offset, singleton_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let vars_addr = self[temp_v!(4)];
                    let vars_offset =
                        Addr::HeapCell(self.heap.to_list(var_list.into_iter()));

                    self.unify(vars_offset, vars_addr);

                    if self.fail {
                        return Ok(());
                    }

                    let var_names_addr = self[temp_v!(5)];
                    let var_names_offset =
                        Addr::HeapCell(self.heap.to_list(list_of_var_eqs.into_iter()));

                    return Ok(self.unify(var_names_offset, var_names_addr));
                }
                Err(err) => {
                    if let ParserError::UnexpectedEOF = err {
                        self.eof_action(
                            self[temp_v!(2)],
                            &mut orig_stream,
                            clause_name!("read_term"),
                            3
                        )?;

                        if orig_stream.options.eof_action == EOFAction::Reset {
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

    pub(crate)
    fn write_term<'a>(
        &'a self,
        op_dir: &'a OpDir,
    ) -> Result<Option<HCPrinter<'a, PrinterOutputter>>, MachineStub>
    {
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
                            &HeapCellValue::NamedStr(2, ref name, _)
                                if name.as_str() == "=" =>
                            {
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
                            _ => {
                            }
                        },
                        _ => {
                        }
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

    #[inline]
    pub(crate)
    fn heap_pstr_iter<'a>(&'a self, focus: Addr) -> HeapPStrIter<'a> {
        HeapPStrIter::new(self, focus)
    }

    pub(super)
    fn try_char_list(&self, addrs: Vec<Addr>) -> Result<String, MachineError> {
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
                _ => {
                }
            };

            let h = self.heap.h();

            return Err(
                MachineError::type_error(h, ValidType::Character, addr)
            );
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

fn try_in_situ_lookup(name: ClauseName, arity: usize, indices: &IndexStore) -> Option<LocalCodePtr>
{
    match indices.in_situ_code_dir.get(&(name.clone(), arity)) {
        Some(p) => Some(LocalCodePtr::InSituDirEntry(*p)),
        None =>
            match indices.code_dir.get(&(name, arity)) {
                Some(ref idx) => {
                    if let IndexPtr::Index(p) = idx.0.borrow().0 {
                        Some(LocalCodePtr::DirEntry(p))
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
            machine_st.execute_at_index(arity, p);
        } else {
            machine_st.call_at_index(arity, p);
        }

        machine_st.p = CodePtr::Local(p);
        Ok(())
    } else {
        let stub = MachineError::functor_stub(name.clone(), arity);
        let h = machine_st.heap.h();
        let key = ExistenceError::Procedure(name, arity);

        Err(machine_st.error_form(MachineError::existence_error(h, key), stub))
    }
}

pub(crate) type CallResult = Result<(), Vec<HeapCellValue>>;

pub(crate) trait CallPolicy: Any + fmt::Debug {
    fn retry_me_else(&mut self, machine_st: &mut MachineState, offset: usize) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1];
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
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1];
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
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1];
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

        machine_st.b = machine_st.stack.index_or_frame(b).prelude.b;
        machine_st.stack.truncate(b);

        machine_st.hb = machine_st.heap.h();
        machine_st.p += offset;

        Ok(())
    }

    fn trust_me(&mut self, machine_st: &mut MachineState) -> CallResult {
        let b = machine_st.b;
        let n = machine_st.stack.index_or_frame(b).prelude.univ_prelude.num_cells;

        for i in 1 .. n + 1 {
            machine_st.registers[i] = machine_st.stack.index_or_frame(b)[i-1];
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

        machine_st.inferences += 1;

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

        machine_st.inferences += 1;

        Ok(())
    }

    fn call_builtin(
        &mut self,
        machine_st: &mut MachineState,
        ct: &BuiltInClauseType,
        indices: &mut IndexStore,
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
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
                                ">" | "<" | "=" => {
                                }
                                _ => {
                                    let stub =
                                        MachineError::functor_stub(clause_name!("compare"), 3);

                                    let err = MachineError::domain_error(DomainErrorType::Order, a1);
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
                    _ => {
                    }
                }

                let atom = match machine_st.compare_term_test(&a2, &a3) {
                    Some(Ordering::Greater) => {
                        let spec = fetch_atom_op_spec(clause_name!(">"), None, &indices.op_dir);
                        HeapCellValue::Atom(clause_name!(">"), spec)
                    }
                    Some(Ordering::Equal) => {
                        let spec = fetch_atom_op_spec(clause_name!("="), None, &indices.op_dir);
                        HeapCellValue::Atom(clause_name!("="), spec)
                    }
                    None | Some(Ordering::Less) => {
                        let spec = fetch_atom_op_spec(clause_name!("<"), None, &indices.op_dir);
                        HeapCellValue::Atom(clause_name!("<"), spec)
                    }
                };

                let h = machine_st.heap.h();

                machine_st.heap.push(atom);
                machine_st.unify(a1, Addr::Con(h));

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::CompareTerm(qt) => {
                machine_st.compare_term(qt);
                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Nl => {
                write!(current_output_stream, "\n").unwrap();
                current_output_stream.flush().unwrap();

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Read => {
                match machine_st.read(
                    current_input_stream.clone(),
                    indices.atom_tbl.clone(),
                    &indices.op_dir,
                ) {
                    Ok(offset) => {
                        let addr = machine_st[temp_v!(1)];
                        machine_st.unify(addr, Addr::HeapCell(offset.heap_loc));
                    }
                    Err(ParserError::UnexpectedEOF) => {
                        let addr = machine_st[temp_v!(1)];
                        let eof = clause_name!("end_of_file".to_string(),
                            indices.atom_tbl);
                        let atom = machine_st.heap.to_unifiable(
                            HeapCellValue::Atom(eof, None)
                        );
                        machine_st.unify(addr, atom);
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
                machine_st.try_functor(&indices)?;
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
                    machine_st.compare_term_test(a1, a2).unwrap_or(Ordering::Less)
                });

                machine_st.term_dedup(&mut list);

                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(list.into_iter()));

                let r2 = machine_st[temp_v!(2)];
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

                key_pairs.sort_by(|a1, a2| {
                    machine_st.compare_term_test(&a1.0, &a2.0).unwrap_or(Ordering::Less)
                });

                let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
                let heap_addr = Addr::HeapCell(machine_st.heap.to_list(key_pairs));

                let r2 = machine_st[temp_v!(2)];
                machine_st.unify(r2, heap_addr);

                return_from_clause!(machine_st.last_call, machine_st)
            }
            &BuiltInClauseType::Is(r, ref at) => {
                let a1 = machine_st[r];
                let n2 = machine_st.get_number(at)?;

                let n2 = machine_st.heap.put_constant(n2.into());
                machine_st.unify(a1, n2);

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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) -> CallResult {
        if let Some((name, arity)) = machine_st.setup_call_n(arity) {
            match ClauseType::from(name.clone(), arity, None) {
                ClauseType::BuiltIn(built_in) => {
                    machine_st.setup_built_in_call(built_in.clone());
                    self.call_builtin(
                        machine_st,
                        &built_in,
                        indices,
                        current_input_stream,
                        current_output_stream,
                    )?;
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
                    let name = functor!(clause_name(name));
                    let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);

                    return Err(machine_st.error_form(
                        MachineError::type_error(machine_st.heap.h(), ValidType::Callable, name),
                        stub,
                    ));
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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) -> CallResult {
        self.prev_policy.call_builtin(
            machine_st,
            ct,
            indices,
            current_input_stream,
            current_output_stream
        )?;

        self.increment(machine_st)
    }

    fn call_n(
        &mut self,
        machine_st: &mut MachineState,
        arity: usize,
        indices: &mut IndexStore,
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) -> CallResult {
        self.prev_policy.call_n(
            machine_st,
            arity,
            indices,
            current_input_stream,
            current_output_stream,
        )?;

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
    pub(crate)
    fn new_in_place(policy: &mut Box<dyn CallPolicy>) {
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

    pub(crate)
    fn add_limit(&mut self, mut limit: Integer, b: usize) -> &Integer {
        limit += &self.count;

        match self.limits.last().cloned() {
            Some((ref inner_limit, _)) if *inner_limit <= limit => {}
            _ => self.limits.push((limit, b)),
        };

        &self.count
    }

    pub(crate)
    fn remove_limit(&mut self, b: usize) -> &Integer {
        if let Some((_, bp)) = self.limits.last().cloned() {
            if bp == b {
                self.limits.pop();
            }
        }

        &self.count
    }

    pub(crate)
    fn is_empty(&self) -> bool {
        self.limits.is_empty()
    }

    pub(crate)
    fn into_inner(&mut self) -> Box<dyn CallPolicy> {
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
