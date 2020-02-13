use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use crate::prolog::arithmetic::*;
use crate::prolog::clause_types::*;
use crate::prolog::forms::*;
use crate::prolog::heap_iter::*;
use crate::prolog::instructions::*;
use crate::prolog::machine::INTERRUPT;
use crate::prolog::machine::attributed_variables::*;
use crate::prolog::machine::code_repo::CodeRepo;
use crate::prolog::machine::copier::*;
use crate::prolog::machine::heap::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;
use crate::prolog::machine::stack::*;
use crate::prolog::ordered_float::*;
use crate::prolog::read::PrologStream;
use crate::prolog::rug::{Integer, Rational};

use indexmap::{IndexMap, IndexSet};

use std::cmp::{max, min, Ordering};
use std::f64;
use std::iter::FromIterator;
use std::mem;
use std::rc::Rc;

macro_rules! try_numeric_result {
    ($s: ident, $e: expr, $caller: expr) => {{
        match $e {
            Ok(val) => Ok(val),
            Err(e) => Err($s.error_form(MachineError::evaluation_error(e), $caller)),
        }
    }};
}

macro_rules! try_or_fail {
    ($s:ident, $e:expr) => {{
        match $e {
            Ok(val) => val,
            Err(msg) => {
                $s.throw_exception(msg);
                return;
            }
        }
    }};
}

impl MachineState {
    pub(crate) fn new() -> Self {
        MachineState {
            s: 0,
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: LocalCodePtr::default(),
            attr_var_init: AttrVarInitializer::new(0, 0),
            fail: false,
            heap: Heap::with_capacity(1024),
            mode: MachineMode::Write,
            stack: Stack::new(),
            registers: vec![Addr::HeapCell(0); MAX_ARITY + 1], // self.registers[0] is never used.
            trail: vec![],
            tr: 0,
            hb: 0,
            block: 0,
            ball: Ball::new(),
            lifted_heap: Vec::with_capacity(1024),
            interms: vec![Number::default(); 256],
            last_call: false,
            heap_locs: HeapVarDict::new(),
            flags: MachineFlags::default(),
            at_end_of_expansion: false
        }
    }

    pub(crate) fn with_capacity(capacity: usize) -> Self {
        MachineState {
            s: 0,
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: LocalCodePtr::default(),
            attr_var_init: AttrVarInitializer::new(0, 0),
            fail: false,
            heap: Heap::with_capacity(capacity),
            mode: MachineMode::Write,
            stack: Stack::new(),
            registers: vec![Addr::HeapCell(0); MAX_ARITY + 1], // self.registers[0] is never used.
            trail: vec![],
            tr: 0,
            hb: 0,
            block: 0,
            ball: Ball::new(),
            lifted_heap: Vec::with_capacity(capacity),
            interms: vec![Number::default(); 0],
            last_call: false,
            heap_locs: HeapVarDict::new(),
            flags: MachineFlags::default(),
            at_end_of_expansion: false
        }
    }

    #[allow(dead_code)]
    pub fn print_heap(&self, start: usize) {
        for h in start .. self.heap.h {
            println!("{} : {}", h, self.heap[h]);
        }
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.flags
    }

    pub(crate) fn store(&self, addr: Addr) -> Addr {
        match addr {
            Addr::AttrVar(h) | Addr::HeapCell(h) => self.heap[h].as_addr(h),
            Addr::StackCell(fr, sc) => self.stack.index_and_frame(fr)[sc].clone(),
            addr => addr,
        }
    }

    pub(crate) fn deref(&self, mut addr: Addr) -> Addr {
        loop {
            let value = self.store(addr.clone());

            if value.is_ref() && value != addr {
                addr = value;
                continue;
            }

            return addr;
        }
    }

    fn bind_attr_var(&mut self, h: usize, addr: Addr) {
        match addr.as_var() {
            Some(Ref::HeapCell(hc)) => {
                self.heap[hc] = HeapCellValue::Addr(Addr::AttrVar(h));
                self.trail(TrailRef::Ref(Ref::HeapCell(hc)));
            }
            Some(Ref::StackCell(fr, sc)) => {
                self.stack.index_and_frame_mut(fr)[sc] = Addr::AttrVar(h);
                self.trail(TrailRef::Ref(Ref::StackCell(fr, sc)));
            }
            _ => {
                self.push_attr_var_binding(h, addr.clone());
                self.heap[h] = HeapCellValue::Addr(addr);
                self.trail(TrailRef::Ref(Ref::AttrVar(h)));
            }
        }
    }

    pub(super) fn bind(&mut self, r1: Ref, a2: Addr) {
        let t1 = self.store(r1.as_addr());
        let t2 = self.store(a2.clone());

        if t1.is_ref() && (!t2.is_ref() || a2 < r1) {
            match r1 {
                Ref::StackCell(fr, sc) => self.stack.index_and_frame_mut(fr)[sc] = t2,
                Ref::HeapCell(h) => self.heap[h] = HeapCellValue::Addr(t2),
                Ref::AttrVar(h) => return self.bind_attr_var(h, t2),
            };

            self.trail(TrailRef::from(r1));
        } else {
            match a2.as_var() {
                Some(Ref::StackCell(fr, sc)) => {
                    self.stack.index_and_frame_mut(fr)[sc] = t1;
                    self.trail(TrailRef::Ref(Ref::StackCell(fr, sc)));
                }
                Some(Ref::HeapCell(h)) => {
                    self.heap[h] = HeapCellValue::Addr(t1);
                    self.trail(TrailRef::Ref(Ref::HeapCell(h)));
                }
                Some(Ref::AttrVar(h)) =>
                    self.bind_attr_var(h, t1),
                None => {}
            }
        }
    }

    fn deconstruct_chars(
        &mut self,
        s: Rc<String>,
        string_offset: usize,
        list_cell: usize,
        pdl: &mut Vec<Addr>,
    ) -> bool {
        if s.len() > string_offset {
            if let Some(c) = s[string_offset ..].chars().next() {
                pdl.push(Addr::Con(Constant::String(string_offset + c.len_utf8(), s)));
                pdl.push(Addr::HeapCell(list_cell + 1));

                pdl.push(Addr::Con(Constant::Char(c)));
                pdl.push(Addr::HeapCell(list_cell));

                return true;
            }
        }

        false
    }

    fn bind_with_occurs_check(&mut self, r: Ref, addr: Addr) {
        let mut fail = false;

        for value in self.acyclic_pre_order_iter(addr.clone()) {
            if let HeapCellValue::Addr(addr) = value {
                if let Some(inner_r) = addr.as_var() {
                    if r == inner_r {
                        fail = true;
                        break;
                    }
                }
            }
        }

        self.fail = fail;
        self.bind(r, addr);
    }

    pub(super)
    fn unify_with_occurs_check(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];
        let mut tabu_list: IndexSet<(Addr, Addr)> = IndexSet::new();

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                let d1 = self.store(d1);
                let d2 = self.store(d2);

                if tabu_list.contains(&(d1.clone(), d2.clone())) {
                    continue;
                } else {
                    tabu_list.insert((d1.clone(), d2.clone()));
                }

                match (d1.clone(), d2.clone()) {
                    (Addr::AttrVar(h), addr) | (addr, Addr::AttrVar(h)) => {
                        self.bind_with_occurs_check(Ref::AttrVar(h), addr)
                    }
                    (Addr::HeapCell(h), addr) | (addr, Addr::HeapCell(h)) => {
                        self.bind_with_occurs_check(Ref::HeapCell(h), addr)
                    }
                    (Addr::StackCell(fr, sc), addr) | (addr, Addr::StackCell(fr, sc)) => {
                        self.bind_with_occurs_check(Ref::StackCell(fr, sc), addr)
                    }
                    (Addr::Lis(a1), Addr::Str(a2)) | (Addr::Str(a2), Addr::Lis(a1)) => {
                        if let &HeapCellValue::NamedStr(n2, ref f2, _) = &self.heap[a2] {
                            if f2.as_str() == "." && n2 == 2 {
                                pdl.push(Addr::HeapCell(a1));
                                pdl.push(Addr::HeapCell(a2 + 1));

                                pdl.push(Addr::HeapCell(a1 + 1));
                                pdl.push(Addr::HeapCell(a2 + 2));

                                continue;
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::Lis(a1), Addr::Con(Constant::String(n, s)))
                  | (Addr::Con(Constant::String(n, s)), Addr::Lis(a1)) => {
                        if self.deconstruct_chars(s, n, a1, &mut pdl) {
                            continue;
                        }

                        self.fail = true;
                    }
                    (Addr::Con(Constant::EmptyList), Addr::Con(Constant::String(n, ref s)))
                  | (Addr::Con(Constant::String(n, ref s)), Addr::Con(Constant::EmptyList))
                        if !self.flags.double_quotes.is_atom() =>
                    {
                        if n >= s.len() {
                            continue;
                        }

                        self.fail = true;
                    }
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    }
                    (Addr::Con(ref c1), Addr::Con(ref c2)) => {
                        if c1 != c2 {
                            self.fail = true;
                        }
                    }
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1, _) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2, _) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1..n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    _ => self.fail = true,
                };
            }
        }
    }

    pub(super)
    fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];
        let mut tabu_list: IndexSet<(Addr, Addr)> = IndexSet::new();

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                let d1 = self.store(d1);
                let d2 = self.store(d2);

                if tabu_list.contains(&(d1.clone(), d2.clone())) {
                    continue;
                } else {
                    tabu_list.insert((d1.clone(), d2.clone()));
                }

                match (d1.clone(), d2.clone()) {
                    (Addr::AttrVar(h), addr) | (addr, Addr::AttrVar(h)) => {
                        self.bind(Ref::AttrVar(h), addr);
                    }
                    (Addr::HeapCell(h), _) => {
                        self.bind(Ref::HeapCell(h), d2);
                    }
                    (_, Addr::HeapCell(h)) => {
                        self.bind(Ref::HeapCell(h), d1);
                    }
                    (Addr::StackCell(fr, sc), _) => {
                        self.bind(Ref::StackCell(fr, sc), d2);
                    }
                    (_, Addr::StackCell(fr, sc)) => {
                        self.bind(Ref::StackCell(fr, sc), d1);
                    }
                    (Addr::Lis(a1), Addr::Str(a2)) | (Addr::Str(a2), Addr::Lis(a1)) => {
                        if let &HeapCellValue::NamedStr(n2, ref f2, _) = &self.heap[a2] {
                            if f2.as_str() == "." && n2 == 2 {
                                pdl.push(Addr::HeapCell(a1));
                                pdl.push(Addr::HeapCell(a2 + 1));

                                pdl.push(Addr::HeapCell(a1 + 1));
                                pdl.push(Addr::HeapCell(a2 + 2));

                                continue;
                            }
                        }

                        self.fail = true;
                    }
                    (Addr::Lis(a1), Addr::Con(Constant::String(n, s)))
                  | (Addr::Con(Constant::String(n, s)), Addr::Lis(a1)) => {
                        if self.deconstruct_chars(s, n, a1, &mut pdl) {
                            continue;
                        }

                        self.fail = true;
                    }
                    (Addr::Con(Constant::EmptyList), Addr::Con(Constant::String(n, ref s)))
                  | (Addr::Con(Constant::String(n, ref s)), Addr::Con(Constant::EmptyList))
                        if !self.flags.double_quotes.is_atom() =>
                    {
                        if n >= s.len() {
                            continue;
                        }

                        self.fail = true;
                    }
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    }
                    (Addr::Con(ref c1), Addr::Con(ref c2)) => {
                        if c1 != c2 {
                            self.fail = true;
                        }
                    }
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1, _) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2, _) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1..n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    }
                    _ => self.fail = true,
                };
            }
        }
    }

    pub(super) fn trail(&mut self, r: TrailRef) {
        match r {
            TrailRef::Ref(Ref::HeapCell(h)) => {
                if h < self.hb {
                    self.trail.push(TrailRef::Ref(Ref::HeapCell(h)));
                    self.tr += 1;
                }
            }
            TrailRef::Ref(Ref::AttrVar(h)) => {
                if h < self.hb {
                    self.trail.push(TrailRef::Ref(Ref::AttrVar(h)));
                    self.tr += 1;
                }
            }
            TrailRef::AttrVarHeapLink(h) => {
                if h < self.hb {
                    self.trail.push(TrailRef::AttrVarHeapLink(h));
                    self.tr += 1;
                }
            }
            TrailRef::AttrVarListLink(h, l) => {
                if h < self.hb {
                    self.trail.push(TrailRef::AttrVarListLink(h, l));
                    self.tr += 1;
                }
            }
            TrailRef::Ref(Ref::StackCell(b, sc)) => {
                if b < self.b {
                    self.trail.push(TrailRef::Ref(Ref::StackCell(b, sc)));
                    self.tr += 1;
                }
            }
        }
    }

    pub(super) fn unwind_trail(&mut self, a1: usize, a2: usize) {
        // the sequence is reversed to respect the chronology of trail
        // additions, now that deleted attributes can be undeleted by
        // backtracking.
        for i in (a1..a2).rev() {
            match self.trail[i] {
                TrailRef::Ref(Ref::HeapCell(h)) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::HeapCell(h))
                }
                TrailRef::Ref(Ref::AttrVar(h)) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::AttrVar(h))
                }
                TrailRef::Ref(Ref::StackCell(fr, sc)) => {
                    self.stack.index_and_frame_mut(fr)[sc] = Addr::StackCell(fr, sc)
                }
                TrailRef::AttrVarHeapLink(h) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::HeapCell(h));
                }
                TrailRef::AttrVarListLink(h, l) => {
                    self.heap[h] = HeapCellValue::Addr(Addr::Lis(l));
                }
            }
        }
    }

    pub(super) fn tidy_trail(&mut self) {
        if self.b == 0 {
            return;
        }

        let b = self.b;
        let hb = self.hb;
        let mut offset = 0;

        for i in self.stack.index_or_frame(b).prelude.tr .. self.tr {
            match self.trail[i] {
                TrailRef::Ref(Ref::AttrVar(tr_i))
              | TrailRef::Ref(Ref::HeapCell(tr_i))
              | TrailRef::AttrVarHeapLink(tr_i)
              | TrailRef::AttrVarListLink(tr_i, _) => {
                    if tr_i >= hb {
                        offset += 1;
                    } else {
                        self.trail[i - offset] = self.trail[i];
                    }
                }
                TrailRef::Ref(Ref::StackCell(b, _)) => {
                    if b < self.b {
                        self.trail[i - offset] = self.trail[i];
                    } else {
                        offset += 1;
                    }
                }
            }
        }

        self.tr -= offset;
        self.trail.truncate(self.tr);
    }

    pub(super) fn write_constant_to_var(&mut self, addr: Addr, c: Constant) {
        match self.store(self.deref(addr)) {
            Addr::Con(c1) =>
                self.fail = self.eq_test(Addr::Con(c), Addr::Con(c1)),
            Addr::Lis(l) =>
                self.unify(Addr::Lis(l), Addr::Con(c)),
            addr => {
                if let Some(r) = addr.as_var() {
                    self.bind(r, Addr::Con(c));
                } else {
                    self.fail = true;
                }
            }
        };
    }

    pub(super) fn get_number(&mut self, at: &ArithmeticTerm) -> Result<Number, MachineStub> {
        match at {
            &ArithmeticTerm::Reg(r) => self.arith_eval_by_metacall(r),
            &ArithmeticTerm::Interm(i) => Ok(mem::replace(
                &mut self.interms[i - 1],
                Number::Integer(Integer::from(0)),
            )),
            &ArithmeticTerm::Number(ref n) => Ok(n.clone()),
        }
    }

    fn rational_from_number(
        &self,
        n: Number,
        caller: &MachineStub,
    ) -> Result<Rational, MachineStub> {
        match n {
            Number::Rational(r) => Ok(r),
            Number::Float(OrderedFloat(f)) => Rational::from_f64(f).ok_or_else(|| {
                self.error_form(MachineError::instantiation_error(), caller.clone())
            }),
            Number::Integer(n) => Ok(Rational::from(n)),
        }
    }

    fn get_rational(
        &mut self,
        at: &ArithmeticTerm,
        caller: &MachineStub,
    ) -> Result<Rational, MachineStub> {
        let n = self.get_number(at)?;
        self.rational_from_number(n, caller)
    }

    pub(super) fn arith_eval_by_metacall(&self, r: RegType) -> Result<Number, MachineStub> {
        let a = self[r].clone();

        let caller = MachineError::functor_stub(clause_name!("(is)"), 2);
        let mut interms: Vec<Number> = Vec::with_capacity(64);

        for heap_val in self.post_order_iter(a) {
            match heap_val {
                HeapCellValue::NamedStr(2, name, _) => {
                    let a2 = interms.pop().unwrap();
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "+" => interms.push(try_numeric_result!(self, a1 + a2, caller.clone())?),
                        "-" => interms.push(try_numeric_result!(self, a1 - a2, caller.clone())?),
                        "*" => interms.push(try_numeric_result!(self, a1 * a2, caller.clone())?),
                        "/" => interms.push(self.div(a1, a2)?),
                        "**" => interms.push(self.pow(a1, a2, "(is)")?),
                        "^" => interms.push(self.int_pow(a1, a2)?),
                        "max" => interms.push(self.max(a1, a2)?),
                        "min" => interms.push(self.min(a1, a2)?),
                        "rdiv" => {
                            let r1 = self.rational_from_number(a1, &caller)?;
                            let r2 = self.rational_from_number(a2, &caller)?;

                            let result = Number::Rational(self.rdiv(r1, r2)?);
                            interms.push(result)
                        }
                        "//" => interms.push(Number::Integer(self.idiv(a1, a2)?)),
                        "div" => interms.push(Number::Integer(self.int_floor_div(a1, a2)?)),
                        ">>" => interms.push(Number::Integer(self.shr(a1, a2)?)),
                        "<<" => interms.push(Number::Integer(self.shl(a1, a2)?)),
                        "/\\" => interms.push(Number::Integer(self.and(a1, a2)?)),
                        "\\/" => interms.push(Number::Integer(self.or(a1, a2)?)),
                        "xor" => interms.push(Number::Integer(self.xor(a1, a2)?)),
                        "mod" => interms.push(Number::Integer(self.modulus(a1, a2)?)),
                        "rem" => interms.push(Number::Integer(self.remainder(a1, a2)?)),
                        "atan2" => interms.push(Number::Float(OrderedFloat(self.atan2(a1, a2)?))),
                        "gcd" => interms.push(Number::Integer(self.gcd(a1, a2)?)),
                        _ => {
                            return Err(self.error_form(MachineError::instantiation_error(), caller))
                        }
                    }
                }
                HeapCellValue::NamedStr(1, name, _) => {
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "-" => interms.push(-a1),
                        "+" => interms.push(a1),
                        "cos" => interms.push(Number::Float(OrderedFloat(self.cos(a1)?))),
                        "sin" => interms.push(Number::Float(OrderedFloat(self.sin(a1)?))),
                        "tan" => interms.push(Number::Float(OrderedFloat(self.tan(a1)?))),
                        "sqrt" => interms.push(Number::Float(OrderedFloat(self.sqrt(a1)?))),
                        "log" => interms.push(Number::Float(OrderedFloat(self.log(a1)?))),
                        "exp" => interms.push(Number::Float(OrderedFloat(self.exp(a1)?))),
                        "acos" => interms.push(Number::Float(OrderedFloat(self.acos(a1)?))),
                        "asin" => interms.push(Number::Float(OrderedFloat(self.asin(a1)?))),
                        "atan" => interms.push(Number::Float(OrderedFloat(self.atan(a1)?))),
                        "abs" => interms.push(a1.abs()),
                        "float" => interms.push(Number::Float(OrderedFloat(self.float(a1)?))),
                        "truncate" => interms.push(Number::Integer(self.truncate(a1))),
                        "round" => interms.push(Number::Integer(self.round(a1)?)),
                        "ceiling" => interms.push(Number::Integer(self.ceiling(a1))),
                        "floor" => interms.push(Number::Integer(self.floor(a1))),
                        "\\" => interms.push(Number::Integer(self.bitwise_complement(a1)?)),
                        "sign" => interms.push(Number::Integer(self.sign(a1))),
                        _ => {
                            return Err(self.error_form(MachineError::instantiation_error(), caller))
                        }
                    }
                }
                HeapCellValue::Addr(Addr::Con(Constant::Integer(n))) => {
                    interms.push(Number::Integer(n))
                }
                HeapCellValue::Addr(Addr::Con(Constant::Float(n))) => {
                    interms.push(Number::Float(n))
                }
                HeapCellValue::Addr(Addr::Con(Constant::Rational(n))) => {
                    interms.push(Number::Rational(n))
                }
                HeapCellValue::Addr(Addr::Con(Constant::Atom(ref name, _)))
                    if name.as_str() == "pi" =>
                {
                    interms.push(Number::Float(OrderedFloat(f64::consts::PI)))
                }
                _ => return Err(self.error_form(MachineError::instantiation_error(), caller)),
            }
        }

        Ok(interms.pop().unwrap())
    }

    fn rdiv(&self, r1: Rational, r2: Rational) -> Result<Rational, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);

        if r2 == 0 {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            Ok(r1 / r2)
        }
    }

    fn int_floor_div(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(div)"), 2);

        match n1 / n2 {
            Ok(result) => Ok(rnd_i(&result).to_owned()),
            Err(e) => Err(self.error_form(MachineError::evaluation_error(e), stub)),
        }
    }

    fn idiv(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(n1.div_rem(n2).0)
                }
            }
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn div(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/)"), 2);

        if n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            try_numeric_result!(self, n1 / n2, stub)
        }
    }

    fn atan2(&self, n1: Number, n2: Number) -> Result<f64, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        if n1.is_zero() && n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub))
        } else {
            let f1 = self.float(n1)?;
            let f2 = self.float(n2)?;

            self.unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.atan2(f2))
        }
    }

    fn int_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        if n1.is_zero() && n2.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n1 != 1 && n2 < 0 {
                    let n = Addr::Con(Constant::Integer(n1));
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(MachineError::type_error(ValidType::Float, n), stub))
                } else {
                    Ok(Number::Integer(binary_pow(n1, n2)))
                }
            }
            (n1, Number::Integer(n2)) => {
                let f1 = self.float(n1)?;
                let f2 = self.float(Number::Integer(n2))?;

                self.unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.powf(f2))
                    .map(|f| Number::Float(OrderedFloat(f)))
            }
            (n1, n2) => {
                let f2 = self.float(n2)?;

                if n1.is_negative() && f2 != f2.floor() {
                    let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
                    return Err(
                        self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub)
                    );
                }

                let f1 = self.float(n1)?;
                self.unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.powf(f2))
                    .map(|f| Number::Float(OrderedFloat(f)))
            }
        }
    }

    fn gcd(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(n1.gcd(&n2))
            }
            (Number::Float(f), _) | (_, Number::Float(f)) => {
                let n = Addr::Con(Constant::Float(f));
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(MachineError::type_error(ValidType::Integer, n), stub))
            }
            (Number::Rational(r), _) | (_, Number::Rational(r)) => {
                let n = Addr::Con(Constant::Rational(r));
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(MachineError::type_error(ValidType::Integer, n), stub))
            }
        }
    }

    fn float_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let f1 = result_f(&n1, rnd_f);
        let f2 = result_f(&n2, rnd_f);

        let stub = MachineError::functor_stub(clause_name!("(**)"), 2);

        let f1 = try_numeric_result!(self, f1, stub.clone())?;
        let f2 = try_numeric_result!(self, f2, stub.clone())?;

        let result = result_f(&Number::Float(OrderedFloat(f1.powf(f2))), rnd_f);

        Ok(Number::Float(OrderedFloat(try_numeric_result!(
            self, result, stub
        )?)))
    }

    fn pow(&self, n1: Number, n2: Number, culprit: &'static str) -> Result<Number, MachineStub> {
        if n2.is_negative() && n1.is_zero() {
            let stub = MachineError::functor_stub(clause_name!(culprit), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => Ok(Number::Integer(binary_pow(n1, n2))),
            (n1, n2) => self.float_pow(n1, n2),
        }
    }

    fn unary_float_fn_template<FloatFn>(&self, n1: Number, f: FloatFn) -> Result<f64, MachineStub>
    where
        FloatFn: Fn(f64) -> f64,
    {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub.clone())?;
        let f1 = result_f(&Number::Float(OrderedFloat(f(f1))), rnd_f);

        try_numeric_result!(self, f1, stub)
    }

    fn sin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.sin())
    }

    fn cos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.cos())
    }

    fn tan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.tan())
    }

    fn log(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.log(f64::consts::E))
    }

    fn exp(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.exp())
    }

    fn asin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.asin())
    }

    fn acos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.acos())
    }

    fn atan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.atan())
    }

    fn sqrt(&self, n1: Number) -> Result<f64, MachineStub> {
        if n1.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        self.unary_float_fn_template(n1, |f| f.sqrt())
    }

    fn float(&self, n: Number) -> Result<f64, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
        try_numeric_result!(self, result_f(&n, rnd_f), stub)
    }

    fn floor(&self, n1: Number) -> Integer {
        rnd_i(&n1).to_owned()
    }

    fn ceiling(&self, n1: Number) -> Integer {
        -self.floor(-n1)
    }

    fn truncate(&self, n: Number) -> Integer {
        if n.is_negative() {
            -self.floor(n.abs())
        } else {
            self.floor(n)
        }
    }

    fn round(&self, n: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        let result = n + Number::Float(OrderedFloat(0.5f64));
        let result = try_numeric_result!(self, result, stub)?;

        Ok(self.floor(result))
    }

    fn shr(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(>>)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => match n2.to_u32() {
                Some(n2) => Ok(n1 >> n2),
                _ => Ok(n1 >> u32::max_value()),
            },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn shl(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(<<)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => match n2.to_u32() {
                Some(n2) => Ok(n1 << n2),
                _ => Ok(n1 << u32::max_value()),
            },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn bitwise_complement(&self, n1: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\)"), 2);

        match n1 {
            Number::Integer(n1) => Ok(!n1),
            _ => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn xor(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(xor)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => Ok(n1 ^ n2),
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn and(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/\\)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => Ok(n1 & n2),
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn modulus(&self, x: Number, y: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(mod)"), 2);

        match (x, y) {
            (Number::Integer(x), Number::Integer(y)) => {
                if y == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(x.div_rem_floor(y).1)
                }
            }
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn max(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n1 > n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Integer(n2))
                }
            }
            (n1, n2) => {
                let stub = MachineError::functor_stub(clause_name!("max"), 2);

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub.clone())?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(max(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    fn min(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n1 < n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Integer(n2))
                }
            }
            (n1, n2) => {
                let stub = MachineError::functor_stub(clause_name!("max"), 2);

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub.clone())?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(min(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    fn sign(&self, n: Number) -> Integer {
        if n.is_positive() {
            Integer::from(1)
        } else if n.is_negative() {
            Integer::from(-1)
        } else {
            Integer::from(0)
        }
    }

    fn remainder(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(rem)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(n1 % n2)
                }
            }
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    fn or(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\/)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => Ok(n1 | n2),
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n2.to_constant())),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(ValidType::Integer, Addr::Con(n1.to_constant())),
                stub,
            )),
        }
    }

    pub(super) fn execute_arith_instr(&mut self, instr: &ArithmeticInstruction) {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        match instr {
            &ArithmeticInstruction::Add(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 + n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Sub(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 - n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Mul(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, try_numeric_result!(self, n1 * n2, stub));
                self.p += 1;
            }
            &ArithmeticInstruction::Max(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.max(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Min(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.min(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::IntPow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.int_pow(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Gcd(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.gcd(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Pow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.pow(n1, n2, "(**)"));
                self.p += 1;
            }
            &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);

                let r1 = try_or_fail!(self, self.get_rational(a1, &stub));
                let r2 = try_or_fail!(self, self.get_rational(a2, &stub));

                self.interms[t - 1] = Number::Rational(try_or_fail!(self, self.rdiv(r1, r2)));
                self.p += 1;
            }
            &ArithmeticInstruction::IntFloorDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] =
                    Number::Integer(try_or_fail!(self, self.int_floor_div(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::IDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.idiv(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Abs(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1.abs();
                self.p += 1;
            }
            &ArithmeticInstruction::Sign(ref a1, t) => {
                let n = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Integer(self.sign(n));
                self.p += 1;
            }
            &ArithmeticInstruction::Neg(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = -n1;
                self.p += 1;
            }
            &ArithmeticInstruction::BitwiseComplement(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Integer(try_or_fail!(self, self.bitwise_complement(n1)));
                self.p += 1;
            }
            &ArithmeticInstruction::Div(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.div(n1, n2));
                self.p += 1;
            }
            &ArithmeticInstruction::Shr(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.shr(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Shl(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.shl(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Xor(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.xor(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::And(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.and(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Or(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.or(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Mod(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.modulus(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Rem(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.remainder(n1, n2)));
                self.p += 1;
            }
            &ArithmeticInstruction::Cos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.cos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.sin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Tan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.tan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Sqrt(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.sqrt(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Log(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.log(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Exp(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Float(OrderedFloat(try_or_fail!(self, self.exp(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ACos(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.acos(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ASin(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.asin(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.atan(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::ATan2(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.atan2(n1, n2))));
                self.p += 1;
            }
            &ArithmeticInstruction::Float(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] =
                    Number::Float(OrderedFloat(try_or_fail!(self, self.float(n1))));
                self.p += 1;
            }
            &ArithmeticInstruction::Truncate(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Integer(self.truncate(n1));
                self.p += 1;
            }
            &ArithmeticInstruction::Round(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.round(n1)));
                self.p += 1;
            }
            &ArithmeticInstruction::Ceiling(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Integer(self.ceiling(n1));
                self.p += 1;
            }
            &ArithmeticInstruction::Floor(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = Number::Integer(self.floor(n1));
                self.p += 1;
            }
            &ArithmeticInstruction::Plus(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1;
                self.p += 1;
            }
        };
    }

    fn get_char_list(&mut self, offset: usize, s: Rc<String>) {
        if let Some(c) = s[offset ..].chars().next() {
            let h = self.heap.h;

            self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::Char(c))));
            self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::String(
                offset + c.len_utf8(),
                s,
            ))));

            self.s = h;
            self.mode = MachineMode::Read;
        }
    }

    pub(super) fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, ref c, reg) => {
                let addr = self[reg].clone();
                self.write_constant_to_var(addr, c.clone());
            }
            &FactInstruction::GetList(_, reg) => {
                let addr = self.store(self.deref(self[reg].clone()));

                match addr {
                    Addr::Con(Constant::String(n, s)) =>
                        match self.flags.double_quotes {
                            DoubleQuotes::Chars | DoubleQuotes::Codes
                                if s.len() > n => {
                                    self.get_char_list(n, s)
                                }
                            _ => {
                                self.fail = true
                            }
                    },
                    addr @ Addr::AttrVar(_)
                  | addr @ Addr::StackCell(..)
                  | addr @ Addr::HeapCell(_) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Lis(h + 1)));
                        self.bind(addr.as_var().unwrap(), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    }
                    Addr::Lis(a) => {
                        self.s = a;
                        self.mode = MachineMode::Read;
                    }
                    _ => self.fail = true,
                };
            }
            &FactInstruction::GetStructure(ref ct, arity, reg) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr.clone()) {
                    Addr::Str(a) => {
                        let result = &self.heap[a];

                        if let &HeapCellValue::NamedStr(narity, ref s, _) = result {
                            if narity == arity && ct.name() == *s {
                                self.s = a + 1;
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        }
                    }
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Str(h + 1)));
                        self.heap
                            .push(HeapCellValue::NamedStr(arity, ct.name(), ct.spec()));

                        self.bind(addr.as_var().unwrap(), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    }
                    _ => self.fail = true,
                };
            }
            &FactInstruction::GetVariable(norm, arg) => self[norm] = self.registers[arg].clone(),
            &FactInstruction::GetValue(norm, arg) => {
                let norm_addr = self[norm].clone();
                let reg_addr = self.registers[arg].clone();

                self.unify(norm_addr, reg_addr);
            }
            &FactInstruction::UnifyConstant(ref c) => {
                match self.mode {
                    MachineMode::Read => {
                        let addr = Addr::HeapCell(self.s);
                        self.write_constant_to_var(addr, c.clone());
                    }
                    MachineMode::Write => {
                        self.heap.push(HeapCellValue::Addr(Addr::Con(c.clone())));
                    }
                };

                self.s += 1;
            }
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read => self[reg] = self.heap[self.s].as_addr(self.s),
                    MachineMode::Write => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        self[reg] = Addr::HeapCell(h);
                    }
                };

                self.s += 1;
            }
            &FactInstruction::UnifyLocalValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    }
                    MachineMode::Write => {
                        let addr = self.deref(self[reg].clone());
                        let h = self.heap.h;

                        if let Addr::HeapCell(hc) = addr {
                            if hc < h {
                                let val = self.heap[hc].clone();

                                self.heap.push(val);
                                self.s += 1;

                                return;
                            }
                        }

                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        self.bind(Ref::HeapCell(h), addr);
                    }
                };

                self.s += 1;
            }
            &FactInstruction::UnifyValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    }
                    MachineMode::Write => {
                        let heap_val = self.store(self[reg].clone());
                        self.heap.push(HeapCellValue::Addr(heap_val));
                    }
                };

                self.s += 1;
            }
            &FactInstruction::UnifyVoid(n) => {
                match self.mode {
                    MachineMode::Read => self.s += n,
                    MachineMode::Write => {
                        let h = self.heap.h;

                        for i in h..h + n {
                            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(i)));
                        }
                    }
                };
            }
        };
    }

    pub(super) fn execute_indexing_instr(&mut self, instr: &IndexingInstruction) {
        match instr {
            &IndexingInstruction::SwitchOnTerm(v, c, l, s) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::HeapCell(_) | Addr::StackCell(..) | Addr::AttrVar(..) => v,
                    Addr::Con(Constant::String(n, ref s)) => {
                        if !self.flags.double_quotes.is_atom() {
                            if n >= s.len() {
                                c
                            } else {
                                l
                            }
                        } else {
                            c
                        }
                    }
                    Addr::Con(_) => c,
                    Addr::Lis(_) => l,
                    Addr::Str(_) => s,
                    Addr::DBRef(_) => {
                        self.fail = true;
                        return;
                    }
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o,
                };
            }
            &IndexingInstruction::SwitchOnConstant(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Con(constant) => match hm.get(&constant) {
                        Some(offset) => *offset,
                        _ => 0,
                    },
                    _ => 0,
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o,
                };
            }
            &IndexingInstruction::SwitchOnStructure(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Str(s) => {
                        if let &HeapCellValue::NamedStr(arity, ref name, _) = &self.heap[s] {
                            match hm.get(&(name.clone(), arity)) {
                                Some(offset) => *offset,
                                _ => 0,
                            }
                        } else {
                            0
                        }
                    }
                    _ => 0,
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o,
                };
            }
        };
    }

    pub(super) fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::GetVariable(norm, arg) => self[norm] = self.registers[arg].clone(),
            &QueryInstruction::PutConstant(_, ref constant, reg) => {
                self[reg] = Addr::Con(constant.clone())
            }
            &QueryInstruction::PutList(_, reg) => self[reg] = Addr::Lis(self.heap.h),
            &QueryInstruction::PutStructure(ref ct, arity, reg) => {
                let h = self.heap.h;

                self.heap
                    .push(HeapCellValue::NamedStr(arity, ct.name(), ct.spec()));
                self[reg] = Addr::Str(h);
            }
            &QueryInstruction::PutUnsafeValue(n, arg) => {
                let e = self.e;
                let addr = self.deref(Addr::StackCell(e, n));

                if addr.is_protected(e) {
                    self.registers[arg] = self.store(addr);
                } else {
                    let h = self.heap.h;

                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                    self.bind(Ref::HeapCell(h), addr);

                    self.registers[arg] = self.heap[h].as_addr(h);
                }
            }
            &QueryInstruction::PutValue(norm, arg) => self.registers[arg] = self[norm].clone(),
            &QueryInstruction::PutVariable(norm, arg) => {
                match norm {
                    RegType::Perm(n) => {
                        let e = self.e;

                        self[norm] = Addr::StackCell(e, n);
                        self.registers[arg] = self[norm].clone();
                    }
                    RegType::Temp(_) => {
                        let h = self.heap.h;
                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));

                        self[norm] = Addr::HeapCell(h);
                        self.registers[arg] = Addr::HeapCell(h);
                    }
                };
            }
            &QueryInstruction::SetConstant(ref c) => {
                self.heap.push(HeapCellValue::Addr(Addr::Con(c.clone())));
            }
            &QueryInstruction::SetLocalValue(reg) => {
                let addr = self.deref(self[reg].clone());
                let h = self.heap.h;

                if let Addr::HeapCell(hc) = addr {
                    if hc < h {
                        let heap_val = self.heap[hc].clone();
                        self.heap.push(heap_val);
                        return;
                    }
                }

                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self.bind(Ref::HeapCell(h), addr);
            }
            &QueryInstruction::SetVariable(reg) => {
                let h = self.heap.h;
                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self[reg] = Addr::HeapCell(h);
            }
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self[reg].clone();
                self.heap.push(HeapCellValue::Addr(heap_val));
            }
            &QueryInstruction::SetVoid(n) => {
                let h = self.heap.h;

                for i in h..h + n {
                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(i)));
                }
            }
        }
    }

    pub(super) fn set_ball(&mut self) {
        self.ball.reset();

        let addr = self[temp_v!(1)].clone();
        self.ball.boundary = self.heap.h;

        copy_term(
            CopyBallTerm::new(&mut self.stack, &mut self.heap, &mut self.ball.stub),
            addr,
            AttrVarPolicy::DeepCopy,
        );
    }

    pub(super) fn handle_internal_call_n(&mut self, arity: usize) {
        let arity = arity + 1;
        let pred = self.registers[1].clone();

        for i in 2..arity {
            self.registers[i - 1] = self.registers[i].clone();
        }

        if arity > 1 {
            self.registers[arity - 1] = pred;
            return;
        }

        self.fail = true;
    }

    pub(super) fn setup_call_n(&mut self, arity: usize) -> Option<PredicateKey> {
        let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
        let addr = self.store(self.deref(self.registers[arity].clone()));

        let (name, narity) = match addr {
            Addr::Str(a) => {
                let result = self.heap[a].clone();

                if let HeapCellValue::NamedStr(narity, name, _) = result {
                    if narity + arity > 63 {
                        let representation_error = self.error_form(
                            MachineError::representation_error(RepFlag::MaxArity),
                            stub,
                        );

                        self.throw_exception(representation_error);
                        return None;
                    }

                    for i in (1 .. arity).rev() {
                        self.registers[i + narity] = self.registers[i].clone();
                    }

                    for i in 1 .. narity + 1 {
                        self.registers[i] = self.heap[a + i].as_addr(a + i);
                    }

                    (name, narity)
                } else {
                    self.fail = true;
                    return None;
                }
            }
            Addr::Con(Constant::Atom(name, _)) => (name, 0),
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let instantiation_error =
                    self.error_form(MachineError::instantiation_error(), stub);
                self.throw_exception(instantiation_error);

                return None;
            }
            _ => {
                let type_error =
                    self.error_form(MachineError::type_error(ValidType::Callable, addr), stub);
                self.throw_exception(type_error);

                return None;
            }
        };

        Some((name, arity + narity - 1))
    }

    pub(super) fn unwind_stack(&mut self) {
        self.b = self.block;
        self.fail = true;
    }

    pub(crate) fn is_cyclic_term(&self, addr: Addr) -> bool {
        let mut seen = IndexSet::new();
        let mut fail = false;
        let mut iter = self.pre_order_iter(addr);

        loop {
            if let Some(addr) = iter.stack().last() {
                if !seen.contains(addr) {
                    seen.insert(addr.clone());
                } else {
                    fail = true;
                    break;
                }
            }

            if iter.next().is_none() {
                break;
            }
        }

        fail
    }

    // arg(+N, +Term, ?Arg)
    pub(super) fn try_arg(&mut self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("arg"), 3);
        let n = self.store(self.deref(self[temp_v!(1)].clone()));

        match n {
            Addr::HeapCell(_) | Addr::StackCell(..) =>
            // 8.5.2.3 a)
            {
                return Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            Addr::Con(Constant::Integer(n)) => {
                if n < 0 {
                    // 8.5.2.3 e)
                    let n = Addr::Con(Constant::Integer(n));
                    let dom_err = MachineError::domain_error(DomainError::NotLessThanZero, n);

                    return Err(self.error_form(dom_err, stub));
                }

                let n = match n.to_usize() {
                    Some(n) => n,
                    None => {
                        self.fail = true;
                        return Ok(());
                    }
                };

                let term = self.store(self.deref(self[temp_v!(2)].clone()));

                match term {
                    Addr::HeapCell(_) | Addr::StackCell(..) =>
                    // 8.5.2.3 b)
                    {
                        return Err(self.error_form(MachineError::instantiation_error(), stub))
                    }
                    Addr::Str(o) => match self.heap[o].clone() {
                        HeapCellValue::NamedStr(arity, _, _) if 1 <= n && n <= arity => {
                            let a3 = self[temp_v!(3)].clone();
                            let h_a = Addr::HeapCell(o + n);

                            self.unify(a3, h_a);
                        }
                        _ => self.fail = true,
                    },
                    Addr::Lis(l) => {
                        if n == 1 || n == 2 {
                            let a3 = self[temp_v!(3)].clone();
                            let h_a = Addr::HeapCell(l + n - 1);

                            self.unify(a3, h_a);
                        } else {
                            self.fail = true;
                        }
                    }
                    Addr::Con(Constant::String(o, ref s))
                        if !self.flags.double_quotes.is_atom() && !s[o ..].is_empty() =>
                    {
                        if n == 1 || n == 2 {
                            let a3 = self[temp_v!(3)].clone();
                            let c = s[o ..].chars().next().unwrap();

                            let h_a = if n == 1 {
                                Addr::Con(Constant::Char(c))
                            } else {
                                Addr::Con(Constant::String(o + c.len_utf8(), s.clone()))
                            };

                            self.unify(a3, h_a);
                        } else {
                            self.fail = true;
                        }
                    }
                    _ =>
                    // 8.5.2.3 d)
                    {
                        return Err(self
                            .error_form(MachineError::type_error(ValidType::Compound, term), stub))
                    }
                }
            }
            _ =>
            // 8.5.2.3 c)
            {
                return Err(self.error_form(MachineError::type_error(ValidType::Integer, n), stub))
            }
        }

        Ok(())
    }

    fn compare_numbers(&mut self, cmp: CompareNumberQT, n1: Number, n2: Number) {
        let ordering = n1.cmp(&n2);

        self.fail = match cmp {
            CompareNumberQT::GreaterThan if ordering == Ordering::Greater => false,
            CompareNumberQT::GreaterThanOrEqual if ordering != Ordering::Less => false,
            CompareNumberQT::LessThan if ordering == Ordering::Less => false,
            CompareNumberQT::LessThanOrEqual if ordering != Ordering::Greater => false,
            CompareNumberQT::NotEqual if ordering != Ordering::Equal => false,
            CompareNumberQT::Equal if ordering == Ordering::Equal => false,
            _ => true,
        };

        self.p += 1;
    }

    pub(super) fn compare_term(&mut self, qt: CompareTermQT) {
        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        match self.compare_term_test(&a1, &a2) {
            Ordering::Greater => match qt {
                CompareTermQT::GreaterThan | CompareTermQT::GreaterThanOrEqual => return,
                _ => self.fail = true,
            },
            Ordering::Equal => match qt {
                CompareTermQT::GreaterThanOrEqual | CompareTermQT::LessThanOrEqual => return,
                _ => self.fail = true,
            },
            Ordering::Less => match qt {
                CompareTermQT::LessThan | CompareTermQT::LessThanOrEqual => return,
                _ => self.fail = true,
            },
        };
    }

    // returns true on failure.
    pub(super)
    fn eq_test(&self, a1: Addr, a2: Addr) -> bool {
        let mut iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        while let Some((v1, v2)) = iter.next() {
            match (v1, v2) {
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) =>
                    if ar1 != ar2 || n1 != n2 {
                        return true;
                    },
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) =>
                    continue,
                (HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                 HeapCellValue::Addr(Addr::Con(Constant::String(n, s))))
              | (HeapCellValue::Addr(Addr::Con(Constant::String(n, s))),
                 HeapCellValue::Addr(Addr::Con(Constant::EmptyList))) =>
                    return match self.flags.double_quotes {
                        DoubleQuotes::Atom => true,
                        _ => n < s.len()
                    },
                (HeapCellValue::Addr(a1), HeapCellValue::Addr(a2)) =>
                    if a1 != a2 {
                        return true;
                    },
                _ => return true,
            }
        }

        // did the two iterators expire at the same step?
        iter.first_to_expire != Ordering::Equal
    }

    pub(super) fn compare_term_test(&self, a1: &Addr, a2: &Addr) -> Ordering {
        let mut iter = self.zipped_acyclic_pre_order_iter(a1.clone(), a2.clone());

        while let Some((v1, v2)) = iter.next() {
            match (v1, v2) {
                (
                    HeapCellValue::Addr(Addr::Lis(_)),
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::Lis(_)),
                ) if !self.flags.double_quotes.is_atom() => {
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                    HeapCellValue::Addr(Addr::Con(Constant::String(n, ref s))),
                ) if !self.flags.double_quotes.is_atom() => {
                    if s[n ..].is_empty() {
                        return Ordering::Equal;
                    } else {
                        return Ordering::Greater;
                    }
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(atom, _))),
                    HeapCellValue::Addr(Addr::Con(Constant::Char(c))),
                ) => {
                    return if atom.as_str().chars().count() == 1 {
                        atom.as_str().chars().next().cmp(&Some(c))
                    } else {
                        Ordering::Greater
                    }
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Char(c))),
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(atom, _))),
                ) => {
                    return if atom.as_str().chars().count() == 1 {
                        Some(c).cmp(&atom.as_str().chars().next())
                    } else {
                        Ordering::Less
                    }
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(n, ref s))),
                    HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                ) if !self.flags.double_quotes.is_atom() => {
                    if s[n ..].is_empty() {
                        return Ordering::Equal;
                    } else {
                        return Ordering::Less;
                    }
                }
                (
                    HeapCellValue::Addr(Addr::HeapCell(hc1)),
                    HeapCellValue::Addr(Addr::HeapCell(hc2)),
                )
                | (
                    HeapCellValue::Addr(Addr::AttrVar(hc1)),
                    HeapCellValue::Addr(Addr::HeapCell(hc2)),
                )
                | (
                    HeapCellValue::Addr(Addr::HeapCell(hc1)),
                    HeapCellValue::Addr(Addr::AttrVar(hc2)),
                )
                | (
                    HeapCellValue::Addr(Addr::AttrVar(hc1)),
                    HeapCellValue::Addr(Addr::AttrVar(hc2)),
                ) => {
                    if hc1 != hc2 {
                        return hc1.cmp(&hc2);
                    }
                }
                (HeapCellValue::Addr(Addr::HeapCell(_)), _)
              | (HeapCellValue::Addr(Addr::AttrVar(_)), _) => {
                    return Ordering::Less;
                }
                (
                    HeapCellValue::Addr(Addr::StackCell(fr1, sc1)),
                    HeapCellValue::Addr(Addr::StackCell(fr2, sc2)),
                ) => {
                    if fr1 > fr2 {
                        return Ordering::Greater;
                    } else if fr1 < fr2 || sc1 < sc2 {
                        return Ordering::Less;
                    } else if sc1 > sc2 {
                        return Ordering::Greater;
                    }
                }
                (
                    HeapCellValue::Addr(Addr::StackCell(..)),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::StackCell(..)),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => {
                    return Ordering::Greater;
                }
                (HeapCellValue::Addr(Addr::StackCell(..)), _) => {
                    return Ordering::Less;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(..))),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(..))),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(..))),
                    HeapCellValue::Addr(Addr::StackCell(..)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(n1))),
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(n2))),
                ) => {
                    if n1 != n2 {
                        return n1.cmp(&n2);
                    }
                }
                (HeapCellValue::Addr(Addr::Con(Constant::Integer(_))), _) => return Ordering::Less,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Float(..))),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::Float(..))),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Float(..))),
                    HeapCellValue::Addr(Addr::StackCell(..)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Float(n1))),
                    HeapCellValue::Addr(Addr::Con(Constant::Float(n2))),
                ) => {
                    if n1 != n2 {
                        return n1.cmp(&n2);
                    }
                }
                (HeapCellValue::Addr(Addr::Con(Constant::Float(_))), _) => return Ordering::Less,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(..))),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(..))),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(..))),
                    HeapCellValue::Addr(Addr::StackCell(..)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(n1))),
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(n2))),
                ) => {
                    if n1 != n2 {
                        return n1.cmp(&n2);
                    }
                }
                (HeapCellValue::Addr(Addr::Con(Constant::Rational(_))), _) => {
                    return Ordering::Less
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::StackCell(..)),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(_))),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(_))),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Float(_))),
                ) => {
                    return Ordering::Greater;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(n1, s1))),
                    HeapCellValue::Addr(Addr::Con(Constant::String(n2, s2))),
                ) => {
                    return s1[n1 ..].cmp(&s2[n2 ..]);
                }
                (HeapCellValue::Addr(Addr::Con(Constant::String(..))), _) => {
                    return Ordering::Less;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::AttrVar(_)),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::StackCell(..)),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Float(_))),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Integer(_))),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::Rational(_))),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                ) => return Ordering::Greater,
                (
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(s1, _))),
                    HeapCellValue::Addr(Addr::Con(Constant::Atom(s2, _))),
                ) => {
                    if s1 != s2 {
                        return s1.cmp(&s2);
                    }
                }
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(..))), _) => {
                    return Ordering::Less;
                }
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) => {
                    if ar1 < ar2 {
                        return Ordering::Less;
                    } else if ar1 > ar2 {
                        return Ordering::Greater;
                    } else if n1 != n2 {
                        return n1.cmp(&n2);
                    }
                }
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) => {
                    continue;
                }
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::NamedStr(ar, n, _))
              | (HeapCellValue::NamedStr(ar, n, _), HeapCellValue::Addr(Addr::Lis(_))) => {
                    if ar == 2 && n.as_str() == "." {
                        continue;
                    } else if ar < 2 {
                        return Ordering::Greater;
                    } else if ar > 2 {
                        return Ordering::Less;
                    } else {
                        return n.as_str().cmp(".");
                    }
                }
                (HeapCellValue::NamedStr(..), _) => return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Lis(_)), _) => return Ordering::Greater,
                _ => {}
            }
        }

        iter.first_to_expire
    }

    pub(super) fn reset_block(&mut self, addr: Addr) {
        match self.store(addr) {
            Addr::Con(Constant::Usize(b)) => self.block = b,
            _ => self.fail = true,
        };
    }

    pub(super) fn execute_inlined(&mut self, inlined: &InlinedClauseType) {
        match inlined {
            &InlinedClauseType::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self, self.get_number(at_1));
                let n2 = try_or_fail!(self, self.get_number(at_2));

                self.compare_numbers(cmp, n1, n2);
            }
            &InlinedClauseType::IsAtom(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Atom(..)) | Addr::Con(Constant::Char(_)) => self.p += 1,
                    Addr::Con(Constant::EmptyList) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsAtomic(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(_) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsInteger(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Integer(_)) => self.p += 1,
                    Addr::Con(Constant::CharCode(_)) => self.p += 1,
                    Addr::Con(Constant::Char(_))
                      if self.flags.double_quotes.is_codes() => self.p += 1,
                    Addr::Con(Constant::Rational(r)) => {
                        if r.denom() == &1 {
                            self.p += 1;
                        } else {
                            self.fail = true;
                        }
                    }
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsCompound(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Str(_) | Addr::Lis(_) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsFloat(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Float(_)) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsRational(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Rational(_)) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsString(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::String(..)) => self.p += 1,
                    _ => self.fail = true,
                };
            }
            &InlinedClauseType::IsNonVar(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(..) => self.fail = true,
                    _ => self.p += 1,
                };
            }
            &InlinedClauseType::IsVar(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::AttrVar(_) | Addr::HeapCell(_) | Addr::StackCell(_, _) => self.p += 1,
                    _ => self.fail = true,
                };
            }
        }
    }

    fn try_functor_unify_components(&mut self, name: Addr, arity: Addr) {
        let a2 = self[temp_v!(2)].clone();
        let a3 = self[temp_v!(3)].clone();

        self.unify(a2, name);

        if !self.fail {
            self.unify(a3, arity);
        }
    }

    fn try_functor_compound_case(
        &mut self,
        name: ClauseName,
        arity: usize,
        spec: Option<SharedOpDesc>,
    ) {
        let name = Addr::Con(Constant::Atom(name, spec));
        let arity = Addr::Con(Constant::Integer(Integer::from(arity)));

        self.try_functor_unify_components(name, arity);
    }

    fn try_functor_fabricate_struct(
        &mut self,
        name: ClauseName,
        arity: isize,
        spec: Option<SharedOpDesc>,
        op_dir: &OpDir,
        r: Ref,
    ) {
        let spec = fetch_atom_op_spec(name.clone(), spec, op_dir);

        let f_a = if name.as_str() == "." && arity == 2 {
            Addr::Lis(self.heap.h)
        } else {
            let h = self.heap.h;
            self.heap
                .push(HeapCellValue::NamedStr(arity as usize, name, spec));
            Addr::Str(h)
        };

        for _ in 0..arity {
            let h = self.heap.h;
            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
        }

        self.bind(r, f_a);
    }

    pub(super) fn try_functor(&mut self, indices: &IndexStore) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("functor"), 3);
        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

        match a1.clone() {
            Addr::DBRef(_) => self.fail = true,
            Addr::Con(Constant::String(n, ref s))
                if !self.flags.double_quotes.is_atom() && !s[n ..].is_empty() =>
            {
                let shared_op_desc = fetch_op_spec(clause_name!("."), 2, None, &indices.op_dir);
                self.try_functor_compound_case(clause_name!("."), 2, shared_op_desc)
            }
            Addr::Con(_) => self
                .try_functor_unify_components(a1, Addr::Con(Constant::Integer(Integer::from(0)))),
            Addr::Str(o) => match self.heap[o].clone() {
                HeapCellValue::NamedStr(arity, name, spec) => {
                    let spec = fetch_op_spec(name.clone(), arity, spec, &indices.op_dir);
                    self.try_functor_compound_case(name, arity, spec)
                }
                _ => self.fail = true,
            },
            Addr::Lis(_) => {
                let shared_op_desc = fetch_op_spec(clause_name!("."), 2, None, &indices.op_dir);
                self.try_functor_compound_case(clause_name!("."), 2, shared_op_desc)
            }
            Addr::AttrVar(..) | Addr::HeapCell(_) | Addr::StackCell(..) => {
                let name = self.store(self.deref(self[temp_v!(2)].clone()));
                let arity = self.store(self.deref(self[temp_v!(3)].clone()));

                if name.is_ref() || arity.is_ref() {
                    // 8.5.1.3 a) & 8.5.1.3 b)
                    return Err(self.error_form(MachineError::instantiation_error(), stub));
                }

                if let Addr::Con(Constant::Integer(arity)) = arity {
                    let arity = match arity.to_isize() {
                        Some(arity) => arity,
                        None => {
                            self.fail = true;
                            return Ok(());
                        }
                    };

                    if arity > MAX_ARITY as isize {
                        let rep_err = MachineError::representation_error(RepFlag::MaxArity);
                        // 8.5.1.3 f)
                        return Err(self.error_form(rep_err, stub));
                    } else if arity < 0 {
                        // 8.5.1.3 g)
                        let arity = Integer::from(arity);
                        let dom_err = MachineError::domain_error(
                            DomainError::NotLessThanZero,
                            Addr::Con(Constant::Integer(arity)),
                        );
                        return Err(self.error_form(dom_err, stub));
                    }

                    match name {
                        Addr::Con(_) if arity == 0 => self.unify(a1, name),
                        Addr::Con(Constant::Atom(name, spec)) => self.try_functor_fabricate_struct(
                            name,
                            arity,
                            spec,
                            &indices.op_dir,
                            a1.as_var().unwrap(),
                        ),
                        Addr::Con(Constant::Char(c)) => {
                            let name = clause_name!(c.to_string(), indices.atom_tbl);
                            self.try_functor_fabricate_struct(
                                name,
                                arity,
                                None,
                                &indices.op_dir,
                                a1.as_var().unwrap(),
                            );
                        }
                        Addr::Con(_) => {
                            return Err(self
                                .error_form(MachineError::type_error(ValidType::Atom, name), stub))
                        } // 8.5.1.3 e)
                        _ => {
                            return Err(self.error_form(
                                MachineError::type_error(ValidType::Atomic, name),
                                stub,
                            ))
                        } // 8.5.1.3 c)
                    };
                } else if !arity.is_ref() {
                    // 8.5.1.3 d)
                    return Err(
                        self.error_form(MachineError::type_error(ValidType::Integer, arity), stub)
                    );
                }
            }
        };

        Ok(())
    }

    pub(super) fn term_dedup(&self, list: &mut Vec<Addr>) {
        let mut result = vec![];

        for a2 in list.iter().cloned() {
            if let Some(a1) = result.last().cloned() {
                if self.compare_term_test(&a1, &a2) == Ordering::Equal {
                    continue;
                }
            }

            result.push(a2);
        }

        *list = result;
    }

    pub(super)
    fn try_from_list(
        &self,
        r: RegType,
        caller: MachineStub,
    ) -> Result<Vec<Addr>, MachineStub> {
        let a1 = self.store(self.deref(self[r].clone()));

        match a1.clone() {
            Addr::Lis(mut l) => {
                let mut result = Vec::new();

                result.push(self.heap[l].as_addr(l));
                l += 1;

                loop {
                    match self.heap[l].clone() {
                        HeapCellValue::Addr(addr) => match self.store(self.deref(addr)) {
                            Addr::Lis(hcp) => {
                                result.push(self.heap[hcp].as_addr(hcp));
                                l = hcp + 1;
                            }
                            Addr::Con(Constant::String(n, ref s))
                                if !self.flags.double_quotes.is_atom() =>
                            {
                                result.push(Addr::Con(Constant::String(n, s.clone())));
                                break;
                            }
                            Addr::Con(Constant::EmptyList) => {
                                break;
                            }
                            Addr::HeapCell(_) | Addr::StackCell(..) => {
                                return Err(
                                    self.error_form(MachineError::instantiation_error(), caller)
                                )
                            }
                            _ => {
                                return Err(self.error_form(
                                    MachineError::type_error(ValidType::List, a1),
                                    caller,
                                ))
                            }
                        },
                        _ => {
                            return Err(self
                                .error_form(MachineError::type_error(ValidType::List, a1), caller))
                        }
                    }
                }

                Ok(result)
            }
            Addr::Con(Constant::String(n, ref s)) if !self.flags.double_quotes.is_atom() => {
                if s.len() > n {
                    Ok(Vec::from_iter(s[n ..].chars().map(|c| Addr::Con(Constant::Char(c)))))
                } else {
                    Ok(vec![])
                }
            }
            Addr::HeapCell(_) | Addr::StackCell(..) => {
                Err(self.error_form(MachineError::instantiation_error(), caller))
            }
            Addr::Con(Constant::EmptyList) => Ok(vec![]),
            _ => Err(self.error_form(MachineError::type_error(ValidType::List, a1), caller)),
        }
    }

    // see 8.4.4.3 of Draft Technical Corrigendum 2 for an error guide.
    pub(super) fn project_onto_key(&self, a: Addr) -> Result<Addr, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.store(self.deref(a)) {
            Addr::HeapCell(_) | Addr::StackCell(..) => {
                Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            Addr::Str(s) => match self.heap[s].clone() {
                HeapCellValue::NamedStr(2, ref name, Some(_)) if *name == clause_name!("-") => {
                    Ok(Addr::HeapCell(s + 1))
                }
                _ => Err(self.error_form(
                    MachineError::type_error(ValidType::Pair, self.heap[s].as_addr(s)),
                    stub,
                )),
            },
            a => Err(self.error_form(MachineError::type_error(ValidType::Pair, a), stub)),
        }
    }

    pub(super) fn copy_term(&mut self, attr_var_policy: AttrVarPolicy) {
        let old_h = self.heap.h;

        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        copy_term(CopyTerm::new(self), a1, attr_var_policy);
        self.unify(Addr::HeapCell(old_h), a2);
    }

    // returns true on failure.
    pub(super) fn structural_eq_test(&self) -> bool {
        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        let mut var_pairs = IndexMap::new();

        let iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        for (v1, v2) in iter {
            match (v1, v2) {
                (
                    HeapCellValue::Addr(Addr::Lis(_)),
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                    HeapCellValue::Addr(Addr::Lis(_)),
                ) if !self.flags.double_quotes.is_atom() => {
                    continue;
                }
                (
                    HeapCellValue::Addr(Addr::Con(Constant::String(n, ref s))),
                    HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                )
                | (
                    HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                    HeapCellValue::Addr(Addr::Con(Constant::String(n, ref s))),
                ) if !self.flags.double_quotes.is_atom() => {
                    if !s[n ..].is_empty() {
                        return true;
                    }
                }
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) => {
                    if ar1 != ar2 || n1 != n2 {
                        return true;
                    }
                }
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) => {
                    continue;
                }
                (
                    HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    HeapCellValue::Addr(v2 @ Addr::AttrVar(_)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::AttrVar(_)),
                    HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::HeapCell(_)),
                    HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    HeapCellValue::Addr(v2 @ Addr::StackCell(..)),
                )
                | (
                    HeapCellValue::Addr(v1 @ Addr::StackCell(..)),
                    HeapCellValue::Addr(v2 @ Addr::HeapCell(_)),
                ) =>
                    match (var_pairs.get(&v1).cloned(), var_pairs.get(&v2).cloned()) {
                        (Some(ref v2_p), Some(ref v1_p)) if *v1_p == v1 && *v2_p == v2 => continue,
                        (Some(_), _) | (_, Some(_)) => return true,
                        (None, None) => {
                            var_pairs.insert(v1.clone(), v2.clone());
                            var_pairs.insert(v2, v1);
                        }
                    },
                (HeapCellValue::Addr(a1), HeapCellValue::Addr(a2)) => {
                    if a1 != a2 {
                        return true;
                    }
                }
                _ => return true,
            }
        }

        false
    }

    // returns true on failure.
    pub(super) fn ground_test(&self) -> bool {
        let a = self.store(self.deref(self[temp_v!(1)].clone()));

        for v in self.acyclic_pre_order_iter(a) {
            match v {
                HeapCellValue::Addr(Addr::HeapCell(..)) => return true,
                HeapCellValue::Addr(Addr::StackCell(..)) => return true,
                HeapCellValue::Addr(Addr::AttrVar(..)) => return true,
                _ => {}
            }
        }

        false
    }

    pub(super) fn setup_built_in_call(&mut self, ct: BuiltInClauseType) {
        self.num_of_args = ct.arity();
        self.b0 = self.b;

        self.p = CodePtr::BuiltInClause(ct, self.p.local());
    }

    pub(super) fn allocate(&mut self, num_cells: usize) {
        let e = self.stack.allocate_and_frame(num_cells);
        let and_frame = self.stack.index_and_frame_mut(e);

        and_frame.prelude.e  = self.e;
        and_frame.prelude.cp = self.cp;

        self.e = e;
        self.p += 1;
    }

    pub(super) fn deallocate(&mut self) {
        let e = self.e;
        let frame = self.stack.index_and_frame(e);

        self.cp = frame.prelude.cp;
        self.e  = frame.prelude.e;

        self.p += 1;
    }

    fn handle_call_clause(
        &mut self,
        indices: &mut IndexStore,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        cut_policy: &mut Box<dyn CutPolicy>,
        parsing_stream: &mut PrologStream,
        ct: &ClauseType,
        arity: usize,
        lco: bool,
        use_default_cp: bool,
    ) {
	let interrupted = INTERRUPT.load(std::sync::atomic::Ordering::Relaxed);

	if INTERRUPT.compare_and_swap(interrupted, false, std::sync::atomic::Ordering::Relaxed) {
	    self.reset();
	    self.fail = true;
	    return;
	}

        let mut default_call_policy: Box<dyn CallPolicy> = Box::new(DefaultCallPolicy {});

        let call_policy = if use_default_cp {
            &mut default_call_policy
        } else {
            call_policy
        };

        self.last_call = lco;

        match ct {
            &ClauseType::BuiltIn(ref ct) => try_or_fail!(
                self,
                call_policy.call_builtin(self, ct, indices, parsing_stream)
            ),
            &ClauseType::CallN => try_or_fail!(
                self,
                call_policy.call_n(self, arity, indices, parsing_stream)
            ),
            &ClauseType::Hook(ref hook) => try_or_fail!(self, call_policy.compile_hook(self, hook)),
            &ClauseType::Inlined(ref ct) => {
                self.execute_inlined(ct);

                if lco {
                    self.p = CodePtr::Local(self.cp);
                }
            }
            &ClauseType::Named(ref name, _, ref idx) | &ClauseType::Op(ref name, _, ref idx) => {
                try_or_fail!(
                    self,
                    call_policy.context_call(self, name.clone(), arity, idx.clone(), indices)
                )
            }
            &ClauseType::System(ref ct) => try_or_fail!(
                self,
                self.system_call(
                    ct,
                    code_repo,
                    indices,
                    call_policy,
                    cut_policy,
                    parsing_stream
                )
            ),
        };

        self.last_call = false;
    }

    pub(super) fn execute_ctrl_instr(
        &mut self,
        indices: &mut IndexStore,
        code_repo: &CodeRepo,
        call_policy: &mut Box<dyn CallPolicy>,
        cut_policy: &mut Box<dyn CutPolicy>,
        parsing_stream: &mut PrologStream,
        instr: &ControlInstruction,
    ) {
        match instr {
            &ControlInstruction::Allocate(num_cells) => self.allocate(num_cells),
            &ControlInstruction::CallClause(ref ct, arity, _, lco, use_default_cp) => self
                .handle_call_clause(
                    indices,
                    code_repo,
                    call_policy,
                    cut_policy,
                    parsing_stream,
                    ct,
                    arity,
                    lco,
                    use_default_cp,
                ),
            &ControlInstruction::Deallocate => self.deallocate(),
            &ControlInstruction::JmpBy(arity, offset, _, lco) => {
                if !lco {
                    self.cp.assign_if_local(self.p.clone() + 1);
                }

                self.num_of_args = arity;
                self.b0 = self.b;
                self.p += offset;
            }
            &ControlInstruction::Proceed => self.p = CodePtr::Local(self.cp.clone())
        };
    }

    pub(super) fn execute_indexed_choice_instr(
        &mut self,
        instr: &IndexedChoiceInstruction,
        call_policy: &mut Box<dyn CallPolicy>,
    ) {
        match instr {
            &IndexedChoiceInstruction::Try(offset) => {
                let n = self.num_of_args;
                let b = self.stack.allocate_or_frame(n);
                let or_frame = self.stack.index_or_frame_mut(b);

                or_frame.prelude.univ_prelude.num_cells = n;
                or_frame.prelude.e = self.e;
                or_frame.prelude.cp = self.cp;
                or_frame.prelude.b = self.b;
                or_frame.prelude.bp = self.p.local() + 1;
                or_frame.prelude.tr = self.tr;
                or_frame.prelude.h  = self.heap.h;
                or_frame.prelude.b0 = self.b0;

                or_frame.prelude.attr_var_init_queue_b =
                    self.attr_var_init.attr_var_queue.len();
                or_frame.prelude.attr_var_init_bindings_b =
                    self.attr_var_init.bindings.len();

                self.b = b;

                for i in 1 .. n + 1 {
                    self.stack.index_or_frame_mut(b)[i-1] = self.registers[i].clone();
                }

                self.hb = self.heap.h;
                self.p += offset;
            }
            &IndexedChoiceInstruction::Retry(l) => try_or_fail!(self, call_policy.retry(self, l)),
            &IndexedChoiceInstruction::Trust(l) => try_or_fail!(self, call_policy.trust(self, l)),
        };
    }

    pub(super) fn execute_choice_instr(
        &mut self,
        instr: &ChoiceInstruction,
        call_policy: &mut Box<dyn CallPolicy>,
    ) {
        match instr {
            &ChoiceInstruction::TryMeElse(offset) => {
                let n = self.num_of_args;
                let b = self.stack.allocate_or_frame(n);
                let or_frame = self.stack.index_or_frame_mut(b);

                or_frame.prelude.univ_prelude.num_cells = n;
                or_frame.prelude.e = self.e;
                or_frame.prelude.cp = self.cp;
                or_frame.prelude.b = self.b;
                or_frame.prelude.bp = self.p.local() + offset;
                or_frame.prelude.tr = self.tr;
                or_frame.prelude.h  = self.heap.h;
                or_frame.prelude.b0 = self.b0;
                or_frame.prelude.attr_var_init_queue_b =
                    self.attr_var_init.attr_var_queue.len();
                or_frame.prelude.attr_var_init_bindings_b =
                    self.attr_var_init.attr_var_queue.len();

                self.b = b;

                for i in 1 .. n + 1  {
                    self.stack.index_or_frame_mut(b)[i-1] = self.registers[i].clone();
                }

                self.hb = self.heap.h;
                self.p += 1;
            }
            &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(self, call_policy.retry_me_else(self, offset))
            }
            &ChoiceInstruction::DefaultTrustMe => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(self, call_policy.trust_me(self))
            }
            &ChoiceInstruction::RetryMeElse(offset) => {
                try_or_fail!(self, call_policy.retry_me_else(self, offset))
            }
            &ChoiceInstruction::TrustMe => try_or_fail!(self, call_policy.trust_me(self)),
        }
    }

    pub(super) fn execute_cut_instr(
        &mut self,
        instr: &CutInstruction,
        cut_policy: &mut Box<dyn CutPolicy>,
    ) {
        match instr {
            &CutInstruction::NeckCut => {
                let b = self.b;
                let b0 = self.b0;

                if b > b0 {
                    self.b = b0;
                    self.tidy_trail();
                }

                self.p += 1;
            }
            &CutInstruction::GetLevel(r) => {
                let b0 = self.b0;

                self[r] = Addr::Con(Constant::CutPoint(b0));
                self.p += 1;
            }
            &CutInstruction::GetLevelAndUnify(r) => {
                let b0 = self[perm_v!(1)].clone();
                let a = self[r].clone();

                self.unify(a, b0);
                self.p += 1;
            }
            &CutInstruction::Cut(r) => {
                if !cut_policy.cut(self, r) {
                    self.p += 1;
                }
            }
        }
    }

    pub fn reset(&mut self) {
        self.stack.drop_in_place();

        self.hb = 0;
        self.e = 0;
        self.b = 0;
        self.b0 = 0;
        self.s = 0;
        self.tr = 0;
        self.p = CodePtr::default();
        self.cp = LocalCodePtr::default();
        self.attr_var_init.reset();
        self.num_of_args = 0;

        self.fail = false;
        self.trail.clear();
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.registers = vec![Addr::HeapCell(0); MAX_ARITY + 1]; // self.registers[0] is never used.
        self.block = 0;

        self.ball.reset();
        self.heap_locs.clear();
        self.lifted_heap.clear();
    }
}
