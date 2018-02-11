use prolog::and_stack::*;
use prolog::ast::*;
use prolog::builtins::*;
use prolog::copier::*;
use prolog::heap_iter::*;
use prolog::heap_print::*;
use prolog::machine::machine_state::*;
use prolog::num::{Integer, ToPrimitive, Zero};
use prolog::num::bigint::{BigInt, BigUint};
use prolog::num::rational::Ratio;
use prolog::or_stack::*;
use prolog::tabled_rc::*;

use std::cmp::max;
use std::rc::Rc;

macro_rules! try_or_fail {
    ($s:ident, $e:expr) => {{
        match $e {
            Ok(val)  => val,
            Err(msg) => {
                $s.throw_exception(msg);
                return;
            }
        }
    }}
}

impl MachineState {
    pub(super) fn new(atom_tbl: TabledData<Atom>) -> MachineState {
        MachineState {
            atom_tbl,
            s: 0,
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: CodePtr::default(),
            fail: false,
            heap: Heap::with_capacity(256),
            mode: MachineMode::Write,
            and_stack: AndStack::new(),
            or_stack: OrStack::new(),
            registers: vec![Addr::HeapCell(0); 64],
            trail: Vec::new(),
            tr: 0,
            hb: 0,
            block: 0,
            ball: (0, Vec::new()),
            interms: vec![Number::default(); 256]
        }
    }

    fn next_global_index(&self) -> usize {
        max(if self.and_stack.len() > 0 { self.and_stack[self.e].global_index } else { 0 },
            if self.b > 0 { self.or_stack[self.b - 1].global_index } else { 0 }) + 1
    }

    pub(crate) fn store(&self, a: Addr) -> Addr {
        match a {
            Addr::HeapCell(r)       => self.heap[r].as_addr(r),
            Addr::StackCell(fr, sc) => self.and_stack[fr][sc].clone(),
            addr                    => addr
        }
    }

    pub(crate) fn deref(&self, mut a: Addr) -> Addr {
        loop {
            let value = self.store(a.clone());

            if value.is_ref() && value != a {
                a = value;
                continue;
            }

            return a;
        };
    }

    fn bind(&mut self, r1: Ref, a2: Addr) {
        let t2 = self.store(a2);

        match r1 {
            Ref::StackCell(fr, sc) =>
                self.and_stack[fr][sc] = t2,
            Ref::HeapCell(hc) =>
                self.heap[hc] = HeapCellValue::Addr(t2)
        };

        self.trail(r1);
    }

    pub(super) fn print_term<Fmt, Outputter>(&self, a: Addr, fmt: Fmt, output: Outputter) -> Outputter
        where Fmt: HeapCellValueFormatter, Outputter: HeapCellValueOutputter
    {
        let iter    = HeapCellPreOrderIterator::new(&self, a);
        let printer = HeapCellPrinter::new(iter, fmt, output);

        printer.print()
    }

    fn unify(&mut self, a1: Addr, a2: Addr) {
        let mut pdl = vec![a1, a2];

        self.fail = false;

        while !(pdl.is_empty() || self.fail) {
            let d1 = self.deref(pdl.pop().unwrap());
            let d2 = self.deref(pdl.pop().unwrap());

            if d1 != d2 {
                match (self.store(d1.clone()), self.store(d2.clone())) {
                    (Addr::HeapCell(hc), _) =>
                        self.bind(Ref::HeapCell(hc), d2),
                    (_, Addr::HeapCell(hc)) =>
                        self.bind(Ref::HeapCell(hc), d1),
                    (Addr::StackCell(fr, sc), _) =>
                        self.bind(Ref::StackCell(fr, sc), d2),
                    (_, Addr::StackCell(fr, sc)) =>
                        self.bind(Ref::StackCell(fr, sc), d1),
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    },
                    (Addr::Con(c1), Addr::Con(c2)) => {
                        if c1 != c2 {
                            self.fail = true;
                        }
                    },
                    (Addr::Str(a1), Addr::Str(a2)) => {
                        let r1 = &self.heap[a1];
                        let r2 = &self.heap[a2];

                        if let &HeapCellValue::NamedStr(n1, ref f1, _) = r1 {
                            if let &HeapCellValue::NamedStr(n2, ref f2, _) = r2 {
                                if n1 == n2 && *f1 == *f2 {
                                    for i in 1 .. n1 + 1 {
                                        pdl.push(Addr::HeapCell(a1 + i));
                                        pdl.push(Addr::HeapCell(a2 + i));
                                    }

                                    continue;
                                }
                            }
                        }

                        self.fail = true;
                    },
                    _ => self.fail = true
                };
            }
        }
    }

    fn trail(&mut self, r: Ref) {
        match r {
            Ref::HeapCell(hc) =>
                if hc < self.hb {
                    self.trail.push(r);
                    self.tr += 1;
                },
            Ref::StackCell(fr, _) => {
                let fr_gi = self.and_stack[fr].global_index;
                let b_gi  = if !self.or_stack.is_empty() {
                    if self.b > 0 {
                        let b = self.b - 1;
                        self.or_stack[b].global_index
                    } else {
                        0
                    }
                } else {
                    0
                };

                if fr_gi < b_gi {
                    self.trail.push(r);
                    self.tr += 1;
                }
            }
        }
    }

    fn unwind_trail(&mut self, a1: usize, a2: usize) {
        for i in a1 .. a2 {
            match self.trail[i] {
                Ref::HeapCell(r) =>
                    self.heap[r] = HeapCellValue::Addr(Addr::HeapCell(r)),
                Ref::StackCell(fr, sc) =>
                    self.and_stack[fr][sc] = Addr::StackCell(fr, sc)
            }
        }
    }

    pub(super) fn tidy_trail(&mut self) {
        if self.b == 0 {
            return;
        }

        let b = self.b - 1;
        let mut i = self.or_stack[b].tr;

        while i < self.tr {
            let tr_i = self.trail[i];
            let hb = self.hb;

            match tr_i {
                Ref::HeapCell(tr_i) =>
                    if tr_i < hb { //|| ((h < tr_i) && tr_i < b) {
                        i += 1;
                    } else {
                        let tr = self.tr;
                        let val = self.trail[tr - 1];
                        self.trail[i] = val;
                    },
                Ref::StackCell(fr, _) => {
                    let b = self.b - 1;
                    let fr_gi = self.and_stack[fr].global_index;
                    let b_gi  = if !self.or_stack.is_empty() {
                        self.or_stack[b].global_index
                    } else {
                        0
                    };

                    if fr_gi < b_gi {
                        i += 1;
                    } else {
                        let tr = self.tr;
                        let val = self.trail[tr - 1];
                        self.trail[i] = val;
                    }
                }
            };
        }
    }

    fn write_constant_to_var(&mut self, addr: Addr, c: Constant) {
        let addr = self.deref(addr);

        match self.store(addr) {
            Addr::HeapCell(hc) => {
                self.heap[hc] = HeapCellValue::Addr(Addr::Con(c.clone()));
                self.trail(Ref::HeapCell(hc));
            },
            Addr::StackCell(fr, sc) => {
                self.and_stack[fr][sc] = Addr::Con(c.clone());
                self.trail(Ref::StackCell(fr, sc));
            },
            Addr::Con(c1) => {
                if c1 != c {
                    self.fail = true;
                }
            },
            _ => self.fail = true
        };
    }

    fn get_number(&self, at: &ArithmeticTerm) -> Result<Number, Vec<HeapCellValue>> {

        match at {
            &ArithmeticTerm::Reg(r) => {
                let addr = self[r].clone();
                let item = self.store(self.deref(addr));

                match item {
                    Addr::Con(Constant::Number(n)) => Ok(n),
                    _ => {
                        let atom_tbl = self.atom_tbl.clone();
                        Err(functor!(self.atom_tbl,
                                     "instantiation_error",
                                     1,
                                     [heap_atom!("(is)/2", atom_tbl)]))
                    }
                }
            },
            &ArithmeticTerm::Interm(i)     => Ok(self.interms[i-1].clone()),
            &ArithmeticTerm::Number(ref n) => Ok(n.clone()),
        }
    }

    fn get_rational(&self, at: &ArithmeticTerm) -> Result<Rc<Ratio<BigInt>>, Vec<HeapCellValue>> {
        let n = self.get_number(at)?;

        match n {
            Number::Rational(r) => Ok(r),
            Number::Float(fl) =>
                if let Some(r) = Ratio::from_float(fl.into_inner()) {
                    Ok(Rc::new(r))
                } else {
                    Err(functor!(self.atom_tbl,
                                 "instantiation_error",
                                 1,
                                 [heap_atom!("(is)/2", self.atom_tbl)]))
                },
            Number::Integer(bi) =>
                Ok(Rc::new(Ratio::from_integer((*bi).clone())))
        }
    }

    fn signed_bitwise_op<Op>(&self, n1: &BigInt, n2: &BigInt, f: Op) -> Rc<BigInt>
        where Op: FnOnce(&BigUint, &BigUint) -> BigUint
    {
        let n1_b = n1.to_signed_bytes_le();
        let n2_b = n2.to_signed_bytes_le();

        let u_n1 = BigUint::from_bytes_le(&n1_b);
        let u_n2 = BigUint::from_bytes_le(&n2_b);

        Rc::new(BigInt::from_signed_bytes_le(&f(&u_n1, &u_n2).to_bytes_le()))
    }

    fn arith_eval_by_metacall(&self, r: RegType) -> Result<Number, Vec<HeapCellValue>>
    {
        let instantiation_err = functor!(self.atom_tbl.clone(), "instantiation_error", 1,
                                         [heap_atom!("(is)/2", self.atom_tbl.clone())]);

        let a = self[r].clone();

        if let &Addr::Con(Constant::Number(ref n)) = &a {
            return Ok(n.clone());
        }

        let mut interms: Vec<Number> = Vec::with_capacity(64);

        for heap_val in self.post_order_iter(a) {
            match heap_val {
                HeapCellValue::NamedStr(2, name, Some(Fixity::In)) => {
                    let a2 = interms.pop().unwrap();
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "+" => interms.push(a1 + a2),
                        "-" => interms.push(a1 - a2),
                        "*" => interms.push(a1 * a2),
                        "rdiv" =>
                            match NumberPair::from(a1, a2) {
                                NumberPair::Rational(r1, r2) =>
                                    interms.push(Number::Rational(self.rdiv(r1, r2)?)),
                                _ =>
                                    return Err(instantiation_err)
                            },
                        "//"  => interms.push(Number::Integer(self.idiv(a1, a2)?)),
                        "div" => interms.push(Number::Integer(self.fidiv(a1, a2)?)),
                        ">>"  => interms.push(Number::Integer(self.shr(a1, a2)?)),
                        "<<"  => interms.push(Number::Integer(self.shl(a1, a2)?)),
                        "/\\" => interms.push(Number::Integer(self.and(a1, a2)?)),
                        "\\/" => interms.push(Number::Integer(self.or(a1, a2)?)),
                        "xor" => interms.push(Number::Integer(self.xor(a1, a2)?)),
                        "mod" => interms.push(Number::Integer(self.modulus(a1, a2)?)),
                        "rem" => interms.push(Number::Integer(self.remainder(a1, a2)?)),
                        _     => return Err(instantiation_err)
                    }
                },
                HeapCellValue::NamedStr(1, name, Some(Fixity::Pre)) => {
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "-" => interms.push(- a1),
                         _  => return Err(instantiation_err)
                    }
                },
                HeapCellValue::Addr(Addr::Con(Constant::Number(n))) =>
                    interms.push(n),
                _ =>
                    return Err(instantiation_err)
            }
        };

        Ok(interms.pop().unwrap())
    }

    fn rdiv(&self, r1: Rc<Ratio<BigInt>>, r2: Rc<Ratio<BigInt>>)
            -> Result<Rc<Ratio<BigInt>>, Vec<HeapCellValue>>
    {
        if *r2 == Ratio::zero() {
            Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                         [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
        } else {
            Ok(Rc::new(&*r1 / &*r2))
        }
    }

    fn fidiv(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                                 [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
                } else {
                    Ok(Rc::new(n1.div_floor(&n2)))
                },
            _ => Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                              [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn idiv(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                                 [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
                } else {
                    Ok(Rc::new(&*n1 / &*n2))
                },
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn div(&self, n1: Number, n2: Number) -> Result<Number, Vec<HeapCellValue>>
    {
        if n2.is_zero() {
            Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                         [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
        } else {
            Ok(n1 / n2)
        }
    }

    fn shr(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                match n2.to_usize() {
                    Some(n2) => Ok(Rc::new(&*n1 >> n2)),
                    _        => Ok(Rc::new(&*n1 >> usize::max_value()))
                },
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn shl(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                match n2.to_usize() {
                    Some(n2) => Ok(Rc::new(&*n1 << n2)),
                    _        => Ok(Rc::new(&*n1 << usize::max_value()))
                },
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn xor(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 ^ u_n2)),
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn and(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 & u_n2)),
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn modulus(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                                 [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
                } else {
                    Ok(Rc::new(n1.mod_floor(&n2)))
                },
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn remainder(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                                 [heap_atom!("zero_divisor", self.atom_tbl.clone())]))
                } else {
                    Ok(Rc::new(&*n1 % &*n2))
                },
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    fn or(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, Vec<HeapCellValue>>
    {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 & u_n2)),
            _ =>
                Err(functor!(self.atom_tbl.clone(), "evaluation_error", 1,
                             [heap_atom!("expected_integer_args", self.atom_tbl.clone())]))
        }
    }

    pub(super) fn execute_arith_instr(&mut self, instr: &ArithmeticInstruction) {
        match instr {
            &ArithmeticInstruction::Add(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = n1 + n2;
                self.p += 1;
            },
            &ArithmeticInstruction::Sub(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = n1 - n2;
                self.p += 1;
            },
            &ArithmeticInstruction::Mul(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = n1 * n2;
                self.p += 1;
            },
            &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                let r1 = try_or_fail!(self, self.get_rational(a1));
                let r2 = try_or_fail!(self, self.get_rational(a2));

                self.interms[t - 1] = Number::Rational(try_or_fail!(self, self.rdiv(r1, r2)));
                self.p += 1;
            },
            &ArithmeticInstruction::FIDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.fidiv(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::IDiv(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.idiv(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Neg(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = - n1;
                self.p += 1;
            },
            &ArithmeticInstruction::Div(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.div(n1, n2));
                self.p += 1;
            },
            &ArithmeticInstruction::Shr(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.shr(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Shl(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.shl(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Xor(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.xor(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::And(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.and(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Or(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.or(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Mod(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.modulus(n1, n2)));
                self.p += 1;
            },
            &ArithmeticInstruction::Rem(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = Number::Integer(try_or_fail!(self, self.remainder(n1, n2)));
                self.p += 1;
            }
        };
    }

    pub(super) fn execute_fact_instr(&mut self, instr: &FactInstruction) {
        match instr {
            &FactInstruction::GetConstant(_, ref c, reg) => {
                let addr = self[reg].clone();
                self.write_constant_to_var(addr, c.clone());
            },
            &FactInstruction::GetList(_, reg) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr.clone()) {
                    Addr::HeapCell(hc) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));
                        self.bind(Ref::HeapCell(hc), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    },
                    Addr::StackCell(fr, sc) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));
                        self.bind(Ref::StackCell(fr, sc), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    },
                    Addr::Lis(a) => {
                        self.s = a;
                        self.mode = MachineMode::Read;
                    },
                    _ => self.fail = true
                };
            },
            &FactInstruction::GetStructure(_, ref name, arity, reg, fixity) => {
                let addr = self.deref(self[reg].clone());

                match self.store(addr.clone()) {
                    Addr::Str(a) => {
                        let result = &self.heap[a];

                        if let &HeapCellValue::NamedStr(narity, ref str, _) = result {
                            if narity == arity && *name == *str {
                                self.s = a + 1;
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        }
                    },
                    Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Str(h + 1)));
                        self.heap.push(HeapCellValue::NamedStr(arity, name.clone(), fixity));

                        self.bind(addr.as_var().unwrap(), Addr::HeapCell(h));

                        self.mode = MachineMode::Write;
                    },
                    _ => self.fail = true
                };
            },
            &FactInstruction::GetVariable(norm, arg) =>
                self[norm] = self.registers[arg].clone(),
            &FactInstruction::GetValue(norm, arg) => {
                let norm_addr = self[norm].clone();
                let reg_addr  = self.registers[arg].clone();

                self.unify(norm_addr, reg_addr);
            },
            &FactInstruction::UnifyConstant(ref c) => {
                match self.mode {
                    MachineMode::Read  => {
                        let addr = Addr::HeapCell(self.s);
                        self.write_constant_to_var(addr, c.clone());
                    },
                    MachineMode::Write => {
                        self.heap.push(HeapCellValue::Addr(Addr::Con(c.clone())));
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyVariable(reg) => {
                match self.mode {
                    MachineMode::Read  =>
                        self[reg] = self.heap[self.s].as_addr(self.s),
                    MachineMode::Write => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        self[reg] = Addr::HeapCell(h);
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyLocalValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    },
                    MachineMode::Write => {
                        let addr = self.deref(self[reg].clone());
                        let h    = self.heap.h;

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
            },
            &FactInstruction::UnifyValue(reg) => {
                let s = self.s;

                match self.mode {
                    MachineMode::Read  => {
                        let reg_addr = self[reg].clone();
                        self.unify(reg_addr, Addr::HeapCell(s));
                    },
                    MachineMode::Write => {
                        let heap_val = self.store(self[reg].clone());
                        self.heap.push(HeapCellValue::Addr(heap_val));
                    }
                };

                self.s += 1;
            },
            &FactInstruction::UnifyVoid(n) => {
                match self.mode {
                    MachineMode::Read =>
                        self.s += n,
                    MachineMode::Write => {
                        let h = self.heap.h;

                        for i in h .. h + n {
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
                    Addr::HeapCell(_) | Addr::StackCell(_, _) => v,
                    Addr::Con(_) => c,
                    Addr::Lis(_) => l,
                    Addr::Str(_) => s
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o
                };
            },
            &IndexingInstruction::SwitchOnConstant(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Con(constant) => {
                        match hm.get(&constant) {
                            Some(offset) => *offset,
                            _ => 0
                        }
                    },
                    _ => 0
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o,
                };
            },
            &IndexingInstruction::SwitchOnStructure(_, ref hm) => {
                let a1 = self.registers[1].clone();
                let addr = self.store(self.deref(a1));

                let offset = match addr {
                    Addr::Str(s) => {
                        if let &HeapCellValue::NamedStr(arity, ref name, _) = &self.heap[s] {
                            match hm.get(&(name.clone(), arity)) {
                                Some(offset) => *offset,
                                _ => 0
                            }
                        } else {
                            0
                        }
                    },
                    _ => 0
                };

                match offset {
                    0 => self.fail = true,
                    o => self.p += o
                };
            }
        };
    }

    pub(super) fn execute_query_instr(&mut self, instr: &QueryInstruction) {
        match instr {
            &QueryInstruction::GetVariable(norm, arg) =>
                self[norm] = self.registers[arg].clone(),
            &QueryInstruction::PutConstant(_, ref constant, reg) =>
                self[reg] = Addr::Con(constant.clone()),
            &QueryInstruction::PutList(_, reg) =>
                self[reg] = Addr::Lis(self.heap.h),
            &QueryInstruction::PutStructure(_, ref name, arity, reg, fixity) => {
                let h = self.heap.h;

                self.heap.push(HeapCellValue::NamedStr(arity, name.clone(), fixity));
                self[reg] = Addr::Str(h);
            },
            &QueryInstruction::PutUnsafeValue(n, arg) => {
                let e    = self.e;
                let addr = self.deref(Addr::StackCell(e, n));

                if addr.is_protected(e) {
                    self.registers[arg] = self.store(addr);
                } else {
                    let h = self.heap.h;

                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                    self.bind(Ref::HeapCell(h), addr);

                    self.registers[arg] = self.heap[h].as_addr(h);
                }
            },
            &QueryInstruction::PutValue(norm, arg) =>
                self.registers[arg] = self[norm].clone(),
            &QueryInstruction::PutVariable(norm, arg) => {
                match norm {
                    RegType::Perm(n) => {
                        let e = self.e;

                        self[norm] = Addr::StackCell(e, n);
                        self.registers[arg] = self[norm].clone();
                    },
                    RegType::Temp(_) => {
                        let h = self.heap.h;
                        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));

                        self[norm] = Addr::HeapCell(h);
                        self.registers[arg] = Addr::HeapCell(h);
                    }
                };
            },
            &QueryInstruction::SetConstant(ref c) => {
                self.heap.push(HeapCellValue::Addr(Addr::Con(c.clone())));
            },
            &QueryInstruction::SetLocalValue(reg) => {
                let addr = self.deref(self[reg].clone());
                let h    = self.heap.h;

                if let Addr::HeapCell(hc) = addr {
                    if hc < h {
                        self.heap.push(HeapCellValue::Addr(addr));
                        return;
                    }
                }

                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self.bind(Ref::HeapCell(h), addr);
            },
            &QueryInstruction::SetVariable(reg) => {
                let h = self.heap.h;
                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                self[reg] = Addr::HeapCell(h);
            },
            &QueryInstruction::SetValue(reg) => {
                let heap_val = self[reg].clone();
                self.heap.push(HeapCellValue::Addr(heap_val));
            },
            &QueryInstruction::SetVoid(n) => {
                let h = self.heap.h;

                for i in h .. h + n {
                    self.heap.push(HeapCellValue::Addr(Addr::HeapCell(i)));
                }
            }
        }
    }

    fn try_call_predicate(&mut self, code_dir: &CodeDir, name: TabledRc<Atom>, arity: usize)
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                self.cp = self.p + 1;
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => self.fail = true
        };
    }

    fn try_execute_predicate(&mut self, code_dir: &CodeDir, name: TabledRc<Atom>, arity: usize)
    {
        let compiled_tl_index = code_dir.get(&(name, arity)).map(|index| index.1);

        match compiled_tl_index {
            Some(compiled_tl_index) => {
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(compiled_tl_index);
            },
            None => self.fail = true
        };
    }

    fn handle_internal_call_n(&mut self, code_dir: &CodeDir)
    {
        let arity = self.num_of_args + 1;
        let pred  = self.registers[1].clone();

        for i in 2 .. arity {
            self.registers[i-1] = self.registers[i].clone();
        }

        if arity > 1 {
            self.registers[arity - 1] = pred;

            if let Some((name, arity)) = self.setup_call_n(arity - 1) {
                self.try_execute_predicate(code_dir, name, arity);
            }
        } else {
            self.fail = true;
        }
    }

    fn goto_throw(&mut self) {
        self.num_of_args = 1;
        self.b0 = self.b;
        self.p  = CodePtr::DirEntry(59);
    }

    fn throw_exception(&mut self, hcv: Vec<HeapCellValue>) {
        let h = self.heap.h;

        self.registers[1] = Addr::HeapCell(h);

        self.heap.append(hcv);
        self.goto_throw();
    }

    fn setup_call_n(&mut self, arity: usize) -> Option<PredicateKey>
    {
        let addr = self.store(self.deref(self.registers[arity].clone()));

        let (name, narity) = match addr {
            Addr::Str(a) => {
                let result = self.heap[a].clone();

                if let HeapCellValue::NamedStr(narity, name, _) = result {
                    if narity + arity > 63 {
                        let atom_tbl = self.atom_tbl.clone();
                        self.throw_exception(functor!(atom_tbl,
                                                      "representation_error",
                                                      1,
                                                      [heap_atom!("exceeds_max_arity", atom_tbl)]));
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
            },
            Addr::Con(Constant::Atom(name)) => (name, 0),
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let atom_tbl = self.atom_tbl.clone();
                self.throw_exception(functor!(atom_tbl, "instantiation_error", 0, []));
                return None;
            },
            _ => {
                let atom_tbl = self.atom_tbl.clone();
                self.throw_exception(functor!(atom_tbl,
                                              "type_error",
                                              2,
                                              [heap_atom!("callable", atom_tbl),
                                               HeapCellValue::Addr(addr)]));
                return None;
            }
        };

        Some((name, arity + narity - 1))
    }

    pub(super) fn copy_and_align_ball_to_heap(&mut self) {
        let diff = self.ball.0 - self.heap.h;

        for heap_value in self.ball.1.iter().cloned() {
            self.heap.push(match heap_value {
                HeapCellValue::Addr(Addr::Con(c)) =>
                    HeapCellValue::Addr(Addr::Con(c)),
                HeapCellValue::Addr(Addr::Lis(a)) =>
                    HeapCellValue::Addr(Addr::Lis(a - diff)),
                HeapCellValue::Addr(Addr::HeapCell(hc)) =>
                    HeapCellValue::Addr(Addr::HeapCell(hc - diff)),
                HeapCellValue::Addr(Addr::Str(s)) =>
                    HeapCellValue::Addr(Addr::Str(s - diff)),
                _ => heap_value
            });
        }
    }

    fn try_get_arg(&mut self) -> Result<(), Vec<HeapCellValue>>
    {
        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

        if let Addr::Con(Constant::Number(Number::Integer(i))) = a1 {
            let a2 = self.store(self.deref(self[temp_v!(2)].clone()));

            if let Addr::Str(o) = a2 {
                match self.heap[o].clone() {
                    HeapCellValue::NamedStr(arity, _, _) =>
                        match i.to_usize() {
                            Some(i) if 1 <= i && i <= arity => {
                                let a3  = self[temp_v!(3)].clone();
                                let h_a = Addr::HeapCell(o + i);

                                self.unify(a3, h_a);
                            },
                            _ => self.fail = true
                        },
                    _ => self.fail = true
                };
            } else {
                return Err(functor!(self.atom_tbl,
                                    "type_error",
                                    1,
                                    [heap_atom!("compound_expected", self.atom_tbl)]));
            }
        }

        Ok(())
    }

    fn compare_numbers(&mut self, cmp: CompareNumberQT, n1: Number, n2: Number) {
        self.fail = match cmp {
            CompareNumberQT::GreaterThan if !(n1.gt(n2)) => true,
            CompareNumberQT::GreaterThanOrEqual if !(n1.gte(n2)) => true,
            CompareNumberQT::LessThan if !(n1.lt(n2)) => true,
            CompareNumberQT::LessThanOrEqual if !(n1.lte(n2)) => true,
            CompareNumberQT::NotEqual if !(n1.ne(n2)) => true,
            CompareNumberQT::Equal if !(n1.eq(n2)) => true,
            _ => false
        };

        self.p += 1;
    }

    fn reset_block(&mut self, addr: Addr) {
        // let addr = self.deref(self[temp_v!(1)].clone());

        match self.store(addr) {
            Addr::Con(Constant::Usize(b)) => {
                self.block = b;
                self.p += 1;
            },
            _ => self.fail = true
        };
    }

    pub(super) fn execute_built_in_instr(&mut self, code_dir: &CodeDir,
                                         cut_policy: &mut Box<CutPolicy>,
                                         instr: &BuiltInInstruction)
    {
        match instr {
            &BuiltInInstruction::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self, self.get_number(at_1));
                let n2 = try_or_fail!(self, self.get_number(at_2));

                self.compare_numbers(cmp, n1, n2);
            },
            &BuiltInInstruction::DynamicCompareNumber(cmp) => {
                let n1 = try_or_fail!(self, self.arith_eval_by_metacall(temp_v!(1)));
                let n2 = try_or_fail!(self, self.arith_eval_by_metacall(temp_v!(2)));

                self.compare_numbers(cmp, n1, n2);
            },
            &BuiltInInstruction::DynamicIs => {
                let a = self[temp_v!(1)].clone();
                let result = try_or_fail!(self, self.arith_eval_by_metacall(temp_v!(2)));

                self.unify(a, Addr::Con(Constant::Number(result)));
                self.p += 1;
            },
            &BuiltInInstruction::GetArgCall =>
                try_or_fail!(self, {
                    let val = self.try_get_arg();
                    self.p += 1;
                    val
                }),
            &BuiltInInstruction::GetArgExecute =>
                try_or_fail!(self, {
                    let val = self.try_get_arg();
                    self.p = self.cp;
                    val
                }),
            &BuiltInInstruction::GetCurrentBlock => {
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, c);
                self.p += 1;
            },
            &BuiltInInstruction::EraseBall => {
                self.ball.0 = 0;
                self.ball.1.truncate(0);
                self.p += 1;
            },
            &BuiltInInstruction::GetBall => {
                let addr = self.store(self.deref(self[temp_v!(1)].clone()));
                let h = self.heap.h;

                if self.ball.1.len() > 0 {
                    self.copy_and_align_ball_to_heap();
                } else {
                    self.fail = true;
                    return;
                }

                let ball = self.heap[h].as_addr(h);

                match addr.as_var() {
                    Some(r) => {
                        self.bind(r, ball);
                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::GetCutPoint(r) => {
                let c = Constant::Usize(self.b);
                self[r] = Addr::Con(c);

                self.p += 1;
            },
            &BuiltInInstruction::InstallCleaner => {
                let addr = self[temp_v!(1)].clone();
                let b = self.b;
                let block = self.block;

                if cut_policy.downcast_ref::<SetupCallCleanupCutPolicy>().is_err() {
                    *cut_policy = Box::new(SetupCallCleanupCutPolicy::new());
                }

                match cut_policy.downcast_mut::<SetupCallCleanupCutPolicy>().ok()
                {
                    Some(cut_policy) => cut_policy.push_cont_pt(addr, b, block),
                    None => panic!("install_cleaner: should have installed \\
SetupCallCleanupCutPolicy.")
                };

                self.p += 1;
            },
            &BuiltInInstruction::RestoreCutPolicy => {
                let restore_default =
                    if let Ok(cut_policy) = cut_policy.downcast_ref::<SetupCallCleanupCutPolicy>() {
                        cut_policy.out_of_cont_pts()
                    } else {
                        false
                    };

                if restore_default {
                    *cut_policy = Box::new(DefaultCutPolicy {});
                }

                self.p += 1;
            },
            &BuiltInInstruction::SetBall => {
                let addr = self[temp_v!(1)].clone();
                self.ball.0 = self.heap.h;

                {
                    let mut duplicator = DuplicateBallTerm::new(self);
                    duplicator.duplicate_term(addr);
                }

                self.p += 1;
            },
            &BuiltInInstruction::SetCutPoint(r) => {
                let addr = self.store(self.deref(self[r].clone()));

                match addr {
                    Addr::Con(Constant::Usize(nb)) => {
                        if self.b > nb {
                            self.b = nb;
                            self.tidy_trail();
                            self.or_stack.truncate(self.b);
                        }

                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::CleanUpBlock => {
                let nb = self.store(self.deref(self[temp_v!(1)].clone()));

                match nb {
                    Addr::Con(Constant::Usize(nb)) => {
                        let b = self.b - 1;

                        if nb > 0 && self.or_stack[b].b == nb {
                            self.b = self.or_stack[nb - 1].b;
                            self.or_stack.truncate(self.b);
                        }

                        self.p += 1;
                    },
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::InstallNewBlock => {
                self.block = self.b;
                let c = Constant::Usize(self.block);
                let addr = self[temp_v!(1)].clone();

                self.write_constant_to_var(addr, c);
                self.p += 1;
            },
            &BuiltInInstruction::ResetBlock => {
                let addr = self.deref(self[temp_v!(1)].clone());
                self.reset_block(addr);
            },
            &BuiltInInstruction::UnwindStack => {
                self.b = self.block;
                self.or_stack.truncate(self.b);

                self.fail = true;
            },
            &BuiltInInstruction::IsAtomic(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Con(_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsInteger(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Integer(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsCompound(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Str(_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsFloat(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Float(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsRational(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Rational(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsString(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::Con(Constant::String(_)) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::IsNonVar(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::HeapCell(_) | Addr::StackCell(..) => self.fail = true,
                    _ => self.p += 1
                };
            },
            &BuiltInInstruction::IsVar(r) => {
                let d = self.store(self.deref(self[r].clone()));

                match d {
                    Addr::HeapCell(_) | Addr::StackCell(_,_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &BuiltInInstruction::InternalCallN =>
                self.handle_internal_call_n(code_dir),
            &BuiltInInstruction::Fail => {
                self.fail = true;
                self.p += 1;
            },
            &BuiltInInstruction::Succeed => {
                self.p += 1;
            },
            &BuiltInInstruction::Unify => {
                let a1 = self[temp_v!(1)].clone();
                let a2 = self[temp_v!(2)].clone();

                self.unify(a1, a2);
                self.p += 1;
            },
        };
    }

    fn try_functor(&mut self) -> Result<(), Vec<HeapCellValue>> {
        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

        match a1.clone() {
            Addr::Str(o) =>
                match self.heap[o].clone() {
                    HeapCellValue::NamedStr(arity, name, _) => {
                        let name  = Addr::Con(Constant::Atom(name)); // A2
                        let arity = Addr::Con(Constant::Number(rc_integer!(arity)));

                        let a2 = self[temp_v!(2)].clone();
                        self.unify(a2, name);

                        if !self.fail {
                            let a3 = self[temp_v!(3)].clone();
                            self.unify(a3, arity);
                        }
                    },
                    _ => self.fail = true
                },
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let name  = self.store(self.deref(self[temp_v!(2)].clone()));
                let arity = self.store(self.deref(self[temp_v!(3)].clone()));

                if let Addr::Con(Constant::Atom(name)) = name {
                    if let Addr::Con(Constant::Number(Number::Integer(arity))) = arity {
                        let f_a = Addr::Str(self.heap.h);
                        let arity = match arity.to_usize() {
                            Some(arity) => arity,
                            None => {
                                self.fail = true;
                                return Ok(());
                            }
                        };

                        if arity > 0 {
                            self.heap.push(HeapCellValue::NamedStr(arity, name, None));
                        } else {
                            let c = Constant::Atom(name.clone());
                            self.heap.push(HeapCellValue::Addr(Addr::Con(c)));
                        }

                        for _ in 0 .. arity {
                            let h = self.heap.h;
                            self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                        }

                        self.unify(a1, f_a);
                    } else {
                        return Err(functor!(self.atom_tbl, "instantiation_error", 0, []));
                    }
                } else {
                    return Err(functor!(self.atom_tbl, "instantiation_error", 0, []));
                }
            },
            _ => {
                let a2 = self[temp_v!(2)].clone();
                self.unify(a1, a2);

                if !self.fail {
                    let a3 = self[temp_v!(3)].clone();
                    self.unify(a3, Addr::Con(Constant::Number(rc_integer!(0))));
                }
            }
        };

        Ok(())
    }

    fn duplicate_term(&mut self) {
        let old_h = self.heap.h;

        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        // drop the mutable references contained in gadget
        // once the term has been duplicated.
        {
            let mut gadget = DuplicateTerm::new(self);
            gadget.duplicate_term(a1);
        }

        self.unify(Addr::HeapCell(old_h), a2);
    }

    // returns true on failure.
    fn eq_test(&self) -> bool
    {
        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));
        let a2 = self.store(self.deref(self[temp_v!(2)].clone()));

        let iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        for (v1, v2) in iter {
            match (v1, v2) {
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) =>
                    if ar1 != ar2 || *n1 != *n2 {
                        return true;
                    },
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) =>
                    continue,
                (HeapCellValue::Addr(a1), HeapCellValue::Addr(a2)) =>
                    if a1 != a2 {
                        return true;
                    },                
                _ => return true
            }
        }

        false
    }

    // returns true on failure.
    fn ground_test(&self) -> bool
    {
        let a = self.store(self.deref(self[temp_v!(1)].clone()));

        for v in self.acyclic_pre_order_iter(a) {
            match v {
                HeapCellValue::Addr(Addr::HeapCell(..)) =>
                    return true,
                HeapCellValue::Addr(Addr::StackCell(..)) =>
                    return true,
                _ => {}
            }
        };

        false
    }

    pub(super) fn execute_ctrl_instr(&mut self, code_dir: &CodeDir, cut_policy: &mut Box<CutPolicy>,
                                     instr: &ControlInstruction)
    {
        match instr {
            &ControlInstruction::Allocate(num_cells) => {
                let gi = self.next_global_index();

                self.p += 1;

                if self.e + 1 < self.and_stack.len() {
                    let and_gi = self.and_stack[self.e].global_index;
                    let or_gi = self.or_stack.top()
                        .map(|or_fr| or_fr.global_index)
                        .unwrap_or(0);

                    if and_gi > or_gi {
                        let index = self.e + 1;

                        self.and_stack[index].e  = self.e;
                        self.and_stack[index].cp = self.cp;
                        self.and_stack[index].global_index = gi;

                        self.and_stack.resize(index, num_cells);

                        self.e = index;

                        return;
                    }
                }

                self.and_stack.push(gi, self.e, self.cp, num_cells);
                self.e = self.and_stack.len() - 1;
            },
            &ControlInstruction::ArgCall => {
                self.cp = self.p + 1;
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(150);
            },
            &ControlInstruction::ArgExecute => {
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(150);
            },
            &ControlInstruction::Call(ref name, arity, _) =>
                self.try_call_predicate(code_dir, name.clone(), arity),
            &ControlInstruction::CatchCall => {
                self.cp = self.p + 1;
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(5);
            },
            &ControlInstruction::CatchExecute => {
                self.num_of_args = 3;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(5);
            },
            &ControlInstruction::CallN(arity) =>
                if let Some((name, arity)) = self.setup_call_n(arity) {
                    self.try_call_predicate(code_dir, name, arity);
                },
            &ControlInstruction::CheckCpExecute => {
                let a = self.store(self.deref(self[temp_v!(2)].clone()));

                match a {
                    Addr::Con(Constant::Usize(old_b)) if self.b > old_b + 1 => {
                        self.p = self.cp;
                    },
                    _ => {
                        self.num_of_args = 2;
                        self.b0 = self.b;
                        self.p = CodePtr::DirEntry(366); // goto sgc_on_success/2, 366.
                    }
                };
            },
            &ControlInstruction::Deallocate => {
                let e = self.e;

                self.cp = self.and_stack[e].cp;
                self.e  = self.and_stack[e].e;

                self.p += 1;
            },
            &ControlInstruction::DisplayCall => {
                let output = self.print_term(self[temp_v!(1)].clone(),
                                             DisplayFormatter {},
                                             PrinterOutputter::new());

                println!("{}", output.result());

                self.p += 1;
            },
            &ControlInstruction::DisplayExecute => {
                let output = self.print_term(self[temp_v!(1)].clone(),
                                             DisplayFormatter {},
                                             PrinterOutputter::new());

                println!("{}", output.result());

                self.p = self.cp;
            },
            &ControlInstruction::DuplicateTermCall => {
                self.duplicate_term();
                self.p += 1;
            },
            &ControlInstruction::DuplicateTermExecute => {
                self.duplicate_term();
                self.p = self.cp;
            },
            &ControlInstruction::EqCall => {
                self.fail = self.eq_test();
                self.p += 1;
            },
            &ControlInstruction::EqExecute => {
                self.fail = self.eq_test();
                self.p = self.cp;
            },
            &ControlInstruction::GroundCall => {
                self.fail = self.ground_test();
                self.p += 1;
            },
            &ControlInstruction::GroundExecute => {
                self.fail = self.ground_test();
                self.p = self.cp;
            },
            &ControlInstruction::Execute(ref name, arity) =>
                self.try_execute_predicate(code_dir, name.clone(), arity),
            &ControlInstruction::ExecuteN(arity) =>
                if let Some((name, arity)) = self.setup_call_n(arity) {
                    self.try_execute_predicate(code_dir, name, arity);
                },
            &ControlInstruction::FunctorCall =>
                try_or_fail!(self, {
                    let val = self.try_functor();
                    self.p += 1;
                    val
                }),
            &ControlInstruction::FunctorExecute =>
                try_or_fail!(self, {
                    let val = self.try_functor();
                    self.p = self.cp;
                    val
                }),
            &ControlInstruction::GetCleanerCall => {
                let dest = self[temp_v!(1)].clone();

                match cut_policy.downcast_mut::<SetupCallCleanupCutPolicy>().ok() {
                    Some(sgc_policy) =>
                        if let Some((addr, b_cutoff, prev_block)) = sgc_policy.pop_cont_pt()
                        {
                            self.p += 1;

                            if self.b <= b_cutoff + 1 {
                                self.block = prev_block;

                                if let Some(r) = dest.as_var() {
                                    self.bind(r, addr);
                                    return;
                                }
                            } else {
                                sgc_policy.push_cont_pt(addr, b_cutoff, prev_block);
                            }
                        },
                    None => panic!("expected SetupCallCleanupCutPolicy trait object.")
                };

                self.fail = true;
            },
            &ControlInstruction::GotoCall(p, arity) => {
                self.cp = self.p + 1;
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(p);
            },
            &ControlInstruction::GotoExecute(p, arity) => {
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p  = CodePtr::DirEntry(p);
            },
            &ControlInstruction::IsCall(r, ref at) => {
                let a1 = self[r].clone();
                let a2 = try_or_fail!(self, self.get_number(at));

                self.unify(a1, Addr::Con(Constant::Number(a2)));
                self.p += 1;
            },
            &ControlInstruction::IsExecute(r, ref at) => {
                let a1 = self[r].clone();
                let a2 = try_or_fail!(self, self.get_number(at));

                self.unify(a1, Addr::Con(Constant::Number(a2)));
                self.p = self.cp;
            },
            &ControlInstruction::JmpByCall(arity, offset) => {
                self.cp = self.p + 1;
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p += offset;
            },
            &ControlInstruction::JmpByExecute(arity, offset) => {
                self.num_of_args = arity;
                self.b0 = self.b;
                self.p += offset;
            },
            &ControlInstruction::NotEqCall => {
                self.fail = !self.eq_test();
                self.p += 1;
            },
            &ControlInstruction::NotEqExecute => {
                self.fail = !self.eq_test();
                self.p = self.cp;
            },            
            &ControlInstruction::Proceed =>
                self.p = self.cp,
            &ControlInstruction::ThrowCall => {
                self.cp = self.p + 1;
                self.goto_throw();
            },
            &ControlInstruction::ThrowExecute => {
                self.goto_throw();
            },
        };
    }

    pub(super) fn execute_indexed_choice_instr(&mut self, instr: &IndexedChoiceInstruction)
    {
        match instr {
            &IndexedChoiceInstruction::Try(l) => {
                let n = self.num_of_args;
                let gi = self.next_global_index();

                self.or_stack.push(gi,
                                   self.e,
                                   self.cp,
                                   self.b,
                                   self.p + 1,
                                   self.tr,
                                   self.heap.h,
                                   self.b0,
                                   self.num_of_args);

                self.b = self.or_stack.len();
                let b = self.b - 1;

                for i in 1 .. n + 1 {
                    self.or_stack[b][i] = self.registers[i].clone();
                }

                self.hb = self.heap.h;
                self.p += l;
            },
            &IndexedChoiceInstruction::Retry(l) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                self.or_stack[b].bp = self.p + 1;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);
                self.tr = self.or_stack[b].tr;

                self.trail.truncate(self.tr);
                self.heap.truncate(self.or_stack[b].h);

                self.hb = self.heap.h;

                self.p += l;
            },
            &IndexedChoiceInstruction::Trust(l) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);

                self.tr = self.or_stack[b].tr;
                self.trail.truncate(self.tr);

                self.heap.truncate(self.or_stack[b].h);
                self.b = self.or_stack[b].b;

                self.or_stack.truncate(self.b);

                self.hb = self.heap.h;
                self.p += l;
            },
        };
    }

    pub(super) fn execute_choice_instr(&mut self, instr: &ChoiceInstruction)
    {
        match instr {
            &ChoiceInstruction::TryMeElse(offset) => {
                let n = self.num_of_args;
                let gi = self.next_global_index();

                self.or_stack.push(gi,
                                   self.e,
                                   self.cp,
                                   self.b,
                                   self.p + offset,
                                   self.tr,
                                   self.heap.h,
                                   self.b0,
                                   self.num_of_args);

                self.b = self.or_stack.len();
                let b  = self.b - 1;

                for i in 1 .. n + 1 {
                    self.or_stack[b][i] = self.registers[i].clone();
                }

                self.hb = self.heap.h;
                self.p += 1;
            },
            &ChoiceInstruction::RetryMeElse(offset) => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                self.or_stack[b].bp = self.p + offset;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);
                self.tr = self.or_stack[b].tr;

                self.trail.truncate(self.tr);
                self.heap.truncate(self.or_stack[b].h);

                self.hb = self.heap.h;

                self.p += 1;
            },
            &ChoiceInstruction::TrustMe => {
                let b = self.b - 1;
                let n = self.or_stack[b].num_args();

                for i in 1 .. n + 1 {
                    self.registers[i] = self.or_stack[b][i].clone();
                }

                self.e  = self.or_stack[b].e;
                self.cp = self.or_stack[b].cp;

                let old_tr  = self.or_stack[b].tr;
                let curr_tr = self.tr;

                self.unwind_trail(old_tr, curr_tr);

                self.tr = self.or_stack[b].tr;
                self.trail.truncate(self.tr);

                self.heap.truncate(self.or_stack[b].h);

                self.b = self.or_stack[b].b;

                self.or_stack.truncate(self.b);

                self.hb = self.heap.h;
                self.p += 1;
            }
        }
    }

    pub(super) fn execute_cut_instr(&mut self, instr: &CutInstruction,
                                    cut_policy: &mut Box<CutPolicy>)
    {
        match instr {
            &CutInstruction::NeckCut => {
                let b  = self.b;
                let b0 = self.b0;

                if b > b0 {
                    self.b = b0;
                    self.tidy_trail();
                    self.or_stack.truncate(self.b);
                }

                self.p += 1;
            },
            &CutInstruction::GetLevel(r) => {
                let b0 = self.b0;

                self[r] = Addr::Con(Constant::Usize(b0));
                self.p += 1;
            },
            &CutInstruction::Cut(r) =>
                cut_policy.cut(self, r),
        }
    }

    pub(super) fn reset(&mut self) {
        self.hb = 0;
        self.e = 0;
        self.b = 0;
        self.b0 = 0;
        self.s = 0;
        self.tr = 0;
        self.p = CodePtr::default();
        self.cp = CodePtr::default();
        self.num_of_args = 0;

        self.fail = false;
        self.trail.clear();
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.and_stack.clear();
        self.or_stack.clear();
        self.registers = vec![Addr::HeapCell(0); 64];
        self.block = 0;
        self.ball = (0, Vec::new());
    }
}
