use prolog::and_stack::*;
use prolog::ast::*;
use prolog::copier::*;
use prolog::heap_iter::*;
use prolog::heap_print::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_state::*;
use prolog::num::{Integer, Signed, ToPrimitive, Zero};
use prolog::num::bigint::{BigInt, BigUint};
use prolog::num::rational::Ratio;
use prolog::or_stack::*;
use prolog::string_list::StringList;

use std::cell::RefCell;
use std::cmp::{max, Ordering};
use std::collections::{HashMap, HashSet};
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
    pub(super) fn new() -> Self {
        MachineState {
            atom_tbl: Rc::new(RefCell::new(HashSet::new())),
            s: 0,
            p: CodePtr::default(),
            b: 0,
            b0: 0,
            e: 0,
            num_of_args: 0,
            cp: LocalCodePtr::default(),
            fail: false,
            heap: Heap::with_capacity(256),
            mode: MachineMode::Write,
            and_stack: AndStack::new(),
            or_stack: OrStack::new(),
            registers: vec![Addr::HeapCell(0); MAX_ARITY + 1], // self.registers[0] is never used.
            trail: Vec::new(),
            tr: 0,
            hb: 0,
            block: 0,
            ball: Ball::new(),
            interms: vec![Number::default(); 256],
            last_call: false,
            flags: MachineFlags::default()
        }
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.flags
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

    pub(super) fn bind(&mut self, r1: Ref, a2: Addr) {
        let t1 = self.store(r1.as_addr());
        let t2 = self.store(a2.clone());

        if t1.is_ref() && (!t2.is_ref() || a2 < r1) {
            match r1 {
                Ref::StackCell(fr, sc) =>
                    self.and_stack[fr][sc] = t2,
                Ref::HeapCell(h) =>
                    self.heap[h] = HeapCellValue::Addr(t2)
            };

            self.trail(r1);
        } else {
            match a2.as_var() {
                Some(Ref::StackCell(fr, sc)) => {
                    self.and_stack[fr][sc] = t1;
                    self.trail(Ref::StackCell(fr, sc));
                },
                Some(Ref::HeapCell(h)) => {
                    self.heap[h] = HeapCellValue::Addr(t1);
                    self.trail(Ref::HeapCell(h));
                },
                None => {}
            }
        }
    }

    pub(super)
    fn print_var_eq<Fmt, Outputter>(&self, var: Rc<Var>, addr: Addr, var_dir: &HeapVarDict,
                                    fmt: Fmt, mut output: Outputter)
                                    -> Outputter
      where Fmt: HCValueFormatter, Outputter: HCValueOutputter
    {
        let orig_len = output.len();

        output.begin_new_var();

        output.append(var.as_str());
        output.append(" = ");

        let printer    = HCPrinter::from_heap_locs(&self, fmt, output, var_dir);
        let mut output = printer.print(addr);

        if output.ends_with(var.as_str()) {
            output.truncate(orig_len);
        }

        output
    }

    pub(super)
    fn print_exception<Fmt, Outputter>(&self, addr: Addr, var_dir: &HeapVarDict,
                                       fmt: Fmt, output: Outputter)
                                       -> Outputter
      where Fmt: HCValueFormatter, Outputter: HCValueOutputter
    {
        let printer = HCPrinter::from_heap_locs(&self, fmt, output, var_dir);
        printer.print(addr)
    }

    pub(super)
    fn print_term<Fmt, Outputter>(&self, addr: Addr, fmt: Fmt, output: Outputter) -> Outputter
      where Fmt: HCValueFormatter, Outputter: HCValueOutputter
    {
        let printer = HCPrinter::new(&self, fmt, output);
        printer.print(addr)
    }

    pub(super) fn unify(&mut self, a1: Addr, a2: Addr) {
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
                    },
                    (Addr::Lis(a1), Addr::Con(Constant::String(ref mut s)))
                  | (Addr::Con(Constant::String(ref mut s)), Addr::Lis(a1))
                        if self.flags.double_quotes.is_chars() => {
                            if let Some(c) = s.head() {
                                pdl.push(Addr::Con(Constant::String(s.tail())));
                                pdl.push(Addr::HeapCell(a1 + 1));

                                pdl.push(Addr::Con(Constant::Char(c)));
                                pdl.push(Addr::HeapCell(a1));

                                continue;
                            } else if s.is_expandable() {
                                let mut stepper = |c| {
                                    let new_s = s.push_char(c);

                                    pdl.push(Addr::HeapCell(a1 + 1));
                                    pdl.push(Addr::Con(Constant::String(new_s)));
                                };

                                match self.heap[a1].clone() {
                                    HeapCellValue::Addr(Addr::Con(Constant::Char(c))) => {
                                        stepper(c);
                                        continue;
                                    },
                                    HeapCellValue::Addr(Addr::Con(Constant::Atom(ref a))) =>
                                        if let Some(c) = a.as_str().chars().next() {
                                            if c.len_utf8() == a.as_str().len() {
                                                stepper(c);
                                                continue;
                                            }
                                        },
                                    _ => {}
                                };
                            }

                            self.fail = true;
                        },
                    (Addr::Con(Constant::EmptyList), Addr::Con(Constant::String(ref s)))
                  | (Addr::Con(Constant::String(ref s)), Addr::Con(Constant::EmptyList))
                        if self.flags.double_quotes.is_chars() => {
                            if s.is_expandable() && s.is_empty() {
                                s.set_non_expandable();
                                continue;
                            }

                            self.fail = !s.is_empty();
                        },
                    (Addr::Lis(a1), Addr::Lis(a2)) => {
                        pdl.push(Addr::HeapCell(a1));
                        pdl.push(Addr::HeapCell(a2));

                        pdl.push(Addr::HeapCell(a1 + 1));
                        pdl.push(Addr::HeapCell(a2 + 1));
                    },
                    (Addr::Con(Constant::String(ref mut s1)), Addr::Con(Constant::String(ref mut s2))) => {
                        let mut stepper = |s1: &mut StringList, s2: &mut StringList| -> bool {
                            if let Some(c1) = s1.head() {
                                if let Some(c2) = s2.head() {
                                    if c1 == c2 {
                                        pdl.push(Addr::Con(Constant::String(s1.tail())));
                                        pdl.push(Addr::Con(Constant::String(s2.tail())));

                                        return true;
                                    }
                                } else if s2.is_expandable() {                                
                                    pdl.push(Addr::Con(Constant::String(s2.push_char(c1))));
                                    pdl.push(Addr::Con(Constant::String(s1.tail())));

                                    return true;
                                }
                            } else if s1.is_expandable() {
                                if let Some(c) = s2.head() {
                                    pdl.push(Addr::Con(Constant::String(s1.push_char(c))));
                                    pdl.push(Addr::Con(Constant::String(s2.tail())));
                                } else if !s2.is_expandable() {
                                    s1.set_non_expandable();
                                }/*else {
                                 //TODO: unify the tails of s1 and s2? I guess?
                                }*/
                                
                                return true;
                            } else if s2.head().is_none() {
                                s2.set_non_expandable();
                                return true;
                            }

                            false
                        };

                        self.fail = !(stepper(s1, s2) || stepper(s2, s1));
                    },
                    (Addr::Con(ref c1), Addr::Con(ref c2)) =>
                        if c1 != c2 {
                            self.fail = true;
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

    pub(super) fn unwind_trail(&mut self, a1: usize, a2: usize) {
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
                        self.tr -= 1;
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
                        self.tr -= 1;
                    }
                }
            };
        }
    }

    pub(super) fn write_constant_to_var(&mut self, addr: Addr, c: Constant) {
        match self.store(self.deref(addr)) {
            Addr::HeapCell(hc) => {
                self.heap[hc] = HeapCellValue::Addr(Addr::Con(c.clone()));
                self.trail(Ref::HeapCell(hc));
            },
            Addr::StackCell(fr, sc) => {
                self.and_stack[fr][sc] = Addr::Con(c.clone());
                self.trail(Ref::StackCell(fr, sc));
            },
            Addr::Con(Constant::String(ref mut s)) =>
                self.fail = match c {
                    Constant::EmptyList if self.flags.double_quotes.is_chars() =>
                        !s.is_empty(),
                    Constant::String(ref s2) if s.is_empty() && s.is_expandable() => {
                        s.append(s2);
                        false
                    },
                    Constant::String(s2) => *s != s2,
                    _ => true
                },
            Addr::Con(c1) => {
                if c1 != c {
                    self.fail = true;
                }
            },
            _ => self.fail = true
        };
    }

    pub(super) fn get_number(&self, at: &ArithmeticTerm) -> Result<Number, MachineStub> {
        match at {
            &ArithmeticTerm::Reg(r)        => self.arith_eval_by_metacall(r),
            &ArithmeticTerm::Interm(i)     => Ok(self.interms[i-1].clone()),
            &ArithmeticTerm::Number(ref n) => Ok(n.clone()),
        }
    }

    fn get_rational(&self, at: &ArithmeticTerm, caller: &MachineStub)
                    -> Result<Rc<Ratio<BigInt>>, MachineStub>
    {
        let n = self.get_number(at)?;

        match n {
            Number::Rational(r) => Ok(r),
            Number::Float(fl) =>
                if let Some(r) = Ratio::from_float(fl.into_inner()) {
                    Ok(Rc::new(r))
                } else {
                    Err(self.error_form(MachineError::instantiation_error(), caller.clone()))
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

    pub(super) fn arith_eval_by_metacall(&self, r: RegType) -> Result<Number, MachineStub>
    {
        let a = self[r].clone();

        let caller = MachineError::functor_stub(clause_name!("(is)"), 2);
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
                        "/" => interms.push(self.div(a1, a2)?),
                        "^" => interms.push(self.pow(a1, a2)?),
                        "rdiv" => {
                            let r1 = self.get_rational(&ArithmeticTerm::Number(a1), &caller)?;
                            let r2 = self.get_rational(&ArithmeticTerm::Number(a2), &caller)?;

                            let result = Number::Rational(self.rdiv(r1, r2)?);
                            interms.push(result)
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
                        _     => return Err(self.error_form(MachineError::instantiation_error(),
                                                            caller))
                    }
                },
                HeapCellValue::NamedStr(1, name, Some(Fixity::Pre)) => {
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "-" => interms.push(- a1),
                        _   => return Err(self.error_form(MachineError::instantiation_error(),
                                                          caller))
                    }
                },
                HeapCellValue::Addr(Addr::Con(Constant::Number(n))) =>
                    interms.push(n),
                _ =>
                    return Err(self.error_form(MachineError::instantiation_error(), caller))
            }
        };

        Ok(interms.pop().unwrap())
    }

    fn rdiv(&self, r1: Rc<Ratio<BigInt>>, r2: Rc<Ratio<BigInt>>)
            -> Result<Rc<Ratio<BigInt>>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);

        if *r2 == Ratio::zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            Ok(Rc::new(&*r1 / &*r2))
        }
    }

    fn fidiv(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(div)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Rc::new(n1.div_floor(&n2)))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn idiv(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Rc::new(&*n1 / &*n2))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn div(&self, n1: Number, n2: Number) -> Result<Number, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(/)"), 2);

        if n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            Ok(n1 / n2)
        }
    }

    fn pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub>
    {
        match n1.pow(n2) {
            Ok(result) => Ok(result),
            Err(_) => {
                let stub = MachineError::functor_stub(clause_name!("^"), 2);
                Err(self.error_form(MachineError::evaluation_error(EvalError::NoRoots),
                                    stub))
            }
        }
    }

    fn shr(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(>>)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                match n2.to_usize() {
                    Some(n2) => Ok(Rc::new(&*n1 >> n2)),
                    _        => Ok(Rc::new(&*n1 >> usize::max_value()))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn shl(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(<<)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                match n2.to_usize() {
                    Some(n2) => Ok(Rc::new(&*n1 << n2)),
                    _        => Ok(Rc::new(&*n1 << usize::max_value()))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn xor(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(xor)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 ^ u_n2)),
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn and(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(/\\)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 & u_n2)),
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                    Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn modulus(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(mod)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor),
                                        stub))
                } else {
                    Ok(Rc::new(n1.mod_floor(&n2)))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn remainder(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(rem)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                if *n2 == BigInt::zero() {
                    Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor),
                                        stub))
                } else {
                    Ok(Rc::new(&*n1 % &*n2))
                },
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n1))),
                                    stub))
        }
    }

    fn or(&self, n1: Number, n2: Number) -> Result<Rc<BigInt>, MachineStub>
    {
        let stub = MachineError::functor_stub(clause_name!("(\\/)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                Ok(self.signed_bitwise_op(&*n1, &*n2, |u_n1, u_n2| u_n1 & u_n2)),
            (Number::Integer(_), n2) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n2))),
                                    stub)),
            (n1, _) =>
                Err(self.error_form(MachineError::type_error(ValidType::Integer,
                                                             Addr::Con(Constant::Number(n1))),
                                    stub))
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
            &ArithmeticInstruction::Pow(ref a1, ref a2, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));
                let n2 = try_or_fail!(self, self.get_number(a2));

                self.interms[t - 1] = try_or_fail!(self, self.pow(n1, n2));
                self.p += 1;
            },
            &ArithmeticInstruction::RDiv(ref a1, ref a2, t) => {
                let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);

                let r1 = try_or_fail!(self, self.get_rational(a1, &stub));
                let r2 = try_or_fail!(self, self.get_rational(a2, &stub));

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
            &ArithmeticInstruction::Abs(ref a1, t) => {
                let n1 = try_or_fail!(self, self.get_number(a1));

                self.interms[t - 1] = n1.abs();
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
                let addr = self.store(self.deref(self[reg].clone()));

                match addr {
                    Addr::Con(Constant::String(ref s))
                        if self.flags.double_quotes.is_chars() => {
                            let h = self.heap.h;

                            if let Some(c) = s.head() {
                                self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::Char(c))));
                                self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::String(s.tail()))));

                                self.s = h;
                                self.mode = MachineMode::Read;
                            } else if s.is_expandable() {
                                self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::String(s.clone()))));

                                self.s = h;
                                self.mode = MachineMode::Read;
                            } else {
                                self.fail = true;
                            }
                        },
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
                    },
                    Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                        let h = self.heap.h;

                        self.heap.push(HeapCellValue::Addr(Addr::Str(h + 1)));
                        self.heap.push(HeapCellValue::NamedStr(arity, ct.name(), ct.fixity()));

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
                    Addr::Con(Constant::String(_)) if self.flags.double_quotes.is_chars() => l,
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
            &QueryInstruction::PutStructure(ref ct, arity, reg) => {
                let h = self.heap.h;

                self.heap.push(HeapCellValue::NamedStr(arity, ct.name(), ct.fixity()));
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

    pub(super) fn handle_internal_call_n(&mut self, arity: usize)
    {
        let arity = arity + 1;
        let pred  = self.registers[1].clone();

        for i in 2 .. arity {
            self.registers[i-1] = self.registers[i].clone();
        }

        if arity > 1 {
            self.registers[arity - 1] = pred;
            return;
        }

        self.fail = true;
    }

    pub(super) fn set_ball(&mut self) {
        let addr = self[temp_v!(1)].clone();
        self.ball.boundary = self.heap.h;

        let mut duplicator = DuplicateBallTerm::new(self);
        duplicator.duplicate_term(addr);
    }

    pub(super) fn setup_call_n(&mut self, arity: usize) -> Option<PredicateKey>
    {
        let stub = MachineError::functor_stub(clause_name!("call"), arity + 1);
        let addr = self.store(self.deref(self.registers[arity].clone()));

        let (name, narity) = match addr {
            Addr::Str(a) => {
                let result = self.heap[a].clone();

                if let HeapCellValue::NamedStr(narity, name, _) = result {
                    if narity + arity > 63 {
                        let representation_error =
                            self.error_form(MachineError::representation_error(RepFlag::MaxArity), stub);

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
            },
            Addr::Con(Constant::Atom(name)) => (name, 0),
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let instantiation_error = self.error_form(MachineError::instantiation_error(), stub);
                self.throw_exception(instantiation_error);

                return None;
            },
            _ => {
                let type_error = self.error_form(MachineError::type_error(ValidType::Callable, addr), stub);
                self.throw_exception(type_error);

                return None;
            }
        };

        Some((name, arity + narity - 1))
    }

    pub(super) fn unwind_stack(&mut self) {
        self.b = self.block;
        self.or_stack.truncate(self.b);

        self.fail = true;
    }

    fn heap_ball_boundary_diff(&self) -> usize {
        if self.ball.boundary > self.heap.h {
            self.ball.boundary - self.heap.h
        } else {
            self.heap.h - self.ball.boundary
        }
    }

    pub(super) fn copy_and_align_ball_to_heap(&mut self) -> usize {
        let diff = self.heap_ball_boundary_diff();

        for heap_value in self.ball.stub.iter().cloned() {
            self.heap.push(match heap_value {
                HeapCellValue::Addr(addr) => HeapCellValue::Addr(addr - diff),
                _ => heap_value
            });
        }

        diff
    }

    pub(crate) fn is_cyclic_term(&self, addr: Addr) -> bool {
        let mut seen = HashSet::new();
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
    pub(super) fn try_arg(&mut self) -> CallResult
    {
        let stub = MachineError::functor_stub(clause_name!("arg"), 3);
        let n = self.store(self.deref(self[temp_v!(1)].clone()));

        match n {
            Addr::HeapCell(_) | Addr::StackCell(..) => // 8.5.2.3 a)
                return Err(self.error_form(MachineError::instantiation_error(), stub)),
            Addr::Con(Constant::Number(Number::Integer(n))) => {
                if n.is_negative() {
                    // 8.5.2.3 e)
                    let n = Addr::Con(Constant::Number(Number::Integer(n)));
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
                    Addr::HeapCell(_) | Addr::StackCell(..) => // 8.5.2.3 b)
                        return Err(self.error_form(MachineError::instantiation_error(), stub)),
                    Addr::Str(o) =>
                        match self.heap[o].clone() {
                            HeapCellValue::NamedStr(arity, _, _) if 1 <= n && n <= arity => {
                                let a3  = self[temp_v!(3)].clone();
                                let h_a = Addr::HeapCell(o + n);

                                self.unify(a3, h_a);
                            },
                            _ => self.fail = true
                        },
                    Addr::Lis(l) =>
                        if n == 1 || n == 2 {
                            let a3  = self[temp_v!(3)].clone();
                            let h_a = Addr::HeapCell(l + n - 1);

                            self.unify(a3, h_a);
                        } else {
                            self.fail = true;
                        },
                    _ => // 8.5.2.3 d)
                        return Err(self.error_form(MachineError::type_error(ValidType::Compound, term),
                                                   stub))
                }


            },
            _ => // 8.5.2.3 c)
                return Err(self.error_form(MachineError::type_error(ValidType::Integer, n), stub))
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
            _ => true
        };

        self.p += 1;
    }

    pub(super) fn compare_term(&mut self, qt: CompareTermQT) {
        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        match self.compare_term_test(&a1, &a2) {
            Ordering::Greater =>
                match qt {
                    CompareTermQT::GreaterThan | CompareTermQT::GreaterThanOrEqual => return,
                    _ => self.fail = true
                },
            Ordering::Equal =>
                match qt {
                    CompareTermQT::GreaterThanOrEqual | CompareTermQT::LessThanOrEqual => return,
                    _ => self.fail = true
                },
            Ordering::Less =>
                match qt {
                    CompareTermQT::LessThan | CompareTermQT::LessThanOrEqual => return,
                    _ => self.fail = true
                }
        };
    }

    // returns true on failure.
    pub(super) fn eq_test(&self) -> bool
    {
        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        let iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        for (v1, v2) in iter {
            match (v1, v2) {
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) =>
                    if ar1 != ar2 || n1 != n2 {
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
    
    pub(super) fn compare_term_test(&self, a1: &Addr, a2: &Addr) -> Ordering {
        let iter = self.zipped_acyclic_pre_order_iter(a1.clone(), a2.clone());

        for (v1, v2) in iter {
            match (v1, v2) {
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Con(Constant::String(_))))
              | (HeapCellValue::Addr(Addr::Con(Constant::String(_))), HeapCellValue::Addr(Addr::Lis(_)))
                    if self.flags.double_quotes.is_chars() => {},
                (HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                 HeapCellValue::Addr(Addr::Con(Constant::String(ref s))))
                    if self.flags.double_quotes.is_chars() => if s.is_empty() {
                        return Ordering::Equal;
                    } else {
                        return Ordering::Greater;
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(atom))),
                 HeapCellValue::Addr(Addr::Con(Constant::Char(c)))) =>
                    return if atom.as_str().chars().count() == 1 {
                        atom.as_str().chars().next().cmp(&Some(c))
                    } else {
                        Ordering::Greater
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::Char(c))),
                 HeapCellValue::Addr(Addr::Con(Constant::Atom(atom)))) =>
                    return if atom.as_str().chars().count() == 1 {
                        Some(c).cmp(&atom.as_str().chars().next())
                    } else {
                        Ordering::Less
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::String(ref s))),
                 HeapCellValue::Addr(Addr::Con(Constant::EmptyList)))
                    if self.flags.double_quotes.is_chars() => if s.is_empty() {
                        return Ordering::Equal;
                    } else {
                        return Ordering::Less;
                    },
                (HeapCellValue::Addr(Addr::HeapCell(hc1)),
                 HeapCellValue::Addr(Addr::HeapCell(hc2))) =>
                    if hc1 != hc2 {
                        return hc1.cmp(&hc2);
                    },
                (HeapCellValue::Addr(Addr::HeapCell(_)), _) =>
                    return Ordering::Less,
                (HeapCellValue::Addr(Addr::StackCell(fr1, sc1)),
                 HeapCellValue::Addr(Addr::StackCell(fr2, sc2))) =>
                    if fr1 > fr2 {
                        return Ordering::Greater;
                    } else if fr1 < fr2 || sc1 < sc2 {
                        return Ordering::Less;
                    } else if sc1 > sc2 {
                        return Ordering::Greater;
                    },
                (HeapCellValue::Addr(Addr::StackCell(..)),
                 HeapCellValue::Addr(Addr::HeapCell(_))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::StackCell(..)), _) =>
                    return Ordering::Less,
                (HeapCellValue::Addr(Addr::Con(Constant::Number(..))),
                 HeapCellValue::Addr(Addr::HeapCell(_))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Number(..))),
                 HeapCellValue::Addr(Addr::StackCell(..))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Number(n1))),
                 HeapCellValue::Addr(Addr::Con(Constant::Number(n2)))) =>
                    if n1 != n2 {
                        return n1.cmp(&n2);
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::Number(_))), _) =>
                    return Ordering::Less,
                (HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                 HeapCellValue::Addr(Addr::HeapCell(_))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::String(..))),
                 HeapCellValue::Addr(Addr::StackCell(..))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::String(_))),
                 HeapCellValue::Addr(Addr::Con(Constant::Number(_)))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::String(s1))),
                 HeapCellValue::Addr(Addr::Con(Constant::String(s2)))) =>                    
                    return s1.cmp(&s2),
                (HeapCellValue::Addr(Addr::Con(Constant::String(_))), _) =>
                    return Ordering::Less,
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                 HeapCellValue::Addr(Addr::HeapCell(_))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(..))),
                 HeapCellValue::Addr(Addr::StackCell(..))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(_))),
                 HeapCellValue::Addr(Addr::Con(Constant::Number(_)))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(_))),
                 HeapCellValue::Addr(Addr::Con(Constant::String(_)))) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(s1))),
                 HeapCellValue::Addr(Addr::Con(Constant::Atom(s2)))) =>
                    if s1 != s2 {
                        return s1.cmp(&s2);
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::Atom(_))), _) =>
                    return Ordering::Less,
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) =>
                    if ar1 < ar2 {
                        return Ordering::Less;
                    } else if ar1 > ar2 {
                        return Ordering::Greater;
                    } else if n1 != n2 {
                        return n1.cmp(&n2);
                    },
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) =>
                    continue,
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::NamedStr(ar, n, _))
              | (HeapCellValue::NamedStr(ar, n, _), HeapCellValue::Addr(Addr::Lis(_))) =>
                    if ar == 2 && n.as_str() == "." {
                        continue;
                    } else if ar < 2 {
                        return Ordering::Greater;
                    } else if ar > 2 {
                        return Ordering::Less;
                    } else {
                        return n.as_str().cmp(".");
                    },
                (HeapCellValue::NamedStr(..), _) =>
                    return Ordering::Greater,
                (HeapCellValue::Addr(Addr::Lis(_)), _) =>
                    return Ordering::Greater,
                _ => {}
            }
        };

        Ordering::Equal
    }

    pub(super) fn reset_block(&mut self, addr: Addr) {
        match self.store(addr) {
            Addr::Con(Constant::Usize(b)) => self.block = b,
            _ => self.fail = true
        };
    }

    pub(super) fn execute_inlined(&mut self, inlined: &InlinedClauseType) {
        match inlined {
            &InlinedClauseType::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self, self.get_number(at_1));
                let n2 = try_or_fail!(self, self.get_number(at_2));

                self.compare_numbers(cmp, n1, n2);
            },
            &InlinedClauseType::IsAtom(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Atom(_)) | Addr::Con(Constant::Char(_)) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsAtomic(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsInteger(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Integer(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsCompound(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Str(_) | Addr::Lis(_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsFloat(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Float(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsRational(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::Number(Number::Rational(_))) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsString(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::String(_)) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsNonVar(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::HeapCell(_) | Addr::StackCell(..) => self.fail = true,
                    _ => self.p += 1
                };
            },
            &InlinedClauseType::IsVar(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::HeapCell(_) | Addr::StackCell(_,_) => self.p += 1,
                    _ => self.fail = true
                };
            },
            &InlinedClauseType::IsPartialString(r1) => {
                let d = self.store(self.deref(self[r1].clone()));

                match d {
                    Addr::Con(Constant::String(ref s)) if s.is_expandable() => self.p += 1,
                    _ => self.fail = true
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

    fn try_functor_compound_case(&mut self, name: ClauseName, arity: usize) {
        let name  = Addr::Con(Constant::Atom(name));
        let arity = Addr::Con(integer!(arity));

        self.try_functor_unify_components(name, arity);
    }

    pub(super) fn try_functor(&mut self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("functor"), 3);
        let a1 = self.store(self.deref(self[temp_v!(1)].clone()));

        match a1.clone() {
            Addr::Con(_) =>
                self.try_functor_unify_components(a1, Addr::Con(integer!(0))),
            Addr::Str(o) =>
                match self.heap[o].clone() {
                    HeapCellValue::NamedStr(arity, name, _) =>
                        self.try_functor_compound_case(name, arity),
                    _ => self.fail = true
                },
            Addr::Lis(_) =>
                self.try_functor_compound_case(clause_name!("."), 2),
            Addr::HeapCell(_) | Addr::StackCell(_, _) => {
                let name  = self.store(self.deref(self[temp_v!(2)].clone()));
                let arity = self.store(self.deref(self[temp_v!(3)].clone()));

                if name.is_ref() || arity.is_ref() { // 8.5.1.3 a) & 8.5.1.3 b)
                    return Err(self.error_form(MachineError::instantiation_error(), stub));
                }

                if let Addr::Con(Constant::Number(Number::Integer(arity))) = arity {
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
                        let dom_err = MachineError::domain_error(DomainError::NotLessThanZero,
                                                                 Addr::Con(integer!(arity)));
                        return Err(self.error_form(dom_err, stub));
                    }

                    match name {
                        Addr::Con(_) if arity == 0 =>
                            self.unify(a1, name),
                        Addr::Con(Constant::Atom(name)) => {
                            let f_a = if name.as_str() == "." && arity == 2 {
                                Addr::Lis(self.heap.h)
                            } else {
                                let h = self.heap.h;
                                self.heap.push(HeapCellValue::NamedStr(arity as usize, name, None));
                                Addr::Str(h)
                            };

                            for _ in 0 .. arity {
                                let h = self.heap.h;
                                self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
                            }

                            self.unify(a1, f_a);
                        },
                        Addr::Con(_) =>
                            return Err(self.error_form(MachineError::type_error(ValidType::Atom, name),
                                                       stub)), // 8.5.1.3 e)
                        _ =>
                            return Err(self.error_form(MachineError::type_error(ValidType::Atomic, name),
                                                       stub))  // 8.5.1.3 c)
                    };
                } else if !arity.is_ref() {
                    // 8.5.1.3 d)
                    return Err(self.error_form(MachineError::type_error(ValidType::Integer, arity), stub));
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

    pub(super) fn to_list<Iter: Iterator<Item=Addr>>(&mut self, values: Iter) -> usize {
        let head_addr = self.heap.h;

        for value in values {
            let h = self.heap.h;

            self.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));
            self.heap.push(HeapCellValue::Addr(value));
        }

        self.heap.push(HeapCellValue::Addr(Addr::Con(Constant::EmptyList)));
        head_addr
    }

    pub(super) fn try_from_list(&self, r: RegType, caller: MachineStub)
                                -> Result<Vec<Addr>, MachineStub>
    {
        let a1 = self.store(self.deref(self[r].clone()));

        match a1.clone() {
            Addr::Lis(mut l) => {
                let mut result = Vec::new();

                result.push(self.heap[l].as_addr(l));
                l += 1;

                loop {
                    match self.heap[l].clone() {
                        HeapCellValue::Addr(addr) =>
                            match self.store(self.deref(addr)) {
                                Addr::Lis(hcp) => {
                                    result.push(self.heap[hcp].as_addr(hcp));
                                    l = hcp + 1;
                                },
                                Addr::Con(Constant::EmptyList) =>
                                    break,
                                Addr::HeapCell(_) | Addr::StackCell(..) =>
                                    return Err(self.error_form(MachineError::instantiation_error(), caller)),
                                _ =>
                                    return Err(self.error_form(MachineError::type_error(ValidType::List, a1),
                                                               caller))
                            },
                        _ =>
                            return Err(self.error_form(MachineError::type_error(ValidType::List, a1),
                                                       caller))
                    };
                }

                Ok(result)
            },
            Addr::HeapCell(_) | Addr::StackCell(..) =>
                Err(self.error_form(MachineError::instantiation_error(), caller)),
            Addr::Con(Constant::EmptyList) =>
                Ok(vec![]),
            _ =>
                Err(self.error_form(MachineError::type_error(ValidType::List, a1), caller))
        }
    }

    // see 8.4.4.3 of Draft Technical Corrigendum 2 for an error guide.
    pub(super) fn project_onto_key(&self, a: Addr) -> Result<Addr, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.store(self.deref(a)) {
            Addr::HeapCell(_) | Addr::StackCell(..) =>
                Err(self.error_form(MachineError::instantiation_error(), stub)),
            Addr::Str(s) =>
                match self.heap[s].clone() {
                    HeapCellValue::NamedStr(2, ref name, Some(Fixity::In))
                        if *name == clause_name!("-") =>
                           Ok(Addr::HeapCell(s+1)),
                    _ => Err(self.error_form(MachineError::type_error(ValidType::Pair,
                                                             self.heap[s].as_addr(s)),
                                             stub))
                },
            a => Err(self.error_form(MachineError::type_error(ValidType::Pair, a), stub))
        }
    }

    pub(super) fn duplicate_term(&mut self) {
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
    pub(super) fn structural_eq_test(&self) -> bool
    {
        let a1 = self[temp_v!(1)].clone();
        let a2 = self[temp_v!(2)].clone();

        let mut var_pairs = HashMap::new();

        let iter = self.zipped_acyclic_pre_order_iter(a1, a2);

        for (v1, v2) in iter {
            match (v1, v2) {
                (HeapCellValue::Addr(Addr::Lis(l)), HeapCellValue::Addr(Addr::Con(Constant::String(ref s))))
              | (HeapCellValue::Addr(Addr::Con(Constant::String(ref s))), HeapCellValue::Addr(Addr::Lis(l)))
                    if self.flags.double_quotes.is_chars() => if s.is_empty() {
                        return true;
                    } else {
                        if let HeapCellValue::Addr(Addr::Con(constant)) = self.heap[l].clone() {
                            if let Some(c) = s.head() {
                                // checks equality on atoms, too.
                                if constant == Constant::Char(c) {
                                    continue;
                                }
                            }
                        }

                        return true;
                    },
               (HeapCellValue::Addr(Addr::Con(Constant::String(ref s1))),
                HeapCellValue::Addr(Addr::Con(Constant::String(ref s2)))) =>
                    match s1.head() {
                        Some(c1) => if let Some(c2) = s2.head() {
                            if c1 != c2 {
                                return true;
                            }
                        } else {
                            return true;
                        },
                        None => return !s2.is_empty()
                    },
                (HeapCellValue::Addr(Addr::Con(Constant::String(ref s))),
                 HeapCellValue::Addr(Addr::Con(Constant::EmptyList)))
              | (HeapCellValue::Addr(Addr::Con(Constant::EmptyList)),
                 HeapCellValue::Addr(Addr::Con(Constant::String(ref s))))
                    if self.flags.double_quotes.is_chars() => if !s.is_empty() {
                        return true;
                    },
                (HeapCellValue::NamedStr(ar1, n1, _), HeapCellValue::NamedStr(ar2, n2, _)) =>
                    if ar1 != ar2 || n1 != n2 {
                        return true;
                    },
                (HeapCellValue::Addr(Addr::Lis(_)), HeapCellValue::Addr(Addr::Lis(_))) =>
                    continue,
                (HeapCellValue::Addr(v1 @ Addr::HeapCell(_)), HeapCellValue::Addr(v2 @ Addr::HeapCell(_)))
              | (HeapCellValue::Addr(v1 @ Addr::HeapCell(_)), HeapCellValue::Addr(v2 @ Addr::StackCell(..)))
              | (HeapCellValue::Addr(v1 @ Addr::StackCell(..)), HeapCellValue::Addr(v2 @ Addr::StackCell(..)))
              | (HeapCellValue::Addr(v1 @ Addr::StackCell(..)), HeapCellValue::Addr(v2 @ Addr::HeapCell(_))) =>
                    match (var_pairs.get(&v1).cloned(), var_pairs.get(&v2).cloned()) {
                        (Some(ref v2_p), Some(ref v1_p)) if *v1_p == v1 && *v2_p == v2 =>
                            continue,
                        (Some(_), _) | (_, Some(_)) =>
                            return true,
                        (None, None) => {
                            var_pairs.insert(v1.clone(), v2.clone());
                            var_pairs.insert(v2, v1);
                        }
                    },
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
    pub(super) fn ground_test(&self) -> bool
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

    pub(super) fn setup_built_in_call(&mut self, ct: BuiltInClauseType)
    {
        self.num_of_args = ct.arity();
        self.b0 = self.b;

        self.p = CodePtr::BuiltInClause(ct, self.p.local());
    }

    pub(super) fn allocate(&mut self, num_cells: usize) {
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
                self.and_stack[index].cp = self.cp.clone();
                self.and_stack[index].global_index = gi;

                self.and_stack.resize(index, num_cells);
                self.e = index;

                return;
            }
        }

        self.and_stack.push(gi, self.e, self.cp.clone(), num_cells);
        self.e = self.and_stack.len() - 1;
    }

    fn deallocate(&mut self) {
        let e = self.e;

        self.cp = self.and_stack[e].cp.clone();
        self.e  = self.and_stack[e].e;

        self.p += 1;
    }

    fn handle_call_clause<'a>(&mut self, code_dirs: CodeDirs<'a>,
                              call_policy: &mut Box<CallPolicy>,
                              cut_policy:  &mut Box<CutPolicy>,
                              ct: &ClauseType,
                              arity: usize,
                              lco: bool,
                              use_default_cp: bool)
    {
        let mut default_call_policy: Box<CallPolicy> = Box::new(DefaultCallPolicy {});
        let call_policy = if use_default_cp {
            &mut default_call_policy
        } else {
            call_policy
        };

        self.last_call = lco;

        match ct {
            &ClauseType::BuiltIn(ref ct) =>
                try_or_fail!(self, call_policy.call_builtin(self, ct, code_dirs)),
            &ClauseType::CallN =>
                try_or_fail!(self, call_policy.call_n(self, arity, code_dirs)),
            &ClauseType::Inlined(ref ct) =>
                self.execute_inlined(ct),
            &ClauseType::Named(ref name, ref idx) | &ClauseType::Op(ref name, _, ref idx) =>
                try_or_fail!(self, call_policy.context_call(self, name.clone(), arity, idx.clone(),
                                                            code_dirs)),
            &ClauseType::System(ref ct) =>
                try_or_fail!(self, self.system_call(ct, code_dirs, call_policy, cut_policy))
        };
    }

    pub(super) fn execute_ctrl_instr<'a>(&mut self, code_dirs: CodeDirs<'a>,
                                         call_policy: &mut Box<CallPolicy>,
                                         cut_policy:  &mut Box<CutPolicy>,
                                         instr: &ControlInstruction)
    {
        match instr {
            &ControlInstruction::Allocate(num_cells) =>
                self.allocate(num_cells),
            &ControlInstruction::CallClause(ref ct, arity, _, lco, use_default_cp) =>
                self.handle_call_clause(code_dirs, call_policy, cut_policy, ct, arity, lco,
                                        use_default_cp),
            &ControlInstruction::Deallocate => self.deallocate(),
            &ControlInstruction::JmpBy(arity, offset, _, lco) => {
                if !lco {
                    self.cp.assign_if_local(self.p.clone() + 1);
                }

                self.num_of_args = arity;
                self.b0 = self.b;
                self.p += offset;
            },
            &ControlInstruction::Proceed =>
                self.p = CodePtr::Local(self.cp.clone())
        };
    }

    pub(super) fn execute_indexed_choice_instr(&mut self, instr: &IndexedChoiceInstruction,
                                               call_policy: &mut Box<CallPolicy>)
    {
        match instr {
            &IndexedChoiceInstruction::Try(l) => {
                let n = self.num_of_args;
                let gi = self.next_global_index();

                self.or_stack.push(gi,
                                   self.e,
                                   self.cp.clone(),
                                   self.b,
                                   self.p.clone() + 1,
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
            &IndexedChoiceInstruction::Retry(l) =>
                try_or_fail!(self, call_policy.retry(self, l)),
            &IndexedChoiceInstruction::Trust(l) =>
                try_or_fail!(self, call_policy.trust(self, l))
        };
    }

    pub(super) fn execute_choice_instr(&mut self, instr: &ChoiceInstruction,
                                       call_policy: &mut Box<CallPolicy>)
    {
        match instr {
            &ChoiceInstruction::TryMeElse(offset) => {
                let n = self.num_of_args;
                let gi = self.next_global_index();

                self.or_stack.push(gi,
                                   self.e,
                                   self.cp.clone(),
                                   self.b,
                                   self.p.clone() + offset,
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
            &ChoiceInstruction::DefaultRetryMeElse(offset) => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(self, call_policy.retry_me_else(self, offset))
            },
            &ChoiceInstruction::DefaultTrustMe => {
                let mut call_policy = DefaultCallPolicy {};
                try_or_fail!(self, call_policy.trust_me(self))
            },
            &ChoiceInstruction::RetryMeElse(offset) =>
                try_or_fail!(self, call_policy.retry_me_else(self, offset)),
            &ChoiceInstruction::TrustMe =>
                try_or_fail!(self, call_policy.trust_me(self))
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
            &CutInstruction::GetLevelAndUnify(r) => {
                // let b0 = Addr::Con(Constant::Usize(self.b0));
                let b0 = self[perm_v!(1)].clone();
                let a  = self[r].clone();

                self.unify(a, b0);
                self.p += 1;
            },
            &CutInstruction::Cut(r) => if !cut_policy.cut(self, r) {
                self.p += 1;
            }
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
        self.cp = LocalCodePtr::default();
        self.num_of_args = 0;

        self.fail = false;
        self.trail.clear();
        self.heap.clear();
        self.mode = MachineMode::Write;
        self.and_stack.clear();
        self.or_stack.clear();
        self.registers = vec![Addr::HeapCell(0); 64];
        self.block = 0;

        self.ball.reset();
    }
}
