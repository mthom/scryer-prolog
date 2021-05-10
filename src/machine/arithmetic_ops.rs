use divrem::*;

use prolog_parser::ast::*;
use prolog_parser::clause_name;

use crate::arithmetic::*;
use crate::clause_types::*;
use crate::forms::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::rug::{Integer, Rational};
use ordered_float::*;

use std::cmp;
use std::convert::TryFrom;
use std::f64;
use std::mem;
use std::rc::Rc;

#[macro_export]
macro_rules! try_numeric_result {
    ($s: ident, $e: expr, $caller: expr) => {
        match $e {
            Ok(val) => Ok(val),
            Err(e) => {
                let caller_copy = $caller.iter().map(|v| v.context_free_clone()).collect();

                Err($s.error_form(MachineError::evaluation_error(e), caller_copy))
            }
        }
    };
}

fn isize_gcd(n1: isize, n2: isize) -> Option<isize> {
    if n1 == 0 {
        return n2.checked_abs().map(|n| n as isize);
    }

    if n2 == 0 {
        return n1.checked_abs().map(|n| n as isize);
    }

    let n1 = n1.checked_abs();
    let n2 = n2.checked_abs();

    let mut n1 = if let Some(n1) = n1 { n1 } else { return None };
    let mut n2 = if let Some(n2) = n2 { n2 } else { return None };

    let mut shift = 0;

    while ((n1 | n2) & 1) == 0 {
        shift += 1;
        n1 >>= 1;
        n2 >>= 1;
    }

    while (n1 & 1) == 0 {
        n1 >>= 1;
    }

    loop {
        while (n2 & 1) == 0 {
            n2 >>= 1;
        }

        if n1 > n2 {
            let t = n2;
            n2 = n1;
            n1 = t;
        }

        n2 -= n1;

        if n2 == 0 {
            break;
        }
    }

    Some(n1 << shift as isize)
}

impl MachineState {
    pub(crate) fn get_number(&mut self, at: &ArithmeticTerm) -> Result<Number, MachineStub> {
        match at {
            &ArithmeticTerm::Reg(r) => self.arith_eval_by_metacall(r),
            &ArithmeticTerm::Interm(i) => {
                Ok(mem::replace(&mut self.interms[i - 1], Number::Fixnum(0)))
            }
            &ArithmeticTerm::Number(ref n) => Ok(n.clone()),
        }
    }

    pub(super) fn rational_from_number(&self, n: Number) -> Result<Rc<Rational>, MachineError> {
        match n {
            Number::Fixnum(n) => Ok(Rc::new(Rational::from(n))),
            Number::Rational(r) => Ok(r),
            Number::Float(OrderedFloat(f)) => match Rational::from_f64(f) {
                Some(r) => Ok(Rc::new(r)),
                None => Err(MachineError::instantiation_error()),
            },
            Number::Integer(n) => Ok(Rc::new(Rational::from(&*n))),
        }
    }

    pub(crate) fn get_rational(
        &mut self,
        at: &ArithmeticTerm,
        caller: MachineStub,
    ) -> Result<(Rc<Rational>, MachineStub), MachineStub> {
        let n = self.get_number(at)?;

        match self.rational_from_number(n) {
            Ok(r) => Ok((r, caller)),
            Err(e) => Err(self.error_form(e, caller)),
        }
    }

    pub(crate) fn arith_eval_by_metacall(&self, r: RegType) -> Result<Number, MachineStub> {
        let caller = MachineError::functor_stub(clause_name!("is"), 2);
        let mut interms: Vec<Number> = Vec::with_capacity(64);

        for addr in self.post_order_iter(self[r]) {
            match self.heap.index_addr(&addr).as_ref() {
                &HeapCellValue::NamedStr(2, ref name, _) => {
                    let a2 = interms.pop().unwrap();
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "+" => interms.push(try_numeric_result!(self, a1 + a2, caller)?),
                        "-" => interms.push(try_numeric_result!(self, a1 - a2, caller)?),
                        "*" => interms.push(try_numeric_result!(self, a1 * a2, caller)?),
                        "/" => interms.push(self.div(a1, a2)?),
                        "**" => interms.push(self.pow(a1, a2, "is")?),
                        "^" => interms.push(self.int_pow(a1, a2)?),
                        "max" => interms.push(self.max(a1, a2)?),
                        "min" => interms.push(self.min(a1, a2)?),
                        "rdiv" => {
                            let r1 = self.rational_from_number(a1);
                            let r2 =
                                r1.and_then(|r1| self.rational_from_number(a2).map(|r2| (r1, r2)));

                            match r2 {
                                Ok((r1, r2)) => {
                                    let result = Number::Rational(Rc::new(self.rdiv(r1, r2)?));
                                    interms.push(result);
                                }
                                Err(e) => {
                                    return Err(self.error_form(e, caller));
                                }
                            }
                        }
                        "//" => interms.push(self.idiv(a1, a2)?),
                        "div" => interms.push(self.int_floor_div(a1, a2)?),
                        ">>" => interms.push(self.shr(a1, a2)?),
                        "<<" => interms.push(self.shl(a1, a2)?),
                        "/\\" => interms.push(self.and(a1, a2)?),
                        "\\/" => interms.push(self.or(a1, a2)?),
                        "xor" => interms.push(self.xor(a1, a2)?),
                        "mod" => interms.push(self.modulus(a1, a2)?),
                        "rem" => interms.push(self.remainder(a1, a2)?),
                        "atan2" => interms.push(Number::Float(OrderedFloat(self.atan2(a1, a2)?))),
                        "gcd" => interms.push(self.gcd(a1, a2)?),
                        _ => {
                            let evaluable_stub = MachineError::functor_stub(name.clone(), 2);

                            return Err(self.error_form(
                                MachineError::type_error(
                                    self.heap.h(),
                                    ValidType::Evaluable,
                                    evaluable_stub,
                                ),
                                caller,
                            ));
                        }
                    }
                }
                &HeapCellValue::NamedStr(1, ref name, _) => {
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
                        "truncate" => interms.push(self.truncate(a1)),
                        "round" => interms.push(self.round(a1)?),
                        "ceiling" => interms.push(self.ceiling(a1)),
                        "floor" => interms.push(self.floor(a1)),
                        "\\" => interms.push(self.bitwise_complement(a1)?),
                        "sign" => interms.push(self.sign(a1)),
                        _ => {
                            let evaluable_stub = MachineError::functor_stub(name.clone(), 1);

                            return Err(self.error_form(
                                MachineError::type_error(
                                    self.heap.h(),
                                    ValidType::Evaluable,
                                    evaluable_stub,
                                ),
                                caller,
                            ));
                        }
                    }
                }
                &HeapCellValue::Addr(Addr::Fixnum(n)) => {
                    interms.push(Number::Fixnum(n));
                }
                &HeapCellValue::Addr(Addr::Float(n)) => interms.push(Number::Float(n)),
                &HeapCellValue::Integer(ref n) => interms.push(Number::Integer(n.clone())),
                &HeapCellValue::Addr(Addr::Usize(n)) => {
                    interms.push(Number::Integer(Rc::new(Integer::from(n))));
                }
                &HeapCellValue::Rational(ref n) => interms.push(Number::Rational(n.clone())),
                &HeapCellValue::Atom(ref name, _) if name.as_str() == "pi" => {
                    interms.push(Number::Float(OrderedFloat(f64::consts::PI)))
                }
                &HeapCellValue::Atom(ref name, _) if name.as_str() == "e" => {
                    interms.push(Number::Float(OrderedFloat(f64::consts::E)))
                }
                &HeapCellValue::Atom(ref name, _) if name.as_str() == "epsilon" => {
                    interms.push(Number::Float(OrderedFloat(f64::EPSILON)))
                }
                &HeapCellValue::NamedStr(arity, ref name, _) => {
                    let evaluable_stub = MachineError::functor_stub(name.clone(), arity);

                    return Err(self.error_form(
                        MachineError::type_error(
                            self.heap.h(),
                            ValidType::Evaluable,
                            evaluable_stub,
                        ),
                        caller,
                    ));
                }
                &HeapCellValue::Atom(ref name, _) => {
                    let evaluable_stub = MachineError::functor_stub(name.clone(), 0);

                    return Err(self.error_form(
                        MachineError::type_error(
                            self.heap.h(),
                            ValidType::Evaluable,
                            evaluable_stub,
                        ),
                        caller,
                    ));
                }
                &HeapCellValue::Addr(addr) if addr.is_ref() => {
                    return Err(self.error_form(MachineError::instantiation_error(), caller));
                }
                val => {
                    return Err(self.type_error(
                        ValidType::Number,
                        val.context_free_clone(),
                        clause_name!("is"),
                        2,
                    ));
                }
            }
        }

        Ok(interms.pop().unwrap())
    }

    pub(crate) fn rdiv(&self, r1: Rc<Rational>, r2: Rc<Rational>) -> Result<Rational, MachineStub> {
        if &*r2 == &0 {
            let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            Ok(Rational::from(&*r1 / &*r2))
        }
    }

    pub(crate) fn int_floor_div(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(div)"), 2);
        let modulus = self.modulus(n1.clone(), n2.clone())?;

        self.idiv(try_numeric_result!(self, n1 - modulus, stub)?, n2)
    }

    pub(crate) fn idiv(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if n2 == 0 {
                    let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    if let Some(result) = n1.checked_div(n2) {
                        Ok(Number::from(result))
                    } else {
                        let n1 = Integer::from(n1);
                        let n2 = Integer::from(n2);

                        Ok(Number::from(n1 / n2))
                    }
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(Integer::from(n1) / &*n2))
                }
            }
            (Number::Integer(n2), Number::Fixnum(n1)) => {
                if n1 == 0 {
                    let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(&*n2 / Integer::from(n1)))
                }
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(
                        <(Integer, Integer)>::from(n1.div_rem_ref(&*n2)).0,
                    ))
                }
            }
            (Number::Fixnum(_), n2) | (Number::Integer(_), n2) => {
                let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                Err(self.error_form(
                    MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                    stub,
                ))
            }
            (n1, _) => {
                let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                Err(self.error_form(
                    MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                    stub,
                ))
            }
        }
    }

    pub(crate) fn div(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/)"), 2);

        if n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            try_numeric_result!(self, n1 / n2, stub)
        }
    }

    pub(crate) fn atan2(&self, n1: Number, n2: Number) -> Result<f64, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("is"), 2);

        if n1.is_zero() && n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub))
        } else {
            let f1 = self.float(n1)?;
            let f2 = self.float(n2)?;

            self.unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.atan2(f2))
        }
    }

    pub(crate) fn int_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        if n1.is_zero() && n2.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("is"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if !(n1 == 1 || n1 == 0 || n1 == -1) && n2 < 0 {
                    let n = Number::from(n1);
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::Float, n),
                        stub,
                    ))
                } else {
                    if let Ok(n2) = u32::try_from(n2) {
                        if let Some(result) = n1.checked_pow(n2) {
                            return Ok(Number::from(result));
                        }
                    }

                    let n1 = Integer::from(n1);
                    let n2 = Integer::from(n2);

                    Ok(Number::from(binary_pow(n1, &n2)))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if !(n1 == 1 || n1 == 0 || n1 == -1) && &*n2 < &0 {
                    let n = Number::from(n1);
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::Float, n),
                        stub,
                    ))
                } else {
                    let n1 = Integer::from(n1);
                    Ok(Number::from(binary_pow(n1, n2.as_ref())))
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => {
                if !(&*n1 == &1 || &*n1 == &0 || &*n1 == &-1) && n2 < 0 {
                    let n = Number::Integer(n1);
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::Float, n),
                        stub,
                    ))
                } else {
                    let n2 = Integer::from(n2);
                    Ok(Number::from(binary_pow(n1.as_ref().clone(), &n2)))
                }
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                if !(&*n1 == &1 || &*n1 == &0 || &*n1 == &-1) && &*n2 < &0 {
                    let n = Number::Integer(n1);
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(
                        MachineError::type_error(self.heap.h(), ValidType::Float, n),
                        stub,
                    ))
                } else {
                    Ok(Number::from(binary_pow(n1.as_ref().clone(), n2.as_ref())))
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
                    let stub = MachineError::functor_stub(clause_name!("is"), 2);
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

    pub(crate) fn gcd(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if let Some(result) = isize_gcd(n1, n2) {
                    Ok(Number::Fixnum(result))
                } else {
                    Ok(Number::from(Integer::from(n1).gcd(&Integer::from(n2))))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2))
            | (Number::Integer(n2), Number::Fixnum(n1)) => {
                let n1 = Integer::from(n1);
                Ok(Number::from(Integer::from(n2.gcd_ref(&n1))))
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Number::from(Integer::from(n1.gcd_ref(&n2))))
            }
            (Number::Float(f), _) | (_, Number::Float(f)) => {
                let n = Number::Float(f);
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(
                    MachineError::type_error(self.heap.h(), ValidType::Integer, n),
                    stub,
                ))
            }
            (Number::Rational(r), _) | (_, Number::Rational(r)) => {
                let n = Number::Rational(r);
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(
                    MachineError::type_error(self.heap.h(), ValidType::Integer, n),
                    stub,
                ))
            }
        }
    }

    pub(crate) fn float_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let f1 = result_f(&n1, rnd_f);
        let f2 = result_f(&n2, rnd_f);

        let stub = MachineError::functor_stub(clause_name!("(**)"), 2);

        let f1 = try_numeric_result!(self, f1, stub)?;
        let f2 = try_numeric_result!(self, f2, stub)?;

        let result = result_f(&Number::Float(OrderedFloat(f1.powf(f2))), rnd_f);

        Ok(Number::Float(OrderedFloat(try_numeric_result!(
            self, result, stub
        )?)))
    }

    pub(crate) fn pow(
        &self,
        n1: Number,
        n2: Number,
        culprit: &'static str,
    ) -> Result<Number, MachineStub> {
        if n2.is_negative() && n1.is_zero() {
            let stub = MachineError::functor_stub(clause_name!(culprit), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        self.float_pow(n1, n2)
    }

    #[inline]
    pub(crate) fn unary_float_fn_template<FloatFn>(
        &self,
        n1: Number,
        f: FloatFn,
    ) -> Result<f64, MachineStub>
    where
        FloatFn: Fn(f64) -> f64,
    {
        let stub = MachineError::functor_stub(clause_name!("is"), 2);

        let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
        let f1 = result_f(&Number::Float(OrderedFloat(f(f1))), rnd_f);

        try_numeric_result!(self, f1, stub)
    }

    #[inline]
    pub(crate) fn sin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.sin())
    }

    #[inline]
    pub(crate) fn cos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.cos())
    }

    #[inline]
    pub(crate) fn tan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.tan())
    }

    #[inline]
    pub(crate) fn log(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.log(f64::consts::E))
    }

    #[inline]
    pub(crate) fn exp(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.exp())
    }

    #[inline]
    pub(crate) fn asin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.asin())
    }

    #[inline]
    pub(crate) fn acos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.acos())
    }

    #[inline]
    pub(crate) fn atan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.atan())
    }

    #[inline]
    pub(crate) fn sqrt(&self, n1: Number) -> Result<f64, MachineStub> {
        if n1.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("is"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        self.unary_float_fn_template(n1, |f| f.sqrt())
    }

    #[inline]
    pub(crate) fn float(&self, n: Number) -> Result<f64, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("is"), 2);
        try_numeric_result!(self, result_f(&n, rnd_f), stub)
    }

    #[inline]
    pub(crate) fn floor(&self, n1: Number) -> Number {
        rnd_i(&n1).to_owned()
    }

    #[inline]
    pub(crate) fn ceiling(&self, n1: Number) -> Number {
        -self.floor(-n1)
    }

    #[inline]
    pub(crate) fn truncate(&self, n: Number) -> Number {
        if n.is_negative() {
            -self.floor(n.abs())
        } else {
            self.floor(n)
        }
    }

    pub(crate) fn round(&self, n: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("is"), 2);

        let result = n + Number::Float(OrderedFloat(0.5f64));
        let result = try_numeric_result!(self, result, stub)?;

        Ok(self.floor(result))
    }

    pub(crate) fn shr(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(>>)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                let n1 = Integer::from(n1);

                if let Ok(n2) = u32::try_from(n2) {
                    return Ok(Number::from(n1 >> n2));
                } else {
                    return Ok(Number::from(n1 >> u32::max_value()));
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                let n1 = Integer::from(n1);

                match n2.to_u32() {
                    Some(n2) => Ok(Number::from(n1 >> n2)),
                    _ => Ok(Number::from(n1 >> u32::max_value())),
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => match u32::try_from(n2) {
                Ok(n2) => Ok(Number::from(Integer::from(&*n1 >> n2))),
                _ => Ok(Number::from(Integer::from(&*n1 >> u32::max_value()))),
            },
            (Number::Integer(n1), Number::Integer(n2)) => match n2.to_u32() {
                Some(n2) => Ok(Number::from(Integer::from(&*n1 >> n2))),
                _ => Ok(Number::from(Integer::from(&*n1 >> u32::max_value()))),
            },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn shl(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(<<)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                let n1 = Integer::from(n1);

                if let Ok(n2) = u32::try_from(n2) {
                    return Ok(Number::from(n1 << n2));
                } else {
                    return Ok(Number::from(n1 << u32::max_value()));
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                let n1 = Integer::from(n1);

                match n2.to_u32() {
                    Some(n2) => Ok(Number::from(n1 << n2)),
                    _ => Ok(Number::from(n1 << u32::max_value())),
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => match u32::try_from(n2) {
                Ok(n2) => Ok(Number::from(Integer::from(&*n1 << n2))),
                _ => Ok(Number::from(Integer::from(&*n1 << u32::max_value()))),
            },
            (Number::Integer(n1), Number::Integer(n2)) => match n2.to_u32() {
                Some(n2) => Ok(Number::from(Integer::from(&*n1 << n2))),
                _ => Ok(Number::from(Integer::from(&*n1 << u32::max_value()))),
            },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn bitwise_complement(&self, n1: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\)"), 2);

        match n1 {
            Number::Fixnum(n) => Ok(Number::Fixnum(!n)),
            Number::Integer(n1) => Ok(Number::from(Integer::from(!&*n1))),
            _ => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn xor(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(xor)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(Number::from(n1 ^ n2)),
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                let n1 = Integer::from(n1);
                Ok(Number::from(n1 ^ &*n2))
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::from(&*n1 ^ Integer::from(n2))),
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Number::from(Integer::from(&*n1 ^ &*n2)))
            }
            (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn and(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/\\)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(Number::from(n1 & n2)),
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                let n1 = Integer::from(n1);
                Ok(Number::from(n1 & &*n2))
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::from(&*n1 & Integer::from(n2))),
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Number::from(Integer::from(&*n1 & &*n2)))
            }
            (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn or(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\/)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(Number::from(n1 | n2)),
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                let n1 = Integer::from(n1);
                Ok(Number::from(n1 | &*n2))
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::from(&*n1 | Integer::from(n2))),
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Number::from(Integer::from(&*n1 | &*n2)))
            }
            (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn modulus(&self, x: Number, y: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(mod)"), 2);

        match (x, y) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(n1.rem_floor(n2)))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    let n1 = Integer::from(n1);
                    Ok(Number::from(
                        <(Integer, Integer)>::from(n1.div_rem_floor_ref(&*n2)).1,
                    ))
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    let n2 = Integer::from(n2);
                    Ok(Number::from(
                        <(Integer, Integer)>::from(n1.div_rem_floor_ref(&n2)).1,
                    ))
                }
            }
            (Number::Integer(x), Number::Integer(y)) => {
                if &*y == &0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(
                        <(Integer, Integer)>::from(x.div_rem_floor_ref(&*y)).1,
                    ))
                }
            }
            (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn remainder(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(rem)"), 2);

        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(n1 % n2))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    let n1 = Integer::from(n1);
                    Ok(Number::from(n1 % &*n2))
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => {
                if n2 == 0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    let n2 = Integer::from(n2);
                    Ok(Number::from(&*n1 % n2))
                }
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Number::from(Integer::from(&*n1 % &*n2)))
                }
            }
            (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n2),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(self.heap.h(), ValidType::Integer, n1),
                stub,
            )),
        }
    }

    pub(crate) fn max(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if n1 > n2 {
                    Ok(Number::Fixnum(n1))
                } else {
                    Ok(Number::Fixnum(n2))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if &*n2 > &n1 {
                    Ok(Number::Integer(n2))
                } else {
                    Ok(Number::Fixnum(n1))
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => {
                if &*n1 > &n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Fixnum(n2))
                }
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n1 > n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Integer(n2))
                }
            }
            (n1, n2) => {
                let stub = MachineError::functor_stub(clause_name!("max"), 2);

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(cmp::max(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    pub(crate) fn min(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        match (n1, n2) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => {
                if n1 < n2 {
                    Ok(Number::Fixnum(n1))
                } else {
                    Ok(Number::Fixnum(n2))
                }
            }
            (Number::Fixnum(n1), Number::Integer(n2)) => {
                if &*n2 < &n1 {
                    Ok(Number::Integer(n2))
                } else {
                    Ok(Number::Fixnum(n1))
                }
            }
            (Number::Integer(n1), Number::Fixnum(n2)) => {
                if &*n1 < &n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Fixnum(n2))
                }
            }
            (Number::Integer(n1), Number::Integer(n2)) => {
                if n1 < n2 {
                    Ok(Number::Integer(n1))
                } else {
                    Ok(Number::Integer(n2))
                }
            }
            (n1, n2) => {
                let stub = MachineError::functor_stub(clause_name!("max"), 2);

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(cmp::min(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    pub(crate) fn sign(&self, n: Number) -> Number {
        if n.is_positive() {
            Number::from(1)
        } else if n.is_negative() {
            Number::from(-1)
        } else {
            Number::from(0)
        }
    }
}
