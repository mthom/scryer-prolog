use crate::prolog_parser::ast::*;

use crate::prolog::arithmetic::*;
use crate::prolog::clause_types::*;
use crate::prolog::forms::*;
use crate::prolog::machine::machine_errors::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;
use crate::prolog::ordered_float::*;
use crate::prolog::rug::{Integer, Rational};

use std::cmp;
use std::f64;
use std::mem;
use std::rc::Rc;

#[macro_export]
macro_rules! try_numeric_result {
    ($s: ident, $e: expr, $caller: expr) => (
        match $e {
            Ok(val) => {
                Ok(val)
            }
            Err(e) => {
                let caller_copy =
                    $caller.iter().map(|v| v.context_free_clone()).collect();
                
                Err($s.error_form(MachineError::evaluation_error(e), caller_copy))
            }
        }
    );
}

impl MachineState {
    pub(crate)
    fn get_number(&mut self, at: &ArithmeticTerm) -> Result<Number, MachineStub> {
        match at {
            &ArithmeticTerm::Reg(r) => {
                self.arith_eval_by_metacall(r)
            }
            &ArithmeticTerm::Interm(i) => Ok(mem::replace(
                &mut self.interms[i - 1],
                Number::Integer(Rc::new(Integer::from(0))),
            )),
            &ArithmeticTerm::Number(ref n) => {
                Ok(n.clone())
            }
        }
    }

    pub(super)
    fn rational_from_number(
        &self,
        n: Number,
    ) -> Result<Rc<Rational>, MachineError> {
        match n {
            Number::Rational(r) => {
                Ok(r)
            }
            Number::Float(OrderedFloat(f)) => {
                match Rational::from_f64(f) {
                    Some(r) => {
                        Ok(Rc::new(r))
                    }
                    None => {
                        Err(MachineError::instantiation_error())
                    }
                }
            }
            Number::Integer(n) => {
                Ok(Rc::new(Rational::from(&*n)))
            }
        }
    }

    pub(crate)
    fn get_rational(
        &mut self,
        at: &ArithmeticTerm,
        caller: MachineStub,
    ) -> Result<(Rc<Rational>, MachineStub), MachineStub> {
        let n = self.get_number(at)?;
        
        match self.rational_from_number(n) {
            Ok(r) => Ok((r, caller)),
            Err(e) => Err(self.error_form(e, caller))
        }
    }

    pub(crate)
    fn arith_eval_by_metacall(&self, r: RegType) -> Result<Number, MachineStub> {
        let a = self[r].clone();

        let caller = MachineError::functor_stub(clause_name!("(is)"), 2);
        let mut interms: Vec<Number> = Vec::with_capacity(64);

        for addr in self.post_order_iter(a) {
            match self.heap.index_addr(&addr).as_ref() {
                &HeapCellValue::NamedStr(2, ref name, _) => {
                    let a2 = interms.pop().unwrap();
                    let a1 = interms.pop().unwrap();

                    match name.as_str() {
                        "+" => interms.push(try_numeric_result!(self, a1 + a2, caller)?),
                        "-" => interms.push(try_numeric_result!(self, a1 - a2, caller)?),
                        "*" => interms.push(try_numeric_result!(self, a1 * a2, caller)?),
                        "/" => interms.push(self.div(a1, a2)?),
                        "**" => interms.push(self.pow(a1, a2, "(is)")?),
                        "^" => interms.push(self.int_pow(a1, a2)?),
                        "max" => interms.push(self.max(a1, a2)?),
                        "min" => interms.push(self.min(a1, a2)?),
                        "rdiv" => {
                            let r1 = self.rational_from_number(a1);
                            let r2 = r1.and_then(|r1| {
                                self.rational_from_number(a2).map(|r2| (r1, r2))
                            });
                                                 
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
                        "//" => interms.push(Number::Integer(Rc::new(self.idiv(a1, a2)?))),
                        "div" => interms.push(Number::Integer(Rc::new(self.int_floor_div(a1, a2)?))),
                        ">>" => interms.push(Number::Integer(Rc::new(self.shr(a1, a2)?))),
                        "<<" => interms.push(Number::Integer(Rc::new(self.shl(a1, a2)?))),
                        "/\\" => interms.push(Number::Integer(Rc::new(self.and(a1, a2)?))),
                        "\\/" => interms.push(Number::Integer(Rc::new(self.or(a1, a2)?))),
                        "xor" => interms.push(Number::Integer(Rc::new(self.xor(a1, a2)?))),
                        "mod" => interms.push(Number::Integer(Rc::new(self.modulus(a1, a2)?))),
                        "rem" => interms.push(Number::Integer(Rc::new(self.remainder(a1, a2)?))),
                        "atan2" => interms.push(Number::Float(OrderedFloat(self.atan2(a1, a2)?))),
                        "gcd" => interms.push(Number::Integer(Rc::new(self.gcd(a1, a2)?))),
                        _ => {
                            return Err(self.error_form(MachineError::instantiation_error(), caller))
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
                        "truncate" => interms.push(Number::Integer(Rc::new(self.truncate(a1)))),
                        "round" => interms.push(Number::Integer(Rc::new(self.round(a1)?))),
                        "ceiling" => interms.push(Number::Integer(Rc::new(self.ceiling(a1)))),
                        "floor" => interms.push(Number::Integer(Rc::new(self.floor(a1)))),
                        "\\" => interms.push(Number::Integer(Rc::new(self.bitwise_complement(a1)?))),
                        "sign" => interms.push(Number::Integer(Rc::new(self.sign(a1)))),
                        _ => {
                            return Err(self.error_form(MachineError::instantiation_error(), caller));
                        }
                    }
                }
                &HeapCellValue::Integer(ref n) => {
                    interms.push(Number::Integer(n.clone()))
                }
                &HeapCellValue::Addr(Addr::Float(n)) => {
                    interms.push(Number::Float(n))
                }
                &HeapCellValue::Rational(ref n) => {
                    interms.push(Number::Rational(n.clone()))
                }
                &HeapCellValue::Atom(ref name, _) if name.as_str() == "pi" => {
                    interms.push(Number::Float(OrderedFloat(f64::consts::PI)))
                }
                _ => {
                    return Err(self.error_form(
                        MachineError::instantiation_error(),
                        caller,
                    ));
                }
            }
        }

        Ok(interms.pop().unwrap())
    }

    pub(crate)
    fn rdiv(&self, r1: Rc<Rational>, r2: Rc<Rational>) -> Result<Rational, MachineStub> {
        if &*r2 == &0 {
            let stub = MachineError::functor_stub(clause_name!("(rdiv)"), 2);
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            Ok(Rational::from(&*r1 / &*r2))
        }
    }

    pub(crate)
    fn int_floor_div(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        match n1 / n2 {
            Ok(result) => Ok(rnd_i(&result).to_owned()),
            Err(e) => {
                let stub = MachineError::functor_stub(clause_name!("(div)"), 2);
                Err(self.error_form(
                    MachineError::evaluation_error(
                        e
                    ),
                    stub
                ))
            }
        }
    }

    pub(crate)
    fn idiv(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                    Err(self.error_form(
                        MachineError::evaluation_error(
                            EvalError::ZeroDivisor
                        ),
                        stub,
                    ))
                } else {
                    Ok(<(Integer, Integer)>::from(n1.div_rem_ref(&*n2)).0)
                }
            }
            (Number::Integer(_), n2) => {
                let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n2,
                    ),
                    stub,
                ))
            }
            (n1, _) => {
                let stub = MachineError::functor_stub(clause_name!("(//)"), 2);

                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n1,
                    ),
                    stub,
                ))
            }
        }
    }

    pub(crate)
    fn div(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/)"), 2);

        if n2.is_zero() {
            Err(self.error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
        } else {
            try_numeric_result!(self, n1 / n2, stub)
        }
    }

    pub(crate)
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

    pub(crate)
    fn int_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
        if n1.is_zero() && n2.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if &*n1 != &1 && &*n2 < &0 {
                    let n = Number::Integer(n1);
                    let stub = MachineError::functor_stub(clause_name!("^"), 2);

                    Err(self.error_form(
                        MachineError::type_error(
                            self.heap.h(),
                            ValidType::Float,
                            n
                        ),
                        stub,
                    ))
                } else {
                    Ok(Number::Integer(Rc::new(binary_pow(n1.as_ref().clone(), n2.as_ref()))))
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

    pub(crate)
    fn gcd(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Integer::from(n1.gcd_ref(&n2)))
            }
            (Number::Float(f), _) | (_, Number::Float(f)) => {
                let n = Number::Float(f);
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n
                    ),
                    stub,
                ))
            }
            (Number::Rational(r), _) | (_, Number::Rational(r)) => {
                let n = Number::Rational(r);
                let stub = MachineError::functor_stub(clause_name!("gcd"), 2);

                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n,
                    ),
                    stub,
                ))
            }
        }
    }

    pub(crate)
    fn float_pow(&self, n1: Number, n2: Number) -> Result<Number, MachineStub> {
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

    pub(crate)
    fn pow(&self, n1: Number, n2: Number, culprit: &'static str) -> Result<Number, MachineStub> {
        if n2.is_negative() && n1.is_zero() {
            let stub = MachineError::functor_stub(clause_name!(culprit), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Number::Integer(Rc::new(binary_pow(n1.as_ref().clone(), &*n2))))
            }
            (n1, n2) => {
                self.float_pow(n1, n2)
            }
        }
    }

    pub(crate)
    fn unary_float_fn_template<FloatFn>(&self, n1: Number, f: FloatFn) -> Result<f64, MachineStub>
    where
        FloatFn: Fn(f64) -> f64,
    {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
        let f1 = result_f(&Number::Float(OrderedFloat(f(f1))), rnd_f);

        try_numeric_result!(self, f1, stub)
    }

    pub(crate)
    fn sin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.sin())
    }

    pub(crate)
    fn cos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.cos())
    }

    pub(crate)
    fn tan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.tan())
    }

    pub(crate)
    fn log(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.log(f64::consts::E))
    }

    pub(crate)
    fn exp(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.exp())
    }

    pub(crate)
    fn asin(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.asin())
    }

    pub(crate)
    fn acos(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.acos())
    }

    pub(crate)
    fn atan(&self, n1: Number) -> Result<f64, MachineStub> {
        self.unary_float_fn_template(n1, |f| f.atan())
    }

    pub(crate)
    fn sqrt(&self, n1: Number) -> Result<f64, MachineStub> {
        if n1.is_negative() {
            let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
            return Err(self.error_form(MachineError::evaluation_error(EvalError::Undefined), stub));
        }

        self.unary_float_fn_template(n1, |f| f.sqrt())
    }

    pub(crate)
    fn float(&self, n: Number) -> Result<f64, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);
        try_numeric_result!(self, result_f(&n, rnd_f), stub)
    }

    pub(crate)
    fn floor(&self, n1: Number) -> Integer {
        rnd_i(&n1).to_owned()
    }

    pub(crate)
    fn ceiling(&self, n1: Number) -> Integer {
        -self.floor(-n1)
    }

    pub(crate)
    fn truncate(&self, n: Number) -> Integer {
        if n.is_negative() {
            -self.floor(n.abs())
        } else {
            self.floor(n)
        }
    }

    pub(crate)
    fn round(&self, n: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(is)"), 2);

        let result = n + Number::Float(OrderedFloat(0.5f64));
        let result = try_numeric_result!(self, result, stub)?;

        Ok(self.floor(result))
    }

    pub(crate)
    fn shr(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(>>)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) =>
                match n2.to_u32() {
                    Some(n2) => Ok(Integer::from(&*n1 >> n2)),
                    _ => Ok(Integer::from(&*n1 >> u32::max_value())),
                },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n2,
                ),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
    fn shl(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(<<)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => match n2.to_u32() {
                Some(n2) => Ok(Integer::from(&*n1 << n2)),
                _ => Ok(Integer::from(&*n1 << u32::max_value())),
            },
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n2,
                ),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
    fn bitwise_complement(&self, n1: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\)"), 2);

        match n1 {
            Number::Integer(n1) => Ok(Integer::from(!&*n1)),
            _ => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
    fn xor(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(xor)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Integer::from(&*n1 ^ &*n2))
            }
            (Number::Integer(_), n2) => {
                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n2
                    ),
                    stub,
                ))
            }
            (n1, _) => {
                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n1
                    ),
                    stub,
                ))
            }
        }
    }

    pub(crate)
    fn and(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(/\\)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => Ok(Integer::from(&*n1 & &*n2)),
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n2,
                ),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
    fn modulus(&self, x: Number, y: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(mod)"), 2);

        match (x, y) {
            (Number::Integer(x), Number::Integer(y)) => {
                if &*y == &0 {
                    Err(self.error_form(
                        MachineError::evaluation_error(EvalError::ZeroDivisor),
                        stub,
                    ))
                } else {
                    Ok(<(Integer, Integer)>::from(x.div_rem_floor_ref(&*y)).1)
                }
            }
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n2,
                ),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
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

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(cmp::max(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    pub(crate)
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

                let f1 = try_numeric_result!(self, result_f(&n1, rnd_f), stub)?;
                let f2 = try_numeric_result!(self, result_f(&n2, rnd_f), stub)?;

                Ok(Number::Float(cmp::min(OrderedFloat(f1), OrderedFloat(f2))))
            }
        }
    }

    pub(crate)
    fn sign(&self, n: Number) -> Integer {
        if n.is_positive() {
            Integer::from(1)
        } else if n.is_negative() {
            Integer::from(-1)
        } else {
            Integer::from(0)
        }
    }

    pub(crate)
    fn remainder(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(rem)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                if &*n2 == &0 {
                    Err(self
                        .error_form(MachineError::evaluation_error(EvalError::ZeroDivisor), stub))
                } else {
                    Ok(Integer::from(&*n1 % &*n2))
                }
            }
            (Number::Integer(_), n2) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n2,
                ),
                stub,
            )),
            (n1, _) => Err(self.error_form(
                MachineError::type_error(
                    self.heap.h(),
                    ValidType::Integer,
                    n1,
                ),
                stub,
            )),
        }
    }

    pub(crate)
    fn or(&self, n1: Number, n2: Number) -> Result<Integer, MachineStub> {
        let stub = MachineError::functor_stub(clause_name!("(\\/)"), 2);

        match (n1, n2) {
            (Number::Integer(n1), Number::Integer(n2)) => {
                Ok(Integer::from(&*n1 | &*n2))
            }
            (Number::Integer(_), n2) => {
                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n2,
                    ),
                    stub,
                ))
            }
            (n1, _) => {
                Err(self.error_form(
                    MachineError::type_error(
                        self.heap.h(),
                        ValidType::Integer,
                        n1
                    ),
                    stub,
                ))
            }
        }
    }
}
