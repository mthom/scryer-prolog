use dashu::base::Abs;
use dashu::base::DivRem;
use dashu::base::Gcd;
use dashu::integer::IBig;
use divrem::*;
use num_order::NumOrd;

use crate::arena::*;
use crate::arithmetic::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_state::*;
use crate::parser::ast::*;
use crate::parser::dashu::{Integer, Rational};
use crate::types::*;

use crate::fixnum;

use ordered_float::*;

use std::cmp;
use std::convert::TryFrom;
use std::f64;
use std::mem;

#[macro_export]
macro_rules! try_numeric_result {
    ($e: expr, $stub_gen: expr) => {
        match $e {
            Ok(val) => Ok(val),
            Err(e) => Err(Box::new(move |machine_st: &mut MachineState| {
                let stub = $stub_gen();
                let evaluation_error = machine_st.evaluation_error(e);

                machine_st.error_form(evaluation_error, stub)
            }) as Box<dyn Fn(&mut MachineState) -> MachineStub>),
        }
    };
}

macro_rules! drop_iter_on_err {
    ($self:expr, $iter: expr, $result: expr) => {
        match $result {
            Ok(val) => val,
            Err(stub_gen) => {
                std::mem::drop($iter);
                return Err(stub_gen($self));
            }
        }
    };
}

fn zero_divisor_eval_error(
    stub_gen: impl Fn() -> FunctorStub + 'static,
) -> MachineStubGen {
    Box::new(move |machine_st| {
        let eval_error = machine_st.evaluation_error(EvalError::ZeroDivisor);
        let stub = stub_gen();

        machine_st.error_form(eval_error, stub)
    })
}

fn undefined_eval_error(
    stub_gen: impl Fn() -> FunctorStub + 'static,
) -> MachineStubGen {
    Box::new(move |machine_st| {
        let eval_error = machine_st.evaluation_error(EvalError::Undefined);
        let stub = stub_gen();

        machine_st.error_form(eval_error, stub)
    })
}

fn numerical_type_error(
    valid_type: ValidType,
    n: Number,
    stub_gen: impl Fn() -> FunctorStub + 'static,
) -> MachineStubGen {
    Box::new(move |machine_st| {
        let type_error = machine_st.type_error(valid_type, n);
        let stub = stub_gen();

        machine_st.error_form(type_error, stub)
    })
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

pub(crate) fn add(lhs: Number, rhs: Number, arena: &mut Arena) -> Result<Number, EvalError> {
    match (lhs, rhs) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(
            if let Some(result) = n1.get_num().checked_add(n2.get_num()) {
                fixnum!(Number, result, arena)
            } else {
                Number::arena_from(
                    Integer::from(n1.get_num()) + Integer::from(n2.get_num()),
                    arena,
                )
            },
        ),
        (Number::Fixnum(n1), Number::Integer(n2)) | (Number::Integer(n2), Number::Fixnum(n1)) => {
            Ok(Number::arena_from(
                Integer::from(n1.get_num()) + &*n2,
                arena,
            ))
        }
        (Number::Fixnum(n1), Number::Rational(n2)) | (Number::Rational(n2), Number::Fixnum(n1)) => {
            Ok(Number::arena_from(
                Rational::from(n1.get_num()) + &*n2,
                arena,
            ))
        }
        (Number::Fixnum(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Fixnum(n1)) => {
            Ok(Number::Float(add_f(float_fn_to_f(n1.get_num())?, n2)?))
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            Ok(Number::arena_from(&*n1 + &*n2, arena)) // add_i
        }
        (Number::Integer(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Integer(n1)) => {
            Ok(Number::Float(add_f(float_i_to_f(&n1)?, n2)?))
        }
        (Number::Integer(n1), Number::Rational(n2))
        | (Number::Rational(n2), Number::Integer(n1)) => {
            Ok(Number::arena_from(&*n1 + &*n2, arena))
        }
        (Number::Rational(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Rational(n1)) => {
            Ok(Number::Float(add_f(float_r_to_f(&n1)?, n2)?))
        }
        (Number::Float(OrderedFloat(f1)), Number::Float(OrderedFloat(f2))) => {
            Ok(Number::Float(add_f(f1, f2)?))
        }
        (Number::Rational(r1), Number::Rational(r2)) => {
            Ok(Number::arena_from(&*r1 + &*r2, arena))
        }
    }
}

pub(crate) fn neg(n: Number, arena: &mut Arena) -> Number {
    match n {
        Number::Fixnum(n) => {
            if let Some(n) = n.get_num().checked_neg() {
                fixnum!(Number, n, arena)
            } else {
                Number::arena_from(-Integer::from(n.get_num()), arena)
            }
        }
        Number::Integer(n) => {
            let n_clone: Integer = (*n).clone();
            Number::arena_from(-Integer::from(n_clone), arena)
        },
        Number::Float(OrderedFloat(f)) => Number::Float(OrderedFloat(-f)),
        Number::Rational(r) => {
            let r_clone: Rational = (*r).clone();
            Number::arena_from(-Rational::from(r_clone), arena)
        },
    }
}

pub(crate) fn abs(n: Number, arena: &mut Arena) -> Number {
    match n {
        Number::Fixnum(n) => {
            if let Some(n) = n.get_num().checked_abs() {
                fixnum!(Number, n, arena)
            } else {
                let arena_int = Integer::from(n.get_num());
                Number::arena_from(arena_int.abs(), arena)
            }
        }
        Number::Integer(n) => {
            let n_clone: Integer = (*n).clone();
            Number::arena_from(Integer::from(n_clone.abs()), arena)
        },
        Number::Float(f) => Number::Float(f.abs()),
        Number::Rational(r) => {
            let r_clone: Rational = (*r).clone();
            Number::arena_from(Rational::from(r_clone.abs()), arena)
        },
    }
}

#[inline]
pub(crate) fn sub(lhs: Number, rhs: Number, arena: &mut Arena) -> Result<Number, EvalError> {
    let neg_result = neg(rhs, arena);
    add(lhs, neg_result, arena)
}

pub(crate) fn mul(lhs: Number, rhs: Number, arena: &mut Arena) -> Result<Number, EvalError> {
    match (lhs, rhs) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(
            if let Some(result) = n1.get_num().checked_mul(n2.get_num()) {
                fixnum!(Number, result, arena)
            } else {
                Number::arena_from(
                    Integer::from(n1.get_num()) * Integer::from(n2.get_num()),
                    arena,
                )
            },
        ),
        (Number::Fixnum(n1), Number::Integer(n2)) | (Number::Integer(n2), Number::Fixnum(n1)) => {
            Ok(Number::arena_from(
                Integer::from(n1.get_num()) * &*n2,
                arena,
            ))
        }
        (Number::Fixnum(n1), Number::Rational(n2)) | (Number::Rational(n2), Number::Fixnum(n1)) => {
            Ok(Number::arena_from(
                Rational::from(n1.get_num()) * &*n2,
                arena,
            ))
        }
        (Number::Fixnum(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Fixnum(n1)) => {
            Ok(Number::Float(mul_f(float_fn_to_f(n1.get_num())?, n2)?))
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            let n1_clone: Integer = (*n1).clone();
            Ok(Number::arena_from(Integer::from(n1_clone) * &*n2, arena)) // mul_i
        }
        (Number::Integer(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Integer(n1)) => {
            Ok(Number::Float(mul_f(float_i_to_f(&n1)?, n2)?))
        }
        (Number::Integer(n1), Number::Rational(n2))
        | (Number::Rational(n2), Number::Integer(n1)) => {
            let n1_clone: Integer = (*n1).clone();
            Ok(Number::arena_from(Rational::from(n1_clone) * &*n2, arena))
        }
        (Number::Rational(n1), Number::Float(OrderedFloat(n2)))
        | (Number::Float(OrderedFloat(n2)), Number::Rational(n1)) => {
            Ok(Number::Float(mul_f(float_r_to_f(&n1)?, n2)?))
        }
        (Number::Float(OrderedFloat(f1)), Number::Float(OrderedFloat(f2))) => {
            Ok(Number::Float(mul_f(f1, f2)?))
        }
        (Number::Rational(r1), Number::Rational(r2)) => {
            let r1_clone: Rational = (*r1).clone();
            Ok(Number::arena_from(Rational::from(r1_clone) * &*r2, arena))
        }
    }
}

pub(crate) fn div(n1: Number, n2: Number) -> Result<Number, MachineStubGen> {
    let stub_gen = || functor_stub(atom!("/"), 2);

    if n2.is_zero() {
        Err(zero_divisor_eval_error(stub_gen))
    } else {
        try_numeric_result!(n1 / n2, stub_gen)
    }
}

pub(crate) fn float_pow(n1: Number, n2: Number) -> Result<Number, MachineStubGen> {
    let f1 = result_f(&n1);
    let f2 = result_f(&n2);

    let stub_gen = || {
        let pow_atom = atom!("**");
        functor_stub(pow_atom, 2)
    };

    let f1 = try_numeric_result!(f1, stub_gen)?;
    let f2 = try_numeric_result!(f2, stub_gen)?;

    let result = result_f(&Number::Float(OrderedFloat(f1.powf(f2))));

    Ok(Number::Float(OrderedFloat(try_numeric_result!(
        result, stub_gen
    )?)))
}

pub(crate) fn int_pow(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    if n1.is_zero() && n2.is_negative() {
        let stub_gen = || {
            let is_atom = atom!("is");
            functor_stub(is_atom, 2)
        };

        return Err(undefined_eval_error(stub_gen));
    }

    let stub_gen = || {
        let caret_atom = atom!("^");
        functor_stub(caret_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n1_i = n1.get_num();
            let n2_i = n2.get_num();

            if !(n1_i == 1 || n1_i == 0 || n1_i == -1) && n2_i < 0 {
                let n = Number::Fixnum(n1);
                Err(numerical_type_error(ValidType::Float, n, stub_gen))
            } else {
                if let Ok(n2_u) = u32::try_from(n2_i) {
                    if let Some(result) = n1_i.checked_pow(n2_u) {
                        return Ok(Number::arena_from(result, arena));
                    }
                }

                let n1 = Integer::from(n1_i);
                let n2 = Integer::from(n2_i);

                Ok(Number::arena_from(binary_pow(n1, &n2), arena))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1_i = n1.get_num();

            if !(n1_i == 1 || n1_i == 0 || n1_i == -1) && &*n2 < &Integer::from(0) {
                let n = Number::Fixnum(n1);
                Err(numerical_type_error(ValidType::Float, n, stub_gen))
            } else {
                let n1 = Integer::from(n1_i);
                Ok(Number::arena_from(binary_pow(n1, &*n2), arena))
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => {
            let n2_i = n2.get_num();

            if !(&*n1 == &Integer::from(1) || &*n1 == &Integer::from(0) || &*n1 == &Integer::from(-1)) && n2_i < 0 {
                let n = Number::Integer(n1);
                Err(numerical_type_error(ValidType::Float, n, stub_gen))
            } else {
                let n2 = Integer::from(n2_i);
                Ok(Number::arena_from(binary_pow((*n1).clone(), &n2), arena))
            }
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            if !(&*n1 == &Integer::from(1) || &*n1 == &Integer::from(0) || &*n1 == &Integer::from(-1)) && &*n2 < &Integer::from(0) {
                let n = Number::Integer(n1);
                Err(numerical_type_error(ValidType::Float, n, stub_gen))
            } else {
                Ok(Number::arena_from(binary_pow((*n1).clone(), &*n2), arena))
            }
        }
        (n1, Number::Integer(n2)) => {
            let f1 = float(n1)?;
            let f2 = float(Number::Integer(n2))?;

            unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.powf(f2))
                .map(|f| Number::Float(OrderedFloat(f)))
        }
        (n1, n2) => {
            let f2 = float(n2)?;

            if n1.is_negative() && f2 != f2.floor() {
                return Err(undefined_eval_error(stub_gen));
            }

            let f1 = float(n1)?;

            unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.powf(f2))
                .map(|f| Number::Float(OrderedFloat(f)))
        }
    }
}

pub(crate) fn pow(n1: Number, n2: Number, culprit: Atom) -> Result<Number, MachineStubGen> {
    if n2.is_negative() && n1.is_zero() {
        let stub_gen = move || functor_stub(culprit, 2);
        return Err(undefined_eval_error(stub_gen));
    }

    float_pow(n1, n2)
}

#[inline]
pub(crate) fn float(n: Number) -> Result<f64, MachineStubGen> {
    let stub_gen = || {
        let is_atom = atom!("is");
        functor_stub(is_atom, 2)
    };

    try_numeric_result!(result_f(&n), stub_gen)
}

#[inline]
pub(crate) fn unary_float_fn_template<FloatFn>(
    n1: Number,
    f: FloatFn,
) -> Result<f64, MachineStubGen>
where
    FloatFn: Fn(f64) -> f64,
{
    let stub_gen = || {
        let is_atom = atom!("is");
        functor_stub(is_atom, 2)
    };

    let f1 = try_numeric_result!(result_f(&n1), stub_gen)?;
    let f1 = result_f(&Number::Float(OrderedFloat(f(f1))));

    try_numeric_result!(f1, stub_gen)
}

pub(crate) fn max(n1: Number, n2: Number) -> Result<Number, MachineStubGen> {
    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            if n1.get_num() > n2.get_num() {
                Ok(Number::Fixnum(n1))
            } else {
                Ok(Number::Fixnum(n2))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            if (&*n2).num_gt(&n1.get_num()) {
                Ok(Number::Integer(n2))
            } else {
                Ok(Number::Fixnum(n1))
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => {
            if (&*n1).num_gt(&n2.get_num()) {
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
            let stub_gen = || {
                let max_atom = atom!("max");
                functor_stub(max_atom, 2)
            };

            let f1 = try_numeric_result!(result_f(&n1), stub_gen)?;
            let f2 = try_numeric_result!(result_f(&n2), stub_gen)?;

            Ok(Number::Float(cmp::max(OrderedFloat(f1), OrderedFloat(f2))))
        }
    }
}

pub(crate) fn min(n1: Number, n2: Number) -> Result<Number, MachineStubGen> {
    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            if n1.get_num() < n2.get_num() {
                Ok(Number::Fixnum(n1))
            } else {
                Ok(Number::Fixnum(n2))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            if (&*n2).num_lt(&n1.get_num()) {
                Ok(Number::Integer(n2))
            } else {
                Ok(Number::Fixnum(n1))
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => {
            if (&*n1).num_lt(&n2.get_num()) {
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
            let stub_gen = || {
                let min_atom = atom!("min");
                functor_stub(min_atom, 2)
            };

            let f1 = try_numeric_result!(result_f(&n1), stub_gen)?;
            let f2 = try_numeric_result!(result_f(&n2), stub_gen)?;

            Ok(Number::Float(cmp::min(OrderedFloat(f1), OrderedFloat(f2))))
        }
    }
}

pub fn rational_from_number(
    n: Number,
    stub_gen: impl Fn() -> FunctorStub + 'static,
    arena: &mut Arena,
) -> Result<TypedArenaPtr<Rational>, MachineStubGen> {
    match n {
        Number::Fixnum(n) => Ok(arena_alloc!(Rational::from(n.get_num()), arena)),
        Number::Rational(r) => Ok(r),
        Number::Float(OrderedFloat(f)) => match Rational::simplest_from_f64(f) {
            Some(r) => Ok(arena_alloc!(r, arena)),
            None => Err(Box::new(move |machine_st| {
                let instantiation_error = machine_st.instantiation_error();
                let stub = stub_gen();

                machine_st.error_form(instantiation_error, stub)
            })),
        },
        Number::Integer(n) => {
            let n_clone: Integer = (*n).clone();
            Ok(arena_alloc!(Rational::from(n_clone), arena))
        },
    }
}

pub(crate) fn rdiv(
    r1: TypedArenaPtr<Rational>,
    r2: TypedArenaPtr<Rational>,
) -> Result<Rational, MachineStubGen> {
    if &*r2 == &Rational::from(0) {
        let stub_gen = || {
            let rdiv_atom = atom!("rdiv");
            functor_stub(rdiv_atom, 2)
        };

        Err(zero_divisor_eval_error(stub_gen))
    } else {
        Ok(Rational::from(&*r1 / &*r2))
    }
}

pub(crate) fn idiv(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let idiv_atom = atom!("//");
        functor_stub(idiv_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            if n2.get_num() == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                if let Some(result) = n1.get_num().checked_div(n2.get_num()) {
                    Ok(Number::arena_from(result, arena))
                } else {
                    let n1 = Integer::from(n1.get_num());
                    let n2 = Integer::from(n2.get_num());

                    Ok(Number::arena_from(n1 / n2, arena))
                }
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            if (&*n2).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                Ok(Number::arena_from(Integer::from(n1) / &*n2, arena))
            }
        }
        (Number::Integer(n2), Number::Fixnum(n1)) => {
            if n1.get_num() == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                Ok(Number::arena_from(&*n2 / Integer::from(n1), arena))
            }
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            if (&*n2).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                Ok(Number::arena_from(
                    <(Integer, Integer)>::from((&*n1).div_rem(&*n2)).0,
                    arena,
                ))
            }
        }
        (Number::Fixnum(_), n2) | (Number::Integer(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn int_floor_div(
    n1: Number,
    n2: Number,
    arena: &mut Arena,
) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let div_atom = atom!("div");
        functor_stub(div_atom, 2)
    };

    let modulus = modulus(n1, n2, arena)?;
    let n1 = try_numeric_result!(sub(n1, modulus, arena), stub_gen)?;

    idiv(n1, n2, arena)
}

pub(crate) fn shr(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let shr_atom = atom!(">>");
        functor_stub(shr_atom, 2)
    };

    if n2.is_integer() && n2.is_negative() {
        return shl(n1, neg(n2, arena), arena);
    }

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n1_i = n1.get_num();
            let n2_i = n2.get_num();

            let n1 = Integer::from(n1_i);

            if let Ok(n2) = usize::try_from(n2_i) {
                return Ok(Number::arena_from(n1 >> n2, arena));
	        } else {
                return Ok(Number::arena_from(n1 >> usize::max_value(), arena));
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1 = Integer::from(n1.get_num());

            let result: Result<usize, _> = (&*n2).try_into();

            match result {
                Ok(n2) => {
                    Ok(Number::arena_from(n1 >> n2, arena))
                }
                Err(_) => {
                    Ok(Number::arena_from(n1 >> usize::max_value(), arena))
                }
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => match usize::try_from(n2.get_num()) {
            Ok(n2) => Ok(Number::arena_from(Integer::from(&*n1 >> n2), arena)),
            _ => {
		        Ok(Number::arena_from(Integer::from(&*n1 >> usize::max_value()),arena))
	        },
        },
        (Number::Integer(n1), Number::Integer(n2)) => {
            let result: Result<usize, _> = (&*n2).try_into();

            match result {
                Ok(n2) => {
                    Ok(Number::arena_from(Integer::from(&*n1 >> n2), arena))
                }
                Err(_) => {
                    Ok(Number::arena_from(Integer::from(&*n1 >> usize::max_value()), arena))
                }
            }
        },
        (Number::Integer(_), n2) => Err(numerical_type_error(ValidType::Integer, n2, stub_gen)),
        (Number::Fixnum(_), n2) => Err(numerical_type_error(ValidType::Integer, n2, stub_gen)),
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn shl(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let shl_atom = atom!("<<");
        functor_stub(shl_atom, 2)
    };

    if n2.is_integer() && n2.is_negative() {
        return shr(n1, neg(n2, arena), arena);
    }

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n1_i = n1.get_num();
            let n2_i = n2.get_num();

            let n1 = Integer::from(n1_i);

            if let Ok(n2) = usize::try_from(n2_i) {
                return Ok(Number::arena_from(n1 << n2, arena));
	        } else {
                return Ok(Number::arena_from(n1 << usize::max_value(), arena));
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1 = Integer::from(n1.get_num());

            match (&*n2).try_into() as Result<u32, _> {
                Ok(n2) => {
                    let n1: u64 = n1.try_into().unwrap();
                    Ok(Number::arena_from(n1 << n2, arena))
                },
                _ => {
			        Ok(Number::arena_from(n1 << usize::max_value(), arena))
		        }
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => match usize::try_from(n2.get_num()) {
            Ok(n2) => Ok(Number::arena_from(Integer::from(&*n1 << n2), arena)),
            _ => {
		        Ok(Number::arena_from(Integer::from(&*n1 << usize::max_value()),arena))
		    }
        },
        (Number::Integer(n1), Number::Integer(n2)) => match (&*n2).try_into() as Result<u32, _> {
            Ok(n2) => {
                let n1: u64 = (&*n1).try_into().unwrap();
                Ok(Number::arena_from(Integer::from(n1 << n2), arena))
            },
            _ => {
		        Ok(Number::arena_from(Integer::from(&*n1 << usize::max_value()),arena))
	        }
        },
        (Number::Integer(_), n2) => Err(numerical_type_error(ValidType::Integer, n2, stub_gen)),
        (Number::Fixnum(_), n2) => Err(numerical_type_error(ValidType::Integer, n2, stub_gen)),
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn and(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let and_atom = atom!("/\\");
        functor_stub(and_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            Ok(Number::arena_from(n1.get_num() & n2.get_num(), arena))
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1 = Integer::from(n1.get_num());
            Ok(Number::arena_from(n1 & &*n2, arena))
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::arena_from(
            &*n1 & Integer::from(n2.get_num()),
            arena,
        )),
        (Number::Integer(n1), Number::Integer(n2)) => {
            Ok(Number::arena_from(Integer::from(&*n1 & &*n2), arena))
        }
        (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn or(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let or_atom = atom!("\\/");
        functor_stub(or_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            Ok(Number::arena_from(n1.get_num() | n2.get_num(), arena))
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1 = Integer::from(n1.get_num());
            Ok(Number::arena_from(n1 | &*n2, arena))
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::arena_from(
            &*n1 | Integer::from(n2.get_num()),
            arena,
        )),
        (Number::Integer(n1), Number::Integer(n2)) => {
            Ok(Number::arena_from(Integer::from(&*n1 | &*n2), arena))
        }
        (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn xor(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let xor_atom = atom!("xor");
        functor_stub(xor_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            Ok(Number::arena_from(n1.get_num() ^ n2.get_num(), arena))
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            let n1 = Integer::from(n1.get_num());
            Ok(Number::arena_from(n1 ^ &*n2, arena))
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::arena_from(
            &*n1 ^ Integer::from(n2.get_num()),
            arena,
        )),
        (Number::Integer(n1), Number::Integer(n2)) => {
            Ok(Number::arena_from(Integer::from(&*n1 ^ &*n2), arena))
        }
        (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, Number::Integer(_)) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
        _ => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn modulus(x: Number, y: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let mod_atom = atom!("mod");
        functor_stub(mod_atom, 2)
    };

    match (x, y) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n2_i = n2.get_num();

            if n2_i == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n1_i = n1.get_num();
                Ok(Number::arena_from(n1_i.rem_floor(n2_i), arena))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            if (&*n2).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n1 = Integer::from(n1.get_num());
                Ok(Number::arena_from(
                    <(Integer, Integer)>::from(n1.div_rem(&*n2)).1,
                    arena,
                ))
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => {
            let n2_i = n2.get_num();

            if n2_i == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n2 = Integer::from(n2_i);
                Ok(Number::arena_from(
                    <(Integer, Integer)>::from((&*n1).div_rem(&n2)).1,
                    arena,
                ))
            }
        }
        (Number::Integer(x), Number::Integer(y)) => {
            if (&*y).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                Ok(Number::arena_from(
                    <(Integer, Integer)>::from((&*x).div_rem(&*y)).1,
                    arena,
                ))
            }
        }
        (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn remainder(x: Number, y: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let rem_atom = atom!("rem");
        functor_stub(rem_atom, 2)
    };

    match (x, y) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n2_i = n2.get_num();

            if n2_i == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n1_i = n1.get_num();
                Ok(Number::arena_from(n1_i % n2_i, arena))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) => {
            if (&*n2).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n1 = Integer::from(n1.get_num());
                Ok(Number::arena_from(n1 % &*n2, arena))
            }
        }
        (Number::Integer(n1), Number::Fixnum(n2)) => {
            let n2_i = n2.get_num();

            if n2_i == 0 {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                let n2 = Integer::from(n2_i);
                Ok(Number::arena_from(&*n1 % n2, arena))
            }
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            if (&*n2).num_eq(&0) {
                Err(zero_divisor_eval_error(stub_gen))
            } else {
                Ok(Number::arena_from(Integer::from(&*n1 % &*n2), arena))
            }
        }
        (Number::Integer(_), n2) | (Number::Fixnum(_), n2) => {
            Err(numerical_type_error(ValidType::Integer, n2, stub_gen))
        }
        (n1, _) => Err(numerical_type_error(ValidType::Integer, n1, stub_gen)),
    }
}

pub(crate) fn gcd(n1: Number, n2: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let gcd_atom = atom!("gcd");
        functor_stub(gcd_atom, 2)
    };

    match (n1, n2) {
        (Number::Fixnum(n1), Number::Fixnum(n2)) => {
            let n1_i = n1.get_num() as isize;
            let n2_i = n2.get_num() as isize;

            if let Some(result) = isize_gcd(n1_i, n2_i) {
                Ok(Number::arena_from(result, arena))
            } else {
                let value: IBig = Integer::from(n1_i).gcd(&Integer::from(n2_i)).into();
                Ok(Number::arena_from(
                    value,
                    arena,
                ))
            }
        }
        (Number::Fixnum(n1), Number::Integer(n2)) | (Number::Integer(n2), Number::Fixnum(n1)) => {
            let n1 = Integer::from(n1.get_num());
            let n2_clone: Integer = (*n2).clone();
            Ok(Number::arena_from(Integer::from(n2_clone.gcd(&n1)), arena))
        }
        (Number::Integer(n1), Number::Integer(n2)) => {
            let n1_clone: Integer = (*n1).clone();
            let n2: isize = (&*n2).try_into().unwrap();
            Ok(Number::arena_from(Integer::from(n1_clone.gcd(&Integer::from(n2))) as IBig, arena))
        }
        (Number::Float(f), _) | (_, Number::Float(f)) => {
            let n = Number::Float(f);
            Err(numerical_type_error(ValidType::Integer, n, stub_gen))
        }
        (Number::Rational(r), _) | (_, Number::Rational(r)) => {
            let n = Number::Rational(r);
            Err(numerical_type_error(ValidType::Integer, n, stub_gen))
        }
    }
}

pub(crate) fn atan2(n1: Number, n2: Number) -> Result<f64, MachineStubGen> {
    if n1.is_zero() && n2.is_zero() {
        let stub_gen = || {
            let is_atom = atom!("is");
            functor_stub(is_atom, 2)
        };

        Err(undefined_eval_error(stub_gen))
    } else {
        let f1 = float(n1)?;
        let f2 = float(n2)?;

        unary_float_fn_template(Number::Float(OrderedFloat(f1)), |f| f.atan2(f2))
    }
}

#[inline]
pub(crate) fn sin(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.sin())
}

#[inline]
pub(crate) fn cos(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.cos())
}

#[inline]
pub(crate) fn tan(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.tan())
}

#[inline]
pub(crate) fn log(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.log(f64::consts::E))
}

#[inline]
pub(crate) fn exp(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.exp())
}

#[inline]
pub(crate) fn asin(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.asin())
}

#[inline]
pub(crate) fn acos(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.acos())
}

#[inline]
pub(crate) fn atan(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.atan())
}

#[inline]
pub(crate) fn asinh(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.asinh())
}

#[inline]
pub(crate) fn acosh(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.acosh())
}

#[inline]
pub(crate) fn atanh(n1: Number) -> Result<f64, MachineStubGen> {
    let stub_gen = || {
        let is_atom = atom!("is");
        functor_stub(is_atom, 2)
    };

    let f1 = try_numeric_result!(result_f(&n1), stub_gen)?;

    try_numeric_result!(if f1 == 1.0 || f1 == -1.0 {
        Err(EvalError::Undefined)
    } else {
        result_f(&Number::Float(OrderedFloat(f1.atanh())))
    },
    stub_gen)
}

#[inline]
pub(crate) fn sinh(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.sinh())
}

#[inline]
pub(crate) fn cosh(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.cosh())
}

#[inline]
pub(crate) fn tanh(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.tanh())
}

#[inline]
pub(crate) fn log10(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.log(10f64))
}

#[inline]
pub(crate) fn float_fractional_part(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.fract())
}

#[inline]
pub(crate) fn float_integer_part(n1: Number) -> Result<f64, MachineStubGen> {
    unary_float_fn_template(n1, |f| f.trunc())
}

#[inline]
pub(crate) fn sqrt(n1: Number) -> Result<f64, MachineStubGen> {
    if n1.is_negative() {
        let stub_gen = || {
            let is_atom = atom!("is");
            functor_stub(is_atom, 2)
        };

        return Err(undefined_eval_error(stub_gen));
    }

    unary_float_fn_template(n1, |f| f.sqrt())
}

#[inline]
pub(crate) fn floor(n1: Number, arena: &mut Arena) -> Number {
    rnd_i(&n1, arena)
}


#[inline]
pub(crate) fn ceiling(n1: Number, arena: &mut Arena) -> Number {
    let n1 = neg(n1, arena);
    let n1 = floor(n1, arena);

    neg(n1, arena)
}

#[inline]
pub(crate) fn truncate(n: Number, arena: &mut Arena) -> Number {
    if n.is_negative() {
        let n = abs(n, arena);
        let n = floor(n, arena);

        neg(n, arena)
    } else {
        floor(n, arena)
    }
}

pub(crate) fn round(n: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    let stub_gen = || {
        let is_atom = atom!("is");
        functor_stub(is_atom, 2)
    };

    let result = add(n, Number::Float(OrderedFloat(0.5f64)), arena);
    let result = try_numeric_result!(result, stub_gen)?;

    Ok(floor(result, arena))
}

pub(crate) fn bitwise_complement(n1: Number, arena: &mut Arena) -> Result<Number, MachineStubGen> {
    match n1 {
        Number::Fixnum(n) => Ok(Number::Fixnum(Fixnum::build_with(!n.get_num()))),
        Number::Integer(n1) => Ok(Number::arena_from(Integer::from(!&*n1), arena)),
        _ => {
            let stub_gen = || {
                let bitwise_atom = atom!("\\");
                functor_stub(bitwise_atom, 2)
            };

            Err(numerical_type_error(ValidType::Integer, n1, stub_gen))
        }
    }
}

impl MachineState {
    #[inline]
    pub fn get_number(&mut self, at: &ArithmeticTerm) -> Result<Number, MachineStub> {
        match at {
            &ArithmeticTerm::Reg(r) => {
		        let value = self.store(self.deref(self[r]));

                match Number::try_from(value) {
                    Ok(n) => Ok(n),
                    Err(_) => self.arith_eval_by_metacall(value),
                }
            }
            &ArithmeticTerm::Interm(i) => {
                Ok(mem::replace(&mut self.interms[i - 1], Number::Fixnum(Fixnum::build_with(0))))
            }
            &ArithmeticTerm::Number(n) => Ok(n),
        }
    }

    pub fn get_rational(
        &mut self,
        at: &ArithmeticTerm,
        caller: impl Fn() -> FunctorStub + 'static,
    ) -> Result<TypedArenaPtr<Rational>, MachineStub> {
        let n = self.get_number(at)?;

        match rational_from_number(n, caller, &mut self.arena) {
            Ok(r) => Ok(r),
            Err(e_gen) => Err(e_gen(self))
        }
    }

    pub(crate) fn arith_eval_by_metacall(&mut self, value: HeapCellValue) -> Result<Number, MachineStub> {
        let stub_gen = || functor_stub(atom!("is"), 2);
        let mut iter = stackful_post_order_iter(&mut self.heap, &mut self.stack, value);

        while let Some(value) = iter.next() {
            if value.get_forwarding_bit() {
                std::mem::drop(iter);

                let (name, arity) = read_heap_cell!(value,
                     (HeapCellValueTag::Atom, (name, arity)) => {
                         (name, arity)
                     }
                     (HeapCellValueTag::Str, s) => {
                         cell_as_atom_cell!(self.heap[s]).get_name_and_arity()
                     }
                     (HeapCellValueTag::Lis | HeapCellValueTag::PStr | HeapCellValueTag::PStrOffset |
                      HeapCellValueTag::PStrLoc) => {
                         (atom!("."), 2)
                     }
                     (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                         let err = self.instantiation_error();
                         return Err(self.error_form(err, stub_gen()));
                     }
                     _ => {
                         unreachable!()
                     }
                );

                let evaluable_error = self.evaluable_error(name, arity);
                return Err(self.error_form(evaluable_error, stub_gen()));
            }

            let value = unmark_cell_bits!(value);

            read_heap_cell!(value,
                (HeapCellValueTag::Atom, (name, arity)) => {
                    if arity == 2 {
                        let a2 = self.interms.pop().unwrap();
                        let a1 = self.interms.pop().unwrap();

                        match name {
                            atom!("+") => self.interms.push(drop_iter_on_err!(
                                self,
                                iter,
                                try_numeric_result!(add(a1, a2, &mut self.arena), stub_gen)
                            )),
                            atom!("-") => self.interms.push(drop_iter_on_err!(
                                self,
                                iter,
                                try_numeric_result!(sub(a1, a2, &mut self.arena), stub_gen)
                            )),
                            atom!("*") => self.interms.push(drop_iter_on_err!(
                                self,
                                iter,
                                try_numeric_result!(mul(a1, a2, &mut self.arena), stub_gen)
                            )),
                            atom!("/") => self.interms.push(
                                drop_iter_on_err!(self, iter, div(a1, a2))
                            ),
                            atom!("**") => self.interms.push(
                                drop_iter_on_err!(self, iter, pow(a1, a2, atom!("is")))
                            ),
                            atom!("^") => self.interms.push(
                                drop_iter_on_err!(self, iter, int_pow(a1, a2, &mut self.arena))
                            ),
                            atom!("max") => self.interms.push(
                                drop_iter_on_err!(self, iter, max(a1, a2))
                            ),
                            atom!("min") => self.interms.push(
                                drop_iter_on_err!(self, iter, min(a1, a2))
                            ),
                            atom!("rdiv") => {
                                let r1 = drop_iter_on_err!(
                                    self,
                                    iter,
                                    rational_from_number(a1, stub_gen, &mut self.arena)
                                );

                                let r2 = drop_iter_on_err!(
                                    self,
                                    iter,
                                    rational_from_number(a2, stub_gen, &mut self.arena)
                                );

                                let result = arena_alloc!(
                                    drop_iter_on_err!(self, iter, rdiv(r1, r2)),
                                    &mut self.arena
                                );

                                self.interms.push(Number::Rational(result));
                            }
                            atom!("//") => self.interms.push(
                                drop_iter_on_err!(self, iter, idiv(a1, a2, &mut self.arena))
                            ),
                            atom!("div") => self.interms.push(
                                drop_iter_on_err!(self, iter, int_floor_div(a1, a2, &mut self.arena))
                            ),
                            atom!(">>") => self.interms.push(
                                drop_iter_on_err!(self, iter, shr(a1, a2, &mut self.arena))
                            ),
                            atom!("<<") => self.interms.push(
                                drop_iter_on_err!(self, iter, shl(a1, a2, &mut self.arena))
                            ),
                            atom!("/\\") => self.interms.push(
                                drop_iter_on_err!(self, iter, and(a1, a2, &mut self.arena))
                            ),
                            atom!("\\/") => self.interms.push(
                                drop_iter_on_err!(self, iter, or(a1, a2, &mut self.arena))
                            ),
                            atom!("xor") => self.interms.push(
                                drop_iter_on_err!(self, iter, xor(a1, a2, &mut self.arena))
                            ),
                            atom!("mod") => self.interms.push(
                                drop_iter_on_err!(self, iter, modulus(a1, a2, &mut self.arena))
                            ),
                            atom!("rem") => self.interms.push(
                                drop_iter_on_err!(self, iter, remainder(a1, a2, &mut self.arena))
                            ),
                            atom!("atan2") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, atan2(a1, a2))
                            ))),
                            atom!("gcd") => self.interms.push(
                                drop_iter_on_err!(self, iter, gcd(a1, a2, &mut self.arena))
                            ),
                            _ => {
                                let evaluable_stub = functor_stub(name, 2);
                                let stub = stub_gen();

                                std::mem::drop(iter);

                                let type_error = self.type_error(ValidType::Evaluable, evaluable_stub);
                                return Err(self.error_form(type_error, stub));
                            }
                        }

                        continue;
                    } else if arity == 1 {
                        let a1 = self.interms.pop().unwrap();

                        match name {
                            atom!("-") => self.interms.push(neg(a1, &mut self.arena)),
                            atom!("+") => self.interms.push(a1),
                            atom!("cos") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, cos(a1))
                            ))),
                            atom!("sin") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, sin(a1))
                            ))),
                            atom!("tan") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, tan(a1))
                            ))),
                            atom!("cosh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, cosh(a1))
                            ))),
                            atom!("sinh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, sinh(a1))
                            ))),
                            atom!("tanh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, tanh(a1))
                            ))),
                            atom!("acosh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, acosh(a1))
                            ))),
                            atom!("asinh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, asinh(a1))
                            ))),
                            atom!("atanh") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, atanh(a1))
                            ))),
                            atom!("log10") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, log10(a1))
                            ))),
                            atom!("float_fractional_part") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, float_fractional_part(a1))
                            ))),
                            atom!("float_integer_part") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, float_integer_part(a1))
                            ))),
                            atom!("sqrt") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, sqrt(a1))
                            ))),
                            atom!("log") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, log(a1))
                            ))),
                            atom!("exp") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, exp(a1))
                            ))),
                            atom!("acos") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, acos(a1))
                            ))),
                            atom!("asin") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, asin(a1))
                            ))),
                            atom!("atan") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, atan(a1))
                            ))),
                            atom!("abs") => self.interms.push(abs(a1, &mut self.arena)),
                            atom!("float") => self.interms.push(Number::Float(OrderedFloat(
                                drop_iter_on_err!(self, iter, float(a1))
                            ))),
                            atom!("truncate") => self.interms.push(truncate(a1, &mut self.arena)),
                            atom!("round") => self.interms.push(drop_iter_on_err!(self, iter, round(a1, &mut self.arena))),
                            atom!("ceiling") => self.interms.push(ceiling(a1, &mut self.arena)),
                            atom!("floor") => self.interms.push(floor(a1, &mut self.arena)),
                            atom!("\\") => self.interms.push(
                                drop_iter_on_err!(self, iter, bitwise_complement(a1, &mut self.arena))
                            ),
                            atom!("sign") => self.interms.push(a1.sign()),
                            _ => {
                                let evaluable_stub = functor_stub(name, 1);
                                std::mem::drop(iter);

                                let type_error = self.type_error(
                                    ValidType::Evaluable,
                                    evaluable_stub,
                                );

                                let stub = stub_gen();
                                return Err(self.error_form(type_error, stub));
                            }
                        }

                        continue;
                    } else if arity == 0 {
                        match name {
                            atom!("pi") => {
                                self.interms.push(Number::Float(OrderedFloat(f64::consts::PI)));
                                continue;
                            }
                            atom!("e") => {
                                self.interms.push(Number::Float(OrderedFloat(f64::consts::E)));
                                continue;
                            }
                            atom!("epsilon") => {
                                self.interms.push(Number::Float(OrderedFloat(f64::EPSILON)));
                                continue;
                            }
                            _ => {
                            }
                        }
                    }

                    std::mem::drop(iter);

                    let evaluable_error = self.evaluable_error(name, arity);
                    let stub = stub_gen();

                    return Err(self.error_form(evaluable_error, stub));
                }
                (HeapCellValueTag::Fixnum, n) => {
                    self.interms.push(Number::Fixnum(n));
                }
                (HeapCellValueTag::F64, fl) => {
                    self.interms.push(Number::Float(*fl));
                }
                (HeapCellValueTag::Cons, ptr) => {
                    match_untyped_arena_ptr!(ptr,
                         (ArenaHeaderTag::Integer, n) => {
                             self.interms.push(Number::Integer(n));
                         }
                         (ArenaHeaderTag::Rational, r) => {
                             self.interms.push(Number::Rational(r));
                         }
                         _ => {
                             std::mem::drop(iter);

                             let type_error = self.type_error(ValidType::Evaluable, value);
                             let stub = stub_gen();

                             return Err(self.error_form(type_error, stub));
                         }
                    )
                }
                (HeapCellValueTag::Var | HeapCellValueTag::AttrVar) => {
                    std::mem::drop(iter);

                    let instantiation_error = self.instantiation_error();
                    let stub = stub_gen();

                    return Err(self.error_form(instantiation_error, stub));
                }
                _ => {
                    std::mem::drop(iter);

                    let type_error = self.type_error(ValidType::Evaluable, value);
                    let stub = stub_gen();

                    return Err(self.error_form(type_error, stub));
                }
            )
        }

        Ok(self.interms.pop().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::mock_wam::*;

    #[test]
    fn arith_eval_by_metacall_tests() {
        let mut wam = MachineState::new();
        let mut op_dir = default_op_dir();

        op_dir.insert(
            (atom!("+"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("-"), Fixity::In),
            OpDesc::build_with(500, YFX as u8),
        );
        op_dir.insert(
            (atom!("-"), Fixity::Pre),
            OpDesc::build_with(200, FY as u8),
        );
        op_dir.insert(
            (atom!("*"), Fixity::In),
            OpDesc::build_with(400, YFX as u8),
        );
        op_dir.insert(
            (atom!("/"), Fixity::In),
            OpDesc::build_with(400, YFX as u8),
        );

        let term_write_result =
            parse_and_write_parsed_term_to_heap(&mut wam, "3 + 4 - 1 + 2.", &op_dir).unwrap();

        assert_eq!(
            wam.arith_eval_by_metacall(heap_loc_as_cell!(term_write_result.heap_loc)),
            Ok(Number::Fixnum(Fixnum::build_with(8))),
        );

        wam.heap.clear();

        let term_write_result =
            parse_and_write_parsed_term_to_heap(&mut wam, "5 * 4 - 1.", &op_dir).unwrap();

        assert_eq!(
            wam.arith_eval_by_metacall(heap_loc_as_cell!(term_write_result.heap_loc)),
            Ok(Number::Fixnum(Fixnum::build_with(19))),
        );

        wam.heap.clear();

        let term_write_result =
            parse_and_write_parsed_term_to_heap(&mut wam, "sign(-1).", &op_dir).unwrap();

        assert_eq!(
            wam.arith_eval_by_metacall(heap_loc_as_cell!(term_write_result.heap_loc)),
            Ok(Number::Fixnum(Fixnum::build_with(-1)))
        );
    }
}
