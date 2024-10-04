#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

use crate::allocator::*;
use crate::arena::*;
use crate::atom_table::*;
use crate::debray_allocator::*;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::targets::QueryInstruction;
use crate::types::*;

use crate::parser::ast::*;
use crate::parser::dashu::{Integer, Rational};

use crate::machine::machine_errors::*;

use dashu::base::Abs;
use dashu::base::BitTest;
use num_order::NumOrd;
use ordered_float::{Float, OrderedFloat};

use std::cell::Cell;
use std::cmp::{max, min, Ordering};
use std::convert::TryFrom;
use std::f64;
use std::num::FpCategory;
use std::ops::Div;
use std::vec::Vec;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Number(Number),
}

impl ArithmeticTerm {
    pub(crate) fn interm_or(&self, interm: usize) -> usize {
        if let &ArithmeticTerm::Interm(interm) = self {
            interm
        } else {
            interm
        }
    }
}

impl Default for ArithmeticTerm {
    fn default() -> Self {
        ArithmeticTerm::Number(Number::default())
    }
}

#[derive(Debug)]
pub(crate) struct ArithInstructionIterator<'a> {
    state_stack: Vec<TermIterState<'a>>,
}

pub(crate) type ArithCont = (CodeDeque, Option<ArithmeticTerm>);

impl<'a> ArithInstructionIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack
            .push(TermIterState::subterm_to_state(lvl, term));
    }

    fn from(term: &'a Term) -> Result<Self, ArithmeticError> {
        let state = match term {
            Term::AnonVar => return Err(ArithmeticError::UninstantiatedVar),
            Term::Clause(cell, name, terms) => {
                TermIterState::Clause(Level::Shallow, 0, cell, *name, terms)
            }
            Term::Literal(cell, cons) => TermIterState::Literal(Level::Shallow, cell, cons),
            Term::Cons(..) | Term::PartialString(..) | Term::CompleteString(..) => {
                return Err(ArithmeticError::NonEvaluableFunctor(
                    Literal::Atom(atom!(".")),
                    2,
                ))
            }
            Term::Var(cell, var_ptr) => TermIterState::Var(Level::Shallow, cell, var_ptr.clone()),
        };

        Ok(ArithInstructionIterator {
            state_stack: vec![state],
        })
    }
}

#[derive(Debug)]
pub(crate) enum ArithTermRef<'a> {
    Literal(&'a Literal),
    Op(Atom, usize), // name, arity.
    Var(Level, &'a Cell<VarReg>, VarPtr),
}

impl<'a> Iterator for ArithInstructionIterator<'a> {
    type Item = Result<ArithTermRef<'a>, ArithmeticError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                TermIterState::AnonVar(_) => return Some(Err(ArithmeticError::UninstantiatedVar)),
                TermIterState::Clause(lvl, child_num, cell, name, subterms) => {
                    let arity = subterms.len();

                    if child_num == arity {
                        return Some(Ok(ArithTermRef::Op(name, arity)));
                    } else {
                        self.state_stack.push(TermIterState::Clause(
                            lvl,
                            child_num + 1,
                            cell,
                            name,
                            subterms,
                        ));

                        self.push_subterm(lvl.child_level(), &subterms[child_num]);
                    }
                }
                TermIterState::Literal(_, _, c) => return Some(Ok(ArithTermRef::Literal(c))),
                TermIterState::Var(lvl, cell, var_ptr) => {
                    return Some(Ok(ArithTermRef::Var(lvl, cell, var_ptr)));
                }
                _ => {
                    return Some(Err(ArithmeticError::NonEvaluableFunctor(
                        Literal::Atom(atom!(".")),
                        2,
                    )));
                }
            };
        }

        None
    }
}

#[derive(Debug)]
pub(crate) struct ArithmeticEvaluator<'a> {
    marker: &'a mut DebrayAllocator,
    interm: Vec<ArithmeticTerm>,
    interm_c: usize,
}

pub(crate) trait ArithmeticTermIter<'a> {
    type Iter: Iterator<Item = Result<ArithTermRef<'a>, ArithmeticError>>;

    fn iter(self) -> Result<Self::Iter, ArithmeticError>;
}

impl<'a> ArithmeticTermIter<'a> for &'a Term {
    type Iter = ArithInstructionIterator<'a>;

    fn iter(self) -> Result<Self::Iter, ArithmeticError> {
        ArithInstructionIterator::from(self)
    }
}

fn push_literal(interm: &mut Vec<ArithmeticTerm>, c: &Literal) -> Result<(), ArithmeticError> {
    match c {
        Literal::Fixnum(n) => interm.push(ArithmeticTerm::Number(Number::Fixnum(*n))),
        Literal::Integer(n) => interm.push(ArithmeticTerm::Number(Number::Integer(*n))),
        Literal::Float(n) => interm.push(ArithmeticTerm::Number(Number::Float(*n.as_ptr()))),
        Literal::Rational(n) => interm.push(ArithmeticTerm::Number(Number::Rational(*n))),
        Literal::Atom(name) if name == &atom!("e") => interm.push(ArithmeticTerm::Number(
            Number::Float(OrderedFloat(std::f64::consts::E)),
        )),
        Literal::Atom(name) if name == &atom!("pi") => interm.push(ArithmeticTerm::Number(
            Number::Float(OrderedFloat(std::f64::consts::PI)),
        )),
        Literal::Atom(name) if name == &atom!("epsilon") => interm.push(ArithmeticTerm::Number(
            Number::Float(OrderedFloat(f64::EPSILON)),
        )),
        _ => return Err(ArithmeticError::NonEvaluableFunctor(*c, 0)),
    }

    Ok(())
}

impl<'a> ArithmeticEvaluator<'a> {
    pub(crate) fn new(marker: &'a mut DebrayAllocator, target_int: usize) -> Self {
        ArithmeticEvaluator {
            marker,
            interm: Vec::new(),
            interm_c: target_int,
        }
    }

    fn get_unary_instr(
        &self,
        name: Atom,
        a1: ArithmeticTerm,
        t: usize,
    ) -> Result<Instruction, ArithmeticError> {
        match name {
            atom!("abs") => Ok(Instruction::Abs(a1, t)),
            atom!("-") => Ok(Instruction::Neg(a1, t)),
            atom!("+") => Ok(Instruction::Plus(a1, t)),
            atom!("cos") => Ok(Instruction::Cos(a1, t)),
            atom!("sin") => Ok(Instruction::Sin(a1, t)),
            atom!("tan") => Ok(Instruction::Tan(a1, t)),
            atom!("log") => Ok(Instruction::Log(a1, t)),
            atom!("exp") => Ok(Instruction::Exp(a1, t)),
            atom!("sqrt") => Ok(Instruction::Sqrt(a1, t)),
            atom!("acos") => Ok(Instruction::ACos(a1, t)),
            atom!("asin") => Ok(Instruction::ASin(a1, t)),
            atom!("atan") => Ok(Instruction::ATan(a1, t)),
            atom!("float") => Ok(Instruction::Float(a1, t)),
            atom!("truncate") => Ok(Instruction::Truncate(a1, t)),
            atom!("round") => Ok(Instruction::Round(a1, t)),
            atom!("ceiling") => Ok(Instruction::Ceiling(a1, t)),
            atom!("floor") => Ok(Instruction::Floor(a1, t)),
            atom!("float_integer_part") => Ok(Instruction::FloatIntegerPart(a1, t)),
            atom!("float_fractional_part") => Ok(Instruction::FloatFractionalPart(a1, t)),
            atom!("sign") => Ok(Instruction::Sign(a1, t)),
            atom!("\\") => Ok(Instruction::BitwiseComplement(a1, t)),
            _ => Err(ArithmeticError::NonEvaluableFunctor(Literal::Atom(name), 1)),
        }
    }

    fn get_binary_instr(
        &self,
        name: Atom,
        a1: ArithmeticTerm,
        a2: ArithmeticTerm,
        t: usize,
    ) -> Result<Instruction, ArithmeticError> {
        match name {
            atom!("+") => Ok(Instruction::Add(a1, a2, t)),
            atom!("-") => Ok(Instruction::Sub(a1, a2, t)),
            atom!("/") => Ok(Instruction::Div(a1, a2, t)),
            atom!("//") => Ok(Instruction::IDiv(a1, a2, t)),
            atom!("max") => Ok(Instruction::Max(a1, a2, t)),
            atom!("min") => Ok(Instruction::Min(a1, a2, t)),
            atom!("div") => Ok(Instruction::IntFloorDiv(a1, a2, t)),
            atom!("rdiv") => Ok(Instruction::RDiv(a1, a2, t)),
            atom!("*") => Ok(Instruction::Mul(a1, a2, t)),
            atom!("**") => Ok(Instruction::Pow(a1, a2, t)),
            atom!("^") => Ok(Instruction::IntPow(a1, a2, t)),
            atom!(">>") => Ok(Instruction::Shr(a1, a2, t)),
            atom!("<<") => Ok(Instruction::Shl(a1, a2, t)),
            atom!("/\\") => Ok(Instruction::And(a1, a2, t)),
            atom!("\\/") => Ok(Instruction::Or(a1, a2, t)),
            atom!("xor") => Ok(Instruction::Xor(a1, a2, t)),
            atom!("mod") => Ok(Instruction::Mod(a1, a2, t)),
            atom!("rem") => Ok(Instruction::Rem(a1, a2, t)),
            atom!("gcd") => Ok(Instruction::Gcd(a1, a2, t)),
            atom!("atan2") => Ok(Instruction::ATan2(a1, a2, t)),
            _ => Err(ArithmeticError::NonEvaluableFunctor(Literal::Atom(name), 2)),
        }
    }

    fn incr_interm(&mut self) -> usize {
        let temp = self.interm_c;

        self.interm.push(ArithmeticTerm::Interm(temp));
        self.interm_c += 1;

        temp
    }

    fn instr_from_clause(
        &mut self,
        name: Atom,
        arity: usize,
    ) -> Result<Instruction, ArithmeticError> {
        match arity {
            1 => {
                let a1 = self.interm.pop().unwrap();

                let ninterm = if a1.interm_or(0) == 0 {
                    self.incr_interm()
                } else {
                    self.interm.push(a1);
                    a1.interm_or(0)
                };

                self.get_unary_instr(name, a1, ninterm)
            }
            2 => {
                let a2 = self.interm.pop().unwrap();
                let a1 = self.interm.pop().unwrap();

                let min_interm = min(a1.interm_or(0), a2.interm_or(0));

                let ninterm = if min_interm == 0 {
                    let max_interm = max(a1.interm_or(0), a2.interm_or(0));

                    if max_interm == 0 {
                        self.incr_interm()
                    } else {
                        self.interm.push(ArithmeticTerm::Interm(max_interm));
                        self.interm_c = max_interm + 1;
                        max_interm
                    }
                } else {
                    self.interm.push(ArithmeticTerm::Interm(min_interm));
                    self.interm_c = min_interm + 1;
                    min_interm
                };

                self.get_binary_instr(name, a1, a2, ninterm)
            }
            _ => Err(ArithmeticError::NonEvaluableFunctor(
                Literal::Atom(name),
                arity,
            )),
        }
    }

    pub(crate) fn compile_is(
        &mut self,
        src: &'a Term,
        term_loc: GenContext,
        arg: usize,
    ) -> Result<ArithCont, ArithmeticError> {
        let mut code = CodeDeque::new();

        for term_ref in src.iter()? {
            match term_ref? {
                ArithTermRef::Literal(c) => push_literal(&mut self.interm, c)?,
                ArithTermRef::Var(lvl, cell, name) => {
                    let var_num = name.to_var_num().unwrap();

                    let r = if lvl == Level::Shallow {
                        self.marker
                            .mark_non_callable(var_num, arg, term_loc, cell, &mut code)
                    } else if term_loc.is_last() || cell.get().norm().reg_num() == 0 {
                        let r = self.marker.get_binding(var_num);

                        if r.reg_num() == 0 {
                            self.marker.mark_var::<QueryInstruction>(
                                var_num, lvl, cell, term_loc, &mut code,
                            );
                            cell.get().norm()
                        } else {
                            self.marker.increment_running_count(var_num);
                            r
                        }
                    } else {
                        self.marker.increment_running_count(var_num);
                        cell.get().norm()
                    };

                    self.interm.push(ArithmeticTerm::Reg(r));
                }
                ArithTermRef::Op(name, arity) => {
                    code.push_back(self.instr_from_clause(name, arity)?);
                }
            }
        }

        Ok((code, self.interm.pop()))
    }
}

// integer division rounding function -- 9.1.3.1.
pub(crate) fn rnd_i(n: &'_ Number, arena: &mut Arena) -> Number {
    match n {
        &Number::Integer(i) => {
            let result = (&*i).try_into();
            if let Ok(value) = result {
                fixnum!(Number, value, arena)
            } else {
                *n
            }
        }
        Number::Fixnum(_) => *n,
        &Number::Float(f) => {
            let f = f.floor();

            const I64_MIN_TO_F: OrderedFloat<f64> = OrderedFloat(i64::MIN as f64);
            const I64_MAX_TO_F: OrderedFloat<f64> = OrderedFloat(i64::MAX as f64);

            if I64_MIN_TO_F <= f && f <= I64_MAX_TO_F {
                fixnum!(Number, f.into_inner() as i64, arena)
            } else {
                Number::Integer(arena_alloc!(Integer::from(f.0 as i64), arena))
            }
        }
        Number::Rational(ref r) => {
            let (_, floor) = (r.fract(), r.floor());

            if let Ok(value) = (&floor).try_into() {
                fixnum!(Number, value, arena)
            } else {
                Number::Integer(arena_alloc!(floor, arena))
            }
        }
    }
}

impl From<Fixnum> for Integer {
    #[inline]
    fn from(n: Fixnum) -> Integer {
        Integer::from(n.get_num())
    }
}

// floating point rounding function -- 9.1.4.1.
pub(crate) fn rnd_f(n: &Number) -> f64 {
    match n {
        &Number::Fixnum(n) => n.get_num() as f64,
        Number::Integer(ref n) => n.to_f64().value(),
        &Number::Float(OrderedFloat(f)) => f,
        Number::Rational(ref r) => r.to_f64().value(),
    }
}

// floating point result function -- 9.1.4.2.
pub(crate) fn result_f(n: &Number) -> Result<f64, EvalError> {
    classify_float(rnd_f(n))
}

fn classify_float(f: f64) -> Result<f64, EvalError> {
    match f.classify() {
        FpCategory::Normal | FpCategory::Zero => Ok(f),
        FpCategory::Infinite => {
            if OrderedFloat(f) == OrderedFloat(f64::MAX) {
                Ok(f)
            } else {
                Err(EvalError::FloatOverflow)
            }
        }
        FpCategory::Nan => Err(EvalError::Undefined),
        _ => Ok(f),
    }
}

#[inline]
pub(crate) fn float_fn_to_f(n: i64) -> Result<f64, EvalError> {
    classify_float(n as f64)
}

#[inline]
pub(crate) fn float_i_to_f(n: &Integer) -> Result<f64, EvalError> {
    classify_float(n.to_f64().value())
}

#[inline]
pub(crate) fn float_r_to_f(r: &Rational) -> Result<f64, EvalError> {
    classify_float(r.to_f64().value())
}

#[inline]
pub(crate) fn add_f(f1: f64, f2: f64) -> Result<OrderedFloat<f64>, EvalError> {
    Ok(OrderedFloat(classify_float(f1 + f2)?))
}

#[inline]
pub(crate) fn mul_f(f1: f64, f2: f64) -> Result<OrderedFloat<f64>, EvalError> {
    Ok(OrderedFloat(classify_float(f1 * f2)?))
}

#[inline]
fn div_f(f1: f64, f2: f64) -> Result<OrderedFloat<f64>, EvalError> {
    if FpCategory::Zero == f2.classify() {
        Err(EvalError::ZeroDivisor)
    } else {
        Ok(OrderedFloat(classify_float(f1 / f2)?))
    }
}

impl Div<Number> for Number {
    type Output = Result<Number, EvalError>;

    fn div(self, rhs: Number) -> Self::Output {
        match (self, rhs) {
            (Number::Fixnum(n1), Number::Fixnum(n2)) => Ok(Number::Float(div_f(
                float_fn_to_f(n1.get_num())?,
                float_fn_to_f(n2.get_num())?,
            )?)),
            (Number::Fixnum(n1), Number::Integer(n2)) => Ok(Number::Float(div_f(
                float_fn_to_f(n1.get_num())?,
                float_i_to_f(&n2)?,
            )?)),
            (Number::Integer(n1), Number::Fixnum(n2)) => Ok(Number::Float(div_f(
                float_i_to_f(&n1)?,
                float_fn_to_f(n2.get_num())?,
            )?)),
            (Number::Fixnum(n1), Number::Rational(n2)) => Ok(Number::Float(div_f(
                float_fn_to_f(n1.get_num())?,
                float_r_to_f(&n2)?,
            )?)),
            (Number::Rational(n1), Number::Fixnum(n2)) => Ok(Number::Float(div_f(
                float_r_to_f(&n1)?,
                float_fn_to_f(n2.get_num())?,
            )?)),
            (Number::Fixnum(n1), Number::Float(OrderedFloat(n2))) => {
                Ok(Number::Float(div_f(float_fn_to_f(n1.get_num())?, n2)?))
            }
            (Number::Float(OrderedFloat(n1)), Number::Fixnum(n2)) => {
                Ok(Number::Float(div_f(n1, float_fn_to_f(n2.get_num())?)?))
            }
            (Number::Integer(n1), Number::Integer(n2)) => Ok(Number::Float(div_f(
                float_i_to_f(&n1)?,
                float_i_to_f(&n2)?,
            )?)),
            (Number::Integer(n1), Number::Float(OrderedFloat(n2))) => {
                Ok(Number::Float(div_f(float_i_to_f(&n1)?, n2)?))
            }
            (Number::Float(OrderedFloat(n2)), Number::Integer(n1)) => {
                Ok(Number::Float(div_f(n2, float_i_to_f(&n1)?)?))
            }
            (Number::Integer(n1), Number::Rational(n2)) => Ok(Number::Float(div_f(
                float_i_to_f(&n1)?,
                float_r_to_f(&n2)?,
            )?)),
            (Number::Rational(n2), Number::Integer(n1)) => Ok(Number::Float(div_f(
                float_r_to_f(&n2)?,
                float_i_to_f(&n1)?,
            )?)),
            (Number::Rational(n1), Number::Float(OrderedFloat(n2))) => {
                Ok(Number::Float(div_f(float_r_to_f(&n1)?, n2)?))
            }
            (Number::Float(OrderedFloat(n2)), Number::Rational(n1)) => {
                Ok(Number::Float(div_f(n2, float_r_to_f(&n1)?)?))
            }
            (Number::Float(OrderedFloat(f1)), Number::Float(OrderedFloat(f2))) => {
                Ok(Number::Float(div_f(f1, f2)?))
            }
            (Number::Rational(r1), Number::Rational(r2)) => Ok(Number::Float(div_f(
                float_r_to_f(&r1)?,
                float_r_to_f(&r2)?,
            )?)),
        }
    }
}

impl PartialEq for Number {
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (&Number::Fixnum(n1), &Number::Fixnum(n2)) => n1.eq(&n2),
            (&Number::Fixnum(n1), Number::Integer(ref n2)) => n1.get_num().num_eq(&**n2),
            (Number::Integer(ref n1), &Number::Fixnum(n2)) => n1.num_eq(&n2.get_num()),
            (&Number::Fixnum(n1), Number::Rational(ref n2)) => {
                Integer::from(n1.get_num()).num_eq(&**n2)
            }
            (Number::Rational(ref n1), &Number::Fixnum(n2)) => {
                n1.num_eq(&Integer::from(n2.get_num()))
            }
            (&Number::Fixnum(n1), &Number::Float(n2)) => OrderedFloat(n1.get_num() as f64).eq(&n2),
            (&Number::Float(n1), &Number::Fixnum(n2)) => n1.eq(&OrderedFloat(n2.get_num() as f64)),
            (Number::Integer(ref n1), Number::Integer(ref n2)) => n1.eq(n2),
            (Number::Integer(ref n1), Number::Float(n2)) => {
                OrderedFloat(n1.to_f64().value()).eq(n2)
            }
            (&Number::Float(n1), Number::Integer(ref n2)) => {
                n1.eq(&OrderedFloat(n2.to_f64().value()))
            }
            (Number::Integer(ref n1), Number::Rational(ref n2)) => n1.num_eq(&**n2),
            (Number::Rational(ref n1), Number::Integer(ref n2)) => n1.num_eq(&**n2),
            (Number::Rational(ref n1), &Number::Float(n2)) => {
                OrderedFloat(n1.to_f64().value()).eq(&n2)
            }
            (&Number::Float(n1), Number::Rational(ref n2)) => {
                n1.eq(&OrderedFloat(n2.to_f64().value()))
            }
            (&Number::Float(f1), &Number::Float(f2)) => f1.eq(&f2),
            (Number::Rational(ref r1), Number::Rational(ref r2)) => r1.eq(r2),
        }
    }
}

impl Eq for Number {}

impl PartialOrd<usize> for Number {
    #[inline]
    fn partial_cmp(&self, rhs: &usize) -> Option<Ordering> {
        match self {
            Number::Fixnum(n) => {
                let n = n.get_num();

                if n < 0i64 {
                    Some(Ordering::Less)
                } else {
                    (n as usize).partial_cmp(rhs)
                }
            }
            Number::Integer(n) => Some((n).num_cmp(rhs)),
            Number::Rational(r) => Some((r).num_cmp(&Integer::from(*rhs))),
            Number::Float(f) => f.partial_cmp(&OrderedFloat(*rhs as f64)),
        }
    }
}

impl PartialEq<usize> for Number {
    #[inline]
    fn eq(&self, rhs: &usize) -> bool {
        match self {
            Number::Fixnum(n) => {
                let n = n.get_num();

                if n < 0i64 {
                    false
                } else {
                    (n as usize).eq(rhs)
                }
            }
            Number::Integer(n) => (n).num_eq(rhs),
            Number::Rational(r) => (r).num_eq(&Integer::from(*rhs)),
            Number::Float(f) => f.eq(&OrderedFloat(*rhs as f64)),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, rhs: &Number) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl Ord for Number {
    fn cmp(&self, rhs: &Number) -> Ordering {
        match (self, rhs) {
            (&Number::Fixnum(n1), &Number::Fixnum(n2)) => n1.get_num().cmp(&n2.get_num()),
            (&Number::Fixnum(n1), Number::Integer(n2)) => Integer::from(n1.get_num()).cmp(n2),
            (Number::Integer(n1), &Number::Fixnum(n2)) => (**n1).cmp(&Integer::from(n2.get_num())),
            (&Number::Fixnum(n1), Number::Rational(n2)) => Rational::from(n1.get_num()).cmp(n2),
            (Number::Rational(n1), &Number::Fixnum(n2)) => {
                (**n1).cmp(&Rational::from(n2.get_num()))
            }
            (&Number::Fixnum(n1), &Number::Float(n2)) => OrderedFloat(n1.get_num() as f64).cmp(&n2),
            (&Number::Float(n1), &Number::Fixnum(n2)) => n1.cmp(&OrderedFloat(n2.get_num() as f64)),
            (&Number::Integer(n1), &Number::Integer(n2)) => (*n1).cmp(&*n2),
            (&Number::Integer(n1), Number::Float(n2)) => OrderedFloat(n1.to_f64().value()).cmp(n2),
            (&Number::Float(n1), Number::Integer(ref n2)) => {
                n1.cmp(&OrderedFloat(n2.to_f64().value()))
            }
            (&Number::Integer(n1), &Number::Rational(n2)) => {
                (*n1).num_partial_cmp(&*n2).unwrap_or(Ordering::Less)
            }
            (&Number::Rational(n1), &Number::Integer(n2)) => {
                (*n1).num_partial_cmp(&*n2).unwrap_or(Ordering::Less)
            }
            (&Number::Rational(n1), &Number::Float(n2)) => {
                OrderedFloat(n1.to_f64().value()).cmp(&n2)
            }
            (&Number::Float(n1), &Number::Rational(n2)) => {
                n1.cmp(&OrderedFloat(n2.to_f64().value()))
            }
            (&Number::Float(f1), &Number::Float(f2)) => f1.cmp(&f2),
            (&Number::Rational(r1), &Number::Rational(r2)) => (*r1).cmp(&*r2),
        }
    }
}

impl TryFrom<HeapCellValue> for Number {
    type Error = ();

    #[inline]
    fn try_from(value: HeapCellValue) -> Result<Number, Self::Error> {
        read_heap_cell!(value,
           (HeapCellValueTag::Cons, c) => {
               match_untyped_arena_ptr!(c,
                  (ArenaHeaderTag::Integer, n) => {
                      Ok(Number::Integer(n))
                  }
                  (ArenaHeaderTag::Rational, n) => {
                      Ok(Number::Rational(n))
                  }
                  _ => {
                      Err(())
                  }
               )
           }
           (HeapCellValueTag::F64, n) => {
               Ok(Number::Float(*n))
           }
           (HeapCellValueTag::Fixnum | HeapCellValueTag::CutPoint, n) => {
               Ok(Number::Fixnum(n))
           }
           _ => {
               Err(())
           }
        )
    }
}

// Computes n ^ power. Ignores the sign of power.
pub(crate) fn binary_pow(mut n: Integer, power: &Integer) -> Integer {
    let mut power = power.abs();

    if power.is_zero() {
        return Integer::ONE;
    }

    let mut oddand = Integer::ONE;

    while power.num_gt(&1) {
        if power.bit(0) {
            oddand *= &n;
        }

        n = n.pow(2);
        power >>= 1;
    }

    n * oddand
}
