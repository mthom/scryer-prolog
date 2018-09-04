use prolog_parser::ast::*;

use prolog::ast::*;
use std::cell::Cell;
use std::cmp::{min, max};
use std::rc::Rc;
use std::vec::Vec;

pub struct ArithInstructionIterator<'a> {
    state_stack: Vec<TermIterState<'a>>
}

pub type ArithCont = (Code, Option<ArithmeticTerm>);

impl<'a> ArithInstructionIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(TermIterState::subterm_to_state(lvl, term));
    }

    fn new(term: &'a Term) -> Result<Self, ArithmeticError> {
        let state = match term {
            &Term::AnonVar =>
                return Err(ArithmeticError::InvalidTerm),
            &Term::Clause(ref cell, ref name, ref terms, fixity) =>
                match ClauseType::from(name.clone(), terms.len(), fixity) {
                    ct @ ClauseType::Named(..) | ct @ ClauseType::Op(..) =>
                        Ok(TermIterState::Clause(Level::Shallow, 0, cell, ct, terms)),
                    _ => Err(ArithmeticError::InvalidOp)
                }?,
            &Term::Constant(ref cell, ref cons) =>
                TermIterState::Constant(Level::Shallow, cell, cons),
            &Term::Cons(_, _, _) =>
                return Err(ArithmeticError::InvalidTerm),
            &Term::Var(ref cell, ref var) =>
                TermIterState::Var(Level::Shallow, cell, var.clone())
        };

        Ok(ArithInstructionIterator { state_stack: vec![state] })
    }
}

pub enum ArithTermRef<'a> {
    Constant(&'a Constant),
    Op(ClauseName, usize), // name, arity.
    Var(&'a Cell<VarReg>, Rc<Var>)
}

impl<'a> Iterator for ArithInstructionIterator<'a> {
    type Item = Result<ArithTermRef<'a>, ArithmeticError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                TermIterState::AnonVar(_) =>
                    return Some(Err(ArithmeticError::UninstantiatedVar)),
                TermIterState::Clause(lvl, child_num, cell, ct, subterms) => {
                    let arity = subterms.len();                    

                    if child_num == arity {
                        return Some(Ok(ArithTermRef::Op(ct.name(), arity)));
                    } else {
                        self.state_stack.push(TermIterState::Clause(lvl, child_num + 1, cell, ct, subterms));
                        self.push_subterm(lvl, subterms[child_num].as_ref());
                    }
                },
                TermIterState::Constant(_, _, c) =>
                    return Some(Ok(ArithTermRef::Constant(c))),
                TermIterState::Var(_, cell, var) =>
                    return Some(Ok(ArithTermRef::Var(cell, var.clone()))),
                _ =>
                    return Some(Err(ArithmeticError::InvalidTerm))
            };
        }

        None
    }
}

pub struct ArithmeticEvaluator<'a> {
    bindings: &'a AllocVarDict,
    interm: Vec<ArithmeticTerm>,
    interm_c: usize
}

pub trait ArithmeticTermIter<'a> {
    type Iter : Iterator<Item=Result<ArithTermRef<'a>, ArithmeticError>>;

    fn iter(self) -> Result<Self::Iter, ArithmeticError>;
}

impl<'a> ArithmeticTermIter<'a> for &'a Term {
    type Iter = ArithInstructionIterator<'a>;

    fn iter(self) -> Result<Self::Iter, ArithmeticError> {
        ArithInstructionIterator::new(self)
    }
}

impl<'a> ArithmeticEvaluator<'a>
{
    pub fn new(bindings: &'a AllocVarDict, target_int: usize) -> Self {
        ArithmeticEvaluator { bindings, interm: Vec::new(), interm_c: target_int }
    }

    fn get_unary_instr(name: ClauseName, a1: ArithmeticTerm, t: usize)
                       -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match name.as_str() {
            "abs" => Ok(ArithmeticInstruction::Abs(a1, t)),
            "-" => Ok(ArithmeticInstruction::Neg(a1, t)),
             _  => Err(ArithmeticError::InvalidOp)
        }
    }

    fn get_binary_instr(name: ClauseName, a1: ArithmeticTerm, a2: ArithmeticTerm, t: usize)
                        -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match name.as_str() {
            "+"    => Ok(ArithmeticInstruction::Add(a1, a2, t)),
            "-"    => Ok(ArithmeticInstruction::Sub(a1, a2, t)),
            "/"    => Ok(ArithmeticInstruction::Div(a1, a2, t)),
            "//"   => Ok(ArithmeticInstruction::IDiv(a1, a2, t)),
            "div"  => Ok(ArithmeticInstruction::FIDiv(a1, a2, t)),
            "rdiv" => Ok(ArithmeticInstruction::RDiv(a1, a2, t)),
            "*"    => Ok(ArithmeticInstruction::Mul(a1, a2, t)),
            "**"    => Ok(ArithmeticInstruction::Pow(a1, a2, t)),
            ">>"   => Ok(ArithmeticInstruction::Shr(a1, a2, t)),
            "<<"   => Ok(ArithmeticInstruction::Shl(a1, a2, t)),
            "/\\"  => Ok(ArithmeticInstruction::And(a1, a2, t)),
            "\\/"  => Ok(ArithmeticInstruction::Or(a1, a2, t)),
            "xor"  => Ok(ArithmeticInstruction::Xor(a1, a2, t)),
            "mod"  => Ok(ArithmeticInstruction::Mod(a1, a2, t)),
            "rem"  => Ok(ArithmeticInstruction::Rem(a1, a2, t)),
             _     => Err(ArithmeticError::InvalidOp)
        }
    }

    fn incr_interm(&mut self) -> usize {
        let temp = self.interm_c;

        self.interm.push(ArithmeticTerm::Interm(temp));
        self.interm_c += 1;

        temp
    }

    fn instr_from_clause(&mut self, name: ClauseName, arity: usize)
                         -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match arity {
            1 => {
                let a1 = self.interm.pop().unwrap();

                let ninterm = if a1.interm_or(0) == 0 {
                    self.incr_interm()
                } else {
                    self.interm.push(a1.clone());
                    a1.interm_or(0)
                };

                Self::get_unary_instr(name, a1, ninterm)
            },
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

                Self::get_binary_instr(name, a1, a2, ninterm)
            },
            _ => Err(ArithmeticError::InvalidOp)
        }
    }

    fn push_constant(&mut self, c: &Constant) -> Result<(), ArithmeticError> {
        match c {
            &Constant::Number(ref n) =>
                self.interm.push(ArithmeticTerm::Number(n.clone())),
            _ =>
                return Err(ArithmeticError::InvalidAtom),
        }

        Ok(())
    }

    pub fn eval<Iter>(&mut self, src: Iter) -> Result<ArithCont, ArithmeticError>
        where Iter: ArithmeticTermIter<'a>
    {
        let mut code = vec![];

        for term_ref in src.iter()?
        {
            match term_ref? {
                ArithTermRef::Constant(c) => self.push_constant(c)?,
                ArithTermRef::Var(cell, name) => {
                    let r = if cell.get().norm().reg_num() == 0 {
                        match self.bindings.get(&name) {
                            Some(&VarData::Temp(_, t, _)) if t != 0 => RegType::Temp(t),
                            Some(&VarData::Perm(p)) if p != 0 => RegType::Perm(p),
                            _ => return Err(ArithmeticError::UninstantiatedVar)
                        }
                    } else {
                        cell.get().norm()
                    };

                    self.interm.push(ArithmeticTerm::Reg(r));
                },
                ArithTermRef::Op(name, arity) => {
                    code.push(Line::Arithmetic(self.instr_from_clause(name, arity)?));
                }
            }
        }

        Ok((code, self.interm.pop()))
    }
}

