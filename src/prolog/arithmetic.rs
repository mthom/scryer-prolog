use prolog::ast::*;
use prolog::fixtures::*;

use std::cell::Cell;
use std::cmp::{min, max};
use std::vec::Vec;

pub struct ArithExprIterator<'a> {
    state_stack: Vec<IteratorState<'a>>
}

impl<'a> ArithExprIterator<'a> {
    fn push_clause(&mut self, child_num: usize, ct: ClauseType<'a>, child_terms: &'a Vec<Box<Term>>)
    {
        self.state_stack.push(IteratorState::Clause(child_num, ct, child_terms));
    }

    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(IteratorState::to_state(lvl, term));
    }

    fn push_final_cons(&mut self, lvl: Level, cell: &'a Cell<RegType>, head: &'a Term, tail: &'a Term)
    {
        self.state_stack.push(IteratorState::FinalCons(lvl, cell, head, tail));
    }

    fn new(term: &'a Term) -> Result<Self, ArithmeticError> {
        let state = match term {
            &Term::AnonVar =>
                return Err(ArithmeticError::InvalidTerm),
            &Term::Clause(_, _, ref terms) =>
                IteratorState::Clause(0, ClauseType::Root, terms),
            &Term::Constant(ref cell, ref cons) =>
                IteratorState::Constant(Level::Shallow, cell, cons),
            &Term::Cons(_, _, _) =>
                return Err(ArithmeticError::InvalidTerm),
            &Term::Var(ref cell, ref var) =>
                IteratorState::Var(Level::Shallow, cell, var)
        };

        Ok(ArithExprIterator { state_stack: vec![state] })
    }
}

impl Term {
    pub fn arith_expr_iter<'a>(&'a self) -> Result<ArithExprIterator<'a>, ArithmeticError> {
        ArithExprIterator::new(self)
    }
}

impl<'a> Iterator for ArithExprIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                IteratorState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                IteratorState::Clause(child_num, ct, child_terms) => {
                    if child_num == child_terms.len() {
                        return Some(TermRef::Clause(ct, child_terms));
                    } else {
                        self.push_clause(child_num + 1, ct, child_terms);
                        self.push_subterm(ct.level_of_subterms(), child_terms[child_num].as_ref());
                    }
                },
                IteratorState::InitialCons(lvl, cell, head, tail) => {
                    self.push_final_cons(lvl, cell, head, tail);
                    self.push_subterm(Level::Deep, tail);
                    self.push_subterm(Level::Deep, head);
                },
                IteratorState::FinalCons(lvl, cell, head, tail) =>
                    return Some(TermRef::Cons(lvl, cell, head, tail)),
                IteratorState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                IteratorState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var))
            };
        }

        None
    }
}

pub struct ArithmeticEvaluator<'a> {
    bindings: &'a AllocVarDict<'a>,
    interm: Vec<ArithmeticTerm>,
    interm_c: usize
}

impl<'a> ArithmeticEvaluator<'a> {
    pub fn new(bindings: &'a AllocVarDict<'a>) -> Self {
        ArithmeticEvaluator { bindings, interm: Vec::new(), interm_c: 1 }
    }

    fn get_un_instr(name: &Atom, a1: ArithmeticTerm, t: ArithEvalPlace)
                    -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match name.as_str() {
            "-" => Ok(ArithmeticInstruction::Neg(a1, t)),
             _  => Err(ArithmeticError::InvalidOp)
        }
    }

    fn gen_bin_instr(name: &Atom, a1: ArithmeticTerm, a2: ArithmeticTerm, t: ArithEvalPlace)
                     -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match name.as_str() {
            "+"   => Ok(ArithmeticInstruction::Add(a1, a2, t)),
            "-"   => Ok(ArithmeticInstruction::Sub(a1, a2, t)),
            "//"  => Ok(ArithmeticInstruction::IDiv(a1, a2, t)),
            "div" => Ok(ArithmeticInstruction::IDiv(a1, a2, t)),
            "*"   => Ok(ArithmeticInstruction::Mul(a1, a2, t)),
             _    => Err(ArithmeticError::InvalidOp)
        }
    }

    fn incr_interm(&mut self) -> usize {
        let temp = self.interm_c;

        self.interm.push(ArithmeticTerm::Interm(temp));
        self.interm_c += 1;

        temp
    }

    fn instr_from_clause(&mut self, name: &Atom, terms: &Vec<Box<Term>>, deep: bool)
                         -> Result<ArithmeticInstruction, ArithmeticError>
    {
        match terms.len() {
            1 => {
                let a1 = self.interm.pop().unwrap();

                if deep {
                    let ninterm = if a1.interm_or(0) == 0 {
                        self.incr_interm()
                    } else {
                        self.interm.push(a1.clone());
                        a1.interm_or(0)
                    };

                    Self::get_un_instr(name, a1, ArithEvalPlace::Interm(ninterm))
                } else {
                    Self::get_un_instr(name, a1, ArithEvalPlace::Reg(RegType::Temp(2)))
                }
            },
            2 => {
                let a2 = self.interm.pop().unwrap();
                let a1 = self.interm.pop().unwrap();

                if deep {
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

                    Self::gen_bin_instr(name, a1, a2, ArithEvalPlace::Interm(ninterm))
                } else {
                    Self::gen_bin_instr(name, a1, a2, ArithEvalPlace::Reg(RegType::Temp(2)))
                }
            },
            _ => Err(ArithmeticError::InvalidOp)
        }
    }

    fn push_constant(&mut self, c: &Constant) -> Result<(), ArithmeticError> {
        match c {
            &Constant::Float(fl) =>
                self.interm.push(ArithmeticTerm::Float(fl)),
            &Constant::Integer(ref bi) =>
                self.interm.push(ArithmeticTerm::Integer(bi.clone())),
            _ =>
                return Err(ArithmeticError::InvalidAtom),
        }

        Ok(())
    }

    pub fn eval(&mut self, term: &Term) -> Result<Code, ArithmeticError> {
        let mut code = Vec::new();

        for term_ref in term.arith_expr_iter()? {
            match term_ref {
                TermRef::Constant(_, _, c) =>
                    try!(self.push_constant(c)),
                TermRef::Var(_, vr, name) => {
                    let r = if vr.get().norm().reg_num() == 0 {
                        match self.bindings.get(name) {
                            Some(&VarData::Temp(_, t, _)) if t != 0 => RegType::Temp(t),
                            Some(&VarData::Perm(p)) => RegType::Perm(p),
                            _ => return Err(ArithmeticError::UninstantiatedVar)
                        }
                    } else {
                        vr.get().norm()
                    };

                    self.interm.push(ArithmeticTerm::Reg(r));
                },
                TermRef::Clause(ClauseType::Deep(_, _, name), terms) => {
                    code.push(Line::Arithmetic(self.instr_from_clause(name, terms, true)?));
                },
                TermRef::Clause(ClauseType::Root, terms) => {
                    let name = term.name().unwrap();
                    code.push(Line::Arithmetic(self.instr_from_clause(name, terms, false)?));
                },
                _ =>
                    return Err(ArithmeticError::InvalidTerm)
            }
        }

        if let Some(arith_term) = self.interm.pop() {
            match arith_term {
                ArithmeticTerm::Integer(n) => {
                    let n = Constant::Integer(n);
                    code.push(query![put_constant!(Level::Shallow, n, temp_v!(2))]);
                },
                ArithmeticTerm::Float(n) => {
                    let n = Constant::Float(n);
                    code.push(query![put_constant!(Level::Shallow, n, temp_v!(2))]);
                },
                ArithmeticTerm::Reg(r) =>
                    code.push(query![put_value!(r, 2)]),                
                _ => return Err(ArithmeticError::InvalidTerm)
            };
        }

        Ok(code)
    }
}
