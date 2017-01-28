use l1::ast::{Atom, CompiledFact, CompiledQuery, FactInstruction,
              Level, QueryInstruction, Reg, Term, TermRef, Var};
use l1::iterators::{FactIterator, QueryIterator};

use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::vec::Vec;

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &QueryInstruction::Call(ref name, ref arity) =>
                write!(f, "call {}/{}", name, arity),
            &QueryInstruction::PutStructure(ref lvl, ref a, ref s, ref r) =>
                write!(f, "put_structure {}/{}, {}{}", a, s, lvl, r),
            &QueryInstruction::PutValue(ref a, ref x) =>
                write!(f, "put_value X{}, A{}", x, a),
            &QueryInstruction::PutVariable(ref a, ref x) =>
                write!(f, "put_variable X{}, A{}", x, a),
            &QueryInstruction::SetVariable(ref r) =>
                write!(f, "set_variable X{}", r),
            &QueryInstruction::SetValue(ref r) =>
                write!(f, "set_value X{}", r),
        }
    }
}

impl fmt::Display for FactInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FactInstruction::GetStructure(ref lvl, ref a, ref s, ref r) =>
                write!(f, "get_structure {}/{}, {}{}", a, s, lvl, r),
            &FactInstruction::GetValue(ref a, ref x) =>
                write!(f, "get_value X{}, A{}", x, a),
            &FactInstruction::GetVariable(ref a, ref x) =>
                write!(f, "get_variable X{}, A{}", x, a),
            &FactInstruction::Proceed =>
                write!(f, "proceed"),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable X{}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value X{}", r)
        }
    }
}

struct TermMarker<'a> {    
    bindings: HashMap<&'a Var, Reg>,
    arg_c:    usize,
    norm_c:   usize
}

impl<'a> TermMarker<'a> {
    fn new(term: &'a Term) -> TermMarker<'a> {
        TermMarker { bindings: HashMap::new(),
                     arg_c:    1,
                     norm_c:   term.subterms() + 1 }
    }

    fn contains_var(&self, var: &'a Var) -> bool {
        self.bindings.contains_key(var)
    }

    fn get(&self, var: &'a Var) -> Reg {
        *self.bindings.get(var).unwrap()
    }

    fn insert(&mut self, var: &'a Var, r: Reg) {
        self.bindings.insert(var, r);
    }
    
    fn mark_non_var(&mut self, lvl: Level, cell: &Cell<usize>) {
        if cell.get() == 0 {            
            match lvl {
                Level::Deep => {
                    let norm = self.norm_c;
                    self.norm_c += 1;
                    cell.set(norm);
                },            
                Level::Shallow => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    cell.set(arg);
                }
            };
        }
    }

    fn mark_var(&mut self, lvl: Level, var: &'a Var) -> Reg {
        if self.contains_var(var) {
            let reg = self.get(var);

            match lvl {
                Level::Deep => Reg::Norm(reg.norm()),
                Level::Shallow if reg.has_arg() => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    
                    Reg::ArgAndNorm(arg, reg.norm())
                },
                Level::Shallow => {
                    let norm = reg.norm();
                    let reg  = Reg::ArgAndNorm(self.arg_c, norm);

                    self.arg_c += 1;
                    self.insert(var, reg);

                    reg
                }
            }
        } else {
            let reg = match lvl {
                Level::Deep    => Reg::Norm(self.norm_c),
                Level::Shallow => {
                    let reg = Reg::ArgAndNorm(self.arg_c, self.norm_c);
                    self.arg_c += 1;
                    reg
                }
            };

            self.norm_c += 1;
            self.insert(var, reg);
            reg
        }
    }
}

trait CompilationTarget<'a> {
    type Iterator : Iterator<Item=TermRef<'a>>;

    fn iter(&'a Term) -> Self::Iterator;

    fn to_structure(Level, Atom, usize, usize) -> Self;

    fn argument_to_variable(usize, usize) -> Self;
    fn argument_to_value(usize, usize) -> Self;
    fn subterm_to_variable(usize) -> Self;
    fn subterm_to_value(usize) -> Self;
}

impl<'a> CompilationTarget<'a> for FactInstruction {
    type Iterator = FactIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        term.breadth_first_iter()
    }

    fn to_structure(lvl: Level, atom: Atom, arity: usize, cell_num: usize) -> Self {        
        FactInstruction::GetStructure(lvl, atom, arity, cell_num)
    }

    fn argument_to_variable(arg: usize, val: usize) -> Self {
        FactInstruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: usize, val: usize) -> Self {
        FactInstruction::GetValue(arg, val)
    }

    fn subterm_to_variable(val: usize) -> Self {
        FactInstruction::UnifyVariable(val)
    }

    fn subterm_to_value(val: usize) -> Self {
        FactInstruction::UnifyValue(val)
    }
}

impl<'a> CompilationTarget<'a> for QueryInstruction {
    type Iterator = QueryIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        term.post_order_iter()
    }

    fn to_structure(lvl: Level, atom: Atom, arity: usize, cell_num: usize) -> Self {
        QueryInstruction::PutStructure(lvl, atom, arity, cell_num)
    }

    fn argument_to_variable(arg: usize, val: usize) -> Self {
        QueryInstruction::PutVariable(arg, val)
    }

    fn argument_to_value(arg: usize, val: usize) -> Self {
        QueryInstruction::PutValue(arg, val)
    }

    fn subterm_to_variable(val: usize) -> Self {
        QueryInstruction::SetVariable(val)
    }

    fn subterm_to_value(val: usize) -> Self {
        QueryInstruction::SetValue(val)
    }
}

fn to_structure<'a, Target>(tm: &mut TermMarker<'a>,
                            lvl: Level,
                            name: &'a Atom,
                            cell: &'a Cell<usize>,
                            arity: usize)
                            -> Target
    where Target: CompilationTarget<'a>
{
    tm.mark_non_var(lvl, cell);
    Target::to_structure(lvl, name.clone(), arity, cell.get())
}

fn non_var_subterm<'a, Target>(tm: &mut TermMarker<'a>, cell: &'a Cell<usize>)
                               -> Target
    where Target: CompilationTarget<'a>
{
    tm.mark_non_var(Level::Deep, cell);
    Target::subterm_to_value(cell.get()) // should be to_value??
}

fn var_term<'a, Target>(tm: &mut TermMarker<'a>,
                        lvl: Level,
                        cell: &'a Cell<Reg>,
                        var: &'a Var)
                        -> Target
    where Target: CompilationTarget<'a>
{
    if !tm.contains_var(var) {
        let reg = tm.mark_var(lvl, var);
        cell.set(reg);
        
        match reg {
            Reg::ArgAndNorm(arg, norm) =>
                Target::argument_to_variable(arg, norm),
            Reg::Norm(norm) =>
                Target::subterm_to_variable(norm)
        }
    } else {
        let reg = tm.mark_var(lvl, var);
        cell.set(reg);
        
        match reg {
            Reg::ArgAndNorm(arg, norm) =>
                Target::argument_to_value(arg, norm),
            Reg::Norm(norm) =>
                Target::subterm_to_value(norm)
        }
    }
}

fn subterm_to_instr<'a, Target>(tm: &mut TermMarker<'a>,
                                subterm: &'a Term)
                                -> Target
    where Target: CompilationTarget<'a>
{
    match subterm {
        &Term::Atom(ref cell, _) | &Term::Clause(ref cell, _, _) =>
            non_var_subterm(tm, cell),
        &Term::Var(ref cell, ref var) =>
            var_term(tm, Level::Deep, cell, var)
    }
}

fn compile_target<'a, Target>(term: &'a Term) -> Vec<Target>
    where Target: CompilationTarget<'a>
{
    let iter       = Target::iter(term);
    let mut target = Vec::<Target>::new();
    let mut marker = TermMarker::new(term);

    for term in iter {
        match term {
            TermRef::Atom(lvl, term, atom) =>
                target.push(to_structure(&mut marker, lvl, atom, term, 0)),
            TermRef::Clause(lvl, term, atom, terms) => {
                target.push(to_structure(&mut marker, lvl, atom, term, terms.len()));

                for subterm in terms {
                    target.push(subterm_to_instr(&mut marker, subterm.as_ref()));
                }
            },
            TermRef::Var(lvl @ Level::Shallow, ref cell, ref var) =>
                target.push(var_term(&mut marker, lvl, cell, var)),
            _ => {}
        };
    }

    target
}

pub fn compile_fact(term: &Term) -> CompiledFact {
    let mut compiled_fact = compile_target(term);

    compiled_fact.push(FactInstruction::Proceed);
    compiled_fact
}

pub fn compile_query(term: &Term) -> CompiledQuery {
    let mut compiled_query = compile_target(term);

    if let &Term::Clause(_, ref atom, ref terms) = term {
        compiled_query.push(QueryInstruction::Call(atom.clone(), terms.len()));
    }

    compiled_query
}
