use l0::ast::{Atom, Term, MachineInstruction, Program, TopLevel, Var};

use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::vec::{Vec};

impl fmt::Display for MachineInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &MachineInstruction::GetStructure(ref a, ref s, ref r) =>
                write!(f, "get_structure {}/{}, X{}", a, s, r),
            &MachineInstruction::PutStructure(ref a, ref s, ref r) =>
                write!(f, "put_structure {}/{}, X{}", a, s, r),
            &MachineInstruction::SetVariable(ref r) =>
                write!(f, "set_variable X{}", r),
            &MachineInstruction::SetValue(ref r) =>
                write!(f, "set_value X{}", r),
            &MachineInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable X{}", r),
            &MachineInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value X{}", r)
        }
    }
}

enum IntTerm<'a> {
    FinishedClause(usize, &'a Atom, &'a Vec<Box<Term>>),
    UnfinishedClause(usize, &'a Atom, &'a Vec<Box<Term>>),
    FinishedAtom(usize, &'a Atom)
}

pub fn compile_query<'a>(t: &'a Term) -> Program
{
    let mut stack : Vec<IntTerm<'a>> = Vec::new();
    let mut variable_allocs : HashMap<&Var, (usize, bool)> = HashMap::new();
    let mut query : Program = Vec::new();

    match t {
        &Term::Clause(ref atom, ref terms) => {
            stack.push(IntTerm::UnfinishedClause(1, atom, terms));
            variable_allocs.insert(atom, (1, true));            
        },
        &Term::Atom(ref atom) => {
            query.push(MachineInstruction::PutStructure(atom.clone(), 0, 1));
            return query;
        },
        &Term::Var(_) => {
            query.push(MachineInstruction::SetVariable(1));
            return query;
        },
    };

    while let Some(int_term) = stack.pop() {
        match int_term {
            IntTerm::UnfinishedClause(r, atom, terms) => {
                stack.push(IntTerm::FinishedClause(r, atom, terms));

                let mut counter : usize = r + 1;
                
                for t in terms {
                    if t.is_variable() && !variable_allocs.contains_key(t.name()) {
                        variable_allocs.insert(t.name(), (counter, false));                        
                    }

                    counter += 1;
                }

                counter = r + terms.len();
                
                for t in terms.iter().rev() {
                    let r = if t.is_variable() {
                        variable_allocs.get(t.name()).unwrap().0
                    } else {
                        counter                        
                    };                    
                    
                    match t.as_ref() {
                        &Term::Atom(ref atom) => 
                            stack.push(IntTerm::FinishedAtom(r, atom)),
                        &Term::Clause(ref atom, ref terms) =>                             
                            stack.push(IntTerm::UnfinishedClause(r, atom, terms)),
                        _ => {}
                    };

                    counter -= 1;
                }
            },
            IntTerm::FinishedAtom(r, atom) =>
                query.push(MachineInstruction::PutStructure(atom.clone(), 0, r)),            
            IntTerm::FinishedClause(r, atom, terms) => {
                query.push(MachineInstruction::PutStructure(atom.clone(), terms.len(), r));

                let mut counter : usize = r + 1;
                
                for t in terms {
                    if let &Term::Var(ref var) = t.as_ref() {
                        let &mut (reg, ref mut seen) = variable_allocs.get_mut(var).unwrap();

                        if !*seen {
                            query.push(MachineInstruction::SetVariable(reg));
                            *seen = true;
                        } else {
                            query.push(MachineInstruction::SetValue(reg));
                        }
                    } else {
                        query.push(MachineInstruction::SetValue(counter));
                    }

                    counter += 1;
                }
            }
        };
    }

    query
}

pub fn compile_fact<'a>(t: &'a Term) -> Program {
    let mut reg : usize = 2;
    let mut queue : VecDeque<(usize, &'a Term)> = VecDeque::new();
    let mut variable_allocs : HashMap<&Var, usize> = HashMap::new();
    let mut fact : Program = Vec::new();

    queue.push_back((1, t));    

    while let Some(t) = queue.pop_front() {        
        match t {
            (r, &Term::Clause(ref atom, ref terms)) => {
                fact.push(MachineInstruction::GetStructure(atom.clone(), terms.len(), r));
                
                let mut counter : usize = reg;
                
                for t in terms {
                    if t.is_variable() && !variable_allocs.contains_key(t.name()) {
                        variable_allocs.insert(t.name(), counter);
                        fact.push(MachineInstruction::UnifyVariable(counter));
                        counter += 1;
                    } else if t.is_variable() {
                        let r = variable_allocs.get(t.name()).unwrap();
                        fact.push(MachineInstruction::UnifyValue(*r));
                    } else {
                        fact.push(MachineInstruction::UnifyVariable(counter));
                        queue.push_back((counter, t));
                        counter += 1;
                    }                                        
                }

                reg = counter;
            },
            (r, &Term::Atom(ref atom)) =>
                fact.push(MachineInstruction::GetStructure(atom.clone(), 0, r)),
            (r, &Term::Var(_)) => {
                fact.push(MachineInstruction::UnifyVariable(r));
                return fact;
            }
        };
    }

    fact
}
