use l0::ast::{Atom, Term, FactInstruction, QueryInstruction, Var};
use l0::iterators::{BreadthFirstIterator, PostOrderIterator};

use std::collections::{HashSet};
use std::fmt;
use std::vec::{Vec};

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &QueryInstruction::PutStructure(ref a, ref s, ref r) =>
                write!(f, "put_structure {}/{}, X{}", a, s, r),
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
            &FactInstruction::GetStructure(ref a, ref s, ref r) =>
                write!(f, "get_structure {}/{}, X{}", a, s, r),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable X{}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value X{}", r)
        }
    }
}

pub trait CompilationTarget<'a> {
    type Iterator : Iterator<Item=&'a Term>;
    
    fn iter(term: &'a Term) -> Self::Iterator;

    fn to_structure(name: Atom, arity: usize, cell_num: usize) -> Self;
    fn to_value(cell_num: usize) -> Self;
    fn to_variable(cell_num: usize) -> Self;
}

impl<'a> CompilationTarget<'a> for FactInstruction {
    type Iterator = BreadthFirstIterator<'a>;
    
    fn iter(term: &'a Term) -> Self::Iterator {
        term.breadth_first_iter()
    }

    fn to_structure(name: Atom, arity: usize, cell_num: usize) -> Self {
        FactInstruction::GetStructure(name, arity, cell_num)
    }

    fn to_value(cell_num: usize) -> Self {
        FactInstruction::UnifyValue(cell_num)
    }

    fn to_variable(cell_num: usize) -> Self {
        FactInstruction::UnifyVariable(cell_num)
    }
}

impl<'a> CompilationTarget<'a> for QueryInstruction {
    type Iterator = PostOrderIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        term.post_order_iter()
    }

    fn to_structure(name: Atom, arity: usize, cell_num: usize) -> Self {
        QueryInstruction::PutStructure(name, arity, cell_num)
    }

    fn to_value(cell_num: usize) -> Self {
        QueryInstruction::SetValue(cell_num)
    }

    fn to_variable(cell_num: usize) -> Self {
        QueryInstruction::SetVariable(cell_num)
    }
}

fn subterm_to_instr<'a, Target>(subterm:  &'a Term,
                                bindings: &mut HashSet<&'a Var>)
                                -> Target
    where Target: CompilationTarget<'a>
{
    match subterm {
        &Term::Atom(ref cell_num, _) =>
            Target::to_value(cell_num.get()),
        &Term::Var(ref cell_num, ref atom) if bindings.contains(atom) =>
            Target::to_value(cell_num.get()),
        &Term::Var(ref cell_num, ref atom) => {
            bindings.insert(atom);
            Target::to_variable(cell_num.get())
        },
        &Term::Clause(ref cell_num, _, _) =>
            Target::to_value(cell_num.get())
    }
}

pub fn compile_target<'a, Target>(term: &'a Term) -> Vec<Target>
    where Target: CompilationTarget<'a>
{
    let mut iter     = Target::iter(term);
    let mut target   = Vec::<Target>::new();
    let mut bindings = HashSet::new();

    while let Some(term) = iter.next() {
        match term {
            &Term::Atom(ref cell_num, ref atom) =>
                target.push(Target::to_structure(atom.clone(), 0, cell_num.get())),
            &Term::Clause(ref cell_num, ref atom, ref terms) => {
                target.push(Target::to_structure(atom.clone(), 0, cell_num.get()));

                for subterm in terms {
                    target.push(subterm_to_instr(subterm.as_ref(), &mut bindings));
                }
            },
            _ => {},
        };
    }

    target
}
