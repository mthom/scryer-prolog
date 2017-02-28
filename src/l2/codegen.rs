use l2::ast::*;
use l2::iterators::{FactIterator, QueryIterator};

use std::cell::Cell;
use std::cmp::max;
use std::collections::HashMap;
use std::fmt;
use std::vec::Vec;

impl fmt::Display for FactInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FactInstruction::GetStructure(Level::Deep, ref name, ref arity, ref r) =>
                write!(f, "get_structure {}/{}, {}", name, arity, r),
            &FactInstruction::GetStructure(Level::Shallow, ref name, ref arity, ref r) =>
                write!(f, "get_structure {}/{}, A{}", name, arity, r.reg_num()),
            &FactInstruction::GetValue(ref x, ref a) =>
                write!(f, "get_value {}, A{}", x, a),
            &FactInstruction::GetVariable(ref x, ref a) =>
                write!(f, "get_variable {}, A{}", x, a),
            &FactInstruction::UnifyVariable(ref r) =>
                write!(f, "unify_variable {}", r),
            &FactInstruction::UnifyValue(ref r) =>
                write!(f, "unify_value {}", r)
        }
    }
}

impl fmt::Display for QueryInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &QueryInstruction::PutStructure(Level::Deep, ref name, ref arity, ref r) =>
                write!(f, "put_structure {}/{}, A{}", name, arity, r.reg_num()),
            &QueryInstruction::PutStructure(Level::Shallow, ref name, ref arity, ref r) =>
                write!(f, "put_structure {}/{}, {}", name, arity, r),
            &QueryInstruction::PutValue(ref x, ref a) =>
                write!(f, "put_value {}, A{}", x, a),
            &QueryInstruction::PutVariable(ref x, ref a) =>
                write!(f, "put_variable {}, A{}", x, a),
            &QueryInstruction::SetVariable(ref r) =>
                write!(f, "set_variable {}", r),
            &QueryInstruction::SetValue(ref r) =>
                write!(f, "set_value {}", r),
        }
    }
}

impl fmt::Display for ControlInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ControlInstruction::Allocate(num_cells) =>
                write!(f, "allocate {}", num_cells),
            &ControlInstruction::Call(ref name, ref arity) =>
                write!(f, "call {}/{}", name, arity),
            &ControlInstruction::Deallocate =>
                write!(f, "deallocate"),
            &ControlInstruction::Proceed =>
                write!(f, "proceed")
        }
    }
}

trait CompilationTarget<'a> {
    type Iterator : Iterator<Item=TermRef<'a>>;

    fn iter(&'a Term) -> Self::Iterator;

    fn to_structure(Level, Atom, usize, RegType) -> Self;

    fn argument_to_variable(RegType, usize) -> Self;
    fn argument_to_value(RegType, usize) -> Self;
    fn subterm_to_variable(RegType) -> Self;
    fn subterm_to_value(RegType) -> Self;

    fn clause_arg_to_instr(RegType) -> Self;
}

impl<'a> CompilationTarget<'a> for FactInstruction {
    type Iterator = FactIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        term.breadth_first_iter()
    }

    fn to_structure(lvl: Level, atom: Atom, arity: usize, reg: RegType) -> Self {
        FactInstruction::GetStructure(lvl, atom, arity, reg)
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Self {
        FactInstruction::GetVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Self {
        FactInstruction::GetValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Self {
        FactInstruction::UnifyVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Self {
        FactInstruction::UnifyValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Self {
        FactInstruction::UnifyVariable(val)
    }
}

impl<'a> CompilationTarget<'a> for QueryInstruction {
    type Iterator = QueryIterator<'a>;

    fn iter(term: &'a Term) -> Self::Iterator {
        term.post_order_iter()
    }

    fn to_structure(lvl: Level, atom: Atom, arity: usize, reg: RegType) -> Self {
        QueryInstruction::PutStructure(lvl, atom, arity, reg)
    }

    fn argument_to_variable(arg: RegType, val: usize) -> Self {
        QueryInstruction::PutVariable(arg, val)
    }

    fn argument_to_value(arg: RegType, val: usize) -> Self {
        QueryInstruction::PutValue(arg, val)
    }

    fn subterm_to_variable(val: RegType) -> Self {
        QueryInstruction::SetVariable(val)
    }

    fn subterm_to_value(val: RegType) -> Self {
        QueryInstruction::SetValue(val)
    }

    fn clause_arg_to_instr(val: RegType) -> Self {
        QueryInstruction::SetValue(val)
    }
}

struct TermMarker<'a> {
    bindings: HashMap<&'a Var, VarReg>,
    arg_c:    usize,
    perm_c:   usize,
    temp_c:   usize
}

impl<'a> TermMarker<'a> {
    fn new() -> TermMarker<'a> {
        TermMarker { bindings: HashMap::new(),
                     arg_c:    1,
                     perm_c:   1,
                     temp_c:   1 }
    }

    fn contains_var(&self, var: &'a Var) -> bool {
        self.bindings.contains_key(var)
    }

    fn get(&self, var: &'a Var) -> VarReg {
        *self.bindings.get(var).unwrap()
    }

    fn insert(&mut self, var: &'a Var, r: VarReg) {
        self.bindings.insert(var, r);
    }

    fn mark_non_var(&mut self, lvl: Level, cell: &Cell<RegType>) {
        let reg_type = cell.get();

        if reg_type.reg_num() == 0 {
            match lvl {
                Level::Deep if reg_type.is_perm() => {
                    let perm = self.perm_c;
                    self.perm_c += 1;
                    cell.set(RegType::Perm(perm));
                },
                Level::Deep => {
                    let temp = self.temp_c;
                    self.temp_c += 1;
                    cell.set(RegType::Temp(temp));
                },
                Level::Shallow if reg_type.is_perm() => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    cell.set(RegType::Perm(arg));
                },
                Level::Shallow => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    cell.set(RegType::Temp(arg));
                }
            };
        }
    }

    fn mark_old_var(&mut self, lvl: Level, var: &'a Var) -> VarReg
    {
        let reg = self.get(var);

        match lvl {
            Level::Deep => VarReg::Norm(reg.norm()),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(reg.norm(), self.arg_c);

                self.arg_c += 1;
                self.insert(var, reg);

                reg
            }
        }
    }

    fn mark_new_var(&mut self, lvl: Level, var: &'a Var, reg: RegType) -> VarReg
    {
        let inner_reg = if reg.is_perm() {
            let perm = self.perm_c;
            self.perm_c += 1;
            RegType::Perm(perm)
        } else {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        };

        let reg = match lvl {
            Level::Deep => VarReg::Norm(inner_reg),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(inner_reg, self.arg_c);
                self.arg_c += 1;
                reg
            }
        };

        self.insert(var, reg);
        reg
    }

    fn advance_at_header(&mut self, term: &'a Term) {
        self.arg_c = 1;
        self.temp_c = max(term.subterms(), self.temp_c) + 1;
    }

    fn advance(&mut self, term: &'a Term) {
        self.arg_c = 1;
        self.temp_c = term.subterms() + 1;
    }
}

#[derive(Copy, Clone)]
enum TermStatus {
    New, Old, Recurrent
}

pub struct CodeGenerator<'a> {
    marker: TermMarker<'a>
}

type VariableFixture<'a>  = (TermStatus, Vec<&'a Cell<VarReg>>);
type VariableFixtures<'a> = HashMap<&'a Var, VariableFixture<'a>>;

impl<'a> CodeGenerator<'a> {
    pub fn new() -> Self {
        CodeGenerator { marker: TermMarker::new() }
    }

    pub fn vars(&self) -> &HashMap<&Var, VarReg> {
        &self.marker.bindings
    }

    fn to_structure<Target>(&mut self,
                            lvl: Level,
                            name: &'a Atom,
                            cell: &'a Cell<RegType>,
                            arity: usize)
                            -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_structure(lvl, name.clone(), arity, cell.get())
    }

    fn var_term<Target>(&mut self,
                        lvl: Level,
                        cell: &'a Cell<VarReg>,
                        var: &'a Var)
                        -> Target
        where Target: CompilationTarget<'a>
    {
        if !self.marker.contains_var(var) {
            let reg = self.marker.mark_new_var(lvl, var, cell.get().norm());
            cell.set(reg);

            match reg {
                VarReg::ArgAndNorm(arg, norm) =>
                    Target::argument_to_variable(arg, norm),
                VarReg::Norm(norm) =>
                    Target::subterm_to_variable(norm)
            }
        } else {
            let reg = self.marker.mark_old_var(lvl, var);
            cell.set(reg);

            match reg {
                VarReg::ArgAndNorm(arg, norm) =>
                    Target::argument_to_value(arg, norm),
                VarReg::Norm(norm) =>
                    Target::subterm_to_value(norm)
            }
        }
    }

    fn non_var_subterm<Target>(&mut self, cell: &'a Cell<RegType>) -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(Level::Deep, cell);
        Target::clause_arg_to_instr(cell.get())
    }

    fn subterm_to_instr<Target>(&mut self, subterm: &'a Term) -> Target
        where Target: CompilationTarget<'a>
    {
        match subterm {
            &Term::Atom(ref cell, _) | &Term::Clause(ref cell, _, _) =>
                self.non_var_subterm(cell),
            &Term::Var(ref cell, ref var) =>
                self.var_term(Level::Deep, cell, var)
        }
    }

    fn compile_target<Target>(&mut self, term: &'a Term) -> Vec<Target>
        where Target: CompilationTarget<'a>
    {
        let iter       = Target::iter(term);
        let mut target = Vec::new();

        for term in iter {
            match term {
                TermRef::Atom(lvl, term, atom) =>
                    target.push(self.to_structure(lvl, atom, term, 0)),
                TermRef::Clause(lvl, term, atom, terms) => {
                    target.push(self.to_structure(lvl, atom, term, terms.len()));

                    for subterm in terms {
                        target.push(self.subterm_to_instr(subterm.as_ref()));
                    }
                },
                TermRef::Var(lvl @ Level::Shallow, ref cell, ref var) =>
                    target.push(self.var_term(lvl, cell, var)),
                _ => {}
            };
        }

        target
    }

    fn mark_vars_in_term<Iter>(iter: Iter, vs: &mut VariableFixtures<'a>)
        where Iter : Iterator<Item=TermRef<'a>>
    {
        for term in iter {
            if let TermRef::Var(_, reg_cell, var) = term {
                let mut status =
                    vs.entry(var)
                      .or_insert((TermStatus::New, Vec::new()));

                status.1.push(reg_cell);

                match status.0 {
                    TermStatus::Old | TermStatus::Recurrent =>
                        status.0 = TermStatus::Recurrent,
                    _ => {}
                };
            }
        }

        for &mut (ref mut term_status, ref mut cb) in vs.values_mut() {
            match *term_status {
                TermStatus::New => *term_status = TermStatus::Old,
                TermStatus::Recurrent => {
                    for cell_reg in cb.drain(0..) {
                        cell_reg.set(VarReg::Norm(RegType::Perm(0)));
                    }
                },
                _ => {}
            }
        }
    }

    fn mark_perm_vars(rule: &'a Rule) -> VariableFixtures {
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let mut vfs = HashMap::new();

        let iter = p0.breadth_first_iter().chain(p1.breadth_first_iter());

        Self::mark_vars_in_term(iter, &mut vfs);

        for term in clauses {
            Self::mark_vars_in_term(term.breadth_first_iter(), &mut vfs);
        }

        vfs
    }

    fn add_conditional_call(compiled_query: &mut Code, term: &Term) {
        match term {
            &Term::Atom(_, ref atom) => {
                let call = ControlInstruction::Call(atom.clone(), 0);
                compiled_query.push(Line::Control(call));
            },
            &Term::Clause(_, ref atom, ref terms) => {
                let call = ControlInstruction::Call(atom.clone(), terms.len());
                compiled_query.push(Line::Control(call));
            },
            _ => {}
        }
    }

    pub fn compile_rule(&mut self, rule: &'a Rule) -> Code {
        let vfs = Self::mark_perm_vars(&rule);
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let mut perm_vars = 0;

        for &(term_status, _) in vfs.values() {
            if let TermStatus::Recurrent = term_status {
                perm_vars += 1;
            }
        }

        let mut body = Vec::new();

        body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

        self.marker.advance(p0);
        body.push(Line::Fact(self.compile_target(p0)));

        self.marker.advance_at_header(p1);
        body.push(Line::Query(self.compile_target(p1)));
        Self::add_conditional_call(&mut body, p1);

        body = clauses.iter()
            .map(|ref term| self.compile_query(term))
            .fold(body, |mut body, ref mut cqs| {
                body.append(cqs);
                body
            });

        body.push(Line::Control(ControlInstruction::Deallocate));

        body
    }

    pub fn compile_fact(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);

        let mut compiled_fact = vec![Line::Fact(self.compile_target(term))];
        let proceed = Line::Control(ControlInstruction::Proceed);

        compiled_fact.push(proceed);
        compiled_fact
    }

    pub fn compile_query(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);

        let mut compiled_query = vec![Line::Query(self.compile_target(term))];
        Self::add_conditional_call(&mut compiled_query, term);

        compiled_query
    }
}
