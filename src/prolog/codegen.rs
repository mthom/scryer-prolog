use prolog::ast::*;
use prolog::iterators::{FactIterator, QueryIterator};

use std::cell::Cell;
use std::cmp::max;
use std::collections::HashMap;
use std::vec::Vec;

trait CompilationTarget<'a> {
    type Iterator : Iterator<Item=TermRef<'a>>;

    fn iter(&'a Term) -> Self::Iterator;

    fn to_constant(Level, Constant, RegType) -> Self;
    fn to_list(Level, RegType) -> Self;
    fn to_structure(Level, Atom, usize, RegType) -> Self;
    fn to_void(usize) -> Self;

    fn constant_subterm(Constant) -> Self;

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

    fn to_constant(lvl: Level, constant: Constant, reg: RegType) -> Self {
        FactInstruction::GetConstant(lvl, constant, reg)
    }

    fn to_structure(lvl: Level, atom: Atom, arity: usize, reg: RegType) -> Self {
        FactInstruction::GetStructure(lvl, atom, arity, reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Self {
        FactInstruction::GetList(lvl, reg)
    }

    fn to_void(subterms: usize) -> Self {
        FactInstruction::UnifyVoid(subterms)
    }

    fn constant_subterm(constant: Constant) -> Self {
        FactInstruction::UnifyConstant(constant)
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

    fn to_constant(lvl: Level, constant: Constant, reg: RegType) -> Self {
        QueryInstruction::PutConstant(lvl, constant, reg)
    }

    fn to_list(lvl: Level, reg: RegType) -> Self {
        QueryInstruction::PutList(lvl, reg)
    }

    fn to_void(subterms: usize) -> Self {
        QueryInstruction::SetVoid(subterms)
    }

    fn constant_subterm(constant: Constant) -> Self {
        QueryInstruction::SetConstant(constant)
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

    fn reset(&mut self) {
        self.bindings.clear();
        self.perm_c = 1;
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

    fn mark_anon_var(&mut self, lvl: Level) -> VarReg {
        let inner_reg = {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        };

        match lvl {
            Level::Deep => VarReg::Norm(inner_reg),
            Level::Shallow => {
                let reg = VarReg::ArgAndNorm(inner_reg, self.arg_c);
                self.arg_c += 1;
                reg
            }
        }
    }

    fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    fn advance_at_head(&mut self, term: &'a Term) {
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

    #[allow(dead_code)]
    fn count_vars(term: &Term) -> HashMap<&Var, usize> {
        let mut var_count = HashMap::new();

        for term in term.breadth_first_iter() {
            if let TermRef::Var(_, _, ref var) = term {
                let entry = var_count.entry(*var).or_insert(0);
                *entry += 1;
            }
        }

        var_count
    }

    #[allow(dead_code)]
    fn all_singleton_vars(terms: &Vec<Box<Term>>,
                          var_count: &HashMap<&Var, usize>)
                          -> bool
    {
        for term in terms {
            match term.as_ref() {
                &Term::AnonVar => {},
                &Term::Var(ref cell, ref var) if cell.get().is_temp() =>
                    if var_count.get(var).unwrap() != &1 {
                        return false;
                    },
                _ => return false
            }
        }

        true
    }

    #[allow(dead_code)]
    fn void_subterms<Target>(subterms: usize) -> Target
        where Target: CompilationTarget<'a>
    {
        Target::to_void(subterms)
    }

    fn to_structure<Target>(&mut self,
                            lvl: Level,
                            cell: &'a Cell<RegType>,
                            name: &'a Atom,
                            arity: usize)
                            -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_structure(lvl, name.clone(), arity, cell.get())
    }

    fn to_constant<Target>(&mut self,
                           lvl: Level,
                           cell: &'a Cell<RegType>,
                           constant: &'a Constant)
                           -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_constant(lvl, constant.clone(), cell.get())
    }

    fn to_list<Target>(&mut self, lvl: Level, cell: &'a Cell<RegType>) -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_list(lvl, cell.get())
    }

    fn constant_subterm<Target>(&mut self,
                                cell: &'a Cell<RegType>,
                                constant: &'a Constant)
                                -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(Level::Deep, cell);
        Target::constant_subterm(constant.clone())
    }

    fn anon_var_term<Target>(&mut self, lvl: Level) -> Target
        where Target: CompilationTarget<'a>
    {
        let reg = self.marker.mark_anon_var(lvl);

        match reg {
            VarReg::ArgAndNorm(arg, norm) =>
                Target::argument_to_variable(arg, norm),
            VarReg::Norm(norm) =>
                Target::subterm_to_variable(norm)
        }
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
            &Term::AnonVar =>
                self.anon_var_term(Level::Deep),
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _) =>
                self.non_var_subterm(cell),
            &Term::Constant(ref cell, ref constant) =>
                self.constant_subterm(cell, constant),
            &Term::Var(ref cell, ref var) =>
                self.var_term(Level::Deep, cell, var)
        }
    }

    fn compile_target<Target>(&mut self, term: &'a Term, has_exposed_vars: bool)
                              -> Vec<Target>
        where Target: CompilationTarget<'a>
    {
        let iter       = Target::iter(term);
        let mut target = Vec::new();
        let var_count  = Self::count_vars(term);

        for term in iter {
            match term {
                TermRef::Clause(lvl, cell, atom, terms) => {
                    target.push(self.to_structure(lvl, cell, atom, terms.len()));

                    if !has_exposed_vars {
                        if Self::all_singleton_vars(terms, &var_count) {
                            target.push(Self::void_subterms(terms.len()));
                            continue;
                        }
                    }

                    for subterm in terms {
                        target.push(self.subterm_to_instr(subterm.as_ref()));
                    }
                },
                TermRef::Cons(lvl, cell, head, tail) => {
                    target.push(self.to_list(lvl, cell));

                    target.push(self.subterm_to_instr(head));
                    target.push(self.subterm_to_instr(tail));
                },
                TermRef::Constant(lvl @ Level::Shallow, cell, constant) =>
                    target.push(self.to_constant(lvl, cell, constant)),
                TermRef::AnonVar(lvl @ Level::Shallow) => {
                    if has_exposed_vars {
                        target.push(self.anon_var_term(lvl));
                    } else {
                        self.marker.advance_arg();
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
                let mut status = vs.entry(var)
                                   .or_insert((TermStatus::New, Vec::new()));

                status.1.push(reg_cell);

                match status.0 {
                    TermStatus::Old => status.0 = TermStatus::Recurrent,
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

    fn add_conditional_call(compiled_query: &mut Code, term: &Term)
    {
        match term {
            &Term::Constant(_, Constant::Atom(ref atom)) => {
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

        if clauses.len() > 0 {
            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));
        }

        self.marker.advance(p0);
        body.push(Line::Fact(self.compile_target(p0, false)));

        self.marker.advance_at_head(p1);
        body.push(Line::Query(self.compile_target(p1, false)));

        Self::add_conditional_call(&mut body, p1);

        body = clauses.iter()
            .map(|ref term| self.compile_internal_query(term))
            .fold(body, |mut body, ref mut cqs| {
                body.append(cqs);
                body
            });

        let last_arity = rule.last_clause().arity();
        let mut dealloc_index = body.len() - 1;

        match rule.last_clause() {
              &Term::Clause(_, ref name, _)
            | &Term::Constant(_, Constant::Atom(ref name)) => {
                if let &mut Line::Control(ref mut ctrl) = body.last_mut().unwrap() {
                    *ctrl = ControlInstruction::Execute(name.clone(), last_arity);
                }
            },
            _ => dealloc_index = body.len()
        };

        if clauses.len() > 0 {
            body.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }
        
        body
    }

    pub fn compile_fact(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);

        let mut compiled_fact = vec![Line::Fact(self.compile_target(term, false))];
        let proceed = Line::Control(ControlInstruction::Proceed);

        compiled_fact.push(proceed);
        compiled_fact
    }

    fn compile_internal_query(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);

        let mut compiled_query = vec![Line::Query(self.compile_target(term, false))];
        Self::add_conditional_call(&mut compiled_query, term);

        compiled_query
    }

    pub fn compile_query(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);

        let mut compiled_query = vec![Line::Query(self.compile_target(term, true))];
        Self::add_conditional_call(&mut compiled_query, term);

        compiled_query
    }

    pub fn compile_predicate(&mut self, clauses: &'a Vec<PredicateClause>) -> Code
    {
        let mut code = Vec::new();

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_code = match clause {
                &PredicateClause::Fact(ref fact) =>
                    self.compile_fact(fact),
                &PredicateClause::Rule(ref rule) =>
                    self.compile_rule(rule)
            };

            let choice = match i {
                0 => ChoiceInstruction::TryMeElse(clause_code.len() + 1),
                _ if i == clauses.len() - 1 => ChoiceInstruction::TrustMe,
                _ => ChoiceInstruction::RetryMeElse(clause_code.len() + 1)
            };

            code.push(Line::Choice(choice));
            code.append(&mut clause_code);
        }

        code
    }
}
