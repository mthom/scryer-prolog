use prolog::ast::*;
use prolog::iterators::{FactIterator, QueryIterator};

use std::cell::Cell;
use std::cmp::max;
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
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
    temp_c:   usize
}

impl<'a> TermMarker<'a> {
    fn new() -> TermMarker<'a> {
        TermMarker { bindings: HashMap::new(),
                     arg_c:    1,
                     temp_c:   1 }
    }

    fn reset(&mut self) {
        self.bindings.clear();
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
                Level::Deep if !reg_type.is_perm() => {
                    let temp = self.temp_c;
                    self.temp_c += 1;
                    cell.set(RegType::Temp(temp));
                },
                Level::Shallow if !reg_type.is_perm() => {
                    let arg = self.arg_c;
                    self.arg_c += 1;
                    cell.set(RegType::Temp(arg));
                },
                _ => {}
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
        let inner_reg = if !reg.is_perm() {
            let temp = self.temp_c;
            self.temp_c += 1;
            RegType::Temp(temp)
        } else {
            reg
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
        self.arg_c  = 1;
        self.temp_c = max(term.subterms() + 1, self.temp_c);
    }

    fn advance(&mut self, term: &'a Term) {
        self.arg_c  = 1;
        self.temp_c = term.subterms() + 1;
    }
}

#[derive(Clone, Copy)]
enum IntIndex {
    External(usize), Fail, Internal(usize)
}

struct CodeOffsets {
    constants:  HashMap<Constant, ThirdLevelIndex>,
    lists: ThirdLevelIndex,
    structures: HashMap<(Atom, usize), ThirdLevelIndex>
}

impl CodeOffsets {
    fn new() -> Self {
        CodeOffsets {
            constants: HashMap::new(),
            lists: Vec::new(),
            structures: HashMap::new()
        }
    }

    fn cap_choice_seq_with_trust(prelude: &mut ThirdLevelIndex) {
        prelude.last_mut().map(|instr| {
            match instr {
                &mut IndexedChoiceInstruction::Retry(i) =>
                    *instr = IndexedChoiceInstruction::Trust(i),
                _ => {}
            };
        });
    }

    fn add_index(is_first_index: bool, index: usize) -> IndexedChoiceInstruction {
        if is_first_index {
            IndexedChoiceInstruction::Try(index)
        } else {
            IndexedChoiceInstruction::Retry(index)
        }
    }

    fn index_term(&mut self, first_arg: &Term, index: usize) {
        match first_arg {
            &Term::Clause(_, ref name, ref terms) => {
                let code = self.structures.entry((name.clone(), terms.len()))
                               .or_insert(Vec::new());

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            },
            &Term::Cons(_, _, _) => {
                let is_initial_index = self.lists.is_empty();
                self.lists.push(Self::add_index(is_initial_index, index));
            },
            &Term::Constant(_, ref constant) => {
                let code = self.constants.entry(constant.clone())
                               .or_insert(Vec::new());

                let is_initial_index = code.is_empty();
                code.push(Self::add_index(is_initial_index, index));
            },
            _ => {}
        };
    }

    fn second_level_index<Index>(indices: HashMap<Index, ThirdLevelIndex>,
                                 prelude: &mut CodeDeque)
                                 -> HashMap<Index, IntIndex>
        where Index: Eq + Hash
    {
        let mut index_locs = HashMap::new();

        for (key, mut code) in indices.into_iter() {
            if code.len() > 1 {
                index_locs.insert(key, IntIndex::Internal(prelude.len()));
                Self::cap_choice_seq_with_trust(&mut code);
                prelude.extend(code.into_iter().map(|code| Line::from(code)));
            } else {
                code.first().map(|i| {
                    index_locs.insert(key, IntIndex::External(i.offset()));
                });
            }
        }

        index_locs
    }

    fn no_indices(&self) -> bool {
        let no_constants = self.constants.is_empty();
        let no_structures = self.structures.is_empty();
        let no_lists = self.lists.is_empty();

        no_constants && no_structures && no_lists
    }

    fn flatten_index<Index>(index: HashMap<Index, IntIndex>, len: usize)
                            -> HashMap<Index, usize>
        where Index: Eq + Hash
    {
        let mut flattened_index = HashMap::new();

        for (key, int_index) in index.into_iter() {
            match int_index {
                IntIndex::External(offset) => {
                    flattened_index.insert(key, offset + len + 1);
                },
                IntIndex::Internal(offset) => {
                    flattened_index.insert(key, offset + 1);
                },
                _ => {}
            };
        }

        flattened_index
    }

    fn switch_on_constant(con_ind: HashMap<Constant, ThirdLevelIndex>,
                          prelude: &mut CodeDeque)
                          -> IntIndex
    {
        let con_ind = Self::second_level_index(con_ind, prelude);

        if con_ind.len() > 1 {
            let index = Self::flatten_index(con_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnConstant(index.len(), index);

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            con_ind.values().next()
                   .map(|i| *i)
                   .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_list(mut lists: ThirdLevelIndex, prelude: &mut CodeDeque) -> IntIndex
    {
        if lists.len() > 1 {
            Self::cap_choice_seq_with_trust(&mut lists);
            prelude.extend(lists.into_iter().map(|i| Line::from(i)));
            IntIndex::Internal(0)
        } else {
            lists.first()
                 .map(|i| IntIndex::External(i.offset()))
                 .unwrap_or(IntIndex::Fail)
        }
    }

    fn switch_on_structure(str_ind: HashMap<(Atom, usize), ThirdLevelIndex>,
                           prelude: &mut CodeDeque)
                           -> IntIndex
    {
        let str_ind = Self::second_level_index(str_ind, prelude);

        if str_ind.len() > 1 {
            let index = Self::flatten_index(str_ind, prelude.len());
            let instr = IndexingInstruction::SwitchOnStructure(index.len(), index);

            prelude.push_front(Line::from(instr));

            IntIndex::Internal(1)
        } else {
            str_ind.values().next()
                   .map(|i| *i)
                   .unwrap_or(IntIndex::Fail)
        }
    }


    fn switch_on_str_offset_from(str_loc: IntIndex, prelude_len: usize, con_loc: IntIndex)
                                 -> usize
    {
        match str_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => match con_loc {
                IntIndex::Internal(_) => 2,
                _ => 1
            }
        }
    }

    fn switch_on_con_offset_from(con_loc: IntIndex, prelude_len: usize) -> usize
    {
        match con_loc {
            IntIndex::External(offset) => offset + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(offset) => offset,
        }
    }

    fn switch_on_lst_offset_from(lst_loc: IntIndex, prelude_len: usize, lst_offset: usize)
                                 -> usize
    {
        match lst_loc {
            IntIndex::External(o) => o + prelude_len + 1,
            IntIndex::Fail => 0,
            IntIndex::Internal(_) => prelude_len - lst_offset + 1
        }        
    }
    
    fn add_indices(self, code: &mut Code, mut code_body: Code)
    {
        if self.no_indices() {
            *code = code_body;
            return;
        }

        let mut prelude = VecDeque::new();

        let lst_loc = Self::switch_on_list(self.lists, &mut prelude);
        let lst_offset = prelude.len();

        let str_loc = Self::switch_on_structure(self.structures, &mut prelude);
        let con_loc = Self::switch_on_constant(self.constants, &mut prelude);

        let prelude_length = prelude.len();

        for (index, line) in prelude.iter_mut().enumerate() {
            match line {
                  &mut Line::IndexedChoice(IndexedChoiceInstruction::Try(ref mut i))
                | &mut Line::IndexedChoice(IndexedChoiceInstruction::Retry(ref mut i))
                | &mut Line::IndexedChoice(IndexedChoiceInstruction::Trust(ref mut i)) =>
                    *i += prelude_length - index,
                _ => {}
            }
        }
                
        let str_loc = Self::switch_on_str_offset_from(str_loc, prelude.len(), con_loc);
        let con_loc = Self::switch_on_con_offset_from(con_loc, prelude.len());
        let lst_loc = Self::switch_on_lst_offset_from(lst_loc, prelude.len(), lst_offset);
        
        let switch_instr = IndexingInstruction::SwitchOnTerm(prelude.len() + 1,
                                                             con_loc,
                                                             lst_loc,
                                                             str_loc);

        prelude.push_front(Line::from(switch_instr));

        *code = Vec::from(prelude);
        code.append(&mut code_body);
    }
}

#[derive(Copy, Clone)]
enum VarStatus {
    New, Old, Permanent(usize)
}

pub struct CodeGenerator<'a> {
    marker: TermMarker<'a>,
    var_count: HashMap<&'a Var, usize>
}

type VariableFixture<'a>  = (VarStatus, Vec<&'a Cell<VarReg>>);
type VariableFixtures<'a> = HashMap<&'a Var, VariableFixture<'a>>;

impl<'a> CodeGenerator<'a> {
    pub fn new() -> Self {
        CodeGenerator { marker: TermMarker::new(),
                        var_count: HashMap::new() }
    }

    pub fn vars(&self) -> &HashMap<&Var, VarReg> {
        &self.marker.bindings
    }

    fn update_var_count<Iter>(&mut self, iter: Iter)
        where Iter : Iterator<Item=TermRef<'a>>
    {
        let mut var_count = HashMap::new();

        for term in iter {
            if let TermRef::Var(_, _, var) = term {
                if self.marker.contains_var(var) {
                    var_count.insert(var, 2);
                    continue;
                }

                let entry = var_count.entry(var).or_insert(0);
                *entry += 1;
            }
        }

        self.var_count = var_count;
    }

    fn all_singleton_vars(&self, terms: &Vec<Box<Term>>) -> bool
    {
        for term in terms {
            match term.as_ref() {
                &Term::AnonVar => {},
                &Term::Var(ref cell, ref var) if cell.get().is_temp() =>
                    if self.var_count.get(var).unwrap() != &1 {
                        return false;
                    },
                _ => return false
            }
        }

        true
    }

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

    fn constant_subterm<Target>(&mut self, constant: &'a Constant) -> Target
        where Target: CompilationTarget<'a>
    {
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
            &Term::Constant(_, ref constant) =>
                self.constant_subterm(constant),
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

        for term in iter {
            match term {
                TermRef::Clause(lvl, cell, atom, terms) => {
                    target.push(self.to_structure(lvl, cell, atom, terms.len()));

                    if !has_exposed_vars {
                        if self.all_singleton_vars(terms) {
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

    fn mark_vars_in_term<Iter>(iter: Iter, vs: &mut VariableFixtures<'a>, i: usize)
        where Iter : Iterator<Item=TermRef<'a>>
    {
        for term in iter {
            if let TermRef::Var(_, reg_cell, var) = term {
                let mut status = vs.entry(var)
                                   .or_insert((VarStatus::New, Vec::new()));

                status.1.push(reg_cell);

                match status.0 {
                    VarStatus::Old =>
                        status.0 = VarStatus::Permanent(i),
                    VarStatus::Permanent(_) =>
                        status.0 = VarStatus::Permanent(i),
                    _ => {}
                };
            }
        }

        for &mut (ref mut term_status, _) in vs.values_mut() {
            match *term_status {
                VarStatus::New =>
                    *term_status = VarStatus::Old,
                _ => {}
            }
        }
    }

    fn set_perm_vals(vs: &VariableFixtures) {
        let mut values_vec : Vec<_> = vs.values()
            .map(|ref v| (v.0, &v.1))
            .collect();

        values_vec.sort_by_key(|ref v| {
            match v.0 {
                VarStatus::Permanent(i) => i,
                _ => usize::min_value()
            }
        });

        for (i, v) in values_vec.into_iter().rev().enumerate() {
            if let VarStatus::Permanent(_) = v.0 {
                for cell in v.1 {
                    cell.set(VarReg::Norm(RegType::Perm(i + 1)));
                }
            } else {
                break;
            }
        }
    }

    fn mark_perm_vars(rule: &'a Rule) -> VariableFixtures {
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let mut vs = HashMap::new();

        let iter = p0.breadth_first_iter().chain(p1.breadth_first_iter());

        Self::mark_vars_in_term(iter, &mut vs, 0);

        for (i, term) in clauses.iter().enumerate() {
            Self::mark_vars_in_term(term.breadth_first_iter(), &mut vs, i + 1);
        }

        Self::set_perm_vals(&vs);

        vs
    }

    fn add_conditional_call(compiled_query: &mut Code, term: &Term, pvs: usize)
    {
        match term {
            &Term::Constant(_, Constant::Atom(ref atom)) => {
                let call = ControlInstruction::Call(atom.clone(), 0, pvs);
                compiled_query.push(Line::Control(call));
            },
            &Term::Clause(_, ref atom, ref terms) => {
                let call = ControlInstruction::Call(atom.clone(), terms.len(), pvs);
                compiled_query.push(Line::Control(call));
            },
            _ => {}
        }
    }

    fn vars_above_threshold(vs: &VariableFixtures, index: usize) -> usize {
        let mut var_count = 0;

        for &(term_status, _) in vs.values() {
            if let VarStatus::Permanent(i) = term_status {
                if i > index {
                    var_count += 1;
                }
            }
        }

        var_count
    }

    fn lco(body: &mut Code, rule: &'a Rule) -> usize {
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

        dealloc_index
    }

    fn mark_unsafe_query_vars(head: &Term,
                              vs: &VariableFixtures,
                              query: &mut CompiledQuery)
    {
        let mut unsafe_vars = HashMap::new();

        for &(_, ref cb) in vs.values() {
            if !cb.is_empty() {
                let index = cb.first().unwrap().get().norm();
                unsafe_vars.insert(index, false);
            }
        }

        for term_ref in head.breadth_first_iter() {
            match term_ref {
                TermRef::Var(_, cell, _) => {
                    unsafe_vars.remove(&cell.get().norm());
                },
                _ => {}
            };
        }

        for query_instr in query.iter_mut() {
            match query_instr {
                &mut QueryInstruction::PutValue(RegType::Perm(i), arg) =>
                    if let Some(found) = unsafe_vars.get_mut(&RegType::Perm(i)) {
                        if !*found {
                            *found = true;
                            *query_instr = QueryInstruction::PutUnsafeValue(i, arg);
                        }
                    },
                &mut QueryInstruction::SetVariable(reg)
              | &mut QueryInstruction::PutVariable(reg, _) =>
                    if let Some(found) = unsafe_vars.get_mut(&reg) {
                        *found = true;
                    },
                &mut QueryInstruction::SetValue(reg) =>
                    if let Some(found) = unsafe_vars.get_mut(&reg) {
                        if !*found {
                            *found = true;
                            *query_instr = QueryInstruction::SetLocalValue(reg);
                        }
                    },
                _ => {}
            };
        }
    }

    pub fn compile_rule(&mut self, rule: &'a Rule) -> Code {
        let vs = Self::mark_perm_vars(&rule);
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;

        let perm_vars = Self::vars_above_threshold(&vs, 0);
        let mut body = Vec::new();

        if clauses.len() > 0 {
            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));
        }

        let iter = p0.breadth_first_iter().chain(p1.breadth_first_iter());
        self.update_var_count(iter);

        self.marker.advance(p0);
        body.push(Line::Fact(self.compile_target(p0, false)));

        self.marker.advance_at_head(p1);
        body.push(Line::Query(self.compile_target(p1, false)));

        Self::add_conditional_call(&mut body, p1, perm_vars);

        body = clauses.iter().enumerate()
            .map(|(i, term)| {
                let num_vars = Self::vars_above_threshold(&vs, i+1);
                self.compile_internal_query(term, num_vars)
            })
            .fold(body, |mut body, ref mut cqs| {
                body.append(cqs);
                body
            });

        if clauses.len() > 0 {
            let mut index = body.len() - 1;

            if let &Line::Control(_) = body.last().unwrap() {
                index -= 1;
            }

            if let &mut Line::Query(ref mut query) = &mut body[index] {
                Self::mark_unsafe_query_vars(p0, &vs, query);
            }
        }

        let dealloc_index = Self::lco(&mut body, &rule);

        if clauses.len() > 0 {
            body.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }

        body
    }

    fn mark_unsafe_fact_vars(fact: &mut CompiledFact, bindings: &HashMap<&Var, VarReg>)
    {
        let mut unsafe_vars = HashMap::new();

        for var_reg in bindings.values() {
            unsafe_vars.insert(var_reg.norm(), false);
        }

        for fact_instr in fact.iter_mut() {
            match fact_instr {
                &mut FactInstruction::UnifyValue(reg) =>
                    if let Some(found) = unsafe_vars.get_mut(&reg) {
                        if !*found {
                            *found = true;
                            *fact_instr = FactInstruction::UnifyLocalValue(reg);
                        }
                    },
                &mut FactInstruction::UnifyVariable(reg) => {
                    if let Some(found) = unsafe_vars.get_mut(&reg) {
                        *found = true;
                    }
                },
                _ => {}
            };
        }
    }

    pub fn compile_fact(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);
        self.update_var_count(term.breadth_first_iter());

        let mut code = Vec::new();

        if term.is_clause() {
            let mut compiled_fact = self.compile_target(term, false);
            Self::mark_unsafe_fact_vars(&mut compiled_fact, self.vars());
            code.push(Line::Fact(compiled_fact));
        }

        let proceed = Line::Control(ControlInstruction::Proceed);

        code.push(proceed);
        code
    }

    fn compile_internal_query(&mut self, term: &'a Term, index: usize) -> Code
    {
        self.marker.advance(term);
        self.update_var_count(term.breadth_first_iter());

        let mut code = Vec::new();

        if term.is_clause() {
            let compiled_query = Line::Query(self.compile_target(term, false));
            code.push(compiled_query);
        }

        Self::add_conditional_call(&mut code, term, index);

        code
    }

    pub fn compile_query(&mut self, term: &'a Term) -> Code {
        self.marker.advance(term);
        self.update_var_count(term.breadth_first_iter());

        let mut code = Vec::new();

        if term.is_clause() {
            let compiled_query = Line::Query(self.compile_target(term, false));
            code.push(compiled_query);
        }

        Self::add_conditional_call(&mut code, term, 0);

        code
    }

    fn split_predicate(clauses: &Vec<PredicateClause>) -> Vec<(usize, usize)>
    {
        let mut subseqs = Vec::new();
        let mut left_index = 0;

        for (right_index, clause) in clauses.iter().enumerate() {
            if let Some(&Term::Var(_, _)) = clause.first_arg() {
                if left_index < right_index {
                    subseqs.push((left_index, right_index));
                }

                subseqs.push((right_index, right_index + 1));
                left_index = right_index + 1;
            }
        }

        if left_index < clauses.len() {
            subseqs.push((left_index, clauses.len()));
        }

        subseqs
    }

    fn compile_pred_subseq(&mut self, clauses: &'a [PredicateClause]) -> Code
    {
        let mut code_body = Vec::new();
        let mut code_offsets = CodeOffsets::new();

        let multi_clause = clauses.len() > 1;

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_code = match clause {
                &PredicateClause::Fact(ref fact) =>
                    self.compile_fact(fact),
                &PredicateClause::Rule(ref rule) =>
                    self.compile_rule(rule)
            };

            if multi_clause {
                let choice = match i {
                    0 => ChoiceInstruction::TryMeElse(clause_code.len() + 1),
                    _ if i == clauses.len() - 1 => ChoiceInstruction::TrustMe,
                    _ => ChoiceInstruction::RetryMeElse(clause_code.len() + 1)
                };

                code_body.push(Line::Choice(choice));
            }

            clause.first_arg().map(|arg| {
                let index = code_body.len();
                code_offsets.index_term(arg, index);
            });

            code_body.append(&mut clause_code);
        }

        let mut code = Vec::new();

        code_offsets.add_indices(&mut code, code_body);
        code
    }

    pub fn compile_predicate(&mut self, clauses: &'a Vec<PredicateClause>) -> Code
    {
        let mut code = Vec::new();
        let split_pred = Self::split_predicate(clauses);
        let multi_seq  = split_pred.len() > 1;

        for &(l, r) in split_pred.iter() {
            let mut code_segment = self.compile_pred_subseq(&clauses[l .. r]);

            if multi_seq {
                let choice = match l {
                    0 => ChoiceInstruction::TryMeElse(code_segment.len() + 1),
                    _ if r == clauses.len() => ChoiceInstruction::TrustMe,
                    _ => ChoiceInstruction::RetryMeElse(code_segment.len() + 1)
                };

                code.push(Line::Choice(choice));
            }

            code.append(&mut code_segment);
        }

        code
    }
}
