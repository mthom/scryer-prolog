use crate::parser::ast::*;

use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::collections::BTreeSet;
use std::mem::swap;
use std::rc::Rc;
use std::vec::Vec;

// labeled with chunk numbers.
#[derive(Debug)]
pub(crate) enum VarStatus {
    Perm(usize),
    Temp(usize, TempVarData), // Perm(chunk_num) | Temp(chunk_num, _)
}

pub(crate) type OccurrenceSet = BTreeSet<(GenContext, usize)>;

// Perm: 0 initially, a stack register once processed.
// Temp: labeled with chunk_num and temp offset (unassigned if 0).
#[derive(Debug)]
pub(crate) enum VarData {
    Perm(usize),
    Temp(usize, usize, TempVarData),
}

impl VarData {
    pub(crate) fn as_reg_type(&self) -> RegType {
        match self {
            &VarData::Temp(_, r, _) => RegType::Temp(r),
            &VarData::Perm(r) => RegType::Perm(r),
        }
    }
}

#[derive(Debug)]
pub(crate) struct TempVarData {
    pub(crate) last_term_arity: usize,
    pub(crate) use_set: OccurrenceSet,
    pub(crate) no_use_set: BTreeSet<usize>,
    pub(crate) conflict_set: BTreeSet<usize>,
}

impl TempVarData {
    pub(crate) fn new(last_term_arity: usize) -> Self {
        TempVarData {
            last_term_arity: last_term_arity,
            use_set: BTreeSet::new(),
            no_use_set: BTreeSet::new(),
            conflict_set: BTreeSet::new(),
        }
    }

    pub(crate) fn uses_reg(&self, reg: usize) -> bool {
        for &(_, nreg) in self.use_set.iter() {
            if reg == nreg {
                return true;
            }
        }

        return false;
    }

    pub(crate) fn populate_conflict_set(&mut self) {
        if self.last_term_arity > 0 {
            let arity = self.last_term_arity;
            let mut conflict_set: BTreeSet<usize> = (1..arity).collect();

            for &(_, reg) in self.use_set.iter() {
                conflict_set.remove(&reg);
            }

            self.conflict_set = conflict_set;
        }
    }
}

type VariableFixture<'a> = (VarStatus, Vec<&'a Cell<VarReg>>);

#[derive(Debug)]
pub(crate) struct VariableFixtures<'a> {
    perm_vars: IndexMap<Rc<String>, VariableFixture<'a>>,
    last_chunk_temp_vars: IndexSet<Rc<String>>,
}

impl<'a> VariableFixtures<'a> {
    pub(crate) fn new() -> Self {
        VariableFixtures {
            perm_vars: IndexMap::new(),
            last_chunk_temp_vars: IndexSet::new(),
        }
    }

    pub(crate) fn insert(&mut self, var: Rc<String>, vs: VariableFixture<'a>) {
        self.perm_vars.insert(var, vs);
    }

    pub(crate) fn insert_last_chunk_temp_var(&mut self, var: Rc<String>) {
        self.last_chunk_temp_vars.insert(var);
    }

    // computes no_use and conflict sets for all temp vars.
    pub(crate) fn populate_restricting_sets(&mut self) {
        // three stages:
        // 1. move the use sets of each variable to a local IndexMap, use_set
        // (iterate mutably, swap mutable refs).
        // 2. drain use_set. For each use set of U, add into the
        // no-use sets of appropriate variables T =/= U.
        // 3. Move the use sets back to their original locations in the fixture.
        // Compute the conflict set of u.

        // 1.
        let mut use_sets: IndexMap<Rc<String>, OccurrenceSet> = IndexMap::new();

        for (var, &mut (ref mut var_status, _)) in self.iter_mut() {
            if let &mut VarStatus::Temp(_, ref mut var_data) = var_status {
                let mut use_set = OccurrenceSet::new();

                swap(&mut var_data.use_set, &mut use_set);
                use_sets.insert((*var).clone(), use_set);
            }
        }

        for (u, use_set) in use_sets.drain(..) {
            // 2.
            for &(term_loc, reg) in use_set.iter() {
                if let GenContext::Last(cn_u) = term_loc {
                    for (ref t, &mut (ref mut var_status, _)) in self.iter_mut() {
                        if let &mut VarStatus::Temp(cn_t, ref mut t_data) = var_status {
                            if cn_u == cn_t && *u != ***t {
                                if !t_data.uses_reg(reg) {
                                    t_data.no_use_set.insert(reg);
                                }
                            }
                        }
                    }
                }
            }

            // 3.
            match self.get_mut(u).unwrap() {
                &mut (VarStatus::Temp(_, ref mut u_data), _) => {
                    u_data.use_set = use_set;
                    u_data.populate_conflict_set();
                }
                _ => {}
            };
        }
    }

    fn get_mut(&mut self, u: Rc<String>) -> Option<&mut VariableFixture<'a>> {
        self.perm_vars.get_mut(&u)
    }

    fn iter_mut(&mut self) -> indexmap::map::IterMut<Rc<String>, VariableFixture<'a>> {
        self.perm_vars.iter_mut()
    }

    fn record_temp_info(&mut self, tvd: &mut TempVarData, arg_c: usize, term_loc: GenContext) {
        match term_loc {
            GenContext::Head | GenContext::Last(_) => {
                tvd.use_set.insert((term_loc, arg_c));
            }
            _ => {}
        };
    }

    pub(crate) fn vars_above_threshold(&self, index: usize) -> usize {
        let mut var_count = 0;

        for &(ref var_status, _) in self.values() {
            if let &VarStatus::Perm(i) = var_status {
                if i > index {
                    var_count += 1;
                }
            }
        }

        var_count
    }

    pub(crate) fn mark_vars_in_chunk<I>(&mut self, iter: I, lt_arity: usize, term_loc: GenContext)
    where
        I: Iterator<Item = TermRef<'a>>,
    {
        let chunk_num = term_loc.chunk_num();
        let mut arg_c = 1;

        for term_ref in iter {
            if let &TermRef::Var(lvl, cell, ref var) = &term_ref {
                let mut status = self.perm_vars.swap_remove(var).unwrap_or((
                    VarStatus::Temp(chunk_num, TempVarData::new(lt_arity)),
                    Vec::new(),
                ));

                status.1.push(cell);

                match status.0 {
                    VarStatus::Temp(cn, ref mut tvd) if cn == chunk_num => {
                        if let Level::Shallow = lvl {
                            self.record_temp_info(tvd, arg_c, term_loc);
                        }
                    }
                    _ => status.0 = VarStatus::Perm(chunk_num),
                };

                self.perm_vars.insert(var.clone(), status);
            }

            if let Level::Shallow = term_ref.level() {
                arg_c += 1;
            }
        }
    }

    pub(crate) fn into_iter(self) -> indexmap::map::IntoIter<Rc<String>, VariableFixture<'a>> {
        self.perm_vars.into_iter()
    }

    fn values(&self) -> indexmap::map::Values<Rc<String>, VariableFixture<'a>> {
        self.perm_vars.values()
    }

    pub(crate) fn size(&self) -> usize {
        self.perm_vars.len()
    }

    pub(crate) fn set_perm_vals(&self, has_deep_cuts: bool) {
        let mut values_vec: Vec<_> = self
            .values()
            .filter_map(|ref v| match &v.0 {
                &VarStatus::Perm(i) => Some((i, &v.1)),
                _ => None,
            })
            .collect();

        values_vec.sort_by_key(|ref v| v.0);

        let offset = has_deep_cuts as usize;

        for (i, (_, cells)) in values_vec.into_iter().rev().enumerate() {
            for cell in cells {
                cell.set(VarReg::Norm(RegType::Perm(i + 1 + offset)));
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct UnsafeVarMarker {
    pub(crate) unsafe_perm_vars: IndexMap<usize, usize>,
    pub(crate) unsafe_temp_vars: IndexSet<usize>,
    pub(crate) safe_perm_vars: IndexSet<usize>,
    pub(crate) safe_temp_vars: IndexSet<usize>,
    pub(crate) temp_vars_to_perm_vars: IndexMap<usize, usize>,
    pub(crate) perm_vars_to_temp_vars: IndexMap<usize, usize>,
}

impl UnsafeVarMarker {
    pub(crate) fn new() -> Self {
        UnsafeVarMarker {
            unsafe_perm_vars: IndexMap::new(),
            unsafe_temp_vars: IndexSet::new(),
            safe_perm_vars: IndexSet::new(),
            safe_temp_vars: IndexSet::new(),
            temp_vars_to_perm_vars: IndexMap::new(),
            perm_vars_to_temp_vars: IndexMap::new(),
        }
    }

    pub(crate) fn from_fact_vars(safe_vars: IndexSet<RegType>) -> Self {
        let mut unsafe_var_marker = Self::new();

        for r in safe_vars {
            unsafe_var_marker.mark_var_as_safe(r);
        }

        unsafe_var_marker
    }

    fn mark_var_as_safe(&mut self, r: RegType) {
        match r {
            RegType::Temp(t) => {
                self.safe_temp_vars.insert(t);
            }
            RegType::Perm(p) => {
                self.safe_perm_vars.insert(p);
            }
        };
    }

    fn mark_var_as_unsafe(&mut self, r: RegType, phase: usize) {
        match r {
            RegType::Temp(t) => {
                self.unsafe_temp_vars.insert(t);
            }
            RegType::Perm(p) => {
                self.unsafe_perm_vars.insert(p, phase);
            }
        }
    }

    // returns true if the instruction at *query_instr cannot be
    // changed by mark_unsafe_vars.
    fn mark_safe_vars(&mut self, query_instr: &Instruction) -> bool {
        match query_instr {
            &Instruction::PutVariable(r @ RegType::Temp(_), _) |
            &Instruction::SetVariable(r) => {
                self.mark_var_as_safe(r);
                true
            }
            &Instruction::PutVariable(RegType::Perm(p), t) => {
                self.temp_vars_to_perm_vars.insert(t, p);
                true
            }
            &Instruction::CallIs(RegType::Temp(t), ..) => {
                if let Some(p) = self.temp_vars_to_perm_vars.get(&t) {
                    self.mark_var_as_safe(RegType::Perm(*p));
                }

                true
            }
            _ => false,
        }
    }

    fn mark_phase(&mut self, query_instr: &Instruction, phase: usize) {
        match query_instr {
            &Instruction::PutValue(r @ RegType::Perm(_), _) |
            &Instruction::SetValue(r) => {
                self.mark_var_as_unsafe(r, phase);
            }
            _ => {}
        }
    }

    fn mark_unsafe_perm_vars(&mut self, query_instr: &mut Instruction, phase: usize) {
        match query_instr {
            &mut Instruction::PutValue(RegType::Perm(p), arg)
                if !self.safe_perm_vars.contains(&p) => {
                    if let Some(ph) = self.unsafe_perm_vars.swap_remove(&p) {
                        if ph == phase {
                            *query_instr = Instruction::PutUnsafeValue(p, arg);
                            self.perm_vars_to_temp_vars.insert(p, arg);
                        } else {
                            self.unsafe_perm_vars.insert(p, ph);
                        }
                    }
                }
            &mut Instruction::SetValue(r @ RegType::Perm(p)) =>
                if let Some(t) = self.perm_vars_to_temp_vars.get(&p) {
                    *query_instr = Instruction::SetValue(RegType::Temp(*t));
                } else {
                    *query_instr = Instruction::SetLocalValue(r);
                }
            _ => {}
        }
    }

    fn mark_unsafe_temp_vars(&mut self, query_instr: &mut Instruction) {
        match query_instr {
            &mut Instruction::SetValue(r @ RegType::Temp(t))
                if !self.safe_temp_vars.contains(&t) => {
                    *query_instr = Instruction::SetLocalValue(r);

                    self.safe_temp_vars.insert(t);
                    self.unsafe_temp_vars.remove(&t);
                }
            _ => {
            }
        }
    }

    fn clear_temp_vars(&mut self) {
        self.safe_temp_vars.clear();
        self.unsafe_temp_vars.clear();
        self.temp_vars_to_perm_vars.clear();
    }

    pub(crate) fn mark_unsafe_instrs(&mut self, code: &mut Code) {
        if code.is_empty() {
            return;
        }

        let mut code_index = 0;

        for phase in 0.. {
            while code[code_index].is_query_instr() {
                let query_instr = &mut code[code_index];

                if !self.mark_safe_vars(query_instr) {
                    self.mark_phase(query_instr, phase);
                    self.mark_unsafe_temp_vars(query_instr);
                }

                code_index += 1;
            }

            while code_index < code.len() && !code[code_index].is_query_instr() {
                self.mark_safe_vars(&code[code_index]);
                code_index += 1;
            }

            self.clear_temp_vars();

            if code_index >= code.len() {
                break;
            }
        }

        code_index = 0;

        for phase in 0.. {
            while code[code_index].is_query_instr() {
                let query_instr = &mut code[code_index];
                self.mark_unsafe_perm_vars(query_instr, phase);
                code_index += 1;
            }

            // ensure phase->instruction assignments match those of
            // the previous for loop.
            while code_index < code.len() && !code[code_index].is_query_instr() {
                code_index += 1;
            }

            if code_index >= code.len() {
                break;
            }
        }
    }
}
