use prolog_parser::ast::*;

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
pub enum VarStatus {
    Perm(usize),
    Temp(usize, TempVarData), // Perm(chunk_num) | Temp(chunk_num, _)
}

pub type OccurrenceSet = BTreeSet<(GenContext, usize)>;

// Perm: 0 initially, a stack register once processed.
// Temp: labeled with chunk_num and temp offset (unassigned if 0).
#[derive(Debug)]
pub enum VarData {
    Perm(usize),
    Temp(usize, usize, TempVarData),
}

impl VarData {
    pub fn as_reg_type(&self) -> RegType {
        match self {
            &VarData::Temp(_, r, _) => RegType::Temp(r),
            &VarData::Perm(r) => RegType::Perm(r),
        }
    }
}

#[derive(Debug)]
pub struct TempVarData {
    pub last_term_arity: usize,
    pub use_set: OccurrenceSet,
    pub no_use_set: BTreeSet<usize>,
    pub conflict_set: BTreeSet<usize>,
}

impl TempVarData {
    pub fn new(last_term_arity: usize) -> Self {
        TempVarData {
            last_term_arity: last_term_arity,
            use_set: BTreeSet::new(),
            no_use_set: BTreeSet::new(),
            conflict_set: BTreeSet::new(),
        }
    }

    pub fn uses_reg(&self, reg: usize) -> bool {
        for &(_, nreg) in self.use_set.iter() {
            if reg == nreg {
                return true;
            }
        }

        return false;
    }

    pub fn populate_conflict_set(&mut self) {
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
pub struct VariableFixtures<'a> {
    perm_vars: IndexMap<Rc<Var>, VariableFixture<'a>>,
    last_chunk_temp_vars: IndexSet<Rc<Var>>,
}

impl<'a> VariableFixtures<'a> {
    pub fn new() -> Self {
        VariableFixtures {
            perm_vars: IndexMap::new(),
            last_chunk_temp_vars: IndexSet::new(),
        }
    }

    pub fn insert(&mut self, var: Rc<Var>, vs: VariableFixture<'a>) {
        self.perm_vars.insert(var, vs);
    }

    pub fn insert_last_chunk_temp_var(&mut self, var: Rc<Var>) {
        self.last_chunk_temp_vars.insert(var);
    }

    // computes no_use and conflict sets for all temp vars.
    pub fn populate_restricting_sets(&mut self) {
        // three stages:
        // 1. move the use sets of each variable to a local IndexMap, use_set
        // (iterate mutably, swap mutable refs).
        // 2. drain use_set. For each use set of U, add into the
        // no-use sets of appropriate variables T =/= U.
        // 3. Move the use sets back to their original locations in the fixture.
        // Compute the conflict set of u.

        // 1.
        let mut use_sets: IndexMap<Rc<Var>, OccurrenceSet> = IndexMap::new();

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

    fn get_mut(&mut self, u: Rc<Var>) -> Option<&mut VariableFixture<'a>> {
        self.perm_vars.get_mut(&u)
    }

    fn iter_mut(&mut self) -> indexmap::map::IterMut<Rc<Var>, VariableFixture<'a>> {
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

    pub fn vars_above_threshold(&self, index: usize) -> usize {
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

    pub fn mark_vars_in_chunk<I>(&mut self, iter: I, lt_arity: usize, term_loc: GenContext)
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

    pub fn into_iter(self) -> indexmap::map::IntoIter<Rc<Var>, VariableFixture<'a>> {
        self.perm_vars.into_iter()
    }

    fn values(&self) -> indexmap::map::Values<Rc<Var>, VariableFixture<'a>> {
        self.perm_vars.values()
    }

    pub fn size(&self) -> usize {
        self.perm_vars.len()
    }

    pub fn set_perm_vals(&self, has_deep_cuts: bool) {
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
pub struct UnsafeVarMarker {
    pub unsafe_vars: IndexMap<RegType, usize>,
    pub safe_vars: IndexSet<RegType>,
}

impl UnsafeVarMarker {
    pub fn new() -> Self {
        UnsafeVarMarker {
            unsafe_vars: IndexMap::new(),
            safe_vars: IndexSet::new(),
        }
    }

    pub fn from_safe_vars(safe_vars: IndexSet<RegType>) -> Self {
        UnsafeVarMarker {
            unsafe_vars: IndexMap::new(),
            safe_vars,
        }
    }

    pub fn mark_safe_vars(&mut self, query_instr: &QueryInstruction) -> bool {
        match query_instr {
            &QueryInstruction::PutVariable(r @ RegType::Temp(_), _)
            | &QueryInstruction::SetVariable(r) => {
                self.safe_vars.insert(r);
                true
            }
            _ => false,
        }
    }

    pub fn mark_phase(&mut self, query_instr: &QueryInstruction, phase: usize) {
        match query_instr {
            &QueryInstruction::PutValue(r @ RegType::Perm(_), _)
            | &QueryInstruction::SetValue(r) => {
                let p = self.unsafe_vars.entry(r).or_insert(0);
                *p = phase;
            }
            _ => {}
        }
    }

    pub fn mark_unsafe_vars(&mut self, query_instr: &mut QueryInstruction, phase: usize) {
        match query_instr {
            &mut QueryInstruction::PutValue(RegType::Perm(i), arg) => {
                if let Some(p) = self.unsafe_vars.swap_remove(&RegType::Perm(i)) {
                    if p == phase {
                        *query_instr = QueryInstruction::PutUnsafeValue(i, arg);
                        self.safe_vars.insert(RegType::Perm(i));
                    } else {
                        self.unsafe_vars.insert(RegType::Perm(i), p);
                    }
                }
            }
            &mut QueryInstruction::SetValue(r) => {
                if !self.safe_vars.contains(&r) {
                    *query_instr = QueryInstruction::SetLocalValue(r);

                    self.safe_vars.insert(r);
                    self.unsafe_vars.remove(&r);
                }
            }
            _ => {}
        }
    }
}
