use crate::forms::*;
use crate::instructions::*;
use crate::machine::disjuncts::ClassifyInfo;
use crate::parser::ast::*;

use bit_set::*;
use indexmap::{IndexMap, IndexSet};

pub(crate) type OccurrenceSet = IndexSet<(GenContext, usize)>;

#[derive(Debug)]
pub(crate) struct TempVarData {
    pub(crate) last_term_arity: usize,
    pub(crate) use_set: OccurrenceSet,
    pub(crate) no_use_set: BitSet<usize>,
    pub(crate) conflict_set: BitSet<usize>,
}

#[derive(Debug)]
pub(crate) struct TempVarStatus {
    chunk_num: usize,
    temp_var_data: TempVarData,
}

// Perm: 0 initially, a stack register once processed.
// Temp: labeled with chunk_num and temp offset (unassigned if 0).
#[derive(Debug)]
pub(crate) enum VarAlloc {
    Perm(usize),
    Temp(usize, usize, TempVarData),
}

impl VarAlloc {
    pub(crate) fn as_reg_type(&self) -> RegType {
        match self {
            &VarAlloc::Temp(_, r, _) => RegType::Temp(r),
            &VarAlloc::Perm(r) => RegType::Perm(r),
        }
    }
}

impl TempVarData {
    pub(crate) fn new(last_term_arity: usize) -> Self {
        TempVarData {
            last_term_arity: last_term_arity,
            use_set: BitSet::<usize>::new(),
            no_use_set: BitSet::new(),
            conflict_set: BitSet::new(),
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
            let mut conflict_set: BitSet<usize> = (1..arity).collect();

            for &(_, reg) in self.use_set.iter() {
                conflict_set.remove(reg);
            }

            self.conflict_set = conflict_set;
        }
    }
}

#[derive(Debug)]
pub(crate) struct VariableFixtures {
    temp_vars: IndexMap<usize, TempVarStatus>,
}

impl VariableFixtures {
    pub(crate) fn new() -> Self {
        VariableFixtures {
            temp_vars: IndexMap::new(),
        }
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
        let mut use_sets: IndexMap<usize, OccurrenceSet> = IndexMap::new();

        for (var_gen_index, ref mut var_status) in self.temp_vars.iter_mut() {
            let TempVarStatus { ref mut temp_var_data, .. } = var_status;
            let mut use_set = OccurrenceSet::new();

            std::mem::swap(&mut temp_var_data.use_set, &mut use_set);
            use_sets.insert(var_gen_index, use_set);
        }

        for (u, use_set) in use_sets.drain(..) {
            // 2.
            for &(term_loc, reg) in use_set.iter() {
                if let GenContext::Last(cn_u) = term_loc {
                    for (var_gen_index, ref mut var_status) in self.terms_vars.iter_mut() {
                        let TempVarStatus { chunk_num, ref mut temp_var_data } = var_status;

                        if cn_u == chunk_num && u != var_gen_index {
                            if !temp_var_data.uses_reg(reg) {
                                temp_var_data.no_use_set.insert(reg);
                            }
                        }
                    }
                }
            }

            // 3.
            let TempVarStatus { ref mut temp_var_data, ..} = self.temp_vars.get_mut(u).unwrap();

            temp_var_data.use_set = use_set;
            temp_var_data.populate_conflict_set();
        }
    }

    fn record_temp_info(&mut self, tvd: &mut TempVarData, arg_c: usize, term_loc: GenContext) {
        match term_loc {
            GenContext::Head | GenContext::Last(_) => {
                tvd.use_set.insert((term_loc, arg_c));
            }
            _ => {}
        };
    }

    pub(crate) fn mark_temp_var(
        &mut self,
        generated_var_index: usize,
        lvl: Level,
        classify_info: &ClassifyInfo,
        term_loc: GenContext,
    ) {
        let chunk_num = term_loc.chunk_num();

        let mut status = self.temp_vars.swap_remove(generated_var_index).unwrap_or_else(|| {
            TempVarStatus {
                chunk_num,
                temp_var_data: TempVarData::new(classify_info.arity),
            }
        });

        if let Level::Shallow = lvl {
            self.record_temp_info(&mut status, classify_info.arg_c, term_loc);
        }

        self.temp_vars.insert(Var::Generated(generated_var_index), status);
    }
}

#[derive(Debug)]
pub(crate) struct UnsafeVarMarker {
    pub(crate) unsafe_perm_vars: IndexMap<usize, usize>,
    pub(crate) unsafe_temp_vars: IndexSet<usize>,
    pub(crate) safe_perm_vars: IndexSet<usize>,
    pub(crate) safe_temp_vars: IndexSet<usize>,
    pub(crate) temp_vars_to_perm_vars: IndexMap<usize, usize>,
}

impl UnsafeVarMarker {
    pub(crate) fn new() -> Self {
        UnsafeVarMarker {
            unsafe_perm_vars: IndexMap::new(),
            unsafe_temp_vars: IndexSet::new(),
            safe_perm_vars: IndexSet::new(),
            safe_temp_vars: IndexSet::new(),
            temp_vars_to_perm_vars: IndexMap::new(),
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
                            self.safe_perm_vars.insert(p);
                        } else {
                            self.unsafe_perm_vars.insert(p, ph);
                        }
                    }
                }
            &mut Instruction::SetValue(r @ RegType::Perm(p))
                if !self.safe_perm_vars.contains(&p) => {
                    *query_instr = Instruction::SetLocalValue(r);

                    self.safe_perm_vars.insert(p);
                    self.unsafe_perm_vars.remove(&p);
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
