use crate::parser::ast::*;

use bit_set::*;
use fxhash::FxBuildHasher;
use indexmap::{IndexMap, IndexSet};
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)]
pub struct TempVarData {
    pub(crate) use_set: IndexSet<(GenContext, usize), FxBuildHasher>,
    pub(crate) no_use_set: BitSet<usize>,
    pub(crate) conflict_set: BitSet<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BranchDesignator {
    pub branch_stack_num: usize,
    pub branch_num: usize,
}

impl BranchDesignator {
    #[inline]
    pub fn is_sub_branch(&self) -> bool {
        self.branch_stack_num > 0
    }
}

#[derive(Debug, Clone, Copy)]
pub enum VarSafetyStatus {
    Needed,
    // which branch planted the last unsafe guarded instruction? It may still be needed.
    LocallyUnneeded(BranchDesignator),
    GloballyUnneeded,
}

impl VarSafetyStatus {
    pub(crate) fn unneeded(current_branch: BranchDesignator) -> Self {
        if current_branch.is_sub_branch() {
            VarSafetyStatus::LocallyUnneeded(current_branch)
        } else {
            VarSafetyStatus::GloballyUnneeded
        }
    }

    #[inline]
    pub(crate) fn needed_if(needed: bool, branch_designator: BranchDesignator) -> Self {
        if needed {
            VarSafetyStatus::Needed
        } else if branch_designator.branch_stack_num == 0 {
            VarSafetyStatus::GloballyUnneeded
        } else {
            VarSafetyStatus::LocallyUnneeded(branch_designator)
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PermVarAllocation {
    Done {
        shallow_safety: VarSafetyStatus,
        deep_safety: VarSafetyStatus,
    },
    Pending,
}

impl PermVarAllocation {
    #[inline]
    pub(crate) fn done() -> Self {
        PermVarAllocation::Done {
            shallow_safety: VarSafetyStatus::Needed,
            deep_safety: VarSafetyStatus::Needed,
        }
    }

    #[inline]
    pub(crate) fn pending(&self) -> bool {
        match self {
            &PermVarAllocation::Pending => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum VarAlloc {
    Temp {
        term_loc: GenContext,
        temp_reg: usize,
        temp_var_data: TempVarData,
        safety: VarSafetyStatus,
        to_perm_var_num: Option<usize>,
    },
    Perm(usize, PermVarAllocation), // stack offset, allocation info
}

impl VarAlloc {
    #[inline]
    pub(crate) fn as_reg_type(&self) -> RegType {
        match self {
            &VarAlloc::Temp { temp_reg, .. } => RegType::Temp(temp_reg),
            &VarAlloc::Perm(r, _) => RegType::Perm(r),
        }
    }

    #[inline]
    pub(crate) fn set_register(&mut self, reg_num: usize) {
        match self {
            VarAlloc::Perm(ref mut p, _) => *p = reg_num,
            VarAlloc::Temp {
                ref mut temp_reg, ..
            } => *temp_reg = reg_num,
        };
    }
}

impl TempVarData {
    pub(crate) fn new() -> Self {
        TempVarData {
            use_set: IndexSet::with_hasher(FxBuildHasher::default()),
            no_use_set: BitSet::default(),
            conflict_set: BitSet::default(),
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
        let arity = self.use_set.len();
        let mut conflict_set: BitSet<usize> = (1..arity).collect();

        for &(_, idx) in &self.use_set {
            conflict_set.remove(idx);
        }

        self.conflict_set = conflict_set;
    }
}

#[derive(Debug, Clone)]
pub struct VariableRecord {
    pub allocation: VarAlloc,
    pub num_occurrences: usize,
    pub running_count: usize,
}

impl Default for VariableRecord {
    fn default() -> Self {
        VariableRecord {
            allocation: VarAlloc::Perm(0, PermVarAllocation::Pending),
            num_occurrences: 0,
            running_count: 0,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct VariableRecords(Vec<VariableRecord>);

impl Deref for VariableRecords {
    type Target = Vec<VariableRecord>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for VariableRecords {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl VariableRecords {
    #[inline]
    pub(crate) fn new(num_records: usize) -> Self {
        Self(vec![VariableRecord::default(); num_records])
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
        let mut use_sets: IndexMap<usize, IndexSet<(GenContext, usize), FxBuildHasher>> =
            IndexMap::new();

        for (var_gen_index, record) in self.0.iter_mut().enumerate() {
            match &mut record.allocation {
                VarAlloc::Temp { temp_var_data, .. } => {
                    let use_set = std::mem::replace(
                        &mut temp_var_data.use_set,
                        IndexSet::with_hasher(FxBuildHasher::default()),
                    );

                    use_sets.insert(var_gen_index, use_set);
                }
                _ => {}
            }
        }

        for (u, use_set) in use_sets.drain(..) {
            // 2.
            for &(term_loc, reg) in &use_set {
                if let GenContext::Last(cn_u) = term_loc {
                    for (var_gen_index, record) in self.0.iter_mut().enumerate() {
                        match &mut record.allocation {
                            VarAlloc::Temp {
                                term_loc,
                                temp_var_data,
                                ..
                            } => {
                                if cn_u == term_loc.chunk_num() && u != var_gen_index {
                                    if !temp_var_data.uses_reg(reg) {
                                        temp_var_data.no_use_set.insert(reg);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }

            // 3.
            if let VarAlloc::Temp { temp_var_data, .. } = &mut self[u].allocation {
                temp_var_data.use_set = use_set;
                temp_var_data.populate_conflict_set();
            }
        }
    }
}
