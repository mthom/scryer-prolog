use crate::allocator::*;
use crate::atom_table::*;
use crate::codegen::SubsumedBranchHits;
use crate::forms::{GenContext, Level};
use crate::instructions::*;
use crate::machine::disjuncts::*;
use crate::machine::heap::*;
use crate::parser::ast::*;
use crate::targets::*;
use crate::types::*;
use crate::variable_records::*;

use bit_set::*;
use bitvec::prelude::*;
use fxhash::FxBuildHasher;
use indexmap::IndexMap;

use std::collections::VecDeque;
use std::ops::{Deref, DerefMut};

pub type BranchHits = IndexMap<usize, BitVec, FxBuildHasher>; // key: var_num, value: branch arm occurrences.

#[derive(Debug, Default)]
pub struct BranchOccurrences {
    pub hits: BranchHits,
    pub shallow_safety: BitSet<usize>, // unset means safe, set means unsafe (after the branch merge)
    pub deep_safety: BitSet<usize>,
    pub num_branches: usize,
    pub current_branch: usize,
    pub subsumed_hits: SubsumedBranchHits,
}

impl BranchOccurrences {
    fn new(num_branches: usize) -> Self {
        Self {
            hits: BranchHits::with_hasher(FxBuildHasher::default()),
            shallow_safety: BitSet::default(),
            deep_safety: BitSet::default(),
            num_branches,
            current_branch: 0,
            subsumed_hits: SubsumedBranchHits::with_hasher(FxBuildHasher::default()),
        }
    }

    pub(crate) fn add_branch_occurrence(&mut self, var_num: usize) {
        debug_assert!(self.current_branch < self.num_branches);
        let num_branches = self.num_branches;

        let entry = self
            .hits
            .entry(var_num)
            .or_insert_with(|| BitVec::repeat(false, num_branches));

        entry.set(self.current_branch, true);
        self.subsumed_hits.insert(var_num);
    }
}

#[derive(Debug)]
pub(crate) struct BranchStack {
    stack: Vec<BranchOccurrences>,
}

impl Deref for BranchStack {
    type Target = Vec<BranchOccurrences>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.stack
    }
}

impl DerefMut for BranchStack {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.stack
    }
}

impl BranchStack {
    fn branch_subsumes(&self, branch: &BranchDesignator, sub_branch: &BranchDesignator) -> bool {
        if branch.branch_stack_num < sub_branch.branch_stack_num {
            if branch.branch_stack_num == 0 {
                true
            } else {
                let idx = branch.branch_stack_num - 1;
                self[idx].current_branch == branch.branch_num
            }
        } else {
            branch == sub_branch
        }
    }

    fn safety_unneeded_in_branch(
        &self,
        safety: &VarSafetyStatus,
        branch: &BranchDesignator,
    ) -> bool {
        match safety {
            VarSafetyStatus::Needed => false,
            VarSafetyStatus::LocallyUnneeded(planter_branch) => {
                self.branch_subsumes(planter_branch, branch)
            }
            VarSafetyStatus::GloballyUnneeded => true,
        }
    }

    pub(crate) fn add_branch_occurrence(&mut self, var_num: usize) {
        if let Some(occurrences) = self.last_mut() {
            occurrences.add_branch_occurrence(var_num);
        }
    }

    pub(crate) fn add_branch_stack(&mut self, num_branches: usize) {
        self.push(BranchOccurrences::new(num_branches));
    }

    pub(crate) fn current_branch_designator(&self) -> BranchDesignator {
        let branch_stack_num = self.len();
        let branch_num = self
            .last()
            .map(|occurrences| occurrences.current_branch)
            .unwrap_or(0);

        BranchDesignator {
            branch_stack_num,
            branch_num,
        }
    }

    #[inline]
    pub(crate) fn incr_current_branch(&mut self) {
        let branch_occurrences = self.last_mut().unwrap();
        branch_occurrences.current_branch += 1;
    }

    #[inline]
    pub(crate) fn drain_branches(&mut self, depth: usize) -> std::vec::Drain<BranchOccurrences> {
        let start_idx = self.len() - depth;
        self.drain(start_idx..)
    }
}

#[derive(Debug)]
pub(crate) struct DebrayAllocator {
    pub(crate) var_data: VarData, // var_data replaces bindings.
    pub(crate) branch_stack: BranchStack,
    pub(crate) in_tail_position: bool,
    arg_c: usize,
    temp_lb: usize,
    perm_lb: usize,
    arity: usize, // 0 if not at head.
    shallow_temp_mappings: IndexMap<usize, usize, FxBuildHasher>,
    in_use: BitSet<usize>, // deep and non-var allocations
    temp_free_list: Vec<usize>,
    perm_free_list: VecDeque<(usize, usize)>, // chunk_num, var_num
    non_var_registers: IndexMap<usize, usize, FxBuildHasher>,
    non_var_register_heap_locs: IndexMap<usize, usize, FxBuildHasher>,
}

impl DebrayAllocator {
    pub(crate) fn add_branch(&mut self) {
        let branch_designator = self.branch_stack.current_branch_designator();
        let subsumed_hits = {
            let branch_occurrences = self.branch_stack.last_mut().unwrap();

            std::mem::replace(
                &mut branch_occurrences.subsumed_hits,
                SubsumedBranchHits::with_hasher(FxBuildHasher::default()),
            )
        };

        for var_num in subsumed_hits {
            match &mut self.var_data.records[var_num].allocation {
                VarAlloc::Perm { ref mut allocation, .. } => {
                    if let PermVarAllocation::Done {
                        shallow_safety,
                        deep_safety,
                        ..
                    } = allocation
                    {
                        if !self
                            .branch_stack
                            .safety_unneeded_in_branch(shallow_safety, &branch_designator)
                        {
                            let branch_occurrences = self.branch_stack.last_mut().unwrap();
                            branch_occurrences.shallow_safety.insert(var_num);
                        }

                        if !self
                            .branch_stack
                            .safety_unneeded_in_branch(deep_safety, &branch_designator)
                        {
                            let branch_occurrences = self.branch_stack.last_mut().unwrap();
                            branch_occurrences.deep_safety.insert(var_num);
                        }
                    }

                    *allocation = PermVarAllocation::Pending;
                }
                _ => unreachable!(),
            }
        }
    }

    pub(crate) fn pop_branch(&mut self, depth: usize, subsumed_hits: SubsumedBranchHits) {
        let removed_branches = self.branch_stack.drain_branches(depth);

        let (deep_safety, shallow_safety) = removed_branches.into_iter().fold(
            (BitSet::default(), BitSet::default()),
            |(mut deep_safety, mut shallow_safety), branch_occurrences| {
                deep_safety.union_with(&branch_occurrences.deep_safety);
                shallow_safety.union_with(&branch_occurrences.shallow_safety);

                (deep_safety, shallow_safety)
            },
        );

        let branch_designator = self.branch_stack.current_branch_designator();

        let (deep_safety, shallow_safety) = match self.branch_stack.last_mut() {
            Some(latest_branch) => {
                latest_branch.deep_safety.union_with(&deep_safety);
                latest_branch.shallow_safety.union_with(&shallow_safety);

                (&latest_branch.deep_safety, &latest_branch.shallow_safety)
            }
            None => (&deep_safety, &shallow_safety),
        };

        for var_num in subsumed_hits.iter().cloned() {
            let running_count = self.var_data.records[var_num].running_count;
            let num_occurrences = self.var_data.records[var_num].num_occurrences;

            match &mut self.var_data.records[var_num].allocation {
                VarAlloc::Perm { allocation, ..} => {
                    let shallow_safety = VarSafetyStatus::needed_if(
                        shallow_safety.contains(var_num),
                        branch_designator,
                    );

                    let deep_safety = VarSafetyStatus::needed_if(
                        deep_safety.contains(var_num),
                        branch_designator,
                    );

                    if running_count < num_occurrences {
                        *allocation = PermVarAllocation::Done {
                            shallow_safety,
                            deep_safety,
                        };
                    }
                }
                _ => unreachable!(),
            }
        }

        if self.branch_stack.len() > 0 {
            for var_num in subsumed_hits {
                self.branch_stack.add_branch_occurrence(var_num);
            }
        }
    }

    fn is_curr_arg_distinct_from(&self, var_num: usize) -> bool {
        match self.shallow_temp_mappings.get(&self.arg_c).cloned() {
            Some(t_var) => t_var != var_num,
            _ => false,
        }
    }

    fn occurs_shallowly_in_head(&self, var_num: usize, r: usize) -> bool {
        match &self.var_data.records[var_num].allocation {
            VarAlloc::Temp {
                temp_var_data,
                term_loc: GenContext::Head,
                ..
            } => temp_var_data.use_set.contains(&(GenContext::Head, r)),
            _ => false,
        }
    }

    #[inline]
    fn is_in_use(&self, r: usize) -> bool {
        let in_use_range = r <= self.arity && r >= self.arg_c;
        in_use_range || self.in_use.contains(r)
    }

    fn alloc_with_cr(&self, var_num: usize) -> usize {
        match &self.var_data.records[var_num].allocation {
            VarAlloc::Temp { temp_var_data, .. } => {
                for &(_, reg) in temp_var_data.use_set.iter() {
                    if !self.is_in_use(reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb.. {
                    if !self.is_in_use(reg) && !temp_var_data.no_use_set.contains(reg) {
                        result = reg;
                        break;
                    }
                }

                result
            }
            _ => 0,
        }
    }

    fn alloc_with_ca(&self, var_num: usize) -> usize {
        match &self.var_data.records[var_num].allocation {
            VarAlloc::Temp { temp_var_data, .. } => {
                for &(_, reg) in temp_var_data.use_set.iter() {
                    if !self.is_in_use(reg) {
                        return reg;
                    }
                }

                let mut result = 0;

                for reg in self.temp_lb.. {
                    if !self.is_in_use(reg)
                        && !temp_var_data.no_use_set.contains(reg)
                        && !temp_var_data.conflict_set.contains(reg)
                    {
                        result = reg;
                        break;
                    }
                }

                result
            }
            _ => 0,
        }
    }

    fn alloc_in_last_goal_hint(&self, chunk_num: usize) -> Option<(usize, usize)> {
        // we want to allocate a register to the k^{th} parameter, par_k.
        // par_k may not be a temporary variable.
        let k = self.arg_c;

        match self.shallow_temp_mappings.get(&k).cloned() {
            Some(t_var) => {
                // suppose this branch fires. then t_var is a
                // temp. var. belonging to the current chunk.
                // consider its use set. T == par_k iff
                // (GenContext::Last(_), k) is in t_var.use_set.

                if let VarAlloc::Temp { temp_var_data, .. } =
                    &self.var_data.records[t_var].allocation
                {
                    if !temp_var_data
                        .use_set
                        .contains(&(GenContext::Last(chunk_num), k))
                    {
                        return Some((t_var, self.alloc_with_ca(t_var)));
                    }
                }

                None
            }
            _ => None,
        }
    }

    fn evacuate_arg<'a, Target: CompilationTarget<'a>>(
        &mut self,
        chunk_num: usize,
        code: &mut CodeDeque,
    ) -> Option<RegType> {
        if let Some((var_num, r)) = self.alloc_in_last_goal_hint(chunk_num) {
            let k = self.arg_c;

            if r != k {
                let r = RegType::Temp(r);

                code.push_back(Target::move_to_register(r, k));

                self.shallow_temp_mappings.swap_remove(&k);
                self.shallow_temp_mappings.insert(r.reg_num(), var_num);

                self.var_data.records[var_num]
                    .allocation
                    .set_register(r.reg_num());
                self.in_use.insert(r.reg_num());

                return Some(r);
            }
        };

        None
    }

    fn alloc_reg_to_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        term_loc: GenContext,
        target: &mut CodeDeque,
    ) -> usize {
        match term_loc {
            GenContext::Head => {
                if let Level::Shallow = lvl {
                    self.evacuate_arg::<Target>(0, target);
                    self.alloc_with_cr(var_num)
                } else {
                    self.alloc_with_ca(var_num)
                }
            }
            GenContext::Mid(_) => self.alloc_with_ca(var_num),
            GenContext::Last(chunk_num) => {
                if let Level::Shallow = lvl {
                    self.evacuate_arg::<Target>(chunk_num, target);
                    self.alloc_with_cr(var_num)
                } else {
                    self.alloc_with_ca(var_num)
                }
            }
        }
    }

    fn alloc_reg_to_non_var(&mut self) -> usize {
        let mut final_index = 0;

        while let Some(r) = self.temp_free_list.pop() {
            if !self.is_in_use(r) {
                self.in_use.insert(r);
                return r;
            }
        }

        for index in self.temp_lb.. {
            if !self.in_use.contains(index) {
                final_index = index;
                self.in_use.insert(final_index);
                break;
            }
        }

        self.temp_lb = final_index + 1;

        final_index
    }

    fn in_place(&self, var_num: usize, term_loc: GenContext, r: RegType, k: usize) -> bool {
        match term_loc {
            GenContext::Head if !r.is_perm() => r.reg_num() == k,
            _ => match &self.var_data.records[var_num].allocation {
                &VarAlloc::Temp { temp_reg, .. } if r.reg_num() == k => temp_reg == k,
                _ => false,
            },
        }
    }

    fn alloc_perm_var(&mut self, var_num: usize, chunk_num: usize) -> usize {
        let p = if let Some(p) = self.pop_free_perm(chunk_num) {
            p
        } else {
            let p = self.perm_lb;
            self.perm_lb += 1;

            p
        };

        self.var_data.records[var_num].allocation = VarAlloc::Perm {
            reg: p,
            allocation: PermVarAllocation::done(),
        };

        p
    }

    pub(crate) fn add_reg_to_free_list(&mut self, r: RegType) {
        if let RegType::Temp(r) = r {
            self.in_use.remove(r);
            self.temp_free_list.push(r);
        }
    }

    pub fn reset_free_list(&mut self) {
        self.temp_free_list.clear();
    }

    #[inline(always)]
    pub fn get_var_binding(&self, var_num: usize) -> RegType {
        self.var_data.records[var_num].allocation.as_reg_type()
    }

    #[inline(always)]
    pub fn get_non_var_binding(&self, heap_loc: usize) -> RegType {
        RegType::Temp(self.non_var_registers.get(&heap_loc).cloned().unwrap_or(0))
    }

    pub fn num_perm_vars(&self) -> usize {
        self.perm_lb - 1
    }

    pub fn increment_running_count(&mut self, var_num: usize) {
        self.var_data.records[var_num].running_count += 1;
    }

    fn add_perm_to_free_list(&mut self, chunk_num: usize, var_num: usize) {
        if let VarAlloc::Perm { .. } = &self.var_data.records[var_num].allocation {
            self.perm_free_list.push_back((chunk_num, var_num));
        }
    }

    fn pop_free_perm(&mut self, chunk_num: usize) -> Option<usize> {
        while let Some((perm_chunk_num, var_num)) = self.perm_free_list.front().cloned() {
            if chunk_num > perm_chunk_num {
                self.perm_free_list.pop_front();

                match &mut self.var_data.records[var_num].allocation {
                    VarAlloc::Perm { reg: p, allocation: PermVarAllocation::Pending }
                      if *p > 0 => {
                          return Some(std::mem::replace(p, 0));
                      }
                    _ => {}
                }
            } else {
                return None;
            }
        }

        None
    }

    pub(crate) fn free_var(&mut self, chunk_num: usize, var_num: usize) {
        match &mut self.var_data.records[var_num].allocation {
            VarAlloc::Perm { allocation, .. } => {
                *allocation = PermVarAllocation::Pending;
                self.add_perm_to_free_list(chunk_num, var_num);
            }
            _ => {}
        }
    }

    pub(crate) fn mark_safe_var_unconditionally(&mut self, var_num: usize) {
        let branch_designator = self.branch_stack.current_branch_designator();

        match &mut self.var_data.records[var_num].allocation {
            VarAlloc::Perm {
                allocation: PermVarAllocation::Done {
                    deep_safety,
                    shallow_safety,
                    ..
                },
                ..
            } => {
                *deep_safety = VarSafetyStatus::unneeded(branch_designator);
                *shallow_safety = VarSafetyStatus::unneeded(branch_designator);
            }
            VarAlloc::Temp { safety, .. } => {
                *safety = VarSafetyStatus::unneeded(branch_designator);
            }
            _ => {
                // the (permanent) variable might have been freed by
                // this point, in which case we do nothing.
            }
        }
    }

    fn mark_safe_var(&mut self, var_num: usize, lvl: Level, term_loc: GenContext) {
        let branch_designator = self.branch_stack.current_branch_designator();

        match &mut self.var_data.records[var_num].allocation {
            VarAlloc::Perm {
                allocation: PermVarAllocation::Done {
                    deep_safety,
                    shallow_safety,
                    ..
                },
                ..
            } => {
                // GetVariable in head chunk is considered safe.
                if lvl == Level::Deep {
                    *deep_safety = VarSafetyStatus::unneeded(branch_designator);
                    *shallow_safety = VarSafetyStatus::unneeded(branch_designator);
                } else if term_loc == GenContext::Head {
                    *shallow_safety = VarSafetyStatus::GloballyUnneeded;
                } else if let Some(&temp_var_num) = self.shallow_temp_mappings.get(&self.arg_c) {
                    match &mut self.var_data.records[temp_var_num].allocation {
                        VarAlloc::Temp {
                            ref mut to_perm_var_num,
                            ..
                        } => {
                            *to_perm_var_num = Some(var_num);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            VarAlloc::Temp { ref mut safety, .. } => {
                *safety = VarSafetyStatus::GloballyUnneeded;
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn argument_to_value<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        r: RegType,
        arg_c: usize,
    ) -> Instruction {
        let branch_designator = self.branch_stack.current_branch_designator();

        match &mut self.var_data.records[var_num].allocation {
            VarAlloc::Perm {
                allocation: PermVarAllocation::Done {
                    ref mut shallow_safety,
                    ..
                },
                ..
            } => {
                if !self.in_tail_position
                    || self
                        .branch_stack
                        .safety_unneeded_in_branch(shallow_safety, &branch_designator)
                {
                    Target::argument_to_value(r, arg_c)
                } else {
                    *shallow_safety = VarSafetyStatus::unneeded(branch_designator);
                    Target::unsafe_argument_to_value(r, arg_c)
                }
            }
            VarAlloc::Temp { .. } => {
                debug_assert!(matches!(r, RegType::Temp(_)));
                Target::argument_to_value(r, arg_c)
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn subterm_to_value<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        r: RegType,
    ) -> Instruction {
        let branch_designator = self.branch_stack.current_branch_designator();

        match &mut self.var_data.records[var_num].allocation {
            VarAlloc::Perm {
                allocation: PermVarAllocation::Done {
                    ref mut deep_safety,
                    ..
                },
                ..
            } => {
                if self
                    .branch_stack
                    .safety_unneeded_in_branch(deep_safety, &branch_designator)
                {
                    Target::subterm_to_value(r)
                } else {
                    *deep_safety = VarSafetyStatus::unneeded(branch_designator);
                    Target::unsafe_subterm_to_value(r)
                }
            }
            VarAlloc::Temp { ref mut safety, .. } => {
                if self
                    .branch_stack
                    .safety_unneeded_in_branch(safety, &branch_designator)
                {
                    Target::subterm_to_value(r)
                } else {
                    *safety = VarSafetyStatus::unneeded(branch_designator);
                    Target::unsafe_subterm_to_value(r)
                }
            }
            _ => {
                unreachable!()
            }
        }
    }
}

impl Allocator for DebrayAllocator {
    fn new() -> DebrayAllocator {
        Self {
            var_data: VarData::default(),
            in_tail_position: false,
            arity: 0,
            arg_c: 1,
            temp_lb: 1,
            perm_lb: 1,
            shallow_temp_mappings: IndexMap::with_hasher(FxBuildHasher::default()),
            in_use: BitSet::default(),
            temp_free_list: vec![],
            perm_free_list: VecDeque::new(),
            branch_stack: BranchStack { stack: vec![] },
            non_var_registers: IndexMap::with_hasher(FxBuildHasher::default()),
            non_var_register_heap_locs: IndexMap::with_hasher(FxBuildHasher::default()),
        }
    }

    fn mark_anon_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType {
        let r = RegType::Temp(self.alloc_reg_to_non_var());

        match lvl {
            Level::Deep => code.push_back(Target::subterm_to_variable(r)),
            Level::Root | Level::Shallow => {
                let k = self.arg_c;

                if let GenContext::Last(chunk_num) = context {
                    self.evacuate_arg::<Target>(chunk_num, code);
                }

                self.arg_c += 1;

                code.push_back(Target::argument_to_variable(r, k));
            }
        };

        r
    }

    fn mark_non_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        lvl: Level,
        heap_loc: usize,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType {
        let r = self.get_non_var_binding(heap_loc);

        let r = match lvl {
            Level::Shallow => {
                let k = self.arg_c;

                if let GenContext::Last(chunk_num) = context {
                    if let Some(new_r) = self.evacuate_arg::<Target>(chunk_num, code) {
                        self.non_var_register_heap_locs
                            .swap_remove(&k)
                            .map(|old_heap_loc| {
                                self.non_var_registers.insert(old_heap_loc, new_r.reg_num());
                                self.non_var_register_heap_locs
                                    .insert(new_r.reg_num(), old_heap_loc);
                            });

                        self.non_var_registers.insert(heap_loc, k);
                        self.non_var_register_heap_locs.insert(k, heap_loc);
                    }
                }

                self.arg_c += 1;
                RegType::Temp(k)
            }
            _ if r.reg_num() == 0 => {
                let r = RegType::Temp(self.alloc_reg_to_non_var());
                self.non_var_registers.insert(heap_loc, r.reg_num());
                self.non_var_register_heap_locs
                    .insert(r.reg_num(), heap_loc);
                r
            }
            _ => {
                self.in_use.insert(r.reg_num());
                r
            }
        };

        r
    }

    fn mark_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType {
        let (r, is_new_var) = match self.get_var_binding(var_num) {
            RegType::Temp(0) => {
                let o = self.alloc_reg_to_var::<Target>(var_num, lvl, context, code);
                (RegType::Temp(o), true)
            }
            RegType::Perm(0) => {
                let p = self.alloc_perm_var(var_num, context.chunk_num());
                (RegType::Perm(p), true)
            }
            r @ RegType::Perm(_) => {
                let is_new_var = match &mut self.var_data.records[var_num].allocation {
                    VarAlloc::Perm { allocation, .. } => {
                        if allocation.pending() {
                            *allocation = PermVarAllocation::done();
                            true
                        } else {
                            false
                        }
                    }
                    _ => unreachable!(),
                };

                (r, is_new_var)
            }
            r => (r, false),
        };

        self.mark_reserved_var::<Target>(var_num, lvl, context, code, r, is_new_var)
    }

    fn mark_reserved_var<'a, Target: CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        lvl: Level,
        context: GenContext,
        code: &mut CodeDeque,
        r: RegType,
        is_new_var: bool,
    ) -> RegType {
        match lvl {
            Level::Root | Level::Shallow => {
                let k = self.arg_c;

                if self.is_curr_arg_distinct_from(var_num) {
                    self.evacuate_arg::<Target>(context.chunk_num(), code);
                }

                if !self.in_place(var_num, context, r, k) {
                    if is_new_var {
                        self.mark_safe_var(var_num, lvl, context);
                        code.push_back(Target::argument_to_variable(r, k));
                    } else {
                        code.push_back(self.argument_to_value::<Target>(var_num, r, k));
                    }
                }

                self.arg_c += 1;
            }
            Level::Deep if is_new_var => {
                if let GenContext::Head = context {
                    if self.occurs_shallowly_in_head(var_num, r.reg_num()) {
                        code.push_back(self.subterm_to_value::<Target>(var_num, r));
                    } else {
                        self.mark_safe_var(var_num, lvl, context);
                        code.push_back(Target::subterm_to_variable(r));
                    }
                } else {
                    self.mark_safe_var(var_num, lvl, context);
                    code.push_back(Target::subterm_to_variable(r));
                }
            }
            Level::Deep => code.push_back(self.subterm_to_value::<Target>(var_num, r)),
        }

        let o = r.reg_num();

        if !r.is_perm() {
            self.shallow_temp_mappings.insert(o, var_num);
        } else if r.is_perm() && is_new_var {
            self.branch_stack.add_branch_occurrence(var_num);
        }

        let record = &mut self.var_data.records[var_num];

        record.allocation.set_register(o);

        if record.running_count < record.num_occurrences {
            record.running_count += 1;
        } else {
            self.free_var(context.chunk_num(), var_num);
        }

        self.in_use.insert(o);
        r
    }

    fn mark_cut_var(&mut self, var_num: usize, chunk_num: usize) -> RegType {
        match self.get_var_binding(var_num) {
            RegType::Perm(0) => RegType::Perm(self.alloc_perm_var(var_num, chunk_num)),
            RegType::Temp(0) => {
                let t = self.alloc_reg_to_non_var();

                match &mut self.var_data.records[var_num].allocation {
                    VarAlloc::Temp {
                        temp_reg, safety, ..
                    } => {
                        *temp_reg = t;
                        *safety = VarSafetyStatus::GloballyUnneeded;
                    }
                    _ => unreachable!(),
                };

                RegType::Temp(t)
            }
            r => r,
        }
    }

    fn reset(&mut self) {
        self.perm_lb = 1;
        self.shallow_temp_mappings.clear();
        self.non_var_registers.clear();
        self.non_var_register_heap_locs.clear();
        self.in_use.clear();
        self.temp_free_list.clear();
    }

    fn reset_contents(&mut self) {
        self.in_use.clear();
        self.shallow_temp_mappings.clear();
        self.non_var_registers.clear();
        self.non_var_register_heap_locs.clear();
        self.temp_free_list.clear();
    }

    fn advance_arg(&mut self) {
        self.arg_c += 1;
    }

    fn reset_at_head(&mut self, heap: &mut Heap, head_loc: usize) {
        let head_cell = heap_bound_store(
            heap,
            heap_bound_deref(heap, heap_loc_as_cell!(head_loc)),
        );

        read_heap_cell!(head_cell,
            (HeapCellValueTag::Str, s) => {
                let arity = cell_as_atom_cell!(heap[s]).get_arity();

                self.reset_arg(arity);
                self.arity = arity;

                for (idx, arg) in heap.splice(s+1 ..= s+arity).enumerate() {
                    if arg.is_var() {
                        let var = heap_bound_store(
                            heap,
                            heap_bound_deref(heap, arg),
                        );

                        if !var.is_var() {
                            continue;
                        }

                        let term_loc = var.get_value() as usize;

                        match self.var_data.var_locs_to_nums.get(
                            VarPtrIndex { chunk_num: 0, term_loc },
                        ) {
                            VarPtr::Numbered(var_num) => {
                                let r = self.get_var_binding(var_num);

                                if !r.is_perm() && r.reg_num() == 0 {
                                    self.in_use.insert(idx + 1);
                                    self.shallow_temp_mappings.insert(idx + 1, var_num);
                                    self.var_data.records[var_num]
                                        .allocation
                                        .set_register(idx + 1);
                                }
                            }
                            VarPtr::Anon => {}
                        }
                    }
                }
            }
            _ => {
                self.reset_arg(0);
            }
        );
    }

    fn reset_arg(&mut self, arity: usize) {
        self.arity = 0;
        self.arg_c = 1;
        self.temp_lb = arity + 1;
    }

    #[inline(always)]
    fn max_reg_allocated(&self) -> usize {
        std::cmp::max(self.temp_lb, self.arg_c)
    }
}
