use crate::allocator::*;
use crate::arena::ArenaHeaderTag;
use crate::arithmetic::*;
use crate::atom_table::*;
use crate::debray_allocator::*;
use crate::forms::*;
use crate::indexing::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::machine::heap::*;
use crate::parser::ast::*;
use crate::targets::*;
use crate::types::*;
use crate::variable_records::*;

use crate::machine::disjuncts::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::CodeIndex;
use crate::machine::stack::Stack;

use fxhash::FxBuildHasher;
use indexmap::IndexMap;
use indexmap::IndexSet;

use std::collections::VecDeque;
use std::rc::Rc;

#[derive(Debug)]
pub struct BranchCodeStack {
    pub stack: Vec<Vec<CodeDeque>>,
}

pub type SubsumedBranchHits = IndexSet<usize, FxBuildHasher>;

impl BranchCodeStack {
    fn new() -> Self {
        Self { stack: vec![] }
    }

    fn add_new_branch_stack(&mut self) {
        self.stack.push(vec![]);
    }

    fn add_new_branch(&mut self) {
        if self.stack.is_empty() {
            self.add_new_branch_stack();
        }

        if let Some(branches) = self.stack.last_mut() {
            branches.push(CodeDeque::new());
        }
    }

    fn code<'a>(&'a mut self, default_code: &'a mut CodeDeque) -> &'a mut CodeDeque {
        self.stack
            .last_mut()
            .and_then(|stack| stack.last_mut())
            .unwrap_or(default_code)
    }

    fn push_missing_vars(
        &mut self,
        depth: usize,
        marker: &mut DebrayAllocator,
    ) -> SubsumedBranchHits {
        let mut subsumed_hits = SubsumedBranchHits::with_hasher(FxBuildHasher::default());
        let mut propagated_var_nums = IndexSet::with_hasher(FxBuildHasher::default());

        for idx in (self.stack.len() - depth..self.stack.len()).rev() {
            let branch = &mut marker.branch_stack[idx];
            let branch_hits = &branch.hits;

            for (&var_num, branches) in branch_hits.iter() {
                let record = &marker.var_data.records[var_num];

                if record.running_count < record.num_occurrences {
                    if !branches.all() {
                        branch.deep_safety.insert(var_num);
                        branch.shallow_safety.insert(var_num);

                        let r = record.allocation.as_reg_type();

                        // iterate over unset bits.
                        for branch_idx in branches.iter_zeros() {
                            if branch_idx + 1 == branches.len() && idx + 1 != self.stack.len() {
                                break;
                            }

                            self.stack[idx][branch_idx].push_back(instr!("put_variable", r, 0));
                        }
                    }

                    if idx > self.stack.len() - depth {
                        propagated_var_nums.insert(var_num);
                    }

                    subsumed_hits.insert(var_num);
                }
            }

            for var_num in propagated_var_nums.drain(..) {
                marker.branch_stack[idx - 1].add_branch_occurrence(var_num);
            }
        }

        subsumed_hits
    }

    fn push_jump_instrs(&mut self, depth: usize) {
        // add 2 in each arm length to compensate for each jump
        // instruction and each branch instruction not yet added.
        let mut jump_span: usize = self.stack[self.stack.len() - depth..]
            .iter()
            .map(|branch| branch.iter().map(|code| code.len() + 2).sum::<usize>())
            .sum();

        jump_span -= depth;

        for idx in self.stack.len() - depth..self.stack.len() {
            let inner_len = self.stack[idx].len();

            for (inner_idx, code) in self.stack[idx].iter_mut().enumerate() {
                if inner_idx + 1 == inner_len {
                    jump_span -= code.len() + 1;
                } else {
                    jump_span -= code.len() + 1;
                    code.push_back(instr!("jmp_by_call", jump_span));

                    jump_span -= 1;
                }
            }
        }
    }

    fn pop_branch(&mut self, depth: usize, settings: CodeGenSettings) -> CodeDeque {
        let mut combined_code = CodeDeque::new();

        for mut branch_arm in self.stack.drain(self.stack.len() - depth..).rev() {
            let num_branch_arms = branch_arm.len();
            if let Some(code) = branch_arm.last_mut() {
                code.extend(combined_code.drain(..))
            }

            for (idx, code) in branch_arm.into_iter().enumerate() {
                combined_code.push_back(if idx == 0 {
                    Instruction::TryMeElse(code.len() + 1)
                } else if idx + 1 < num_branch_arms {
                    settings.retry_me_else(code.len() + 1)
                } else {
                    settings.trust_me()
                });

                combined_code.extend(code.into_iter());
            }
        }

        combined_code
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CodeGenSettings {
    pub global_clock_tick: Option<usize>,
    pub is_extensible: bool,
    pub non_counted_bt: bool,
}

impl CodeGenSettings {
    #[inline]
    pub(crate) fn is_dynamic(&self) -> bool {
        self.global_clock_tick.is_some()
    }

    #[inline]
    pub(crate) fn internal_try_me_else(&self, offset: usize) -> Instruction {
        if let Some(global_clock_time) = self.global_clock_tick {
            Instruction::DynamicInternalElse(
                global_clock_time,
                Death::Infinity,
                if offset == 0 {
                    NextOrFail::Next(0)
                } else {
                    NextOrFail::Next(offset)
                },
            )
        } else {
            Instruction::TryMeElse(offset)
        }
    }

    pub(crate) fn try_me_else(&self, offset: usize) -> Instruction {
        if let Some(global_clock_tick) = self.global_clock_tick {
            Instruction::DynamicElse(
                global_clock_tick,
                Death::Infinity,
                if offset == 0 {
                    NextOrFail::Next(0)
                } else {
                    NextOrFail::Next(offset)
                },
            )
        } else {
            Instruction::TryMeElse(offset)
        }
    }

    pub(crate) fn internal_retry_me_else(&self, offset: usize) -> Instruction {
        if let Some(global_clock_tick) = self.global_clock_tick {
            Instruction::DynamicInternalElse(
                global_clock_tick,
                Death::Infinity,
                if offset == 0 {
                    NextOrFail::Next(0)
                } else {
                    NextOrFail::Next(offset)
                },
            )
        } else {
            Instruction::RetryMeElse(offset)
        }
    }

    pub(crate) fn retry_me_else(&self, offset: usize) -> Instruction {
        if let Some(global_clock_tick) = self.global_clock_tick {
            Instruction::DynamicElse(
                global_clock_tick,
                Death::Infinity,
                if offset == 0 {
                    NextOrFail::Next(0)
                } else {
                    NextOrFail::Next(offset)
                },
            )
        } else if self.non_counted_bt {
            Instruction::DefaultRetryMeElse(offset)
        } else {
            Instruction::RetryMeElse(offset)
        }
    }

    pub(crate) fn internal_trust_me(&self) -> Instruction {
        if let Some(global_clock_tick) = self.global_clock_tick {
            Instruction::DynamicInternalElse(
                global_clock_tick,
                Death::Infinity,
                NextOrFail::Fail(0),
            )
        } else if self.non_counted_bt {
            Instruction::DefaultTrustMe(0)
        } else {
            Instruction::TrustMe(0)
        }
    }

    pub(crate) fn trust_me(&self) -> Instruction {
        if let Some(global_clock_tick) = self.global_clock_tick {
            Instruction::DynamicElse(global_clock_tick, Death::Infinity, NextOrFail::Fail(0))
        } else if self.non_counted_bt {
            Instruction::DefaultTrustMe(0)
        } else {
            Instruction::TrustMe(0)
        }
    }

    pub(crate) fn default_call_policy(&self) -> CallPolicy {
        // calls are inference counted by default if and only if
        // backtracking is counted too.
        if self.non_counted_bt {
            CallPolicy::Default
        } else {
            CallPolicy::Counted
        }
    }
}

#[derive(Debug)]
pub(crate) struct CodeGenerator {
    marker: DebrayAllocator,
    settings: CodeGenSettings,
    pub(crate) skeleton: PredicateSkeleton,
}

impl DebrayAllocator {
    pub(crate) fn mark_non_callable(
        &mut self,
        var_num: usize,
        arg: usize,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> RegType {
        match self.get_var_binding(var_num) {
            RegType::Temp(t) if t != 0 => RegType::Temp(t),
            RegType::Perm(p) if p != 0 => {
                if let GenContext::Last(_) = context {
                    self.mark_var::<QueryInstruction>(var_num, Level::Shallow, context, code);
                    temp_v!(arg)
                } else {
                    if let VarAlloc::Perm {
                        allocation: PermVarAllocation::Pending,
                        ..
                    } = &self.var_data.records[var_num].allocation
                    {
                        self.mark_var::<QueryInstruction>(var_num, Level::Shallow, context, code);
                    } else {
                        self.increment_running_count(var_num);
                    }

                    RegType::Perm(p)
                }
            }
            _ => self.mark_var::<QueryInstruction>(var_num, Level::Shallow, context, code),
        }
    }
}

trait AddToFreeList<'a, Target: CompilationTarget<'a>> {
    fn add_term_to_free_list(&mut self, r: RegType);
    fn add_subterm_to_free_list(&mut self, r: RegType);
}

impl<'a> AddToFreeList<'a, FactInstruction> for CodeGenerator {
    fn add_term_to_free_list(&mut self, r: RegType) {
        self.marker.add_reg_to_free_list(r);
    }

    fn add_subterm_to_free_list(&mut self, _r: RegType) {}
}

impl<'a> AddToFreeList<'a, QueryInstruction> for CodeGenerator {
    #[inline(always)]
    fn add_term_to_free_list(&mut self, _r: RegType) {}

    #[inline(always)]
    fn add_subterm_to_free_list(&mut self, r: RegType) {
        self.marker.add_reg_to_free_list(r);
    }
}

fn add_index_ptr<'a, Target: crate::targets::CompilationTarget<'a>>(
    index_ptrs: &IndexMap<usize, CodeIndex, FxBuildHasher>,
    heap: &Heap,
    heap_loc: usize,
) -> Option<Instruction> {
    if let Some(index_ptr) = index_ptrs.get(&heap_loc) {
        let subterm = HeapCellValue::from(*index_ptr);
        return Some(Target::constant_subterm(subterm));
    } else if !heap[heap_loc.saturating_sub(1)].get_mark_bit() {
        if let Some(index_ptr) = fetch_index_ptr(heap, heap_loc) {
            let subterm = HeapCellValue::from(index_ptr);
            return Some(Target::constant_subterm(subterm));
        }
    }

    None
}

impl CodeGenerator {
    pub(crate) fn new(settings: CodeGenSettings) -> Self {
        CodeGenerator {
            marker: DebrayAllocator::new(),
            settings,
            skeleton: PredicateSkeleton::new(),
        }
    }

    fn add_or_increment_void_instr<'a, Target>(target: &mut CodeDeque)
    where
        Target: crate::targets::CompilationTarget<'a>,
    {
        if let Some(ref mut instr) = target.back_mut() {
            if Target::is_void_instr(instr) {
                Target::incr_void_instr(instr);
                return;
            }
        }

        target.push_back(Target::to_void(1));
    }

    fn deep_var_instr<'a, Target: crate::targets::CompilationTarget<'a>>(
        &mut self,
        var_num: usize,
        context: GenContext,
        target: &mut CodeDeque,
    ) {
        if self.marker.var_data.records[var_num].num_occurrences > 1 {
            self.marker
                .mark_var::<Target>(var_num, Level::Deep, context, target);
        } else {
            Self::add_or_increment_void_instr::<Target>(target);
        }
    }

    fn subterm_to_instr<'a, Target: crate::targets::CompilationTarget<'a>>(
        &mut self,
        subterm: HeapCellValue,
        heap_loc: usize,
        context: GenContext,
        index_ptrs: &IndexMap<usize, CodeIndex, FxBuildHasher>,
        target: &mut CodeDeque,
    ) -> Option<RegType> {
        let subterm = unmark_cell_bits!(subterm);
        let chunk_num = context.chunk_num();

        read_heap_cell!(subterm,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, term_loc) => {
                match self.marker.var_data.var_locs_to_nums.get(VarPtrIndex { chunk_num, term_loc }) {
                    VarPtr::Numbered(var_num) => {
                        self.deep_var_instr::<Target>(
                            var_num,
                            context,
                            target,
                        );
                    }
                    VarPtr::Anon => {
                        Self::add_or_increment_void_instr::<Target>(target);
                    }
                }

                None
            }
            (HeapCellValueTag::Atom, (name, _arity)) => {
                if index_ptrs.contains_key(&heap_loc) {
                    let r = self.marker.mark_non_var::<Target>(Level::Deep, heap_loc, context, target);
                    target.push_back(Target::clause_arg_to_instr(r));
                    return Some(r);
                } else {
                    target.push_back(Target::constant_subterm(atom_as_cell!(name)));
                }

                None
            }
            (HeapCellValueTag::Str
             | HeapCellValueTag::Lis
             | HeapCellValueTag::PStrLoc) => {
                let r = self.marker.mark_non_var::<Target>(Level::Deep, heap_loc, context, target);
                target.push_back(Target::clause_arg_to_instr(r));
                Some(r)
            }
            _ => {
                target.push_back(Target::constant_subterm(subterm));
                None
            }
        )
    }

    fn compile_target<'a, Target, Iter>(
        &mut self,
        mut iter: Iter,
        index_ptrs: &IndexMap<usize, CodeIndex, FxBuildHasher>,
        context: GenContext,
    ) -> CodeDeque
    where
        Target: crate::targets::CompilationTarget<'a>,
        Iter: TermIterator,
        CodeGenerator: AddToFreeList<'a, Target>,
    {
        let mut target = CodeDeque::new();
        let chunk_num = context.chunk_num();

        while let Some(term) = iter.next() {
            let lvl = iter.level();
            let term = unmark_cell_bits!(term);

            read_heap_cell!(term,
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, term_loc) => {
                    if lvl == Level::Shallow {
                        match self.marker.var_data.var_locs_to_nums.get(
                            VarPtrIndex { chunk_num, term_loc }
                        ) {
                            VarPtr::Numbered(var_num) => {
                                self.marker.mark_var::<Target>(
                                    var_num,
                                    lvl,
                                    context,
                                    &mut target,
                                );
                            }
                            VarPtr::Anon => {
                                if let GenContext::Head = context {
                                    self.marker.advance_arg();
                                } else {
                                    self.marker.mark_anon_var::<Target>(lvl, context, &mut target);
                                }
                            }
                        }
                    }
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    let heap_loc = iter.focus().value() as usize;
                    let (heap_loc, _) = subterm_index(iter.deref(), heap_loc);

                    if arity == 0 {
                        if let Some(instr) = add_index_ptr::<Target>(index_ptrs, &iter, heap_loc) {
                            let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);
                            target.push_back(instr);
                            target.push_back(Target::to_structure(lvl, name, 0, r));
                        } else if lvl == Level::Shallow {
                            let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);
                            target.push_back(Target::to_constant(lvl, atom_as_cell!(name), r));
                        }
                    } else {
                        let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);

                        <CodeGenerator as AddToFreeList<'a, Target>>::add_term_to_free_list(
                            self,
                            r,
                        );

                        if let Some(instr) = add_index_ptr::<Target>(index_ptrs, &iter, heap_loc) {
                            target.push_back(instr);
                        }

                        target.push_back(Target::to_structure(lvl, name, arity, r));

                        let free_list_regs: Vec<_> = (heap_loc + 1 ..= heap_loc + arity)
                            .map(|subterm_loc| {
                                let (subterm_loc, subterm) = subterm_index(iter.deref(), subterm_loc);

                                self.subterm_to_instr::<Target>(
                                    subterm, subterm_loc, context, index_ptrs, &mut target,
                                )
                            })
                            .collect();

                        for r_opt in free_list_regs.into_iter().flatten() {
                            <CodeGenerator as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                                self, r_opt,
                            );
                        }
                    }
                }
                (HeapCellValueTag::Lis, l) => {
                    let heap_loc = iter.focus().value() as usize;
                    let (heap_loc, _) = subterm_index(iter.deref(), heap_loc);

                    let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);

                    target.push_back(Target::to_list(lvl, r));

                    <CodeGenerator as AddToFreeList<'a, Target>>::add_term_to_free_list(
                        self,
                        r,
                    );

                    let (head_loc, head) = subterm_index(iter.deref(), l);
                    let (tail_loc, tail) = subterm_index(iter.deref(), l+1);

                    let head_r_opt = self.subterm_to_instr::<Target>(
                        head,
                        head_loc,
                        context,
                        index_ptrs,
                        &mut target,
                    );

                    let tail_r_opt = self.subterm_to_instr::<Target>(
                        tail,
                        tail_loc,
                        context,
                        index_ptrs,
                        &mut target,
                    );

                    if let Some(r) = head_r_opt {
                        <CodeGenerator as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                            self, r,
                        );
                    }

                    if let Some(r) = tail_r_opt {
                        <CodeGenerator as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                            self, r,
                        );
                    }
                }
                (HeapCellValueTag::PStrLoc, pstr_loc) => {
                    let heap_loc = iter.focus().value() as usize;
                    let (heap_loc, _) = subterm_index(iter.deref(), heap_loc);
                    let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);
                    let HeapStringScan { string, tail_idx } = iter.scan_slice_to_str(pstr_loc);

                    target.push_back(Target::to_pstr(lvl, Rc::new(string.to_owned()), r));

                    let (tail_loc, tail) = subterm_index(iter.deref(), tail_idx);
                    self.subterm_to_instr::<Target>(
                        tail, tail_loc, context, index_ptrs, &mut target,
                    );
                }
                _ if lvl == Level::Shallow => {
                    if term.is_constant() {
                        let heap_loc = iter.focus().value() as usize;
                        let (heap_loc, _) = subterm_index(iter.deref(), heap_loc);
                        let r = self.marker.mark_non_var::<Target>(lvl, heap_loc, context, &mut target);
                        target.push_back(Target::to_constant(lvl, term, r));
                    }
                }
                _ => {}
            );
        }

        target
    }

    fn add_call(&mut self, code: &mut CodeDeque, call_instr: Instruction, call_policy: CallPolicy) {
        if self.marker.in_tail_position && self.marker.var_data.allocates {
            code.push_back(instr!("deallocate"));
        }

        match call_policy {
            CallPolicy::Default => {
                if self.marker.in_tail_position {
                    code.push_back(call_instr.into_execute().into_default());
                } else {
                    code.push_back(call_instr.into_default())
                }
            }
            CallPolicy::Counted => {
                if self.marker.in_tail_position {
                    code.push_back(call_instr.into_execute());
                } else {
                    code.push_back(call_instr)
                }
            }
        }
    }

    fn compile_inlined(
        &mut self,
        ct: &InlinedClauseType,
        terms: &mut FocusedHeapRefMut,
        term_loc: usize,
        context: GenContext,
        code: &mut CodeDeque,
    ) -> Result<(), CompilationError> {
        let first_arg_loc = terms.nth_arg(term_loc, 1).unwrap();
        let first_arg = terms.deref_loc(first_arg_loc);

        let chunk_num = context.chunk_num();
        let mut variable_marker = |marker: &mut DebrayAllocator| {
            read_heap_cell!(first_arg,
                (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, first_arg_loc) => {
                    match marker.var_data.var_locs_to_nums.get(
                        VarPtrIndex { chunk_num, term_loc: first_arg_loc },
                    ) {
                        VarPtr::Numbered(var_num) => {
                            Some(marker.mark_non_callable(
                                var_num,
                                1,
                                context,
                                code,
                            ))
                        }
                        VarPtr::Anon => {
                            Some(marker.mark_anon_var::<QueryInstruction>(
                                Level::Shallow,
                                context,
                                code,
                            ))
                        }
                    }
                }
                _ => {
                    marker.advance_arg();
                    None
                }
            )
        };

        let call_instr = match ct {
            &InlinedClauseType::CompareNumber(mut cmp) => {
                self.marker.reset_arg(2);

                let (mut lcode, at_1) = if let Some(r) = variable_marker(&mut self.marker) {
                    (CodeDeque::default(), Some(ArithmeticTerm::Reg(r)))
                } else {
                    self.compile_arith_expr(terms, first_arg_loc, 1, context, 1)?
                };

                let (mut rcode, at_2) =
                    self.compile_arith_expr(terms, first_arg_loc + 1, 2, context, 2)?;

                code.append(&mut lcode);
                code.append(&mut rcode);

                let at_1 = at_1.unwrap_or(interm!(1));
                let at_2 = at_2.unwrap_or(interm!(2));

                compare_number_instr!(cmp, at_1, at_2)
            }
            InlinedClauseType::IsAtom(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("atom", r)
                } else {
                    read_heap_cell!(first_arg,
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                instr!("$succeed")
                            } else {
                                instr!("$fail")
                            }
                        }
                        _ => {
                            instr!("$fail")
                        }
                    )
                }
            }
            InlinedClauseType::IsAtomic(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("atomic", r)
                } else {
                    read_heap_cell!(first_arg,
                        (HeapCellValueTag::Fixnum |
                         HeapCellValueTag::F64) => {
                            instr!("$succeed")
                        }
                        (HeapCellValueTag::Cons, cons_ptr) => {
                            match cons_ptr.get_tag() {
                                ArenaHeaderTag::Integer | ArenaHeaderTag::Rational => {
                                    instr!("$succeed")
                                }
                                _ => {
                                    instr!("$fail")
                                }
                            }
                        }
                        (HeapCellValueTag::Atom, (_name, arity)) => {
                            if arity == 0 {
                                instr!("$succeed")
                            } else {
                                instr!("$fail")
                            }
                        }
                        (HeapCellValueTag::Lis
                         | HeapCellValueTag::Str
                         | HeapCellValueTag::PStrLoc) => {
                            instr!("$fail")
                        }
                        _ => {
                            if first_arg.is_constant() {
                                instr!("$succeed")
                            } else {
                                instr!("$fail")
                            }
                        }
                    )
                }
            }
            InlinedClauseType::IsCompound(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("compound", r)
                } else {
                    read_heap_cell!(first_arg,
                        (HeapCellValueTag::Atom, (_, arity)) => {
                            if arity > 0 {
                                instr!("$succeed")
                            } else {
                                instr!("$fail")
                            }
                        }
                        (HeapCellValueTag::Lis
                         | HeapCellValueTag::Str
                         | HeapCellValueTag::PStrLoc) => {
                            instr!("$succeed")
                        }
                        _ => {
                            instr!("$fail")
                        }
                    )
                }
            }
            InlinedClauseType::IsRational(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("rational", r)
                } else {
                    read_heap_cell!(first_arg,
                        (HeapCellValueTag::Cons, cons_ptr) => {
                            match cons_ptr.get_tag() {
                                ArenaHeaderTag::Integer | ArenaHeaderTag::Rational => {
                                    instr!("$succeed")
                                }
                                _ => {
                                    instr!("$fail")
                                }
                            }
                        }
                        (HeapCellValueTag::Fixnum) => {
                            instr!("$succeed")
                        }
                        _ => {
                            instr!("$fail")
                        }
                    )
                }
            }
            InlinedClauseType::IsFloat(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("float", r)
                } else {
                    read_heap_cell!(first_arg,
                        (HeapCellValueTag::F64) => {
                            instr!("$succeed")
                        }
                        _ => {
                            instr!("$fail")
                        }
                    )
                }
            }
            InlinedClauseType::IsNumber(..) => {
                self.marker.reset_arg(1);
                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("number", r)
                } else if Number::try_from(first_arg).is_ok() {
                    instr!("$succeed")
                } else {
                    instr!("$fail")
                }
            }
            InlinedClauseType::IsNonVar(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("nonvar", r)
                } else if first_arg.is_var() {
                    instr!("$fail")
                } else {
                    instr!("$succeed")
                }
            }
            InlinedClauseType::IsInteger(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("integer", r)
                } else {
                    match Number::try_from(first_arg) {
                        Ok(Number::Integer(_) | Number::Fixnum(_)) => {
                            instr!("$succeed")
                        }
                        _ => {
                            instr!("$fail")
                        }
                    }
                }
            }
            InlinedClauseType::IsVar(..) => {
                self.marker.reset_arg(1);

                if let Some(r) = variable_marker(&mut self.marker) {
                    instr!("var", r)
                } else if first_arg.is_var() {
                    instr!("$succeed")
                } else {
                    instr!("$fail")
                }
            }
        };

        // inlined predicates are never counted, so this overrides nothing.
        self.add_call(code, call_instr, CallPolicy::Counted);
        Ok(())
    }

    fn compile_arith_expr(
        &mut self,
        terms: &mut FocusedHeapRefMut,
        term_loc: usize,
        target_int: usize,
        context: GenContext,
        arg: usize,
    ) -> Result<ArithCont, ArithmeticError> {
        let mut evaluator = ArithmeticEvaluator::new(&mut self.marker, target_int);
        evaluator.compile_is(terms, term_loc, context, arg)
    }

    fn compile_is_call(
        &mut self,
        terms: &mut FocusedHeapRefMut,
        term_loc: usize,
        code: &mut CodeDeque,
        context: GenContext,
        call_policy: CallPolicy,
    ) -> Result<(), CompilationError> {
        macro_rules! compile_expr {
            ($self:expr, $terms:expr, $context:expr, $code:expr) => {{
                let (acode, at) = $self.compile_arith_expr($terms, term_loc + 2, 1, $context, 2)?;
                $code.extend(acode.into_iter());
                at
            }};
        }

        self.marker.reset_arg(2);

        let var = heap_bound_store(
            terms.heap,
            heap_bound_deref(terms.heap, heap_loc_as_cell!(term_loc + 1)),
        );

        let at = read_heap_cell!(var,
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, term_loc) => {
                let chunk_num = context.chunk_num();

                match self.marker.var_data.var_locs_to_nums.get(
                    VarPtrIndex { chunk_num, term_loc },
                ) {
                    VarPtr::Numbered(var_num) => {
                        if self.marker.var_data.records[var_num].num_occurrences > 1 {
                            self.marker.mark_var::<QueryInstruction>(
                                var_num,
                                Level::Shallow,
                                context,
                                code,
                            );

                            self.marker.mark_safe_var_unconditionally(var_num);
                        }
                    }
                    VarPtr::Anon => {}
                };

                compile_expr!(self, terms, context, code)
            }
            _ => {
                if Number::try_from(var).is_ok() {
                    let v = var;
                    code.push_back(instr!("put_constant", Level::Shallow, v, temp_v!(1)));

                    self.marker.advance_arg();
                    compile_expr!(self, terms, context, code)
                } else {
                    code.push_back(instr!("$fail"));
                    return Ok(());
                }
            }
        );

        let at = at.unwrap_or(interm!(1));
        self.add_call(code, instr!("is", temp_v!(1), at), call_policy);
        Ok(())
    }

    fn compile_seq(
        &mut self,
        mut focused_heap: FocusedHeapRefMut,
        clauses: &ChunkedTermVec,
        code: &mut CodeDeque,
    ) -> Result<(), CompilationError> {
        let mut branch_code_stack = BranchCodeStack::new();
        let mut clause_iter = ClauseIterator::new(clauses);

        while let Some(clause_item) = clause_iter.next() {
            match clause_item {
                ClauseItem::Chunk { chunk_num, terms } => {
                    for (idx, term) in terms.iter().enumerate() {
                        let context = if idx + 1 < terms.len() {
                            GenContext::Mid(chunk_num)
                        } else {
                            self.marker.in_tail_position = clause_iter.in_tail_position();
                            GenContext::Last(chunk_num)
                        };

                        match term {
                            &QueryTerm::GetLevel(var_num) => {
                                let code = branch_code_stack.code(code);
                                let r = self.marker.mark_cut_var(var_num, chunk_num);
                                code.push_back(instr!("get_level", r));
                            }
                            &QueryTerm::GetCutPoint { var_num, prev_b } => {
                                let code = branch_code_stack.code(code);
                                let r = self.marker.mark_cut_var(var_num, chunk_num);

                                code.push_back(if prev_b {
                                    instr!("get_prev_level", r)
                                } else {
                                    instr!("get_cut_point", r)
                                });
                            }
                            &QueryTerm::GlobalCut(var_num) => {
                                let code = branch_code_stack.code(code);

                                if chunk_num == 0 {
                                    code.push_back(instr!("neck_cut"));
                                } else {
                                    let r = self.marker.get_var_binding(var_num);
                                    code.push_back(instr!("cut", r));
                                }

                                if self.marker.in_tail_position {
                                    if self.marker.var_data.allocates {
                                        code.push_back(instr!("deallocate"));
                                    }

                                    code.push_back(instr!("proceed"));
                                }
                            }
                            &QueryTerm::LocalCut { var_num, cut_prev } => {
                                let code = branch_code_stack.code(code);
                                let r = self.marker.get_var_binding(var_num);

                                code.push_back(if cut_prev {
                                    instr!("cut_prev", r)
                                } else {
                                    instr!("cut", r)
                                });

                                if self.marker.in_tail_position {
                                    if self.marker.var_data.allocates {
                                        code.push_back(instr!("deallocate"));
                                    }

                                    code.push_back(instr!("proceed"));
                                } else {
                                    self.marker.free_var(chunk_num, var_num);
                                }
                            }
                            &QueryTerm::Clause(
                                ref clause @ QueryClause {
                                    ct: ClauseType::BuiltIn(BuiltInClauseType::Is(..)),
                                    call_policy,
                                    ..
                                },
                            ) => self.compile_is_call(
                                &mut focused_heap,
                                clause.term_loc(),
                                branch_code_stack.code(code),
                                context,
                                call_policy,
                            )?,
                            &QueryTerm::Clause(
                                ref clause @ QueryClause {
                                    ct: ClauseType::Inlined(ref ct),
                                    ..
                                },
                            ) => self.compile_inlined(
                                ct,
                                &mut focused_heap,
                                clause.term_loc(),
                                context,
                                branch_code_stack.code(code),
                            )?,
                            &QueryTerm::Fail => {
                                branch_code_stack.code(code).push_back(instr!("$fail"));
                            }
                            &QueryTerm::Succeed => {
                                let code = branch_code_stack.code(code);

                                if self.marker.in_tail_position && self.marker.var_data.allocates {
                                    code.push_back(instr!("deallocate"));
                                }

                                code.push_back(if self.marker.in_tail_position {
                                    instr!("$succeed").into_execute()
                                } else {
                                    instr!("$succeed")
                                });
                            }
                            QueryTerm::Clause(clause) => {
                                self.compile_query_line(
                                    &mut focused_heap,
                                    clause,
                                    context,
                                    branch_code_stack.code(code),
                                );

                                if self.marker.max_reg_allocated() > MAX_ARITY {
                                    return Err(CompilationError::ExceededMaxArity);
                                }
                            }
                        }
                    }

                    self.marker.in_tail_position = false;
                    self.marker.reset_contents();
                }
                ClauseItem::FirstBranch(num_branches) => {
                    branch_code_stack.add_new_branch_stack();
                    branch_code_stack.add_new_branch();

                    self.marker.branch_stack.add_branch_stack(num_branches);
                    self.marker.add_branch();
                }
                ClauseItem::NextBranch => {
                    branch_code_stack.add_new_branch();

                    self.marker.add_branch();
                    self.marker.branch_stack.incr_current_branch();
                }
                ClauseItem::BranchEnd(depth) => {
                    if !clause_iter.in_tail_position() {
                        let subsumed_hits =
                            branch_code_stack.push_missing_vars(depth, &mut self.marker);
                        self.marker.pop_branch(depth, subsumed_hits);
                        branch_code_stack.push_jump_instrs(depth);
                    } else {
                        self.marker.branch_stack.drain_branches(depth);
                    }

                    let settings = CodeGenSettings {
                        non_counted_bt: self.settings.non_counted_bt,
                        is_extensible: false,
                        global_clock_tick: None,
                    };

                    let branch_code = branch_code_stack.pop_branch(depth, settings);
                    branch_code_stack.code(code).extend(branch_code);
                }
            }
        }

        if self.marker.var_data.allocates {
            code.push_front(instr!("allocate", self.marker.num_perm_vars()));
        }

        Ok(())
    }

    pub(crate) fn compile_rule(
        &mut self,
        heap: &mut Heap,
        rule: &mut Rule,
        var_data: VarData,
    ) -> Result<Code, CompilationError> {
        let Rule { term_loc, clauses } = rule;

        self.marker.var_data = var_data;

        let term = FocusedHeapRefMut {
            heap,
            focus: *term_loc,
        };
        let mut code = VecDeque::new();

        let head_loc = term.nth_arg(term.focus, 1).unwrap();

        self.marker.reset_at_head(term.heap, head_loc);

        let mut stack = Stack::uninitialized();
        let iter = fact_iterator::<true>(term.heap, &mut stack, head_loc);

        let fact = self.compile_target::<FactInstruction, _>(
            iter,
            &IndexMap::with_hasher(FxBuildHasher::default()),
            GenContext::Head,
        );

        if self.marker.max_reg_allocated() > MAX_ARITY {
            return Err(CompilationError::ExceededMaxArity);
        }

        self.marker.reset_free_list();
        code.extend(fact);

        self.compile_seq(term, clauses, &mut code)?;

        Ok(Vec::from(code))
    }

    pub(crate) fn compile_fact(
        &mut self,
        heap: &mut Heap,
        fact: &mut Fact,
        var_data: VarData,
    ) -> Result<Code, CompilationError> {
        let mut code = Vec::new();

        let mut stack = Stack::uninitialized();

        self.marker.var_data = var_data;
        self.marker.reset_at_head(heap, fact.term_loc);

        let iter = fact_iterator::<true>(heap, &mut stack, fact.term_loc);

        let compiled_fact = self.compile_target::<FactInstruction, _>(
            iter,
            &IndexMap::with_hasher(FxBuildHasher::default()),
            GenContext::Head,
        );

        if self.marker.max_reg_allocated() > MAX_ARITY {
            return Err(CompilationError::ExceededMaxArity);
        }

        code.extend(compiled_fact);
        code.push(instr!("proceed"));

        Ok(code)
    }

    fn compile_query_line(
        &mut self,
        term: &mut FocusedHeapRefMut,
        clause: &QueryClause,
        context: GenContext,
        code: &mut CodeDeque,
    ) {
        self.marker.reset_arg(term.arity(clause.term_loc()));

        let mut stack = Stack::uninitialized();
        let iter = query_iterator::<true>(term.heap, &mut stack, clause.term_loc());

        let query = self.compile_target::<QueryInstruction, _>(iter, &clause.code_indices, context);

        code.extend(query);
        self.add_call(code, clause.ct.to_instr(), clause.call_policy);
    }

    fn split_predicate(heap: &mut Heap, clauses: &[PredicateClause]) -> Vec<ClauseSpan> {
        let mut subseqs = Vec::new();
        let mut left = 0;
        let mut optimal_index = 0;

        'outer: for (right, clause) in clauses.iter().enumerate() {
            if let Some(args) = clause.args(heap) {
                for (instantiated_arg_index, arg_idx) in args.enumerate() {
                    let arg = heap[arg_idx];
                    let arg = heap_bound_store(heap, heap_bound_deref(heap, arg));

                    if !arg.is_var() {
                        if optimal_index != instantiated_arg_index {
                            if left >= right {
                                optimal_index = instantiated_arg_index;
                                continue 'outer;
                            }

                            subseqs.push(ClauseSpan {
                                left,
                                right,
                                instantiated_arg_index: optimal_index,
                            });

                            optimal_index = instantiated_arg_index;
                            left = right;
                        }

                        continue 'outer;
                    }
                }
            }

            if left < right {
                subseqs.push(ClauseSpan {
                    left,
                    right,
                    instantiated_arg_index: optimal_index,
                });
            }

            optimal_index = 0;

            subseqs.push(ClauseSpan {
                left: right,
                right: right + 1,
                instantiated_arg_index: optimal_index,
            });

            left = right + 1;
        }

        if left < clauses.len() {
            subseqs.push(ClauseSpan {
                left,
                right: clauses.len(),
                instantiated_arg_index: optimal_index,
            });
        }

        subseqs
    }

    fn compile_pred_subseq<I: Indexer>(
        &mut self,
        heap: &mut Heap,
        clauses: &mut [PredicateClause],
        optimal_index: usize,
    ) -> Result<Code, CompilationError> {
        let mut code = VecDeque::new();
        let mut code_offsets =
            CodeOffsets::new(I::new(), optimal_index + 1, self.settings.non_counted_bt);

        let mut skip_stub_try_me_else = false;
        let clauses_len = clauses.len();

        for (i, clause) in clauses.iter_mut().enumerate() {
            self.marker.reset();

            let mut clause_index_info = ClauseIndexInfo::new(code.len());

            let clause_code = match clause {
                PredicateClause::Fact(fact, var_data) => {
                    let var_data = std::mem::take(var_data);
                    self.compile_fact(heap, fact, var_data)?
                }
                PredicateClause::Rule(rule, var_data) => {
                    let var_data = std::mem::take(var_data);
                    self.compile_rule(heap, rule, var_data)?
                }
            };

            if clauses_len > 1 {
                let choice = match i {
                    0 => self.settings.internal_try_me_else(clause_code.len() + 1),
                    _ if i + 1 == clauses_len => self.settings.internal_trust_me(),
                    _ => self.settings.internal_retry_me_else(clause_code.len() + 1),
                };

                code.push_back(choice);
            } else if self.settings.is_extensible {
                /*
                   generate stub choice instructions for extensible
                   predicates. if predicates are added to either the
                   inner or outer thread of choice instructions,
                   these stubs will be used, and surrounding indexing
                   instructions modified accordingly.

                   until then, the v offset of SwitchOnTerm will skip
                   over them.
                */

                code.push_front(self.settings.internal_try_me_else(0));
                skip_stub_try_me_else = !self.settings.is_dynamic();
            }

            let arg = clause.args(heap).map(|r| heap[r.start() + optimal_index]);

            if let Some(arg) = arg {
                let index = code.len();

                if clauses_len > 1 || self.settings.is_extensible {
                    let arg = heap_bound_store(heap, heap_bound_deref(heap, arg));
                    code_offsets.index_term(heap, arg, index, &mut clause_index_info);
                }
            }

            self.skeleton.clauses.push_back(clause_index_info);
            code.extend(clause_code.into_iter());
        }

        let index_code = if clauses_len > 1 || self.settings.is_extensible {
            code_offsets.compute_indices(skip_stub_try_me_else)
        } else {
            vec![]
        };

        if !index_code.is_empty() {
            code.push_front(Instruction::IndexingCode(index_code));
        } else if clauses.len() == 1 && self.settings.is_extensible {
            // the condition is the value of skip_stub_try_me_else, which is
            // true if the predicate is not dynamic. This operation must apply
            // to dynamic predicates also, though.

            // remove the TryMeElse(0).
            code.pop_front();
        }

        Ok(Vec::from(code))
    }

    pub(crate) fn compile_predicate(
        &mut self,
        heap: &mut Heap,
        mut clauses: Vec<PredicateClause>,
    ) -> Result<Code, CompilationError> {
        let mut code = Code::new();

        let split_pred = Self::split_predicate(heap, &clauses);
        let multi_seq = split_pred.len() > 1;

        for ClauseSpan {
            left,
            right,
            instantiated_arg_index,
        } in split_pred
        {
            let skel_lower_bound = self.skeleton.clauses.len();
            let code_segment = if self.settings.is_dynamic() {
                self.compile_pred_subseq::<DynamicCodeIndices>(
                    heap,
                    &mut clauses[left..right],
                    instantiated_arg_index,
                )?
            } else {
                self.compile_pred_subseq::<StaticCodeIndices>(
                    heap,
                    &mut clauses[left..right],
                    instantiated_arg_index,
                )?
            };

            let clause_start_offset = code.len();

            if multi_seq {
                let choice = match left {
                    0 => self.settings.try_me_else(code_segment.len() + 1),
                    _ if right == clauses.len() => self.settings.trust_me(),
                    _ => self.settings.retry_me_else(code_segment.len() + 1),
                };

                code.push(choice);
            } else if self.settings.is_extensible {
                code.push(self.settings.try_me_else(0));
            }

            if self.settings.is_extensible {
                let segment_is_indexed = code_segment[0].to_indexing_line().is_some();

                for clause_index_info in
                    self.skeleton.clauses.make_contiguous()[skel_lower_bound..].iter_mut()
                {
                    clause_index_info.clause_start +=
                        clause_start_offset + 2 * (segment_is_indexed as usize);
                    clause_index_info.opt_arg_index_key += clause_start_offset + 1;
                }
            }

            code.extend(code_segment.into_iter());
        }

        Ok(code)
    }
}
