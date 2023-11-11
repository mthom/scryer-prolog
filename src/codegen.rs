use crate::allocator::*;
use crate::arithmetic::*;
use crate::atom_table::*;
use crate::debray_allocator::*;
use crate::forms::*;
use crate::indexing::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::parser::ast::*;
use crate::targets::*;
use crate::temp_v;
use crate::types::*;
use crate::variable_records::*;

use crate::instr;
use crate::machine::disjuncts::*;
use crate::machine::machine_errors::*;

use fxhash::FxBuildHasher;
use indexmap::IndexSet;

use std::cell::Cell;
use std::collections::VecDeque;

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

                    subsumed_hits.insert(var_num);
                }
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
pub(crate) struct CodeGenerator<'a> {
    pub(crate) atom_tbl: &'a AtomTable,
    marker: DebrayAllocator,
    settings: CodeGenSettings,
    pub(crate) skeleton: PredicateSkeleton,
}

impl DebrayAllocator {
    fn mark_var_in_non_callable(
        &mut self,
        var_num: usize,
        term_loc: GenContext,
        vr: &Cell<VarReg>,
        code: &mut CodeDeque,
    ) -> RegType {
        self.mark_var::<QueryInstruction>(var_num, Level::Shallow, vr, term_loc, code);
        vr.get().norm()
    }

    pub(crate) fn mark_non_callable(
        &mut self,
        var_num: usize,
        arg: usize,
        term_loc: GenContext,
        vr: &Cell<VarReg>,
        code: &mut CodeDeque,
    ) -> RegType {
        match self.get_binding(var_num) {
            RegType::Temp(t) if t != 0 => RegType::Temp(t),
            RegType::Perm(p) if p != 0 => {
                if let GenContext::Last(_) = term_loc {
                    self.mark_var_in_non_callable(var_num, term_loc, vr, code);
                    temp_v!(arg)
                } else {
		    match &self.var_data.records[var_num].allocation {
			VarAlloc::Perm(_, PermVarAllocation::Pending) => {
			    self.mark_var_in_non_callable(var_num, term_loc, vr, code);
			}
			_ => {}
		    }

                    self.increment_running_count(var_num);
                    RegType::Perm(p)
                }
            }
            _ => self.mark_var_in_non_callable(var_num, term_loc, vr, code),
        }
    }
}

// if the final argument of the structure is a Literal::Index,
// decrement the arity of the PutStructure instruction by 1.
fn trim_structure_by_last_arg(instr: &mut Instruction, last_arg: &Term) {
    match instr {
        Instruction::PutStructure(_, ref mut arity, _)
        | Instruction::GetStructure(.., ref mut arity, _) => {
            if let Term::Literal(_, Literal::CodeIndex(_)) = last_arg {
                // it is acceptable if arity == 0 is the result of
                // this decrement. call/N will have to read the index
                // constant for '$call_inline' to succeed. to find it,
                // it must know the heap location of the index.
                // self.store must stop before reading the atom into a
                // register.

                *arity -= 1;
            }
        }
        _ => {}
    }
}

trait AddToFreeList<'a, Target: CompilationTarget<'a>> {
    fn add_term_to_free_list(&mut self, r: RegType);
    fn add_subterm_to_free_list(&mut self, term: &Term);
}

impl<'a, 'b> AddToFreeList<'a, FactInstruction> for CodeGenerator<'b> {
    fn add_term_to_free_list(&mut self, r: RegType) {
        self.marker.add_reg_to_free_list(r);
    }

    fn add_subterm_to_free_list(&mut self, _term: &Term) {}
}

impl<'a, 'b> AddToFreeList<'a, QueryInstruction> for CodeGenerator<'b> {
    #[inline(always)]
    fn add_term_to_free_list(&mut self, _r: RegType) {}

    #[inline(always)]
    fn add_subterm_to_free_list(&mut self, term: &Term) {
        if let Some(cell) = structure_cell(term) {
            self.marker.add_reg_to_free_list(cell.get());
        }
    }
}

fn structure_cell(term: &Term) -> Option<&Cell<RegType>> {
    match term {
        &Term::Cons(ref cell, ..)
        | &Term::Clause(ref cell, ..)
        | Term::PartialString(ref cell, ..)
        | Term::CompleteString(ref cell, ..) => Some(cell),
        _ => None,
    }
}

impl<'b> CodeGenerator<'b> {
    pub(crate) fn new(atom_tbl: &'b AtomTable, settings: CodeGenSettings) -> Self {
        CodeGenerator {
            atom_tbl,
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
        cell: &'a Cell<VarReg>,
        var_num: usize,
        term_loc: GenContext,
        target: &mut CodeDeque,
    ) {
        if self.marker.var_data.records[var_num].num_occurrences > 1 {
            self.marker
                .mark_var::<Target>(var_num, Level::Deep, cell, term_loc, target);
        } else {
            Self::add_or_increment_void_instr::<Target>(target);
        }
    }

    fn subterm_to_instr<'a, Target: crate::targets::CompilationTarget<'a>>(
        &mut self,
        subterm: &'a Term,
        term_loc: GenContext,
        target: &mut CodeDeque,
    ) {
        match subterm {
            &Term::AnonVar => {
                Self::add_or_increment_void_instr::<Target>(target);
            }
            &Term::Cons(ref cell, ..)
            | &Term::Clause(ref cell, ..)
            | Term::PartialString(ref cell, ..)
            | Term::CompleteString(ref cell, ..) => {
                self.marker
                    .mark_non_var::<Target>(Level::Deep, term_loc, cell, target);
                target.push_back(Target::clause_arg_to_instr(cell.get()));
            }
            Term::Literal(_, ref constant) => {
                target.push_back(Target::constant_subterm(*constant));
            }
            Term::Var(ref cell, ref var_ptr) => {
                self.deep_var_instr::<Target>(
                    cell,
                    var_ptr.to_var_num().unwrap(),
                    term_loc,
                    target,
                );
            }
        };
    }

    fn compile_target<'a, Target, Iter>(&mut self, iter: Iter, term_loc: GenContext) -> CodeDeque
    where
        Target: crate::targets::CompilationTarget<'a>,
        Iter: Iterator<Item = TermRef<'a>>,
        CodeGenerator<'b>: AddToFreeList<'a, Target>,
    {
        let mut target = CodeDeque::new();

        for term in iter {
            match term {
                TermRef::AnonVar(lvl @ Level::Shallow) => {
                    if let GenContext::Head = term_loc {
                        self.marker.advance_arg();
                    } else {
                        self.marker
                            .mark_anon_var::<Target>(lvl, term_loc, &mut target);
                    }
                }
                TermRef::Clause(lvl, cell, name, terms) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push_back(Target::to_structure(lvl, name, terms.len(), cell.get()));

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_term_to_free_list(
                        self,
                        cell.get(),
                    );

                    if let Some(instr) = target.back_mut() {
                        if let Some(term) = terms.last() {
                            trim_structure_by_last_arg(instr, term);
                        }
                    }

                    for subterm in terms {
                        self.subterm_to_instr::<Target>(subterm, term_loc, &mut target);
                    }

                    for subterm in terms {
                        <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                            self, subterm,
                        );
                    }
                }
                TermRef::Cons(lvl, cell, head, tail) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push_back(Target::to_list(lvl, cell.get()));

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_term_to_free_list(
                        self,
                        cell.get(),
                    );

                    self.subterm_to_instr::<Target>(head, term_loc, &mut target);
                    self.subterm_to_instr::<Target>(tail, term_loc, &mut target);

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                        self, head,
                    );
                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(
                        self, tail,
                    );
                }
                TermRef::Literal(lvl @ Level::Shallow, cell, Literal::String(ref string)) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push_back(Target::to_pstr(lvl, *string, cell.get(), false));
                }
                TermRef::Literal(lvl @ Level::Shallow, cell, constant) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push_back(Target::to_constant(lvl, *constant, cell.get()));
                }
                TermRef::PartialString(lvl, cell, string, tail) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    let atom = AtomTable::build_with(self.atom_tbl, string);

                    target.push_back(Target::to_pstr(lvl, atom, cell.get(), true));
                    self.subterm_to_instr::<Target>(tail, term_loc, &mut target);
                }
                TermRef::CompleteString(lvl, cell, atom) => {
                    self.marker
                        .mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push_back(Target::to_pstr(lvl, atom, cell.get(), false));
                }
                TermRef::Var(lvl @ Level::Shallow, cell, var) => {
                    self.marker.mark_var::<Target>(
                        var.to_var_num().unwrap(),
                        lvl,
                        cell,
                        term_loc,
                        &mut target,
                    );
                }
                _ => {}
            };
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
                    code.push_back(call_instr.to_execute().to_default());
                } else {
                    code.push_back(call_instr.to_default())
                }
            }
            CallPolicy::Counted => {
                if self.marker.in_tail_position {
                    code.push_back(call_instr.to_execute());
                } else {
                    code.push_back(call_instr)
                }
            }
        }
    }

    fn compile_inlined(
        &mut self,
        ct: &InlinedClauseType,
        terms: &'_ [Term],
        term_loc: GenContext,
        code: &mut CodeDeque,
    ) -> Result<(), CompilationError> {
        let call_instr = match ct {
            &InlinedClauseType::CompareNumber(mut cmp) => {
                self.marker.reset_arg(2);

                let (mut lcode, at_1) = self.compile_arith_expr(&terms[0], 1, term_loc, 1)?;

                if !matches!(terms[0], Term::Var(..)) {
                    self.marker.advance_arg();
                }

                let (mut rcode, at_2) = self.compile_arith_expr(&terms[1], 2, term_loc, 2)?;

                code.append(&mut lcode);
                code.append(&mut rcode);

                let at_1 = at_1.unwrap_or(interm!(1));
                let at_2 = at_2.unwrap_or(interm!(2));

                compare_number_instr!(cmp, at_1, at_2)
            }
            InlinedClauseType::IsAtom(..) => match &terms[0] {
                Term::Literal(_, Literal::Char(_))
                | Term::Literal(_, Literal::Atom(atom!("[]")))
                | Term::Literal(_, Literal::Atom(..)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("atom", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsAtomic(..) => match &terms[0] {
                Term::AnonVar
                | Term::Clause(..)
                | Term::Cons(..)
                | Term::PartialString(..)
                | Term::CompleteString(..) => {
                    instr!("$fail")
                }
                Term::Literal(_, Literal::String(_)) => {
                    instr!("$fail")
                }
                Term::Literal(..) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("atomic", r)
                }
            },
            InlinedClauseType::IsCompound(..) => match &terms[0] {
                Term::Clause(..)
                | Term::Cons(..)
                | Term::PartialString(..)
                | Term::CompleteString(..)
                | Term::Literal(_, Literal::String(..)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("compound", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsRational(..) => match terms[0] {
                Term::Literal(_, Literal::Rational(_)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );
                    instr!("rational", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsFloat(..) => match terms[0] {
                Term::Literal(_, Literal::Float(_)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("float", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsNumber(..) => match terms[0] {
                Term::Literal(_, Literal::Float(_))
                | Term::Literal(_, Literal::Rational(_))
                | Term::Literal(_, Literal::Integer(_))
                | Term::Literal(_, Literal::Fixnum(_)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("number", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsNonVar(..) => match terms[0] {
                Term::AnonVar => {
                    instr!("$fail")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("nonvar", r)
                }
                _ => {
                    instr!("$succeed")
                }
            },
            InlinedClauseType::IsInteger(..) => match &terms[0] {
                Term::Literal(_, Literal::Integer(_)) | Term::Literal(_, Literal::Fixnum(_)) => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("integer", r)
                }
                _ => {
                    instr!("$fail")
                }
            },
            InlinedClauseType::IsVar(..) => match terms[0] {
                Term::Literal(..)
                | Term::Clause(..)
                | Term::Cons(..)
                | Term::PartialString(..)
                | Term::CompleteString(..) => {
                    instr!("$fail")
                }
                Term::AnonVar => {
                    instr!("$succeed")
                }
                Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.to_var_num().unwrap(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    instr!("var", r)
                }
            },
        };

        // inlined predicates are never counted, so this overrides nothing.
        self.add_call(code, call_instr, CallPolicy::Counted);

        Ok(())
    }

    fn compile_arith_expr(
        &mut self,
        term: &Term,
        target_int: usize,
        term_loc: GenContext,
        arg: usize,
    ) -> Result<ArithCont, ArithmeticError> {
        let mut evaluator = ArithmeticEvaluator::new(&mut self.marker, target_int);
        evaluator.compile_is(term, term_loc, arg)
    }

    fn compile_is_call(
        &mut self,
        terms: &[Term],
        code: &mut CodeDeque,
        term_loc: GenContext,
        call_policy: CallPolicy,
    ) -> Result<(), CompilationError> {
        macro_rules! compile_expr {
            ($self:expr, $terms:expr, $term_loc:expr, $code:expr) => {{
                let (acode, at) = $self.compile_arith_expr($terms, 1, $term_loc, 2)?;
                $code.extend(acode.into_iter());
                at
            }};
        }

        self.marker.reset_arg(2);

        let at = match terms[0] {
            Term::Var(ref vr, ref name) => {
                let var_num = name.to_var_num().unwrap();

                if self.marker.var_data.records[var_num].num_occurrences > 1 {
                    self.marker.mark_var::<QueryInstruction>(
                        var_num,
                        Level::Shallow,
                        vr,
                        term_loc,
                        code,
                    );

                    self.marker.mark_safe_var_unconditionally(var_num);
                    compile_expr!(self, &terms[1], term_loc, code)
                } else {
                    if let Term::Var(ref vr, ref var) = &terms[1] {
                        let var_num = var.to_var_num().unwrap();

                        // if var is an anonymous variable, insert
                        // is/2 call so that an instantiation error is
                        // thrown when the predicate is run.
                        if self.marker.var_data.records[var_num].num_occurrences > 1 {
                            self.marker.mark_var::<QueryInstruction>(
                                var_num,
                                Level::Shallow,
                                vr,
                                term_loc,
                                code,
                            );

                            self.marker.mark_safe_var_unconditionally(var_num);

                            let at = ArithmeticTerm::Reg(vr.get().norm());
                            self.add_call(code, instr!("$get_number", at), call_policy);

                            return Ok(());
                        }
                    }

                    compile_expr!(self, &terms[1], term_loc, code)
                }
            }
            Term::Literal(
                _,
                c @ Literal::Integer(_)
                | c @ Literal::Float(_)
                | c @ Literal::Rational(_)
                | c @ Literal::Fixnum(_),
            ) => {
                let v = HeapCellValue::from(c);
                code.push_back(instr!("put_constant", Level::Shallow, v, temp_v!(1)));

                self.marker.advance_arg();
                compile_expr!(self, &terms[1], term_loc, code)
            }
            _ => {
                code.push_back(instr!("$fail"));
                return Ok(());
            }
        };

        let at = at.unwrap_or(interm!(1));
        self.add_call(code, instr!("is", temp_v!(1), at), call_policy);

        Ok(())
    }

    fn compile_seq(
        &mut self,
        clauses: &ChunkedTermVec,
        code: &mut CodeDeque,
    ) -> Result<(), CompilationError> {
        let mut chunk_num = 0;
        let mut branch_code_stack = BranchCodeStack::new();
        let mut clause_iter = ClauseIterator::new(clauses);

        while let Some(clause_item) = clause_iter.next() {
            match clause_item {
                ClauseItem::Chunk(chunk) => {
                    for (idx, term) in chunk.iter().enumerate() {
                        let term_loc = if idx + 1 < chunk.len() {
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
                                    let r = self.marker.get_binding(var_num);
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
                                let r = self.marker.get_binding(var_num);

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
                                _,
                                ClauseType::BuiltIn(BuiltInClauseType::Is(..)),
                                ref terms,
                                call_policy,
                            ) => self.compile_is_call(
                                terms,
                                branch_code_stack.code(code),
                                term_loc,
                                call_policy,
                            )?,
                            &QueryTerm::Clause(_, ClauseType::Inlined(ref ct), ref terms, _) => {
                                self.compile_inlined(
                                    ct,
                                    terms,
                                    term_loc,
                                    branch_code_stack.code(code),
                                )?
                            }
                            &QueryTerm::Fail => {
                                branch_code_stack.code(code).push_back(instr!("$fail"));
                            }
                            term @ &QueryTerm::Clause(..) => {
                                self.compile_query_line(
                                    term,
                                    term_loc,
                                    branch_code_stack.code(code),
                                );

                                if self.marker.max_reg_allocated() > MAX_ARITY {
                                    return Err(CompilationError::ExceededMaxArity);
                                }
                            }
                        }
                    }

                    chunk_num += 1;
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
        rule: &Rule,
        var_data: VarData,
    ) -> Result<Code, CompilationError> {
        let Rule {
            head: (_, args),
            clauses,
        } = rule;
        self.marker.var_data = var_data;
        let mut code = VecDeque::new();

        self.marker.reset_at_head(args);

        let iter = FactIterator::from_rule_head_clause(args);
        let fact = self.compile_target::<FactInstruction, _>(iter, GenContext::Head);

        if self.marker.max_reg_allocated() > MAX_ARITY {
            return Err(CompilationError::ExceededMaxArity);
        }

        self.marker.reset_free_list();
        code.extend(fact);

        self.compile_seq(clauses, &mut code)?;

        Ok(Vec::from(code))
    }

    pub(crate) fn compile_fact(
        &mut self,
        fact: &Fact,
        var_data: VarData,
    ) -> Result<Code, CompilationError> {
        let mut code = Vec::new();
        self.marker.var_data = var_data;

        if let Term::Clause(_, _, args) = &fact.head {
            self.marker.reset_at_head(args);

            let iter = FactInstruction::iter(&fact.head);
            let compiled_fact = self.compile_target::<FactInstruction, _>(iter, GenContext::Head);

            if self.marker.max_reg_allocated() > MAX_ARITY {
                return Err(CompilationError::ExceededMaxArity);
            }

            code.extend(compiled_fact);
        }

        code.push(instr!("proceed"));
        Ok(code)
    }

    fn compile_query_line(&mut self, term: &QueryTerm, term_loc: GenContext, code: &mut CodeDeque) {
        self.marker.reset_arg(term.arity());

        let iter = QueryIterator::new(term);
        let query = self.compile_target::<QueryInstruction, _>(iter, term_loc);

        code.extend(query);

        match term {
            &QueryTerm::Clause(_, ref ct, _, call_policy) => {
                self.add_call(code, ct.to_instr(), call_policy);
            }
            _ => unreachable!(),
        };
    }

    fn split_predicate(clauses: &[PredicateClause]) -> Vec<ClauseSpan> {
        let mut subseqs = Vec::new();
        let mut left = 0;
        let mut optimal_index = 0;

        'outer: for (right, clause) in clauses.iter().enumerate() {
            if let Some(args) = clause.args() {
                for (instantiated_arg_index, arg) in args.iter().enumerate() {
                    match arg {
                        Term::Var(..) | Term::AnonVar => {}
                        _ => {
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
                    self.compile_fact(fact, var_data)?
                }
                PredicateClause::Rule(rule, var_data) => {
                    let var_data = std::mem::take(var_data);
                    self.compile_rule(rule, var_data)?
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

            let arg = clause.args().and_then(|args| args.get(optimal_index));

            if let Some(arg) = arg {
                let index = code.len();

                if clauses_len > 1 || self.settings.is_extensible {
                    code_offsets.index_term(arg, index, &mut clause_index_info, self.atom_tbl);
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
        mut clauses: Vec<PredicateClause>,
    ) -> Result<Code, CompilationError> {
        let mut code = Code::new();

        let split_pred = Self::split_predicate(&clauses);
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
                    &mut clauses[left..right],
                    instantiated_arg_index,
                )?
            } else {
                self.compile_pred_subseq::<StaticCodeIndices>(
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
