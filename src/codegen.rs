use crate::atom_table::*;
use crate::parser::ast::*;
use crate::{perm_v, temp_v};

use crate::allocator::*;
use crate::arithmetic::*;
use crate::debray_allocator::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::indexing::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::targets::*;
use crate::types::*;

use crate::instr;
use crate::machine::machine_errors::*;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::collections::VecDeque;

#[derive(Debug)]
pub(crate) struct ConjunctInfo<'a> {
    pub(crate) perm_vs: VariableFixtures<'a>,
    pub(crate) num_of_chunks: usize,
    pub(crate) has_deep_cut: bool,
}

impl<'a> ConjunctInfo<'a> {
    fn new(perm_vs: VariableFixtures<'a>, num_of_chunks: usize, has_deep_cut: bool) -> Self {
        ConjunctInfo {
            perm_vs,
            num_of_chunks,
            has_deep_cut,
        }
    }

    fn allocates(&self) -> bool {
        self.perm_vs.size() > 0 || self.num_of_chunks > 1 || self.has_deep_cut
    }

    fn perm_vars(&self) -> usize {
        self.perm_vs.size() + self.perm_var_offset()
    }

    fn perm_var_offset(&self) -> usize {
        self.has_deep_cut as usize
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
    pub(crate) atom_tbl: &'a mut AtomTable,
    marker: DebrayAllocator,
    pub(crate) var_count: IndexMap<Var, usize>,
    settings: CodeGenSettings,
    pub(crate) skeleton: PredicateSkeleton,
    pub(crate) jmp_by_locs: Vec<usize>,
    global_jmp_by_locs_offset: usize,
}

impl DebrayAllocator {
    fn mark_var_in_non_callable(
        &mut self,
        name: Var,
        term_loc: GenContext,
        vr: &Cell<VarReg>,
        code: &mut Code,
    ) -> RegType {
        self.mark_var::<QueryInstruction>(name, Level::Shallow, vr, term_loc, code);
        vr.get().norm()
    }

    #[inline(always)]
    pub(crate) fn get_binding(&self, name: &Var) -> Option<RegType> {
        match self.bindings().get(name) {
            Some(&VarData::Temp(_, t, _)) if t != 0 => Some(RegType::Temp(t)),
            Some(&VarData::Perm(p)) if p != 0 => Some(RegType::Perm(p)),
            _ => None,
        }
    }

    pub(crate) fn mark_non_callable(
        &mut self,
        name: Var,
        arg: usize,
        term_loc: GenContext,
        vr: &Cell<VarReg>,
        code: &mut Code,
    ) -> RegType {
        match self.get_binding(&name) {
            Some(RegType::Temp(t)) => RegType::Temp(t),
            Some(RegType::Perm(p)) => {
                if let GenContext::Last(_) = term_loc {
                    self.mark_var_in_non_callable(name.clone(), term_loc, vr, code);
                    temp_v!(arg)
                } else {
                    RegType::Perm(p)
                }
            }
            None => self.mark_var_in_non_callable(name, term_loc, vr, code),
        }
    }
}

// if the final argument of the structure is a Literal::Index,
// decrement the arity of the PutStructure instruction by 1.
fn trim_structure_by_last_arg(instr: &mut Instruction, last_arg: &Term) {
    match instr {
        Instruction::PutStructure(_, ref mut arity, _) |
        Instruction::GetStructure(_, ref mut arity, _) => {
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
        self.marker.add_to_free_list(r);
    }

    fn add_subterm_to_free_list(&mut self, _term: &Term) {}
}

impl<'a, 'b> AddToFreeList<'a, QueryInstruction> for CodeGenerator<'b> {
    #[inline(always)]
    fn add_term_to_free_list(&mut self, _r: RegType) {}

    #[inline(always)]
    fn add_subterm_to_free_list(&mut self, term: &Term) {
        if let Some(cell) = structure_cell(term) {
            self.marker.add_to_free_list(cell.get());
        }
    }
}

fn structure_cell(term: &Term) -> Option<&Cell<RegType>> {
    match term {
        &Term::Cons(ref cell, ..) |
        &Term::Clause(ref cell, ..) |
        Term::PartialString(ref cell, ..) |
        Term::CompleteString(ref cell, ..) => Some(cell),
        _ => None,
    }
}

impl<'b> CodeGenerator<'b> {
    pub(crate) fn new(atom_tbl: &'b mut AtomTable, settings: CodeGenSettings) -> Self {
        CodeGenerator {
            atom_tbl,
            marker: DebrayAllocator::new(),
            var_count: IndexMap::new(),
            settings,
            skeleton: PredicateSkeleton::new(),
            jmp_by_locs: vec![],
            global_jmp_by_locs_offset: 0,
        }
    }

    fn update_var_count<'a, Iter: Iterator<Item = TermRef<'a>>>(&mut self, iter: Iter) {
        for term in iter {
            if let TermRef::Var(_, _, var) = term {
                let entry = self.var_count.entry(var).or_insert(0);
                *entry += 1;
            }
        }
    }

    fn get_var_count(&self, var: &Var) -> usize {
        *self.var_count.get(var).unwrap()
    }

    fn add_or_increment_void_instr<'a, Target>(target: &mut Code)
    where
        Target: crate::targets::CompilationTarget<'a>,
    {
        if let Some(ref mut instr) = target.last_mut() {
            if Target::is_void_instr(&*instr) {
                Target::incr_void_instr(instr);
                return;
            }
        }

        target.push(Target::to_void(1));
    }

    fn deep_var_instr<'a, Target: crate::targets::CompilationTarget<'a>>(
        &mut self,
        cell: &'a Cell<VarReg>,
        var: &Var,
        term_loc: GenContext,
        target: &mut Code,
    ) {
        if self.get_var_count(var.as_ref()) > 1 {
            self.marker.mark_var::<Target>(var.clone(), Level::Deep, cell, term_loc, target);
        } else {
            Self::add_or_increment_void_instr::<Target>(target);
        }
    }

    fn subterm_to_instr<'a, Target: crate::targets::CompilationTarget<'a>>(
        &mut self,
        subterm: &'a Term,
        term_loc: GenContext,
        target: &mut Code,
    ) {
        match subterm {
            &Term::AnonVar => {
                Self::add_or_increment_void_instr::<Target>(target);
            }
            &Term::Cons(ref cell, ..) |
            &Term::Clause(ref cell, ..) |
            Term::PartialString(ref cell, ..) |
            Term::CompleteString(ref cell, ..) => {
                self.marker.mark_non_var::<Target>(Level::Deep, term_loc, cell, target);
                target.push(Target::clause_arg_to_instr(cell.get()));
            }
            &Term::Literal(_, ref constant) => {
                target.push(Target::constant_subterm(constant.clone()));
            }
            &Term::Var(ref cell, ref var) => {
                self.deep_var_instr::<Target>(cell, var, term_loc, target);
            }
        };
    }

    fn compile_target<'a, Target, Iter>(
        &mut self,
        iter: Iter,
        term_loc: GenContext,
    ) -> Code
    where
        Target: crate::targets::CompilationTarget<'a>,
        Iter: Iterator<Item = TermRef<'a>>,
        CodeGenerator<'b>: AddToFreeList<'a, Target>
    {
        let mut target: Code = Vec::new();

        for term in iter {
            match term {
                TermRef::AnonVar(lvl @ Level::Shallow) => {
                    if let GenContext::Head = term_loc {
                        self.marker.advance_arg();
                    } else {
                        self.marker.mark_anon_var::<Target>(lvl, term_loc, &mut target);
                    }
                }
                TermRef::Clause(lvl, cell, name, terms) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_structure(name, terms.len(), cell.get()));

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_term_to_free_list(self, cell.get());

                    if let Some(instr) = target.last_mut() {
                        if let Some(term) = terms.last() {
                            trim_structure_by_last_arg(instr, term);
                        }
                    }

                    for subterm in terms {
                        self.subterm_to_instr::<Target>(subterm, term_loc, &mut target);
                    }

                    for subterm in terms {
                        <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(self, subterm);
                    }
                }
                TermRef::Cons(lvl, cell, head, tail) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_list(lvl, cell.get()));

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_term_to_free_list(self, cell.get());

                    self.subterm_to_instr::<Target>(head, term_loc, &mut target);
                    self.subterm_to_instr::<Target>(tail, term_loc, &mut target);

                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(self, head);
                    <CodeGenerator<'b> as AddToFreeList<'a, Target>>::add_subterm_to_free_list(self, tail);
                }
                TermRef::Literal(lvl @ Level::Shallow, cell, Literal::String(ref string)) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_pstr(lvl, *string, cell.get(), false));
                }
                TermRef::Literal(lvl @ Level::Shallow, cell, constant) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_constant(lvl, *constant, cell.get()));
                }
                TermRef::PartialString(lvl, cell, string, tail) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    let atom = self.atom_tbl.build_with(&string);

                    target.push(Target::to_pstr(lvl, atom, cell.get(), true));
                    self.subterm_to_instr::<Target>(tail, term_loc, &mut target);
                }
                TermRef::CompleteString(lvl, cell, atom) => {
                    self.marker.mark_non_var::<Target>(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_pstr(lvl, atom, cell.get(), false));
                }
                TermRef::Var(lvl @ Level::Shallow, cell, var) if var.as_str() == Some("!") => {
                    if self.marker.is_unbound(var.clone()) {
                        if term_loc != GenContext::Head {
                            self.marker.mark_reserved_var::<Target>(
                                var.clone(),
                                lvl,
                                cell,
                                term_loc,
                                &mut target,
                                perm_v!(1),
                                false,
                            );

                            continue;
                        }
                    }

                    self.marker.mark_var::<Target>(var.clone(), lvl, cell, term_loc, &mut target);
                }
                TermRef::Var(lvl @ Level::Shallow, cell, var) => {
                    self.marker.mark_var::<Target>(var.clone(), lvl, cell, term_loc, &mut target);
                }
                _ => {}
            };
        }

        target
    }

    fn collect_var_data<'a>(&mut self, mut iter: ChunkedIterator<'a>) -> ConjunctInfo<'a> {
        let mut vs = VariableFixtures::new();

        while let Some((chunk_num, lt_arity, chunked_terms)) = iter.next() {
            for (i, chunked_term) in chunked_terms.iter().enumerate() {
                let term_loc = match chunked_term {
                    &ChunkedTerm::HeadClause(..) => GenContext::Head,
                    &ChunkedTerm::BodyTerm(_) => {
                        if i < chunked_terms.len() - 1 {
                            GenContext::Mid(chunk_num)
                        } else {
                            GenContext::Last(chunk_num)
                        }
                    }
                };

                self.update_var_count(chunked_term.post_order_iter());
                vs.mark_vars_in_chunk(chunked_term.post_order_iter(), lt_arity, term_loc);
            }
        }

        let num_of_chunks = iter.chunk_num;
        let has_deep_cut = iter.encountered_deep_cut();

        vs.populate_restricting_sets();
        vs.set_perm_vals(has_deep_cut);

        let vs = self.marker.drain_var_data(vs, num_of_chunks);
        ConjunctInfo::new(vs, num_of_chunks, has_deep_cut)
    }

    fn add_conditional_call(&mut self, code: &mut Code, qt: &QueryTerm, pvs: usize) {
        match qt {
            &QueryTerm::Jump(ref vars) => {
                self.jmp_by_locs.push(code.len());
                code.push(instr!("jmp_by_call", vars.len(), 0, pvs));
            }
            &QueryTerm::Clause(_, ref ct, _, CallPolicy::Default) => {
                code.push(call_clause_by_default!(ct.clone(), pvs));
            }
            &QueryTerm::Clause(_, ref ct, _, CallPolicy::Counted) => {
                code.push(call_clause!(ct.clone(), pvs));
            }
            _ => {}
        }
    }

    fn lco(code: &mut Code) -> usize {
        let mut dealloc_index = code.len() - 1;
        let last_instr = code.pop();

        match last_instr {
            Some(instr @ Instruction::Proceed) => {
                code.push(instr);
            }
            Some(instr @ Instruction::Cut(_)) => {
                dealloc_index += 1;
                code.push(instr);
            }
            Some(mut instr) if instr.is_ctrl_instr() => {
                code.push(if instr.perm_vars_mut().is_some() {
                    instr.to_execute()
                } else {
                    dealloc_index += 1;
                    instr
                });
            }
            Some(instr) => {
                code.push(instr);
            }
            None => {}
        }

        dealloc_index
    }

    fn compile_inlined<'a>(
        &mut self,
        ct: &InlinedClauseType,
        terms: &'a Vec<Term>,
        term_loc: GenContext,
        code: &mut Code,
    ) -> Result<(), CompilationError> {
        match ct {
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

                code.push(compare_number_instr!(cmp, at_1, at_2));
            }
            &InlinedClauseType::IsAtom(..) => match &terms[0] {
                &Term::Literal(_, Literal::Char(_)) |
                &Term::Literal(_, Literal::Atom(atom!("[]"))) |
                &Term::Literal(_, Literal::Atom(..)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("atom", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsAtomic(..) => match &terms[0] {
                &Term::AnonVar |
                &Term::Clause(..) |
                &Term::Cons(..) |
                &Term::PartialString(..) |
                &Term::CompleteString(..) => {
                    code.push(instr!("$fail", 0));
                }
                &Term::Literal(_, Literal::String(_)) => {
                    code.push(instr!("$fail", 0));
                }
                &Term::Literal(..) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("atomic", r, 0));
                }
            },
            &InlinedClauseType::IsCompound(..) => match &terms[0] {
                &Term::Clause(..) |
                &Term::Cons(..) |
                &Term::PartialString(..) |
                &Term::CompleteString(..) |
                &Term::Literal(_, Literal::String(..)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("compound", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsRational(..) => match &terms[0] {
                &Term::Literal(_, Literal::Rational(_)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.marker.mark_non_callable(name.clone(), 1,  term_loc, vr, code);
                    code.push(instr!("rational", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsFloat(..) => match &terms[0] {
                &Term::Literal(_, Literal::Float(_)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("float", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsNumber(..) => match &terms[0] {
                &Term::Literal(_, Literal::Float(_)) |
                &Term::Literal(_, Literal::Rational(_)) |
                &Term::Literal(_, Literal::Integer(_)) |
                &Term::Literal(_, Literal::Fixnum(_)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("number", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsNonVar(..) => match &terms[0] {
                &Term::AnonVar => {
                    code.push(instr!("$fail", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("nonvar", r, 0));
                }
                _ => {
                    code.push(instr!("$succeed", 0));
                }
            },
            &InlinedClauseType::IsInteger(..) => match &terms[0] {
                &Term::Literal(_, Literal::Integer(_)) |
                &Term::Literal(_, Literal::Fixnum(_)) => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("integer", r, 0));
                }
                _ => {
                    code.push(instr!("$fail", 0));
                }
            },
            &InlinedClauseType::IsVar(..) => match &terms[0] {
                &Term::Literal(..) |
                &Term::Clause(..) |
                &Term::Cons(..) |
                &Term::PartialString(..) |
                &Term::CompleteString(..) => {
                    code.push(instr!("$fail", 0));
                }
                &Term::AnonVar => {
                    code.push(instr!("$succeed", 0));
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);

                    let r = self.marker.mark_non_callable(
                        name.clone(),
                        1,
                        term_loc,
                        vr,
                        code,
                    );

                    code.push(instr!("var", r, 0));
                }
            },
        }

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
        terms: &Vec<Term>,
        code: &mut Code,
        term_loc: GenContext,
        call_policy: CallPolicy,
    ) -> Result<(), CompilationError> {
        macro_rules! compile_expr {
            ($self:expr, $terms:expr, $term_loc:expr, $code:expr) => ({
                let (acode, at) = $self.compile_arith_expr($terms, 1, $term_loc, 2)?;
                $code.extend(acode.into_iter());
                at
            });
        }

        self.marker.reset_arg(2);

        let at = match &terms[0] {
            &Term::Var(ref vr, ref name) => {
                self.marker.mark_var::<QueryInstruction>(
                    name.clone(),
                    Level::Shallow,
                    vr,
                    term_loc,
                    code,
                );

                compile_expr!(self, &terms[1], term_loc, code)
            }
            &Term::Literal(_, c @ Literal::Integer(_) |
                              c @ Literal::Float(_) |
                              c @ Literal::Rational(_) |
                              c @ Literal::Fixnum(_)) => {
                let v = HeapCellValue::from(c);
                code.push(instr!("put_constant", Level::Shallow, v, temp_v!(1)));

                self.marker.advance_arg();
                compile_expr!(self, &terms[1], term_loc, code)
            }
            _ => {
                code.push(instr!("$fail", 0));
                return Ok(());
            }
        };

        let at = at.unwrap_or(interm!(1));

        Ok(if let CallPolicy::Default = call_policy {
            code.push(instr!("is", default, temp_v!(1), at, 0));
        } else {
            code.push(instr!("is", temp_v!(1), at, 0));
        })
    }

    #[inline]
    fn compile_unblocked_cut(&mut self, code: &mut Code, cell: &Cell<VarReg>) {
        let r = self.marker.get(Var::from("!"));
        cell.set(VarReg::Norm(r));
        code.push(instr!("$set_cp", cell.get().norm(), 0));
    }

    fn compile_get_level_and_unify(
        &mut self,
        code: &mut Code,
        cell: &Cell<VarReg>,
        var: Var,
        term_loc: GenContext,
    ) {
        let mut target = Code::new();

        self.marker.reset_arg(1);
        self.marker.mark_var::<QueryInstruction>(var, Level::Shallow, cell, term_loc, &mut target);

        if !target.is_empty() {
            code.extend(target.into_iter());
        }

        code.push(instr!("get_level_and_unify", cell.get().norm()));
    }

    fn compile_seq<'a>(
        &mut self,
        iter: ChunkedIterator<'a>,
        conjunct_info: &ConjunctInfo<'a>,
        code: &mut Code,
    ) -> Result<(), CompilationError> {
        for (chunk_num, _, terms) in iter.rule_body_iter() {
            for (i, term) in terms.iter().enumerate() {
                let term_loc = if i + 1 < terms.len() {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                match *term {
                    &QueryTerm::GetLevelAndUnify(ref cell, ref var) => {
                        self.compile_get_level_and_unify(code, cell, var.clone(), term_loc)
                    }
                    &QueryTerm::UnblockedCut(ref cell) => self.compile_unblocked_cut(code, cell),
                    &QueryTerm::BlockedCut => code.push(if chunk_num == 0 {
                        Instruction::NeckCut
                    } else {
                        Instruction::Cut(perm_v!(1))
                    }),
                    &QueryTerm::Clause(
                        _,
                        ClauseType::BuiltIn(BuiltInClauseType::Is(..)),
                        ref terms,
                        call_policy,
                    ) => self.compile_is_call(terms, code, term_loc, call_policy)?,
                    &QueryTerm::Clause(_, ClauseType::Inlined(ref ct), ref terms, _) => {
                        self.compile_inlined(ct, terms, term_loc, code)?
                    }
                    _ => {
                        let num_perm_vars = if chunk_num == 0 {
                            conjunct_info.perm_vars()
                        } else {
                            conjunct_info.perm_vs.vars_above_threshold(i + 1)
                        };

                        self.compile_query_line(term, term_loc, code, num_perm_vars);

                        if self.marker.max_reg_allocated() > MAX_ARITY {
                            return Err(CompilationError::ExceededMaxArity);
                        }
                    }
                }
            }

            self.marker.reset_contents();
        }

        Ok(())
    }

    fn compile_seq_prelude(&mut self, conjunct_info: &ConjunctInfo, body: &mut Code) {
        if conjunct_info.allocates() {
            let perm_vars = conjunct_info.perm_vars();

            body.push(Instruction::Allocate(perm_vars));

            if conjunct_info.has_deep_cut {
                body.push(Instruction::GetLevel(perm_v!(1)));
            }
        }
    }

    fn compile_cleanup<'a>(
        &mut self,
        code: &mut Code,
        conjunct_info: &ConjunctInfo<'a>,
        toc: &'a QueryTerm,
    ) {
        // add a proceed to bookend any trailing cuts.
        match toc {
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => {
                code.push(instr!("proceed"));
            }
            _ => {}
        };

        // perform lco.
        let dealloc_index = Self::lco(code);

        if conjunct_info.allocates() {
            let offset = self.global_jmp_by_locs_offset;

            if let Some(jmp_by_offset) = self.jmp_by_locs[offset..].last_mut() {
                if *jmp_by_offset == dealloc_index {
                    *jmp_by_offset += 1;
                }
            }

            code.insert(dealloc_index, instr!("deallocate"));
        }
    }

    pub(crate) fn compile_rule(&mut self, rule: &Rule) -> Result<Code, CompilationError> {
        let iter = ChunkedIterator::from_rule(rule);
        let conjunct_info = self.collect_var_data(iter);

        let &Rule {
            head: (_, ref args, ref p1),
            ref clauses,
        } = rule;

        let mut code = Code::new();

        self.marker.reset_at_head(args);
        self.compile_seq_prelude(&conjunct_info, &mut code);

        let iter = FactIterator::from_rule_head_clause(args);
        let mut fact = self.compile_target::<FactInstruction, _>(iter, GenContext::Head);

        if self.marker.max_reg_allocated() > MAX_ARITY {
            return Err(CompilationError::ExceededMaxArity);
        }

        self.marker.reset_free_list();

        let mut unsafe_var_marker = UnsafeVarMarker::new();

        if !fact.is_empty() {
            unsafe_var_marker = self.mark_unsafe_fact_vars(&mut fact);
            code.extend(fact.into_iter());
        }

        let iter = ChunkedIterator::from_rule_body(p1, clauses);
        self.compile_seq(iter, &conjunct_info, &mut code)?;

        unsafe_var_marker.mark_unsafe_instrs(&mut code);

        self.compile_cleanup(&mut code, &conjunct_info, clauses.last().unwrap_or(p1));

        Ok(code)
    }

    fn mark_unsafe_fact_vars(&self, fact: &mut Code) -> UnsafeVarMarker {
        let mut safe_vars = IndexSet::new();

        for fact_instr in fact.iter_mut() {
            match fact_instr {
                &mut Instruction::UnifyValue(r) => {
                    if !safe_vars.contains(&r) {
                        *fact_instr = Instruction::UnifyLocalValue(r);
                        safe_vars.insert(r);
                    }
                }
                &mut Instruction::UnifyVariable(r) => {
                    safe_vars.insert(r);
                }
                _ => {}
            }
        }

        UnsafeVarMarker::from_fact_vars(safe_vars)
    }

    pub(crate) fn compile_fact(&mut self, term: &Term) -> Result<Code, CompilationError> {
        self.update_var_count(post_order_iter(term));

        let mut vs = VariableFixtures::new();

        vs.mark_vars_in_chunk(post_order_iter(term), term.arity(), GenContext::Head);

        vs.populate_restricting_sets();
        self.marker.drain_var_data(vs, 1);

        let mut code = Vec::new();

        if let &Term::Clause(_, _, ref args) = term {
            self.marker.reset_at_head(args);

            let iter = FactInstruction::iter(term);
            let mut compiled_fact = self.compile_target::<FactInstruction, _>(
                iter,
                GenContext::Head,
            );

            if self.marker.max_reg_allocated() > MAX_ARITY {
                return Err(CompilationError::ExceededMaxArity);
            }

            self.mark_unsafe_fact_vars(&mut compiled_fact);

            if !compiled_fact.is_empty() {
                code.extend(compiled_fact.into_iter());
            }
        }

        code.push(instr!("proceed"));
        Ok(code)
    }

    fn compile_query_line(
        &mut self,
        term: &QueryTerm,
        term_loc: GenContext,
        code: &mut Code,
        num_perm_vars_left: usize,
    ) {
        self.marker.reset_arg(term.arity());

        let iter = query_term_post_order_iter(term);
        let query = self.compile_target::<QueryInstruction, _>(iter, term_loc);

        code.extend(query.into_iter());
        self.add_conditional_call(code, term, num_perm_vars_left);
    }

    #[inline]
    fn increment_jmp_by_locs_by(&mut self, incr: usize) {
        let offset = self.global_jmp_by_locs_offset;

        for loc in &mut self.jmp_by_locs[offset..] {
            *loc += incr;
        }
    }

    fn split_predicate(clauses: &[PredicateClause]) -> Vec<ClauseSpan> {
        let mut subseqs = Vec::new();
        let mut left = 0;
        let mut optimal_index = 0;

        'outer: for (right, clause) in clauses.iter().enumerate() {
            if let Some(args) = clause.args() {
                for (instantiated_arg_index, arg) in args.iter().enumerate() {
                    match arg {
                        Term::Var(..) | Term::AnonVar => {
                        }
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
                subseqs.push(ClauseSpan { left, right, instantiated_arg_index: optimal_index });
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
        clauses: &[PredicateClause],
        optimal_index: usize,
    ) -> Result<Code, CompilationError> {
        let mut code = VecDeque::new();
        let mut code_offsets = CodeOffsets::new(I::new(), optimal_index + 1);

        let mut skip_stub_try_me_else = false;
        let jmp_by_locs_len = self.jmp_by_locs.len();

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_index_info = ClauseIndexInfo::new(code.len());
            self.global_jmp_by_locs_offset = self.jmp_by_locs.len();

            let clause_code = match clause {
                &PredicateClause::Fact(ref fact, ..) => self.compile_fact(fact)?,
                &PredicateClause::Rule(ref rule, ..) => self.compile_rule(rule)?,
            };

            if clauses.len() > 1 {
                let choice = match i {
                    0 => self.settings.internal_try_me_else(clause_code.len() + 1),
                    _ if i == clauses.len() - 1 => self.settings.internal_trust_me(),
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

            let arg = clause.args().and_then(|args| args.iter().nth(optimal_index));

            if let Some(arg) = arg {
                let index = code.len();

                if clauses.len() > 1 || self.settings.is_extensible {
                    code_offsets.index_term(arg, index, &mut clause_index_info, self.atom_tbl);
                }
            }

            if !(code_offsets.no_indices() && clauses.len() == 1 && self.settings.is_extensible) {
                // the peculiar condition of this block, when false,
                // anticipates code.pop_front() being called about a
                // dozen lines below.

                if !skip_stub_try_me_else {
                    // if the condition is false, code_offsets.no_indices() is false,
                    // so don't repeat the work of the condition on skip_stub_try_me_else
                    // below.
                    self.increment_jmp_by_locs_by(code.len());
                }
            }

            self.skeleton.clauses.push_back(clause_index_info);
            code.extend(clause_code.into_iter());
        }

        let index_code = if clauses.len() > 1 || self.settings.is_extensible {
            code_offsets.compute_indices(skip_stub_try_me_else)
        } else {
            vec![]
        };

        self.global_jmp_by_locs_offset = jmp_by_locs_len;

        if !index_code.is_empty() {
            code.push_front(Instruction::IndexingCode(index_code));

            if skip_stub_try_me_else {
                // skip the TryMeElse(0) also.
                self.increment_jmp_by_locs_by(2);
            } else {
                self.increment_jmp_by_locs_by(1);
            }
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
        clauses: &Vec<PredicateClause>,
    ) -> Result<Code, CompilationError> {
        let mut code = Code::new();

        let split_pred = Self::split_predicate(&clauses);
        let multi_seq = split_pred.len() > 1;

        for ClauseSpan { left, right, instantiated_arg_index } in split_pred {
            let skel_lower_bound = self.skeleton.clauses.len();
            let code_segment = if self.settings.is_dynamic() {
                self.compile_pred_subseq::<DynamicCodeIndices>(
                    &clauses[left..right],
                    instantiated_arg_index,
                )?
            } else {
                self.compile_pred_subseq::<StaticCodeIndices>(
                    &clauses[left..right],
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

                for clause_index_info in self.skeleton.clauses
                                             .make_contiguous()[skel_lower_bound..]
                                             .iter_mut()
                {
                    clause_index_info.clause_start +=
                        clause_start_offset + 2 * (segment_is_indexed as usize);
                    clause_index_info.opt_arg_index_key += clause_start_offset + 1;
                }
            }

            self.increment_jmp_by_locs_by(code.len());
            self.global_jmp_by_locs_offset = self.jmp_by_locs.len();

            code.extend(code_segment.into_iter());
        }

        Ok(code)
    }
}
