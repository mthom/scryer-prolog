/// Code generation to WAM-like instructions.
use crate::prolog_parser_rebis::ast::*;
use crate::prolog_parser_rebis::tabled_rc::TabledData;
use crate::prolog_parser_rebis::{perm_v, temp_v};

use crate::allocator::*;
use crate::arithmetic::*;
use crate::clause_types::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::indexing::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::targets::*;

use crate::machine::machine_errors::*;

use crate::indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

#[inline]
pub fn trust_me(non_counted_bt: bool) -> ChoiceInstruction {
    if non_counted_bt {
        ChoiceInstruction::DefaultTrustMe(0)
    } else {
        ChoiceInstruction::TrustMe(0)
    }
}

#[inline]
pub fn retry_me_else(offset: usize, non_counted_bt: bool) -> ChoiceInstruction {
    if non_counted_bt {
        ChoiceInstruction::DefaultRetryMeElse(offset)
    } else {
        ChoiceInstruction::RetryMeElse(offset)
    }
}

#[derive(Debug)]
pub struct ConjunctInfo<'a> {
    pub perm_vs: VariableFixtures<'a>,
    pub num_of_chunks: usize,
    pub has_deep_cut: bool,
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

    fn mark_unsafe_vars(&self, mut unsafe_var_marker: UnsafeVarMarker, code: &mut Code) {
        if code.is_empty() {
            return;
        }

        let mut code_index = 0;

        for phase in 0.. {
            while let Line::Query(ref query_instr) = &code[code_index] {
                if !unsafe_var_marker.mark_safe_vars(query_instr) {
                    unsafe_var_marker.mark_phase(query_instr, phase);
                }

                code_index += 1;
            }

            if code_index + 1 < code.len() {
                code_index += 1;
            } else {
                break;
            }
        }

        code_index = 0;

        for phase in 0.. {
            while let Line::Query(ref mut query_instr) = &mut code[code_index] {
                unsafe_var_marker.mark_unsafe_vars(query_instr, phase);
                code_index += 1;
            }

            if code_index + 1 < code.len() {
                code_index += 1;
            } else {
                break;
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CodeGenSettings {
    pub is_extensible: bool,
    pub non_counted_bt: bool,
}

impl CodeGenSettings {
    #[inline]
    pub fn new(is_extensible: bool, non_counted_bt: bool) -> Self {
        CodeGenSettings {
            is_extensible,
            non_counted_bt,
        }
    }
}

#[derive(Debug)]
pub struct CodeGenerator<TermMarker> {
    atom_tbl: TabledData<Atom>,
    marker: TermMarker,
    pub var_count: IndexMap<Rc<Var>, usize>,
    non_counted_bt: bool,
    is_extensible: bool,
    pub skeleton: PredicateSkeleton,
    pub jmp_by_locs: Vec<usize>,
    global_jmp_by_locs_offset: usize,
}

impl<'a, TermMarker: Allocator<'a>> CodeGenerator<TermMarker> {
    pub fn new(atom_tbl: TabledData<Atom>, settings: CodeGenSettings) -> Self {
        CodeGenerator {
            atom_tbl,
            marker: Allocator::new(),
            var_count: IndexMap::new(),
            non_counted_bt: settings.non_counted_bt,
            is_extensible: settings.is_extensible,
            skeleton: PredicateSkeleton::new(),
            jmp_by_locs: vec![],
            global_jmp_by_locs_offset: 0,
        }
    }

    fn update_var_count<Iter: Iterator<Item = TermRef<'a>>>(&mut self, iter: Iter) {
        for term in iter {
            if let TermRef::Var(_, _, var) = term {
                let entry = self.var_count.entry(var).or_insert(0);
                *entry += 1;
            }
        }
    }

    fn get_var_count(&self, var: &'a Var) -> usize {
        *self.var_count.get(var).unwrap()
    }

    fn mark_var_in_non_callable(
        &mut self,
        name: Rc<Var>,
        term_loc: GenContext,
        vr: &'a Cell<VarReg>,
        code: &mut Code,
    ) -> RegType {
        let mut target = Vec::new();
        self.marker
            .mark_var(name, Level::Shallow, vr, term_loc, &mut target);

        if !target.is_empty() {
            code.extend(target.into_iter().map(Line::Query));
        }

        vr.get().norm()
    }

    fn mark_non_callable(
        &mut self,
        name: Rc<Var>,
        arg: usize,
        term_loc: GenContext,
        vr: &'a Cell<VarReg>,
        code: &mut Code,
    ) -> RegType {
        match self.marker.bindings().get(&name) {
            Some(&VarData::Temp(_, t, _)) if t != 0 => RegType::Temp(t),
            Some(&VarData::Perm(p)) if p != 0 => {
                if let GenContext::Last(_) = term_loc {
                    self.mark_var_in_non_callable(name.clone(), term_loc, vr, code);
                    temp_v!(arg)
                } else {
                    RegType::Perm(p)
                }
            }
            _ => self.mark_var_in_non_callable(name, term_loc, vr, code),
        }
    }

    fn add_or_increment_void_instr<Target>(target: &mut Vec<Target>)
    where
        Target: CompilationTarget<'a>,
    {
        if let Some(ref mut instr) = target.last_mut() {
            if Target::is_void_instr(&*instr) {
                Target::incr_void_instr(instr);
                return;
            }
        }

        target.push(Target::to_void(1));
    }

    fn deep_var_instr<Target: CompilationTarget<'a>>(
        &mut self,
        cell: &'a Cell<VarReg>,
        var: &'a Rc<Var>,
        term_loc: GenContext,
        is_exposed: bool,
        target: &mut Vec<Target>,
    ) {
        if is_exposed || self.get_var_count(var.as_ref()) > 1 {
            self.marker
                .mark_var(var.clone(), Level::Deep, cell, term_loc, target);
        } else {
            Self::add_or_increment_void_instr(target);
        }
    }

    fn subterm_to_instr<Target: CompilationTarget<'a>>(
        &mut self,
        subterm: &'a Term,
        term_loc: GenContext,
        is_exposed: bool,
        target: &mut Vec<Target>,
    ) {
        match subterm {
            &Term::AnonVar if is_exposed => {
                self.marker.mark_anon_var(Level::Deep, term_loc, target);
            }
            &Term::AnonVar => {
                Self::add_or_increment_void_instr(target);
            }
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _, _) => {
                self.marker
                    .mark_non_var(Level::Deep, term_loc, cell, target);
                target.push(Target::clause_arg_to_instr(cell.get()));
            }
            &Term::Constant(_, ref constant) => {
                target.push(Target::constant_subterm(constant.clone()));
            }
            &Term::Var(ref cell, ref var) => {
                self.deep_var_instr(cell, var, term_loc, is_exposed, target);
            }
        };
    }

    fn compile_target<Target, Iter>(
        &mut self,
        iter: Iter,
        term_loc: GenContext,
        is_exposed: bool,
    ) -> Vec<Target>
    where
        Target: CompilationTarget<'a>,
        Iter: Iterator<Item = TermRef<'a>>,
    {
        let mut target = Vec::new();

        for term in iter {
            match term {
                TermRef::AnonVar(lvl @ Level::Shallow) => {
                    if let GenContext::Head = term_loc {
                        self.marker.advance_arg();
                    } else {
                        self.marker.mark_anon_var(lvl, term_loc, &mut target);
                    }
                }
                TermRef::Clause(lvl, cell, ct, terms) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_structure(ct, terms.len(), cell.get()));

                    for subterm in terms {
                        self.subterm_to_instr(subterm.as_ref(), term_loc, is_exposed, &mut target);
                    }
                }
                TermRef::Cons(lvl, cell, head, tail) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_list(lvl, cell.get()));

                    self.subterm_to_instr(head, term_loc, is_exposed, &mut target);
                    self.subterm_to_instr(tail, term_loc, is_exposed, &mut target);
                }
                TermRef::Constant(lvl @ Level::Shallow, cell, Constant::String(ref string)) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_pstr(lvl, string.to_string(), cell.get(), false));
                }
                TermRef::Constant(lvl @ Level::Shallow, cell, constant) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_constant(lvl, constant.clone(), cell.get()));
                }
                TermRef::PartialString(lvl, cell, string, tail) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);

                    if let Some(tail) = tail {
                        target.push(Target::to_pstr(lvl, string, cell.get(), true));
                        self.subterm_to_instr(tail, term_loc, is_exposed, &mut target);
                    } else {
                        target.push(Target::to_pstr(lvl, string, cell.get(), false));
                    }
                }
                TermRef::Var(lvl @ Level::Shallow, cell, ref var) if var.as_str() == "!" => {
                    if self.marker.is_unbound(var.clone()) {
                        if term_loc != GenContext::Head {
                            self.marker.mark_reserved_var(
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

                    self.marker
                        .mark_var(var.clone(), lvl, cell, term_loc, &mut target);
                }
                TermRef::Var(lvl @ Level::Shallow, cell, var) => {
                    self.marker
                        .mark_var(var.clone(), lvl, cell, term_loc, &mut target);
                }
                _ => {}
            };
        }

        target
    }

    fn collect_var_data(&mut self, mut iter: ChunkedIterator<'a>) -> ConjunctInfo<'a> {
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
                code.push(jmp_call!(vars.len(), 0, pvs));
            }
            &QueryTerm::Clause(_, ref ct, ref terms, true) => {
                code.push(call_clause_by_default!(ct.clone(), terms.len(), pvs));
            }
            &QueryTerm::Clause(_, ref ct, ref terms, false) => {
                code.push(call_clause!(ct.clone(), terms.len(), pvs));
            }
            _ => {}
        }
    }

    fn lco(code: &mut Code) -> usize {
        let mut dealloc_index = code.len() - 1;

        match code.last_mut() {
            Some(&mut Line::Control(ref mut ctrl)) => match ctrl {
                &mut ControlInstruction::CallClause(_, _, _, ref mut last_call, _) => {
                    *last_call = true;
                }
                &mut ControlInstruction::JmpBy(_, _, _, ref mut last_call) => {
                    *last_call = true;
                }
                &mut ControlInstruction::Proceed => {}
                _ => {
                    dealloc_index += 1;
                }
            },
            Some(&mut Line::Cut(CutInstruction::Cut(_))) => {
                dealloc_index += 1;
            }
            _ => {}
        };

        dealloc_index
    }

    fn compile_inlined(
        &mut self,
        ct: &InlinedClauseType,
        terms: &'a Vec<Box<Term>>,
        term_loc: GenContext,
        code: &mut Code,
    ) -> Result<(), CompilationError> {
        match ct {
            &InlinedClauseType::CompareNumber(cmp, ..) => {
                self.marker.reset_arg(2);

                let (mut lcode, at_1) = self.call_arith_eval(terms[0].as_ref(), 1)?;
                let (mut rcode, at_2) = self.call_arith_eval(terms[1].as_ref(), 2)?;

                let at_1 = if let &Term::Var(ref vr, ref name) = terms[0].as_ref() {
                    ArithmeticTerm::Reg(self.mark_non_callable(name.clone(), 1, term_loc, vr, code))
                } else {
                    at_1.unwrap_or(interm!(1))
                };

                let at_2 = if let &Term::Var(ref vr, ref name) = terms[1].as_ref() {
                    ArithmeticTerm::Reg(self.mark_non_callable(name.clone(), 2, term_loc, vr, code))
                } else {
                    at_2.unwrap_or(interm!(2))
                };

                code.append(&mut lcode);
                code.append(&mut rcode);

                code.push(compare_number_instr!(cmp, at_1, at_2));
            }
            &InlinedClauseType::IsAtom(..) => match terms[0].as_ref() {
                &Term::Constant(_, Constant::Char(_))
                | &Term::Constant(_, Constant::EmptyList)
                | &Term::Constant(_, Constant::Atom(..)) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_atom!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsAtomic(..) => match terms[0].as_ref() {
                &Term::AnonVar | &Term::Clause(..) | &Term::Cons(..) => {
                    code.push(fail!());
                }
                &Term::Constant(..) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_atomic!(r));
                }
            },
            &InlinedClauseType::IsCompound(..) => match terms[0].as_ref() {
                &Term::Clause(..) | &Term::Cons(..) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_compound!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsRational(..) => match terms[0].as_ref() {
                &Term::Constant(_, Constant::Rational(_)) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_rational!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsFloat(..) => match terms[0].as_ref() {
                &Term::Constant(_, Constant::Float(_)) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_float!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsNumber(..) => match terms[0].as_ref() {
                &Term::Constant(_, Constant::Float(_))
                | &Term::Constant(_, Constant::Rational(_))
                | &Term::Constant(_, Constant::Integer(_))
                | &Term::Constant(_, Constant::Fixnum(_))
                | &Term::Constant(_, Constant::Usize(_)) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_number!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsNonVar(..) => match terms[0].as_ref() {
                &Term::AnonVar => {
                    code.push(fail!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_nonvar!(r));
                }
                _ => {
                    code.push(succeed!());
                }
            },
            &InlinedClauseType::IsInteger(..) => match terms[0].as_ref() {
                &Term::Constant(_, Constant::Integer(_))
                | &Term::Constant(_, Constant::Fixnum(_))
                | &Term::Constant(_, Constant::Usize(_)) => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_integer!(r));
                }
                _ => {
                    code.push(fail!());
                }
            },
            &InlinedClauseType::IsVar(..) => match terms[0].as_ref() {
                &Term::Constant(..) | &Term::Clause(..) | &Term::Cons(..) => {
                    code.push(fail!());
                }
                &Term::AnonVar => {
                    code.push(succeed!());
                }
                &Term::Var(ref vr, ref name) => {
                    self.marker.reset_arg(1);
                    let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                    code.push(is_var!(r));
                }
            },
        }

        Ok(())
    }

    fn call_arith_eval(
        &self,
        term: &'a Term,
        target_int: usize,
    ) -> Result<ArithCont, ArithmeticError> {
        let mut evaluator = ArithmeticEvaluator::new(&self.marker.bindings(), target_int);
        evaluator.eval(term)
    }

    fn compile_is_call(
        &mut self,
        terms: &'a Vec<Box<Term>>,
        code: &mut Code,
        term_loc: GenContext,
        use_default_call_policy: bool,
    ) -> Result<(), CompilationError> {
        let (mut acode, at) = self.call_arith_eval(terms[1].as_ref(), 1)?;
        code.append(&mut acode);

        self.marker.reset_arg(2);

        match terms[0].as_ref() {
            &Term::Var(ref vr, ref name) => {
                let mut target = vec![];

                self.marker
                    .mark_var(name.clone(), Level::Shallow, vr, term_loc, &mut target);

                if !target.is_empty() {
                    code.extend(target.into_iter().map(Line::Query));
                }
            }
            &Term::Constant(_, ref c @ Constant::Integer(_))
            | &Term::Constant(_, ref c @ Constant::Fixnum(_)) => {
                code.push(Line::Query(put_constant!(
                    Level::Shallow,
                    c.clone(),
                    temp_v!(1)
                )));

                self.marker.advance_arg();
            }
            &Term::Constant(_, ref c @ Constant::Float(_)) => {
                code.push(Line::Query(put_constant!(
                    Level::Shallow,
                    c.clone(),
                    temp_v!(1)
                )));

                self.marker.advance_arg();
            }
            &Term::Constant(_, ref c @ Constant::Rational(_)) => {
                code.push(Line::Query(put_constant!(
                    Level::Shallow,
                    c.clone(),
                    temp_v!(1)
                )));

                self.marker.advance_arg();
            }
            _ => {
                code.push(fail!());
                return Ok(());
            }
        }

        let at = if let &Term::Var(ref vr, ref name) = terms[1].as_ref() {
            ArithmeticTerm::Reg(self.mark_non_callable(name.clone(), 2, term_loc, vr, code))
        } else {
            at.unwrap_or(interm!(1))
        };

        Ok(if use_default_call_policy {
            code.push(is_call_by_default!(temp_v!(1), at));
        } else {
            code.push(is_call!(temp_v!(1), at));
        })
    }

    #[inline]
    fn compile_unblocked_cut(&mut self, code: &mut Code, cell: &'a Cell<VarReg>) {
        let r = self.marker.get(Rc::new(String::from("!")));
        cell.set(VarReg::Norm(r));
        code.push(set_cp!(cell.get().norm()));
    }

    fn compile_get_level_and_unify(
        &mut self,
        code: &mut Code,
        cell: &'a Cell<VarReg>,
        var: Rc<Var>,
        term_loc: GenContext,
    ) {
        let mut target = Vec::new();

        self.marker.reset_arg(1);
        self.marker
            .mark_var(var, Level::Shallow, cell, term_loc, &mut target);

        if !target.is_empty() {
            code.extend(
                target
                    .into_iter()
                    .map(|query_instr| Line::Query(query_instr)),
            );
        }

        code.push(get_level_and_unify!(cell.get().norm()));
    }

    fn compile_seq(
        &mut self,
        iter: ChunkedIterator<'a>,
        conjunct_info: &ConjunctInfo<'a>,
        code: &mut Code,
        is_exposed: bool,
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
                        Line::Cut(CutInstruction::NeckCut)
                    } else {
                        Line::Cut(CutInstruction::Cut(perm_v!(1)))
                    }),
                    &QueryTerm::Clause(
                        _,
                        ClauseType::BuiltIn(BuiltInClauseType::Is(..)),
                        ref terms,
                        use_default_call_policy,
                    ) => self.compile_is_call(terms, code, term_loc, use_default_call_policy)?,
                    &QueryTerm::Clause(_, ClauseType::Inlined(ref ct), ref terms, _) => {
                        self.compile_inlined(ct, terms, term_loc, code)?
                    }
                    _ => {
                        let num_perm_vars = if chunk_num == 0 {
                            conjunct_info.perm_vars()
                        } else {
                            conjunct_info.perm_vs.vars_above_threshold(i + 1)
                        };

                        self.compile_query_line(term, term_loc, code, num_perm_vars, is_exposed);
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

            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

            if conjunct_info.has_deep_cut {
                body.push(Line::Cut(CutInstruction::GetLevel(perm_v!(1))));
            }
        }
    }

    fn compile_cleanup(
        &mut self,
        code: &mut Code,
        conjunct_info: &ConjunctInfo,
        toc: &'a QueryTerm,
    ) {
        // add a proceed to bookend any trailing cuts.
        match toc {
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => code.push(proceed!()),
            &QueryTerm::Clause(_, ClauseType::Inlined(..), ..) => code.push(proceed!()),
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

            code.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }
    }

    pub fn compile_rule<'b: 'a>(&mut self, rule: &'b Rule) -> Result<Code, CompilationError> {
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
        let mut fact = self.compile_target(iter, GenContext::Head, false);

        let mut unsafe_var_marker = UnsafeVarMarker::new();

        if !fact.is_empty() {
            unsafe_var_marker = self.mark_unsafe_fact_vars(&mut fact);

            for fact_instr in fact {
                code.push(Line::Fact(fact_instr));
            }
        }

        let iter = ChunkedIterator::from_rule_body(p1, clauses);
        self.compile_seq(iter, &conjunct_info, &mut code, false)?;

        conjunct_info.mark_unsafe_vars(unsafe_var_marker, &mut code);
        self.compile_cleanup(&mut code, &conjunct_info, clauses.last().unwrap_or(p1));

        Ok(code)
    }

    fn mark_unsafe_fact_vars(&self, fact: &mut CompiledFact) -> UnsafeVarMarker {
        let mut safe_vars = IndexSet::new();

        for fact_instr in fact.iter_mut() {
            match fact_instr {
                &mut FactInstruction::UnifyValue(r) => {
                    if !safe_vars.contains(&r) {
                        *fact_instr = FactInstruction::UnifyLocalValue(r);
                        safe_vars.insert(r);
                    }
                }
                &mut FactInstruction::UnifyVariable(r) => {
                    safe_vars.insert(r);
                }
                _ => {}
            }
        }

        UnsafeVarMarker::from_safe_vars(safe_vars)
    }

    pub fn compile_fact<'b: 'a>(&mut self, term: &'b Term) -> Code {
        self.update_var_count(post_order_iter(term));

        let mut vs = VariableFixtures::new();
        vs.mark_vars_in_chunk(post_order_iter(term), term.arity(), GenContext::Head);

        vs.populate_restricting_sets();
        self.marker.drain_var_data(vs, 1);

        let mut code = Vec::new();

        if let &Term::Clause(_, _, ref args, _) = term {
            self.marker.reset_at_head(args);

            let iter = FactInstruction::iter(term);
            let mut compiled_fact = self.compile_target(iter, GenContext::Head, false);

            self.mark_unsafe_fact_vars(&mut compiled_fact);

            if !compiled_fact.is_empty() {
                for fact_instr in compiled_fact {
                    code.push(Line::Fact(fact_instr));
                }
            }
        }

        code.push(proceed!());
        code
    }

    fn compile_query_line(
        &mut self,
        term: &'a QueryTerm,
        term_loc: GenContext,
        code: &mut Code,
        num_perm_vars_left: usize,
        is_exposed: bool,
    ) {
        self.marker.reset_arg(term.arity());

        let iter = query_term_post_order_iter(term);
        let query = self.compile_target(iter, term_loc, is_exposed);

        if !query.is_empty() {
            for query_instr in query {
                code.push(Line::Query(query_instr));
            }
        }

        self.add_conditional_call(code, term, num_perm_vars_left);
    }

    /*
        pub fn compile_query(&mut self, query: &'a Vec<QueryTerm>) -> Result<Code, CompilationError> {
            let iter = ChunkedIterator::from_term_sequence(query);
            let conjunct_info = self.collect_var_data(iter);

            let mut code = Vec::new();
            self.compile_seq_prelude(&conjunct_info, &mut code);

            let iter = ChunkedIterator::from_term_sequence(query);
            self.compile_seq(iter, &conjunct_info, &mut code, true)?;

            conjunct_info.mark_unsafe_vars(UnsafeVarMarker::new(), &mut code);

            if let Some(query_term) = query.last() {
                Self::compile_cleanup(&mut code, &conjunct_info, query_term);
            }

            Ok(code)
        }
    */

    #[inline]
    fn increment_jmp_by_locs_by(&mut self, incr: usize) {
        let offset = self.global_jmp_by_locs_offset;

        for loc in &mut self.jmp_by_locs[offset..] {
            *loc += incr;
        }
    }

    /// Returns the index of the first instantiated argument.
    fn first_instantiated_index(clauses: &[PredicateClause]) -> Option<usize> {
        let mut optimal_index = None;
        let has_args = match clauses.first() {
            Some(clause) => match clause.args() {
                Some(args) => !args.is_empty(),
                None => false,
            },
            None => false,
        };
        if !has_args {
            return optimal_index;
        }
        for clause in clauses.iter() {
            let args = clause.args().unwrap();
            for (i, arg) in args.iter().enumerate() {
                if let Some(optimal_index) = optimal_index {
                    if i >= optimal_index {
                        break;
                    }
                }
                match **arg {
                    Term::AnonVar | Term::Var(..) => (),
                    _ => {
                        match optimal_index {
                            Some(ref mut optimal_i) => *optimal_i = i,
                            None => optimal_index = Some(i),
                        }
                        break;
                    }
                }
            }
        }

        optimal_index
    }

    fn split_predicate(clauses: &[PredicateClause], optimal_index: usize) -> Vec<(usize, usize)> {
        let mut subseqs = Vec::new();
        let mut left_index = 0;

        if clauses.first().unwrap().args().is_some() {
            for (right_index, clause) in clauses.iter().enumerate() {
                // Can unwrap safely.
                if let Some(arg) = clause.args().unwrap().iter().nth(optimal_index) {
                    match **arg {
                        Term::Var(..) | Term::AnonVar => {
                            if left_index < right_index {
                                subseqs.push((left_index, right_index));
                            }

                            subseqs.push((right_index, right_index + 1));
                            left_index = right_index + 1;
                        }
                        _ => (),
                    }
                }
            }
        }

        if left_index < clauses.len() {
            subseqs.push((left_index, clauses.len()));
        }

        subseqs
    }

    fn compile_pred_subseq<'b: 'a>(
        &mut self,
        clauses: &'b [PredicateClause],
        optimal_index: usize,
    ) -> Result<Code, CompilationError> {
        let mut code = VecDeque::new();
        let mut code_offsets = CodeOffsets::new(self.atom_tbl.clone(), optimal_index + 1);
        let mut skip_stub_try_me_else = false;

        let jmp_by_locs_len = self.jmp_by_locs.len();

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_index_info = ClauseIndexInfo::new(code.len());
            self.global_jmp_by_locs_offset = self.jmp_by_locs.len();

            let clause_code = match clause {
                &PredicateClause::Fact(ref fact, ..) => self.compile_fact(fact),
                &PredicateClause::Rule(ref rule, ..) => self.compile_rule(rule)?,
            };

            if clauses.len() > 1 {
                let choice = match i {
                    0 => ChoiceInstruction::TryMeElse(clause_code.len() + 1),
                    _ if i == clauses.len() - 1 => trust_me(self.non_counted_bt),
                    _ => retry_me_else(clause_code.len() + 1, self.non_counted_bt),
                };

                code.push_back(Line::Choice(choice));
            } else if self.is_extensible {
                /*
                   generate stub choice instructions for extensible
                   predicates. if predicates are added to either the
                   inner or outer thread of choice instructions,
                   these stubs will be used, and surrounding indexing
                   instructions modified accordingly.

                   until then, the v offset of SwitchOnTerm will skip
                   over them.
                */

                code.push_front(Line::Choice(ChoiceInstruction::TryMeElse(0)));
                skip_stub_try_me_else = true;
            }

            let arg = match clause.args() {
                Some(args) => match args.iter().nth(optimal_index) {
                    Some(term) => Some(term),
                    None => None,
                },
                None => None,
            };

            if let Some(arg) = arg {
                let index = code.len();
                code_offsets.index_term(arg, index, &mut clause_index_info);
            }

            if !skip_stub_try_me_else {
                self.increment_jmp_by_locs_by(code.len());
            }

            self.skeleton.clauses.push_back(clause_index_info);
            code.extend(clause_code.into_iter());
        }

        let index_code = code_offsets.compute_indices(skip_stub_try_me_else);
        self.global_jmp_by_locs_offset = jmp_by_locs_len;

        if !index_code.is_empty() {
            code.push_front(Line::IndexingCode(index_code));

            if skip_stub_try_me_else {
                // skip the TryMeElse(0) also.
                self.increment_jmp_by_locs_by(2);
            } else {
                self.increment_jmp_by_locs_by(1);
            }
        } else if skip_stub_try_me_else {
            // remove the TryMeElse(0).
            code.pop_front();
        }

        Ok(Vec::from(code))
    }

    pub fn compile_predicate<'b: 'a>(
        &mut self,
        clauses: &'b Vec<PredicateClause>,
    ) -> Result<Code, CompilationError> {
        let mut code = Code::new();

        let optimal_index = match Self::first_instantiated_index(&clauses) {
            Some(index) => index,
            None => 0, // Default to first argument indexing.
        };

        let split_pred = Self::split_predicate(&clauses, optimal_index);
        let multi_seq = split_pred.len() > 1;

        for (l, r) in split_pred {
            let skel_lower_bound = self.skeleton.clauses.len();
            let code_segment = self.compile_pred_subseq(&clauses[l..r], optimal_index)?;
            let clause_start_offset = code.len();

            if multi_seq {
                let choice = match l {
                    0 => ChoiceInstruction::TryMeElse(code_segment.len() + 1),
                    _ if r == clauses.len() => trust_me(self.non_counted_bt),
                    _ => retry_me_else(code_segment.len() + 1, self.non_counted_bt),
                };

                code.push(Line::Choice(choice));
            } else if self.is_extensible {
                code.push(Line::Choice(ChoiceInstruction::TryMeElse(0)));
            }

            if self.is_extensible {
                let segment_is_indexed = to_indexing_line(&code_segment[0]).is_some();

                for clause_index_info in self.skeleton.clauses[skel_lower_bound..].iter_mut() {
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
