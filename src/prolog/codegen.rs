use prolog::allocator::*;
use prolog::arithmetic::*;
use prolog::ast::*;
use prolog::fixtures::*;
use prolog::indexing::*;
use prolog::iterators::*;
use prolog::targets::*;

use std::cell::Cell;
use std::collections::{HashMap};
use std::rc::Rc;
use std::vec::Vec;

pub struct CodeGenerator<TermMarker> {
    marker: TermMarker,
    var_count: HashMap<Rc<Var>, usize>
}

pub struct ConjunctInfo<'a> {
    pub perm_vs: VariableFixtures<'a>,
    pub num_of_chunks: usize,
    pub has_deep_cut: bool
}

impl<'a> ConjunctInfo<'a>
{
    fn new(perm_vs: VariableFixtures<'a>, num_of_chunks: usize, has_deep_cut: bool) -> Self {
        ConjunctInfo { perm_vs, num_of_chunks, has_deep_cut }
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

impl<'a, TermMarker: Allocator<'a>> CodeGenerator<TermMarker>
{
    pub fn new() -> Self {
        CodeGenerator { marker:  Allocator::new(),
                        var_count: HashMap::new() }
    }

    pub fn take_vars(self) -> AllocVarDict {
        self.marker.take_bindings()
    }

    fn update_var_count<Iter: Iterator<Item=TermRef<'a>>>(&mut self, iter: Iter)
    {
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

    fn mark_non_callable(&mut self, name: Rc<Atom>, arity: usize, term_loc: GenContext,
                         vr: &'a Cell<VarReg>, code: &mut Code)
                         -> RegType
    {
        match self.marker.bindings().get(&name) {
            Some(&VarData::Temp(_, t, _)) if t != 0 => RegType::Temp(t),
            Some(&VarData::Perm(p)) if p != 0 => RegType::Perm(p),
            _ => {
                let mut target = Vec::new();

                self.marker.reset_arg(arity);
                self.marker.mark_var(name, Level::Shallow, vr, term_loc, &mut target);

                if !target.is_empty() {
                    code.push(Line::Query(target));
                }

                vr.get().norm()
            }
        }
    }

    fn add_or_increment_void_instr<Target>(target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        if let Some(ref mut instr) = target.last_mut() {
            if Target::is_void_instr(&*instr) {
                Target::incr_void_instr(instr);
                return;
            }
        }

        target.push(Target::to_void(1));
    }

    fn subterm_to_instr<Target>(&mut self,
                                subterm: &'a Term,
                                term_loc: GenContext,
                                is_exposed: bool,
                                target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        match subterm {
            &Term::AnonVar if is_exposed =>
                self.marker.mark_anon_var(Level::Deep, target),
            &Term::AnonVar =>
                Self::add_or_increment_void_instr(target),
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _, _) => {
                self.marker.mark_non_var(Level::Deep, term_loc, cell, target);
                target.push(Target::clause_arg_to_instr(cell.get()));
            },
            &Term::Constant(_, ref constant) =>
                target.push(Target::constant_subterm(constant.clone())),
            &Term::Var(ref cell, ref var) =>
                if is_exposed || self.get_var_count(var) > 1 {
                    self.marker.mark_var(var.clone(), Level::Deep, cell, term_loc, target);
                } else {
                    Self::add_or_increment_void_instr(target);
                }
        };
    }

    fn compile_target<Target, Iter>(&mut self, iter: Iter, term_loc: GenContext, is_exposed: bool)
                                    -> Vec<Target>
        where Target: CompilationTarget<'a>, Iter: Iterator<Item=TermRef<'a>>
    {
        let mut target = Vec::new();

        for term in iter {
            match term {
                TermRef::Clause(lvl, cell, ct, terms) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_structure(ct, terms.len(), cell.get()));

                    for subterm in terms {
                        self.subterm_to_instr(subterm.as_ref(), term_loc, is_exposed, &mut target);
                    }
                },
                TermRef::Cons(lvl, cell, head, tail) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_list(lvl, cell.get()));

                    self.subterm_to_instr(head, term_loc, is_exposed, &mut target);
                    self.subterm_to_instr(tail, term_loc, is_exposed, &mut target);
                },
                TermRef::Constant(lvl @ Level::Shallow, cell, constant) => {
                    self.marker.mark_non_var(lvl, term_loc, cell, &mut target);
                    target.push(Target::to_constant(lvl, constant.clone(), cell.get()));
                },
                TermRef::AnonVar(lvl @ Level::Shallow) =>
                    if let GenContext::Head = term_loc {
                        self.marker.advance_arg();
                    } else {
                        self.marker.mark_anon_var(lvl, &mut target);
                    },
                TermRef::Var(lvl @ Level::Shallow, cell, ref var) if var.as_str() == "!" => {
                    if self.marker.is_unbound(var.clone()) {
                        if term_loc != GenContext::Head {
                            self.marker.mark_reserved_var(var.clone(), lvl, cell, term_loc,
                                                          &mut target, perm_v!(1), false);
                            continue;
                        }
                    }

                    self.marker.mark_var(var.clone(), lvl, cell, term_loc, &mut target);
                },
                TermRef::Var(lvl @ Level::Shallow, cell, var) =>
                    self.marker.mark_var(var.clone(), lvl, cell, term_loc, &mut target),
                _ => {}
            };
        }

        target
    }

    fn collect_var_data(&mut self, mut iter: ChunkedIterator<'a>) -> ConjunctInfo<'a>
    {
        let mut vs = VariableFixtures::new();

        while let Some((chunk_num, lt_arity, chunked_terms)) = iter.next() {
            for (i, chunked_term) in chunked_terms.iter().enumerate() {
                let term_loc = match chunked_term {
                    &ChunkedTerm::HeadClause(..) => GenContext::Head,
                    &ChunkedTerm::BodyTerm(_) => if i < chunked_terms.len() - 1 {
                        GenContext::Mid(chunk_num)
                    } else {
                        GenContext::Last(chunk_num)
                    }
                };
                
                self.update_var_count(chunked_term.post_order_iter());
                vs.mark_vars_in_chunk(chunked_term.post_order_iter(), lt_arity, term_loc);
            }
        }

        let num_of_chunks = iter.chunk_num;
        let has_deep_cut  = iter.encountered_deep_cut();

        vs.populate_restricting_sets();
        vs.set_perm_vals(has_deep_cut);

        let vs = self.marker.drain_var_data(vs);

        ConjunctInfo::new(vs, num_of_chunks, has_deep_cut)
    }

    fn add_conditional_call(code: &mut Code, qt: &QueryTerm, pvs: usize)
    {
        match qt {
            &QueryTerm::Jump(ref vars) =>
                code.push(jmp_call!(vars.len(), 0, pvs)),
            &QueryTerm::Clause(_, ref ct, ref terms) =>
                code.push(call_clause!(ct.clone(), terms.len(), pvs)),
            _ => {}
        }
    }

    fn lco(code: &mut Code) -> usize
    {
        let mut dealloc_index = code.len() - 1;

        match code.last_mut() {
            Some(&mut Line::Control(ref mut ctrl)) =>
                match ctrl.clone() {
                    ControlInstruction::CallClause(ct, arity, pvs, false) =>
                        *ctrl = ControlInstruction::CallClause(ct, arity, pvs, true),
                    ControlInstruction::Goto(p, arity, false) =>
                        *ctrl = ControlInstruction::Goto(p, arity, true),
                    ControlInstruction::JmpBy(arity, offset, pvs, false) =>
                        *ctrl = ControlInstruction::JmpBy(arity, offset, pvs, true),
                    ControlInstruction::IsClause(false, r, at) =>
                        *ctrl = ControlInstruction::IsClause(true, r, at),
                    ControlInstruction::Proceed => {},
                    _ => dealloc_index += 1 // = code.len()
                },
            Some(&mut Line::Cut(CutInstruction::Cut(_))) =>
                dealloc_index += 1,
            _ => {}
        };

        dealloc_index
    }

    fn compile_inlined(&mut self, ct: InlinedClauseType, terms: &'a Vec<Box<Term>>,
                       term_loc: GenContext, code: &mut Code)
                       -> Result<(), ParserError>
    {
        match ct {
            InlinedClauseType::CompareNumber(cmp, ..) => {
                let (mut lcode, at_1) = self.call_arith_eval(terms[0].as_ref(), 1)?;
                let (mut rcode, at_2) = self.call_arith_eval(terms[1].as_ref(), 2)?;

                code.append(&mut lcode);
                code.append(&mut rcode);
                
                code.push(compare_number_instr!(cmp,
                                                at_1.unwrap_or(interm!(1)),
                                                at_2.unwrap_or(interm!(2))));
            },
            InlinedClauseType::IsAtom(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Atom(_)) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_atom!(r));
                    }
                    _ => {
                        code.push(fail!());
                    }
                },
            InlinedClauseType::IsAtomic(..) =>
                match terms[0].as_ref() {
                    &Term::AnonVar | &Term::Clause(..) | &Term::Cons(..) => {
                        code.push(fail!());
                    },
                    &Term::Constant(..) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_atomic!(r));
                    }
                },
            InlinedClauseType::IsCompound(..) =>
                match terms[0].as_ref() {
                    &Term::Clause(..) | &Term::Cons(..) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_compound!(r));
                    },
                    _ => {
                        code.push(fail!());
                    }
                },
            InlinedClauseType::IsRational(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Number(Number::Rational(_))) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_rational!(r));
                    },
                    _ => {
                        code.push(fail!());
                    }
                },
            InlinedClauseType::IsFloat(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Number(Number::Float(_))) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_float!(r));
                    },
                    _ => {
                        code.push(fail!());
                    }
                },
            InlinedClauseType::IsString(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::String(_)) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_string!(r));
                    },
                    _ => {
                        code.push(fail!());
                    }
                },
            InlinedClauseType::IsNonVar(..) =>
                match terms[0].as_ref() {
                    &Term::AnonVar => {
                        code.push(fail!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_nonvar!(r));
                    },
                    _ => {
                        code.push(succeed!());
                    }
                },
            InlinedClauseType::IsInteger(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(_, Constant::Number(Number::Integer(_))) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_integer!(r));
                    },
                    _ => {
                        code.push(fail!());
                    },
                },
            InlinedClauseType::IsVar(..) =>
                match terms[0].as_ref() {
                    &Term::Constant(..) | &Term::Clause(..) | &Term::Cons(..) => {
                        code.push(fail!());
                    },
                    &Term::AnonVar => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name.clone(), 1, term_loc, vr, code);
                        code.push(is_var!(r));
                    }
                }
        }

        Ok(())
    }

    fn call_arith_eval(&self, term: &'a Term, target_int: usize) -> Result<ArithCont, ArithmeticError>
    {
        let mut evaluator = ArithmeticEvaluator::new(self.marker.bindings(), target_int);
        evaluator.eval(term)
    }

    fn compile_seq(&mut self, iter: ChunkedIterator<'a>, conjunct_info: &ConjunctInfo<'a>,
                   code: &mut Code, is_exposed: bool)
                   -> Result<(), ParserError>
    {
        for (chunk_num, _, terms) in iter.rule_body_iter()
        {
            for (i, term) in terms.iter().enumerate()
            {
                let term_loc = if i + 1 < terms.len() {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                match *term {
                    &QueryTerm::UnblockedCut(ref cell) =>
                        code.push(set_cp!(cell.get().norm())),
                    &QueryTerm::BlockedCut =>
                        code.push(if chunk_num == 0 {
                            Line::Cut(CutInstruction::NeckCut)
                        } else {
                            Line::Cut(CutInstruction::Cut(perm_v!(1)))
                        }),
                    &QueryTerm::Clause(_, ClauseType::BuiltIn(BuiltInClauseType::Is), ref terms) =>
                    {
                        let (mut acode, at) = self.call_arith_eval(terms[1].as_ref(), 1)?;
                        code.append(&mut acode);

                        match terms[0].as_ref() {
                            &Term::Var(ref vr, ref name) => {
                                let mut target = Vec::new();

                                self.marker.reset_arg(2);
                                self.marker.mark_var(name.clone(), Level::Shallow, vr,
                                                     term_loc, &mut target);

                                if !target.is_empty() {
                                    code.push(Line::Query(target));
                                }

                                code.push(is_call!(temp_v!(1), at.unwrap_or(interm!(1))));
                            },
                            &Term::Constant(_, ref c @ Constant::Number(_)) => {
                                code.push(query![put_constant!(Level::Shallow,
                                                               c.clone(),
                                                               temp_v!(1))]);
                                code.push(is_call!(temp_v!(1), at.unwrap_or(interm!(1))));
                            },
                            _ => {
                                code.push(fail!());
                            }
                        }
                    },
                    &QueryTerm::Clause(_, ClauseType::Inlined(ct), ref terms) =>
                        try!(self.compile_inlined(ct, terms, term_loc, code)),
                    _ => {
                        let num_perm_vars = if chunk_num == 0 {
                            conjunct_info.perm_vars()
                        } else {
                            conjunct_info.perm_vs.vars_above_threshold(i + 1)
                        };

                        self.compile_query_line(term, term_loc, code, num_perm_vars, is_exposed);
                    },
                };
            }

            self.marker.reset_contents();
        }

        Ok(())
    }

    fn compile_seq_prelude(&mut self, conjunct_info: &ConjunctInfo, body: &mut Code)
    {
        if conjunct_info.allocates() {
            let perm_vars = conjunct_info.perm_vars();

            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

            if conjunct_info.has_deep_cut {
                body.push(Line::Cut(CutInstruction::GetLevel(perm_v!(1))));
            }
        }
    }

    fn compile_cleanup(code: &mut Code, conjunct_info: &ConjunctInfo, toc: &'a QueryTerm)
    {
        // add a proceed to bookend any trailing cuts.
        match toc {
            &QueryTerm::BlockedCut | &QueryTerm::UnblockedCut(..) => code.push(proceed!()),
            _ => {}
        };

        // perform lco.
        let dealloc_index = Self::lco(code);

        if conjunct_info.allocates() {
            code.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }
    }

    pub fn compile_rule<'b: 'a>(&mut self, rule: &'b Rule) -> Result<Code, ParserError>
    {
        let iter = ChunkedIterator::from_rule(rule);
        let conjunct_info = self.collect_var_data(iter);

        let &Rule { head: (_, ref args, ref p1), ref clauses } = rule;
        let mut code = Vec::new();

        self.marker.reset_at_head(args);
        self.compile_seq_prelude(&conjunct_info, &mut code);

        let iter = FactIterator::from_rule_head_clause(args);
        let fact = self.compile_target(iter, GenContext::Head, false);

        if !fact.is_empty() {
            code.push(Line::Fact(fact));
        }

        let iter = ChunkedIterator::from_rule_body(p1, clauses);
        try!(self.compile_seq(iter, &conjunct_info, &mut code, false));

        if conjunct_info.allocates() {
            let index = if let &Line::Control(_) = code.last().unwrap() {
                code.len() - 2
            } else {
                code.len() - 1
            };

            if let &mut Line::Query(ref mut query) = &mut code[index] {
                let head_iter = FactIterator::from_rule_head_clause(args);
                conjunct_info.perm_vs.mark_unsafe_vars_in_rule(head_iter, query);
            }
        }

        Self::compile_cleanup(&mut code, &conjunct_info, clauses.last().unwrap_or(p1));
        Ok(code)
    }

    fn mark_unsafe_fact_vars(&self, fact: &mut CompiledFact)
    {
        let mut unsafe_vars = HashMap::new();

        for var_status in self.marker.bindings().values() {
            unsafe_vars.insert(var_status.as_reg_type(), false);
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

    pub fn compile_fact<'b: 'a>(&mut self, term: &'b Term) -> Code
    {
        self.update_var_count(term.post_order_iter());

        let mut vs = VariableFixtures::new();
        vs.mark_vars_in_chunk(term.post_order_iter(), term.arity(), GenContext::Head);

        vs.populate_restricting_sets();
        self.marker.drain_var_data(vs);

        let mut code = Vec::new();

        if let &Term::Clause(_, _, ref args, _) = term {
            self.marker.reset_at_head(args);

            let iter = FactInstruction::iter(term);
            let mut compiled_fact = self.compile_target(iter, GenContext::Head, false);

            self.mark_unsafe_fact_vars(&mut compiled_fact);

            if !compiled_fact.is_empty() {
                code.push(Line::Fact(compiled_fact));
            }
        }

        code.push(proceed!());
        code
    }

    fn compile_query_line(&mut self, term: &'a QueryTerm, term_loc: GenContext,
                          code: &mut Code, num_perm_vars_left: usize, is_exposed: bool)
    {
        self.marker.reset_arg(term.arity());

        let iter  = term.post_order_iter();
        let query = self.compile_target(iter, term_loc, is_exposed);

        if !query.is_empty() {
            code.push(Line::Query(query));
        }

        Self::add_conditional_call(code, term, num_perm_vars_left);
    }

    pub fn compile_query(&mut self, query: &'a Vec<QueryTerm>) -> Result<Code, ParserError>
    {
        let iter = ChunkedIterator::from_term_sequence(query);
        let conjunct_info = self.collect_var_data(iter);

        let mut code = Vec::new();
        self.compile_seq_prelude(&conjunct_info, &mut code);

        let iter = ChunkedIterator::from_term_sequence(query);
        try!(self.compile_seq(iter, &conjunct_info, &mut code, true));

        if conjunct_info.allocates() {
            let index = if let &Line::Control(_) = code.last().unwrap() {
                code.len() - 2
            } else {
                code.len() - 1
            };

            if let &mut Line::Query(ref mut query) = &mut code[index] {
                conjunct_info.perm_vs.mark_unsafe_vars_in_query(query);
            }
        }

        if let Some(query_term) = query.last() {
            Self::compile_cleanup(&mut code, &conjunct_info, query_term);
        }

        Ok(code)
    }

    fn split_predicate(clauses: &Vec<PredicateClause>) -> Vec<(usize, usize)>
    {
        let mut subseqs = Vec::new();
        let mut left_index = 0;

        for (right_index, clause) in clauses.iter().enumerate() {
            match clause.first_arg() {
                Some(&Term::Var(_, _)) | Some(&Term::AnonVar) => {
                    if left_index < right_index {
                        subseqs.push((left_index, right_index));
                    }

                    subseqs.push((right_index, right_index + 1));
                    left_index = right_index + 1;
                },
                _ => {}
            }
        }

        if left_index < clauses.len() {
            subseqs.push((left_index, clauses.len()));
        }

        subseqs
    }

    fn compile_pred_subseq<'b: 'a>(&mut self, clauses: &'b [PredicateClause])
                                   -> Result<Code, ParserError>
    {
        let mut code_body = Vec::new();
        let mut code_offsets = CodeOffsets::new();

        let num_clauses  = clauses.len();

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_code = match clause {
                &PredicateClause::Fact(ref fact) =>
                    self.compile_fact(fact),
                &PredicateClause::Rule(ref rule) =>
                    try!(self.compile_rule(rule))
            };

            if num_clauses > 1 {
                let choice = match i {
                    0 => ChoiceInstruction::TryMeElse(clause_code.len() + 1),
                    _ if i == num_clauses - 1 => ChoiceInstruction::TrustMe,
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
        Ok(code)
    }

    pub fn compile_predicate<'b: 'a>(&mut self, clauses: &'b Vec<PredicateClause>)
                                     -> Result<Code, ParserError>
    {
        let mut code   = Vec::new();
        let split_pred = Self::split_predicate(&clauses);
        let multi_seq  = split_pred.len() > 1;

        for (l, r) in split_pred {
            let mut code_segment = try!(self.compile_pred_subseq(&clauses[l .. r]));

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

        Ok(code)
    }
}
