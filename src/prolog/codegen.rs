use prolog::allocator::*;
use prolog::arithmetic::*;
use prolog::ast::*;
use prolog::fixtures::*;
use prolog::indexing::*;
use prolog::iterators::*;
use prolog::targets::*;

use std::cell::Cell;
use std::collections::HashMap;
use std::mem::swap;
use std::vec::Vec;

pub struct CodeGenerator<'a, TermMarker> {
    marker: TermMarker,
    var_count: HashMap<&'a Var, usize>
}

pub enum EvalSession<'a> {
    OpIsInfixAndPostFix,
    NamelessEntry,
    ParserError(ParserError),
    ImpermissibleEntry(String),
    EntrySuccess,
    InitialQuerySuccess(AllocVarDict<'a>, HeapVarDict<'a>),
    QueryFailure,
    QueryFailureWithException(String),
    SubsequentQuerySuccess,
}

pub struct ConjunctInfo<'a> {
    pub perm_vs: VariableFixtures<'a>,
    pub num_of_chunks: usize,
    pub has_deep_cut: bool
}

impl<'a> ConjunctInfo<'a>
{
    fn new(perm_vs: VariableFixtures<'a>, num_of_chunks: usize, has_deep_cut: bool) -> Self
    {
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

impl<'a, TermMarker: Allocator<'a>> CodeGenerator<'a, TermMarker>
{
    pub fn new() -> Self {
        CodeGenerator { marker:  Allocator::new(),
                        var_count: HashMap::new() }
    }

    pub fn take_vars(self) -> AllocVarDict<'a> {
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

    fn mark_non_callable(&mut self,
                         name: &'a Atom,
                         arity: usize,
                         term_loc: GenContext,
                         vr: &'a Cell<VarReg>,
                         code: &mut Code)
                         -> RegType
    {
        match self.marker.bindings().get(name) {
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
                    self.marker.mark_var(var, Level::Deep, cell, term_loc, target);
                } else {
                    Self::add_or_increment_void_instr(target);
                }
        };
    }

    fn compile_clause<Target>(&mut self,
                              ct: ClauseType<'a>,
                              term_loc: GenContext,
                              is_exposed: bool,
                              terms: &'a Vec<Box<Term>>,
                              target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        match ct {
            ClauseType::Deep(lvl, cell, atom, fixity) => {
                self.marker.mark_non_var(lvl, term_loc, cell, target);
                target.push(Target::to_structure(lvl, atom.clone(), terms.len(),
                                                 cell.get(), fixity));

                for subterm in terms {
                    self.subterm_to_instr(subterm.as_ref(), term_loc, is_exposed, target);
                }
            },
            _ => {}
        }
    }

    fn compile_target<Target, Iter>(&mut self, iter: Iter, term_loc: GenContext, is_exposed: bool)
                                    -> Vec<Target>
        where Target: CompilationTarget<'a>, Iter: Iterator<Item=TermRef<'a>>
    {
        let mut target = Vec::new();

        for term in iter {
            match term {
                TermRef::Clause(ct, terms) =>
                    self.compile_clause(ct, term_loc, is_exposed, terms, &mut target),
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
                TermRef::Var(lvl @ Level::Shallow, ref cell, ref var) =>
                    self.marker.mark_var(var, lvl, cell, term_loc, &mut target),
                _ => {}
            };
        }

        target
    }

    fn collect_var_data(&mut self, mut iter: ChunkedIterator<'a>) -> ConjunctInfo<'a>
    {
        let mut vs = VariableFixtures::new();
        let at_rule_head = iter.at_rule_head();

        while let Some((chunk_num, lt_arity, terms)) = iter.next() {
            for (i, query_term) in terms.iter().enumerate() {
                let term_loc = if chunk_num == 0 && i == 0 && at_rule_head {
                    GenContext::Head
                } else if i < terms.len() - 1 {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                self.update_var_count(query_term.post_order_iter());
                vs.mark_vars_in_chunk(query_term.post_order_iter(), lt_arity, term_loc);
            }
        }

        let num_of_chunks = iter.chunk_num();
        let has_deep_cut  = iter.encountered_deep_cut();

        vs.populate_restricting_sets();
        vs.set_perm_vals(has_deep_cut);

        let vs = self.marker.drain_var_data(vs);

        ConjunctInfo::new(vs, num_of_chunks, has_deep_cut)
    }

    fn add_conditional_call(code: &mut Code, qt: &QueryTerm, pvs: usize)
    {
        match qt {
            &QueryTerm::Arg(_) => {
                let call = ControlInstruction::ArgCall;
                code.push(Line::Control(call));
            },
            &QueryTerm::CallN(ref terms) => {
                let call = ControlInstruction::CallN(terms.len());
                code.push(Line::Control(call));
            },
            &QueryTerm::Catch(_) =>
                code.push(Line::Control(ControlInstruction::CatchCall)),
            &QueryTerm::Display(_) =>
                code.push(Line::Control(ControlInstruction::DisplayCall)),
            &QueryTerm::DuplicateTerm(_) =>
                code.push(Line::Control(ControlInstruction::DuplicateTermCall)),
            &QueryTerm::Functor(_) =>
                code.push(Line::Control(ControlInstruction::FunctorCall)),            
            &QueryTerm::Inlined(_) =>
                code.push(proceed!()),
            &QueryTerm::Term(Term::Constant(_, Constant::Atom(ref atom))) => {
                let call = ControlInstruction::Call(atom.clone(), 0, pvs);
                code.push(Line::Control(call));
            },
            &QueryTerm::Term(Term::Clause(_, ref atom, ref terms, _)) => {
                let call = ControlInstruction::Call(atom.clone(), terms.len(), pvs);
                code.push(Line::Control(call));
            },
            &QueryTerm::Throw(_) =>
                code.push(Line::Control(ControlInstruction::ThrowCall)),
            _ => {}
        }
    }

    fn lco(code: &mut Code) -> usize
    {
        let mut dealloc_index = code.len() - 1;

        match code.last_mut() {
            Some(&mut Line::Control(ref mut ctrl)) => {
                let mut instr = ControlInstruction::Proceed;
                swap(ctrl, &mut instr);

                match instr {
                    ControlInstruction::ArgCall =>
                        *ctrl = ControlInstruction::ArgExecute,
                    ControlInstruction::Call(name, arity, _) =>
                        *ctrl = ControlInstruction::Execute(name, arity),
                    ControlInstruction::CallN(arity) =>
                        *ctrl = ControlInstruction::ExecuteN(arity),
                    ControlInstruction::DisplayCall =>
                        *ctrl = ControlInstruction::DisplayExecute,
                    ControlInstruction::DuplicateTermCall =>
                        *ctrl = ControlInstruction::DuplicateTermExecute,
                    ControlInstruction::FunctorCall =>
                        *ctrl = ControlInstruction::FunctorExecute,
                    ControlInstruction::CatchCall =>
                        *ctrl = ControlInstruction::CatchExecute,
                    ControlInstruction::ThrowCall =>
                        *ctrl = ControlInstruction::ThrowExecute,
                    ControlInstruction::IsCall(r, at) =>
                        *ctrl = ControlInstruction::IsExecute(r, at),
                    ControlInstruction::Proceed => {},
                    _ => dealloc_index += 1 // = code.len()
                }
            },
            Some(&mut Line::Cut(CutInstruction::Cut)) =>
                dealloc_index += 1,
            _ => {}
        };

        dealloc_index
    }

    fn compile_inlined(&mut self, term: &'a InlinedQueryTerm, term_loc: GenContext, code: &mut Code)
                       -> Result<(), ParserError>
    {
        match term {
            &InlinedQueryTerm::CompareNumber(cmp, ref terms) => {
                let (mut lcode, at_1) = self.call_arith_eval(terms[0].as_ref(), 1)?;
                let (mut rcode, at_2) = self.call_arith_eval(terms[1].as_ref(), 2)?;

                code.append(&mut lcode);
                code.append(&mut rcode);

                code.push(compare_number_instr!(cmp,
                                                at_1.unwrap_or(interm!(1)),
                                                at_2.unwrap_or(interm!(2))));
            },            
            &InlinedQueryTerm::IsAtomic(ref inner_term) =>
                match inner_term[0].as_ref() {
                    &Term::AnonVar | &Term::Clause(..) | &Term::Cons(..) => {
                        code.push(fail!());
                    },
                    &Term::Constant(..) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name, 1, term_loc, vr, code);
                        code.push(is_atomic!(r));
                    }
                },
            &InlinedQueryTerm::IsInteger(ref inner_term) =>
                match inner_term[0].as_ref() {                    
                    &Term::Constant(_, Constant::Number(Number::Integer(_))) => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name, 1, term_loc, vr, code);
                        code.push(is_integer!(r));
                    },
                    _ => {
                        code.push(fail!());
                    },
                },
            &InlinedQueryTerm::IsVar(ref inner_term) =>
                match inner_term[0].as_ref() {
                    &Term::Constant(..) | &Term::Clause(..) | &Term::Cons(..) => {
                        code.push(fail!());
                    },
                    &Term::AnonVar => {
                        code.push(succeed!());
                    },
                    &Term::Var(ref vr, ref name) => {
                        let r = self.mark_non_callable(name, 1, term_loc, vr, code);
                        code.push(is_var!(r));
                    }
                }        
        }

        Ok(())
    }

    fn call_arith_eval(&self, term: &'a Term, target_int: usize)
                       -> Result<ArithCont, ArithmeticError>
    {
        let mut evaluator = ArithmeticEvaluator::new(self.marker.bindings(), target_int);
        evaluator.eval(term)
    }

    fn compile_seq(&mut self,
                   iter: ChunkedIterator<'a>,
                   conjunct_info: &ConjunctInfo<'a>,
                   code: &mut Code,
                   is_exposed: bool)
                   -> Result<(), ParserError>
    {
        for (chunk_num, _, terms) in iter {
            for (i, term) in terms.iter().enumerate()
            {
                let term_loc = if i + 1 < terms.len() {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                match *term {
                    &QueryTerm::Cut => {
                        code.push(if chunk_num == 0 {
                            Line::Cut(CutInstruction::NeckCut)
                        } else {
                            Line::Cut(CutInstruction::Cut)
                        });
                    },
                    &QueryTerm::Is(ref terms) => {
                        let (mut acode, at) = self.call_arith_eval(terms[1].as_ref(), 1)?;
                        code.append(&mut acode);

                        match terms[0].as_ref() {
                            &Term::Var(ref vr, ref name) => {
                                let r = self.mark_non_callable(name,
                                                               2,
                                                               term_loc,
                                                               vr,
                                                               code);

                                code.push(is_call!(r, at.unwrap_or(interm!(1))));
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
                    &QueryTerm::Inlined(ref term) =>
                        self.compile_inlined(term, term_loc, code)?,
                    _ if chunk_num == 0 => {
                        self.marker.reset_arg(term.arity());

                        let iter = term.post_order_iter();
                        let query = self.compile_target(iter, term_loc, is_exposed);

                        if !query.is_empty() {
                            code.push(Line::Query(query));
                        }

                        Self::add_conditional_call(code, term, conjunct_info.perm_vars());
                    },
                    _ => {
                        let num_vars = conjunct_info.perm_vs.vars_above_threshold(i + 1);
                        self.compile_query_line(term, term_loc, code, num_vars, is_exposed);
                    },
                };

                self.marker.reset_contents();
            }
        }

        Ok(())
    }

    fn compile_seq_prelude(&mut self, conjunct_info: &ConjunctInfo, body: &mut Code)
    {
        if conjunct_info.allocates() {
            let perm_vars = conjunct_info.perm_vars();

            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

            if conjunct_info.has_deep_cut {
                body.push(Line::Cut(CutInstruction::GetLevel));
            }
        }
    }

    fn compile_cleanup(code: &mut Code, conjunct_info: &ConjunctInfo, toc: &'a QueryTerm)
    {
        match toc {
            &QueryTerm::Inlined(_) | &QueryTerm::Cut =>
                code.push(proceed!()),
            _ => {}
        };

        let dealloc_index = Self::lco(code);

        if conjunct_info.allocates() {
            code.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }
    }

    pub fn compile_rule<'b: 'a>(&mut self, rule: &'b Rule) -> Result<Code, ParserError>
    {
        let iter = ChunkedIterator::from_rule(rule);
        let conjunct_info = self.collect_var_data(iter);

        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let mut code = Vec::new();

        self.marker.reset_arg(p0.arity());
        self.compile_seq_prelude(&conjunct_info, &mut code);

        if let &QueryTerm::Term(ref term) = p0 {
            if let &Term::Clause(..) = term {
                let iter = FactInstruction::iter(term);
                let fact = self.compile_target(iter, GenContext::Head, false);

                if !fact.is_empty() {
                    code.push(Line::Fact(fact));
                }
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
                    conjunct_info.perm_vs.mark_unsafe_vars_in_rule(term, query);
                }
            }

            Self::compile_cleanup(&mut code, &conjunct_info, clauses.last().unwrap_or(p1));
            Ok(code)
        } else {
            Err(ParserError::InvalidRuleHead)
        }
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
        self.marker.reset_arg(term.arity());

        let mut code = Vec::new();

        if let &Term::Clause(..) = term {
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
                          code: &mut Code, index: usize, is_exposed: bool)
    {
        self.marker.reset_arg(term.arity());

        let iter = term.post_order_iter();
        let compiled_query = self.compile_target(iter, term_loc, is_exposed);

        if !compiled_query.is_empty() {
            code.push(Line::Query(compiled_query));
        }

        Self::add_conditional_call(code, term, index);
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
