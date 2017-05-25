use prolog::allocator::*;
use prolog::ast::*;
use prolog::fixtures::*;
use prolog::indexing::*;
use prolog::iterators::*;
use prolog::targets::*;

use std::collections::HashMap;
use std::vec::Vec;

pub struct CodeGenerator<'a, TermMarker> {
    marker: TermMarker,
    var_count: HashMap<&'a Var, usize>
}

pub enum EvalSession<'a> {
    EntryFailure,
    EntrySuccess,
    InitialQuerySuccess(AllocVarDict<'a>, HeapVarDict<'a>),
    QueryFailure,
    SubsequentQuerySuccess,
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

    fn update_var_count<Iter>(&mut self, iter: Iter)
        where Iter: Iterator<Item=TermRef<'a>>
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
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _) => {
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
            ClauseType::Deep(lvl, cell, atom) => {
                self.marker.mark_non_var(lvl, term_loc, cell, target);
                target.push(Target::to_structure(lvl, atom.clone(), terms.len(), cell.get()));

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

    fn collect_var_data(&mut self, iter: ChunkedIterator<'a>) -> (VariableFixtures<'a>, bool)
    {
        let mut vs = VariableFixtures::new();
        let has_deep_cut = iter.contains_deep_cut();
        let has_head = iter.at_head();

        for (chunk_num, (last_term_arity, terms)) in iter.enumerate() {
            for (i, term_or_cut_ref) in terms.iter().enumerate() {
                let term_loc = if chunk_num == 0 && i == 0 && has_head {
                    GenContext::Head
                } else if i < terms.len() - 1 {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                self.update_var_count(term_or_cut_ref.post_order_iter());
                vs.mark_vars_in_chunk(term_or_cut_ref.post_order_iter(),
                                      last_term_arity,
                                      chunk_num,
                                      term_loc);
            }
        }

        vs.populate_restricting_sets();
        vs.set_perm_vals(has_deep_cut);

        (vs, has_deep_cut)
    }

    fn add_conditional_call(compiled_query: &mut Code, qt: QueryTermRef, pvs: usize)
    {
        match qt {
            QueryTermRef::CallN(terms) => {
                let call = ControlInstruction::CallN(terms.len());
                compiled_query.push(Line::Control(call));
            },
            QueryTermRef::Term(&Term::Constant(_, Constant::Atom(ref atom))) => {
                let call = ControlInstruction::Call(atom.clone(), 0, pvs);
                compiled_query.push(Line::Control(call));
            },
            QueryTermRef::Term(&Term::Clause(_, ref atom, ref terms)) => {
                let call = ControlInstruction::Call(atom.clone(), terms.len(), pvs);
                compiled_query.push(Line::Control(call));
            },
            _ => {}
        }
    }

    fn lco(body: &mut Code, toc: &QueryTerm) -> usize
    {
        let last_arity = toc.arity();
        let mut dealloc_index = body.len() - 1;

        match toc {
            &QueryTerm::Term(Term::Clause(_, ref name, _))
          | &QueryTerm::Term(Term::Constant(_, Constant::Atom(ref name))) =>
                if let &mut Line::Control(ref mut ctrl) = body.last_mut().unwrap() {
                    *ctrl = ControlInstruction::Execute(name.clone(), last_arity);
                },
            &QueryTerm::CallN(ref terms) =>
                if let &mut Line::Control(ref mut ctrl) = body.last_mut().unwrap() {
                    *ctrl = ControlInstruction::ExecuteN(terms.len());
                },
            _ => dealloc_index = body.len()
            
        };

        dealloc_index
    }

    fn compile_seq(&mut self,
                   clauses: &'a [QueryTerm],
                   vs: &VariableFixtures<'a>,
                   body: &mut Code,
                   is_exposed: bool)
    {
        let iter = ChunkedIterator::from_term_sequence(clauses);

        for (chunk_num, (_, terms)) in iter.enumerate() {
            self.marker.reset_contents();

            for (i, term) in terms.iter().enumerate() {
                let term_loc = if i + 1 < terms.len() {
                    GenContext::Mid(chunk_num)
                } else {
                    GenContext::Last(chunk_num)
                };

                let mut body_appendage = match term {
                    &QueryTermRef::Cut if i + 1 < terms.len() =>
                        vec![Line::Cut(CutInstruction::Cut(Terminal::Non))],
                    &QueryTermRef::Cut =>
                        vec![Line::Cut(CutInstruction::Cut(Terminal::Terminal))],
                    _ => {
                        let num_vars = vs.vars_above_threshold(i + 1);
                        self.compile_query_line(*term, term_loc, num_vars, is_exposed)
                    }
                };

                body.append(&mut body_appendage);
            }
        }
    }

    fn compile_seq_prelude(&mut self,
                           num_clauses: usize,
                           vs: &VariableFixtures<'a>,
                           deep_cuts: bool,
                           body: &mut Code)
                           -> usize
    {
        let perm_vars = vs.vars_above_threshold(0) + deep_cuts as usize;

        if num_clauses > 0 {
            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

            if deep_cuts {
                body.push(Line::Cut(CutInstruction::GetLevel));
            }
        }

        perm_vars
    }

    fn compile_neck_cut_or(&mut self,
                           p1: &'a QueryTerm,
                           body: &mut Code,
                           perm_vars: usize,
                           is_exposed: bool,
                           at_end: bool)
    {
        match p1 {
            &QueryTerm::Cut => {
                let term = if at_end {
                    Terminal::Terminal
                } else {
                    Terminal::Non
                };

                body.push(Line::Cut(CutInstruction::NeckCut(term)));
            },
            _ => {
                let p1 = p1.to_ref();

                self.marker.advance(GenContext::Head, p1);

                let term_loc = if p1.is_callable() {
                    GenContext::Last(0)
                } else {
                    GenContext::Mid(0)
                };

                let iter = p1.post_order_iter();
                body.push(Line::Query(self.compile_target(iter, term_loc, is_exposed)));

                Self::add_conditional_call(body, p1, perm_vars);
            }
        };
    }

    fn compile_cleanup(body: &mut Code, num_clauses: usize, toc: &QueryTerm)
    {
        let dealloc_index = Self::lco(body, toc);

        if num_clauses > 0 {
            body.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }
    }

    pub fn compile_rule<'b: 'a>(&mut self, rule: &'b Rule) -> Code
    {
        let iter = ChunkedIterator::from_rule(rule);
        let (mut vs, deep_cuts) = self.collect_var_data(iter);
        vs = self.marker.drain_var_data(vs);

        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let mut code = Vec::new();

        self.marker.advance(GenContext::Head, QueryTermRef::Term(p0));

        let perm_vars = self.compile_seq_prelude(clauses.len(), &vs, deep_cuts, &mut code);

        if p0.is_clause() {
            let iter = FactInstruction::iter(p0);
            code.push(Line::Fact(self.compile_target(iter, GenContext::Head, false)));
        }

        self.compile_neck_cut_or(p1, &mut code, perm_vars, false, clauses.len() == 0);
        self.compile_seq(clauses, &vs, &mut code, false);

        if perm_vars > 0 {
            let index = if let &Line::Control(_) = code.last().unwrap() {
                code.len() - 2
            } else {
                code.len() - 1
            };

            if let &mut Line::Query(ref mut query) = &mut code[index] {
                vs.mark_unsafe_vars_in_rule(p0, query);
            }
        }

        Self::compile_cleanup(&mut code, clauses.len(), clauses.last().unwrap_or(p1));

        code
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
        let iter = ChunkedIterator::from_term(term, true);
        let (vs, _) = self.collect_var_data(iter);
        self.marker.drain_var_data(vs);

        self.marker.advance(GenContext::Head, QueryTermRef::Term(term));

        let mut code = Vec::new();

        if term.is_clause() {
            let iter = FactInstruction::iter(term);
            let mut compiled_fact = self.compile_target(iter, GenContext::Head, false);

            self.mark_unsafe_fact_vars(&mut compiled_fact);
            code.push(Line::Fact(compiled_fact));
        }

        let proceed = Line::Control(ControlInstruction::Proceed);

        code.push(proceed);
        code
    }

    fn compile_query_line(&mut self,
                          term: QueryTermRef<'a>,
                          term_loc: GenContext,
                          index: usize,
                          is_exposed: bool)
                          -> Code
    {
        self.marker.advance(term_loc, term);

        let mut code = Vec::new();

        let iter = term.post_order_iter();
        let compiled_query = Line::Query(self.compile_target(iter, term_loc, is_exposed));

        code.push(compiled_query);

        Self::add_conditional_call(&mut code, term, index);

        code
    }

    pub fn compile_query(&mut self, query: &'a Vec<QueryTerm>) -> Code
    {
        let iter = ChunkedIterator::from_term_sequence(query);
        let (mut vs, deep_cuts) = self.collect_var_data(iter);
        let p1 = query.first().unwrap();

        vs = self.marker.drain_var_data(vs);

        let mut code  = Vec::new();
        let perm_vars = self.compile_seq_prelude(query.len() - 1,
                                                 &vs,
                                                 deep_cuts,
                                                 &mut code);

        self.compile_neck_cut_or(p1, &mut code, perm_vars, true, query.len() == 1);
        self.compile_seq(&query[1 .. ], &vs, &mut code, true);

        if perm_vars > 0 {
            let index = if let &Line::Control(_) = code.last().unwrap() {
                code.len() - 2
            } else {
                code.len() - 1
            };

            if let &mut Line::Query(ref mut query) = &mut code[index] {
                vs.mark_unsafe_vars_in_query(query);
            }
        }

        Self::compile_cleanup(&mut code, query.len() - 1, query.last().unwrap());

        code
    }

    fn split_predicate(clauses: &Vec<PredicateClause>) -> Vec<(usize, usize)>
    {
        let mut subseqs = Vec::new();
        let mut left_index = 0;

        for (right_index, clause) in clauses.iter().enumerate() {
            if let Some(&Term::Var(_, _)) = clause.first_arg() {
                if left_index < right_index {
                    subseqs.push((left_index, right_index));
                }

                subseqs.push((right_index, right_index + 1));
                left_index = right_index + 1;
            }
        }

        if left_index < clauses.len() {
            subseqs.push((left_index, clauses.len()));
        }

        subseqs
    }

    fn compile_pred_subseq<'b: 'a>(&mut self, clauses: &'b [PredicateClause]) -> Code
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
                    self.compile_rule(rule)
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
        code
    }

    pub fn compile_predicate<'b: 'a>(&mut self, clauses: &'b Vec<PredicateClause>) -> Code
    {
        let mut code   = Vec::new();
        let split_pred = Self::split_predicate(&clauses);
        let multi_seq  = split_pred.len() > 1;

        for (l, r) in split_pred {
            let mut code_segment = self.compile_pred_subseq(&clauses[l .. r]);

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

        code
    }
}
