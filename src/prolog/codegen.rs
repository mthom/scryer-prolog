use prolog::ast::*;
use prolog::debray_allocator::*;
use prolog::fixtures::*;
use prolog::indexing::*;
use prolog::iterators::*;
use prolog::targets::*;

use std::cell::Cell;
use std::collections::HashMap;
use std::vec::Vec;

pub struct CodeGenerator<'a> {
    marker: TermMarker<'a>,
    var_count: HashMap<&'a Var, usize>
}

impl<'a> CodeGenerator<'a> {
    pub fn new() -> Self {
        CodeGenerator { marker: TermMarker::new(),
                        var_count: HashMap::new() }
    }

    pub fn vars(&self) -> &HashMap<&Var, VarData> {
        &self.marker.bindings
    }

    fn update_var_count<Iter>(&mut self, iter: Iter)
        where Iter : Iterator<Item=TermRef<'a>>
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

    fn to_structure<Target>(&mut self,
                            lvl: Level,
                            cell: &'a Cell<RegType>,
                            term_loc: GenContext,
                            name: &'a Atom,
                            arity: usize,
                            target: &mut Vec<Target>)
                            -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, term_loc, cell, target);
        Target::to_structure(lvl, name.clone(), arity, cell.get())
    }

    fn to_constant<Target>(&mut self,
                           lvl: Level,
                           cell: &'a Cell<RegType>,
                           term_loc: GenContext,
                           constant: &'a Constant,
                           target: &mut Vec<Target>)
                           -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, term_loc, cell, target);
        Target::to_constant(lvl, constant.clone(), cell.get())
    }

    fn to_list<Target>(&mut self,
                       lvl: Level,
                       term_loc: GenContext,
                       cell: &'a Cell<RegType>,
                       target: &mut Vec<Target>)
                       -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, term_loc, cell, target);
        Target::to_list(lvl, cell.get())
    }

    fn constant_subterm<Target>(&mut self, constant: &'a Constant) -> Target
        where Target: CompilationTarget<'a>
    {
        Target::constant_subterm(constant.clone())
    }

    fn non_var_subterm<Target>(&mut self,
                               lvl: Level,
                               term_loc: GenContext,
                               cell: &'a Cell<RegType>,
                               target: &mut Vec<Target>)
                               -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, term_loc, cell, target);
        Target::clause_arg_to_instr(cell.get())
    }

    fn flatten_void_instrs<Target>(target: Vec<Target>) -> Vec<Target>
        where Target: CompilationTarget<'a>
    {
        let mut compressed_target = Vec::new();
        let mut void_count = 0;

        for term in target.into_iter() {
            if Target::is_void_instr(&term) {
                void_count += 1;
            } else {
                if void_count > 0 {
                    compressed_target.push(Target::to_void(void_count));
                    void_count = 0;
                }

                compressed_target.push(term);
            }
        }

        if void_count > 0 {
            compressed_target.push(Target::to_void(void_count));
        }

        compressed_target
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
                target.push(Target::to_void(1)),
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _) => {
                let instr = self.non_var_subterm(Level::Deep, term_loc, cell, target);
                target.push(instr);
            },
            &Term::Constant(_, ref constant) =>
                target.push(self.constant_subterm(constant)),
            &Term::Var(ref cell, ref var) =>
                if is_exposed || self.get_var_count(var) > 1 {
                    self.marker.mark_var(var, Level::Deep, cell, term_loc, target);
                } else {
                    target.push(Target::to_void(1));
                }
        };
    }

    fn compile_target<Target>(&mut self, term: &'a Term, term_loc: GenContext, is_exposed: bool)
                              -> Vec<Target>
        where Target: CompilationTarget<'a>
    {
        let iter       = Target::iter(term);
        let mut target = Vec::<Target>::new();

        for term in iter {
            match term {
                TermRef::Clause(lvl, cell, atom, terms) => {
                    let str_instr = self.to_structure(lvl,
                                                      cell,
                                                      term_loc,
                                                      atom,
                                                      terms.len(),
                                                      &mut target);

                    target.push(str_instr);

                    for subterm in terms {
                        self.subterm_to_instr(subterm.as_ref(), term_loc, is_exposed, &mut target);
                    }
                },
                TermRef::Cons(lvl, cell, head, tail) => {
                    let list_instr = self.to_list(lvl, term_loc, cell, &mut target);
                    target.push(list_instr);

                    self.subterm_to_instr(head, term_loc, is_exposed, &mut target);
                    self.subterm_to_instr(tail, term_loc, is_exposed, &mut target);
                },
                TermRef::Constant(lvl @ Level::Shallow, cell, constant) => {
                    let const_instr = self.to_constant(lvl, cell, term_loc, constant, &mut target);
                    target.push(const_instr);
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

        Self::flatten_void_instrs(target)
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

                match term_or_cut_ref {
                    &TermOrCutRef::Term(term) => {
                        self.update_var_count(term.breadth_first_iter());
                        vs.mark_vars_in_chunk(term, last_term_arity, chunk_num, term_loc);
                    },
                    _ => {}
                };
            }
        }

        vs.populate_restricting_sets();
        vs.set_perm_vals(has_deep_cut);

        (vs, has_deep_cut)
    }

    fn add_conditional_call(compiled_query: &mut Code, term: &Term, pvs: usize)
    {
        match term {
            &Term::Constant(_, Constant::Atom(ref atom)) => {
                let call = ControlInstruction::Call(atom.clone(), 0, pvs);
                compiled_query.push(Line::Control(call));
            },
            &Term::Clause(_, ref atom, ref terms) => {
                let call = ControlInstruction::Call(atom.clone(), terms.len(), pvs);
                compiled_query.push(Line::Control(call));
            },
            _ => {}
        }
    }

    fn lco(body: &mut Code, rule: &'a Rule) -> usize
    {
        let last_arity = rule.last_clause().arity();
        let mut dealloc_index = body.len() - 1;

        match rule.last_clause() {
              &TermOrCut::Term(Term::Clause(_, ref name, _))
            | &TermOrCut::Term(Term::Constant(_, Constant::Atom(ref name))) => {
                if let &mut Line::Control(ref mut ctrl) = body.last_mut().unwrap() {
                    *ctrl = ControlInstruction::Execute(name.clone(), last_arity);
                }
            },
            _ => dealloc_index = body.len()
        };

        dealloc_index
    }

    pub fn compile_rule(&mut self, rule: &'a Rule) -> Code
    {
        let iter = ChunkedIterator::from_rule(rule);
        let (mut vs, deep_cuts) = self.collect_var_data(iter);
        vs = self.marker.drain_var_data(vs);

        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;

        self.marker.advance(p0);

        let perm_vars = vs.vars_above_threshold(0) + deep_cuts as usize;
        let mut body  = Vec::new();

        if clauses.len() > 0 {
            body.push(Line::Control(ControlInstruction::Allocate(perm_vars)));

            if deep_cuts {
                body.push(Line::Cut(CutInstruction::GetLevel));
            }
        }

        if p0.is_clause() {
            body.push(Line::Fact(self.compile_target(p0, GenContext::Head, false)));
        }

        match p1 {
            &TermOrCut::Cut => {
                let term = if clauses.is_empty() {
                    Terminal::Terminal
                } else {
                    Terminal::Non
                };

                body.push(Line::Cut(CutInstruction::NeckCut(term)));
            },
            &TermOrCut::Term(ref p1) => {
                self.marker.advance(p1);

                if p1.is_clause() {
                    let term_loc = if p1.is_callable() {
                        GenContext::Last(0)
                    } else {
                        GenContext::Mid(0)
                    };

                    body.push(Line::Query(self.compile_target(p1, term_loc, false)));
                }

                Self::add_conditional_call(&mut body, p1, perm_vars);
            }
        };

        let iter = ChunkedIterator::from_term_sequence(clauses);

        for (chunk_num, (_, terms)) in iter.enumerate() {
            self.marker.reset_contents();

            for (i, term) in terms.iter().enumerate() {
                let mut body_appendage = match term {
                    &TermOrCutRef::Cut if i + 1 < terms.len() =>
                        vec![Line::Cut(CutInstruction::Cut(Terminal::Non))],
                    &TermOrCutRef::Cut =>
                        vec![Line::Cut(CutInstruction::Cut(Terminal::Terminal))],
                    &TermOrCutRef::Term(term) if i + 1 < terms.len() => {
                        let num_vars = vs.vars_above_threshold(i + 1);
                        self.compile_internal_query(term, GenContext::Mid(chunk_num), num_vars)
                    },
                    &TermOrCutRef::Term(term) => {
                        let num_vars = vs.vars_above_threshold(i + 1);
                        self.compile_internal_query(term, GenContext::Last(chunk_num), num_vars)
                    }
                };

                body.append(&mut body_appendage);
            }
        }

        if clauses.len() > 0 {
            let mut index = body.len() - 1;

            if let &Line::Control(_) = body.last().unwrap() {
                index -= 1;
            }

            if let &mut Line::Query(ref mut query) = &mut body[index] {
                vs.mark_unsafe_query_vars(p0, query);
            }
        }

        let dealloc_index = Self::lco(&mut body, &rule);

        if clauses.len() > 0 {
            body.insert(dealloc_index, Line::Control(ControlInstruction::Deallocate));
        }

        body
    }

    fn mark_unsafe_fact_vars(&self, fact: &mut CompiledFact)
    {
        let mut unsafe_vars = HashMap::new();

        for var_status in self.marker.bindings.values() {
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

    pub fn compile_fact(&mut self, term: &'a Term) -> Code
    {
        let iter = ChunkedIterator::from_term(term, true);
        let (vs, _) = self.collect_var_data(iter);
        self.marker.drain_var_data(vs);

        self.marker.advance(term);

        let mut code = Vec::new();

        if term.is_clause() {
            let mut compiled_fact = self.compile_target(term, GenContext::Head, false);
            self.mark_unsafe_fact_vars(&mut compiled_fact);
            code.push(Line::Fact(compiled_fact));
        }

        let proceed = Line::Control(ControlInstruction::Proceed);

        code.push(proceed);
        code
    }

    fn compile_internal_query(&mut self, term: &'a Term, term_loc: GenContext, index: usize) -> Code
    {
        self.marker.advance(term);

        let mut code = Vec::new();

        if term.is_clause() {
            let compiled_query = Line::Query(self.compile_target(term, term_loc, false));
            code.push(compiled_query);
        }

        Self::add_conditional_call(&mut code, term, index);

        code
    }

    pub fn compile_query(&mut self, term: &'a Term) -> Code
    {
        let iter = ChunkedIterator::from_term(term, true);
        let (vs, _) = self.collect_var_data(iter);

        self.marker.drain_var_data(vs);
        self.marker.advance(term);

        let mut code = Vec::new();

        if term.is_clause() {
            let compiled_query = self.compile_target(term, GenContext::Last(0), true);
            code.push(Line::Query(compiled_query));
        }

        Self::add_conditional_call(&mut code, term, 0);

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

    fn compile_pred_subseq(&mut self, clauses: &'a [PredicateClause]) -> Code
    {
        let mut code_body = Vec::new();
        let mut code_offsets = CodeOffsets::new();

        let multi_clause = clauses.len() > 1;

        for (i, clause) in clauses.iter().enumerate() {
            self.marker.reset();

            let mut clause_code = match clause {
                &PredicateClause::Fact(ref fact) =>
                    self.compile_fact(fact),
                &PredicateClause::Rule(ref rule) =>
                    self.compile_rule(rule)
            };

            if multi_clause {
                let choice = match i {
                    0 => ChoiceInstruction::TryMeElse(clause_code.len() + 1),
                    _ if i == clauses.len() - 1 => ChoiceInstruction::TrustMe,
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

    pub fn compile_predicate(&mut self, clauses: &'a Vec<PredicateClause>) -> Code
    {
        let mut code   = Vec::new();
        let split_pred = Self::split_predicate(clauses);
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
