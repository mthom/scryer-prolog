use prolog::ast::*;
use prolog::fixtures::*;
use prolog::indexing::*;
use prolog::iterators::*;
use prolog::naive_allocator::*;
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
        let mut var_count = HashMap::new();

        for term in iter {
            if let TermRef::Var(_, _, var) = term {
                if self.marker.contains_var(var) {
                    var_count.insert(var, 2);
                    continue;
                }

                let entry = var_count.entry(var).or_insert(0);
                *entry += 1;
            }
        }

        self.var_count = var_count;
    }

    fn all_singleton_vars(&self, terms: &Vec<Box<Term>>) -> bool
    {
        for term in terms {
            match term.as_ref() {
                &Term::AnonVar => {},
                &Term::Var(ref cell, ref var) if cell.get().is_temp() =>
                    if self.var_count.get(var).unwrap() != &1 {
                        return false;
                    },
                _ => return false
            }
        }

        true
    }

    fn void_subterms<Target>(subterms: usize) -> Target
        where Target: CompilationTarget<'a>
    {
        Target::to_void(subterms)
    }

    fn to_structure<Target>(&mut self,
                            lvl: Level,
                            cell: &'a Cell<RegType>,
                            name: &'a Atom,
                            arity: usize)
                            -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_structure(lvl, name.clone(), arity, cell.get())
    }

    fn to_constant<Target>(&mut self,
                           lvl: Level,
                           cell: &'a Cell<RegType>,
                           constant: &'a Constant)
                           -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_constant(lvl, constant.clone(), cell.get())
    }

    fn to_list<Target>(&mut self, lvl: Level, cell: &'a Cell<RegType>) -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(lvl, cell);
        Target::to_list(lvl, cell.get())
    }

    fn constant_subterm<Target>(&mut self, constant: &'a Constant) -> Target
        where Target: CompilationTarget<'a>
    {
        Target::constant_subterm(constant.clone())
    }

    fn anon_var_term<Target>(&mut self, lvl: Level, target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        let reg = self.marker.mark_anon_var(lvl);

        let instr = match reg {
            VarReg::ArgAndNorm(arg, norm) =>
                Target::argument_to_variable(arg, norm),
            VarReg::Norm(norm) =>
                Target::subterm_to_variable(norm)
        };

        target.push(instr);
    }

    fn var_term<Target>(&mut self,
                        lvl: Level,
                        cell: &'a Cell<VarReg>,
                        var: &'a Var,
                        _: GenContext,
                        target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        if !self.marker.marked_var(var) {
            let reg = self.marker.mark_new_var(lvl, var, cell.get().norm());
            cell.set(reg);

            match reg {
                VarReg::ArgAndNorm(arg, norm) => // if arg.reg_num() != norm =>
                    target.push(Target::argument_to_variable(arg, norm)),
                VarReg::Norm(norm) =>
                    target.push(Target::subterm_to_variable(norm)),
            };
        } else {
            let reg = self.marker.mark_old_var(lvl, var);
            cell.set(reg);

            match reg {
                VarReg::ArgAndNorm(arg, norm) => // if arg.reg_num() != norm =>
                    target.push(Target::argument_to_value(arg, norm)),
                VarReg::Norm(norm) =>
                    target.push(Target::subterm_to_value(norm)),
            };
        }
    }

    fn non_var_subterm<Target>(&mut self, cell: &'a Cell<RegType>) -> Target
        where Target: CompilationTarget<'a>
    {
        self.marker.mark_non_var(Level::Deep, cell);
        Target::clause_arg_to_instr(cell.get())
    }

    fn subterm_to_instr<Target>(&mut self,
                                subterm: &'a Term,
                                term_loc: GenContext,
                                target: &mut Vec<Target>)
        where Target: CompilationTarget<'a>
    {
        match subterm {
            &Term::AnonVar =>
                self.anon_var_term(Level::Deep, target),
            &Term::Cons(ref cell, _, _) | &Term::Clause(ref cell, _, _) =>
                target.push(self.non_var_subterm(cell)),
            &Term::Constant(_, ref constant) =>
                target.push(self.constant_subterm(constant)),
            &Term::Var(ref cell, ref var) =>
                self.var_term(Level::Deep, cell, var, term_loc, target)
        };
    }

    fn compile_target<Target>(&mut self,
                              term: &'a Term,
                              term_loc: GenContext,
                              has_exposed_vars: bool)
                              -> Vec<Target>
        where Target: CompilationTarget<'a>
    {
        let iter       = Target::iter(term);
        let mut target = Vec::<Target>::new();

        for term in iter {
            match term {
                TermRef::Clause(lvl, cell, atom, terms) => {
                    target.push(self.to_structure(lvl, cell, atom, terms.len()));

                    if !has_exposed_vars {
                        if self.all_singleton_vars(terms) {
                            target.push(Self::void_subterms(terms.len()));
                            continue;
                        }
                    }

                    for subterm in terms {
                        self.subterm_to_instr(subterm.as_ref(), term_loc, &mut target);
                    }
                },
                TermRef::Cons(lvl, cell, head, tail) => {
                    target.push(self.to_list(lvl, cell));

                    self.subterm_to_instr(head, term_loc, &mut target);
                    self.subterm_to_instr(tail, term_loc, &mut target);
                },
                TermRef::Constant(lvl @ Level::Shallow, cell, constant) =>
                    target.push(self.to_constant(lvl, cell, constant)),
                TermRef::AnonVar(lvl @ Level::Shallow) =>
                    if has_exposed_vars {
                        self.anon_var_term(lvl, &mut target);
                    } else {
                        self.marker.advance_arg();
                    },
                TermRef::Var(lvl @ Level::Shallow, ref cell, ref var) =>
                    self.var_term(lvl, cell, var, term_loc, &mut target),
                _ => {}
            };
        }

        target
    }

    fn collect_var_data(iter: ChunkedIterator<'a>) -> (VariableFixtures, bool)
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
                    &TermOrCutRef::Term(term) =>
                        vs.mark_vars_in_chunk(term, last_term_arity, chunk_num, term_loc),
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
        let (mut vs, deep_cuts) = Self::collect_var_data(iter);
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

        match p1 {
            &TermOrCut::Cut => {
                let iter = p0.breadth_first_iter();
                self.update_var_count(iter);
            },
            &TermOrCut::Term(ref p1) => {
                let iter = p0.breadth_first_iter().chain(p1.breadth_first_iter());
                self.update_var_count(iter);
            }
        };

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
                self.marker.advance_at_head(p1);

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
        let (vs, _) = Self::collect_var_data(iter);
        self.marker.drain_var_data(vs);

        self.update_var_count(term.breadth_first_iter());
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
        self.update_var_count(term.breadth_first_iter());

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
        let (vs, _) = Self::collect_var_data(iter);

        self.marker.drain_var_data(vs);

        self.marker.advance(term);
        self.update_var_count(term.breadth_first_iter());

        let mut code = Vec::new();

        if term.is_clause() {
            let compiled_query = self.compile_target(term, GenContext::Last(0), false);
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
