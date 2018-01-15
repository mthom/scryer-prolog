use prolog::ast::*;
use prolog::builtins::*;
use prolog::codegen::*;
use prolog::heap_iter::*;
use prolog::heap_print::*;
use prolog::fixtures::*;

pub(crate) mod machine_state;

use std::collections::HashMap;
use std::ops::Index;
use std::rc::Rc;
use std::vec::Vec;

pub struct Machine {
    ms: machine_state::MachineState,
    code: Code,
    code_dir: CodeDir,
    op_dir: OpDir,
    cached_query: Option<Code>
}

impl Index<CodePtr> for Machine {
    type Output = Line;

    fn index(&self, ptr: CodePtr) -> &Self::Output {
        match ptr {
            CodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => panic!("Out-of-bounds top level index.")
                }
            },
            CodePtr::DirEntry(p) => &self.code[p]
        }
    }
}

impl Machine {
    pub fn new() -> Self {
        let (code, code_dir, op_dir) = build_code_dir();

        Machine {
            ms: machine_state::MachineState::new(),
            code: code,
            code_dir: code_dir,
            op_dir: op_dir,
            cached_query: None
        }
    }

    pub fn failed(&self) -> bool {
        self.ms.fail
    }

    fn add_user_code<'a>(&mut self, name: Rc<Atom>, arity: usize, offset: usize) -> EvalSession<'a>
    {
        match self.code_dir.get(&(name.clone(), arity)) {
            Some(&(PredicateKeyType::BuiltIn, _)) =>
                return EvalSession::ImpermissibleEntry(format!("{}/{}", name, arity)),
            _ => {}
        };

        self.code_dir.insert((name, arity), (PredicateKeyType::User, offset));
        EvalSession::EntrySuccess
    }

    pub fn add_fact<'a>(&mut self, fact: &Term, mut code: Code) -> EvalSession<'a>
    {
        match fact {
            &Term::Clause(_, ref name, ..) | &Term::Constant(_, Constant::Atom(ref name)) => {
                let p = self.code.len();
                let arity = fact.arity();

                self.code.append(&mut code);
                self.add_user_code(name.clone(), arity, p)
            },
            _ => EvalSession::NamelessEntry
        }
    }

    pub fn add_rule<'a>(&mut self, rule: &Rule, mut code: Code) -> EvalSession<'a>
    {
        match &rule.head.0 {
            &QueryTerm::Term(Term::Clause(_, ref name, ..))
          | &QueryTerm::Term(Term::Constant(_, Constant::Atom(ref name))) => {
                let p = self.code.len();
                let arity = rule.head.0.arity();

                self.code.append(&mut code);
                self.add_user_code(name.clone(), arity, p)
            },
            _ => EvalSession::NamelessEntry
        }
    }

    pub fn add_predicate<'a>(&mut self, clauses: &Vec<PredicateClause>, mut code: Code)
                             -> EvalSession<'a>
    {
        let p = self.code.len();

        if let Some(ref clause) = clauses.first() {
            if let Some(name) = clause.name() {
                let arity = clause.arity();

                self.code.append(&mut code);
                self.add_user_code(name.clone(), arity, p)
            } else {
                EvalSession::NamelessEntry
            }
        } else {
            EvalSession::ImpermissibleEntry(String::from("predicate must have clauses."))
        }
    }

    fn cached_query_size(&self) -> usize {
        match &self.cached_query {
            &Some(ref query) => query.len(),
            _ => 0
        }
    }

    fn execute_instr(&mut self)
    {
        let instr = match self.ms.p {
            CodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => return
                }
            },
            CodePtr::DirEntry(p) => &self.code[p]
        };

        match instr {
            &Line::Arithmetic(ref arith_instr) =>
                self.ms.execute_arith_instr(arith_instr),
            &Line::BuiltIn(ref built_in_instr) =>
                self.ms.execute_built_in_instr(&self.code_dir, built_in_instr),
            &Line::Choice(ref choice_instr) =>
                self.ms.execute_choice_instr(choice_instr),
            &Line::Cut(ref cut_instr) =>
                self.ms.execute_cut_instr(cut_instr),
            &Line::Control(ref control_instr) =>
                self.ms.execute_ctrl_instr(&self.code_dir, control_instr),
            &Line::Fact(ref fact) => {
                for fact_instr in fact {
                    if self.failed() {
                        break;
                    }

                    self.ms.execute_fact_instr(&fact_instr);
                }

                self.ms.p += 1;
            },
            &Line::Indexing(ref indexing_instr) =>
                self.ms.execute_indexing_instr(&indexing_instr),
            &Line::IndexedChoice(ref choice_instr) =>
                self.ms.execute_indexed_choice_instr(choice_instr),
            &Line::Query(ref query) => {
                for query_instr in query {
                    if self.failed() {
                        break;
                    }

                    self.ms.execute_query_instr(&query_instr);
                }

                self.ms.p += 1;
            }
        }
    }

    fn backtrack(&mut self)
    {
        if self.ms.b > 0 {
            let b = self.ms.b - 1;

            self.ms.b0 = self.ms.or_stack[b].b0;
            self.ms.p  = self.ms.or_stack[b].bp;

            if let CodePtr::TopLevel(_, p) = self.ms.p {
                self.ms.fail = p == 0;
            } else {
                self.ms.fail = false;
            }
        } else {
            self.ms.p = CodePtr::TopLevel(0, 0);
        }
    }

    fn query_stepper<'a>(&mut self)
    {
        loop
        {
            self.execute_instr();

            if self.failed() {
                self.backtrack();
            }

            match self.ms.p {
                CodePtr::DirEntry(p) if p < self.code.len() => {},
                _ => break
            };
        }
    }

    fn record_var_places<'a>(&self,
                             chunk_num: usize,
                             alloc_locs: &AllocVarDict<'a>,
                             heap_locs: &mut HeapVarDict<'a>)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(_) => {
                    let e = self.ms.e;

                    let r = var_data.as_reg_type().reg_num();
                    let addr = self.ms.and_stack[e][r].clone();

                    heap_locs.insert(var, addr);
                },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();
                    let addr = self.ms[r].clone();

                    heap_locs.insert(var, addr);
                },
                _ => {}
            }
        }
    }

    fn run_query<'a>(&mut self, alloc_locs: &AllocVarDict<'a>, heap_locs: &mut HeapVarDict<'a>)
    {
        let end_ptr = CodePtr::TopLevel(0, self.cached_query_size());

        while self.ms.p < end_ptr {
            if let CodePtr::TopLevel(mut cn, p) = self.ms.p {
                match &self[CodePtr::TopLevel(cn, p)] {
                    &Line::Control(ref ctrl_instr) if ctrl_instr.is_jump_instr() => {
                        self.record_var_places(cn, alloc_locs, heap_locs);
                        cn += 1;
                    },
                    _ => {}
                }

                self.ms.p = CodePtr::TopLevel(cn, p);
            }

            self.query_stepper();

            match self.ms.p {
                CodePtr::TopLevel(_, p) if p > 0 => {},
                _ => break
            };
        }
    }

    fn fail<'a>(&mut self) -> EvalSession<'a>
    {
        if self.ms.ball.1.len() > 0 {
            let h = self.ms.heap.h;
            self.ms.copy_and_align_ball_to_heap();

            EvalSession::QueryFailureWithException(self.print_term(&Addr::HeapCell(h)))
        } else {
            EvalSession::QueryFailure
        }
    }

    pub fn submit_decl<'a>(&mut self, decl: &Declaration) -> EvalSession<'a>
    {
        match decl {
            &Declaration::Op(prec, spec, ref name) => {
                if is_infix!(spec) {
                    match self.op_dir.get(&(name.clone(), Fixity::Post)) {
                        Some(_) => return EvalSession::OpIsInfixAndPostFix,
                        _ => {}
                    };
                }

                if is_postfix!(spec) {
                    match self.op_dir.get(&(name.clone(), Fixity::In)) {
                        Some(_) => return EvalSession::OpIsInfixAndPostFix,
                        _ => {}
                    };
                }

                if prec > 0 {
                    match spec {
                        XFY | XFX | YFX => self.op_dir.insert((name.clone(), Fixity::In),
                                                              (spec, prec)),
                        XF | YF => self.op_dir.insert((name.clone(), Fixity::Post), (spec, prec)),
                        FX | FY => self.op_dir.insert((name.clone(), Fixity::Pre), (spec,prec)),
                        _ => None
                    };
                } else {
                    self.op_dir.remove(&(name.clone(), Fixity::Pre));
                    self.op_dir.remove(&(name.clone(), Fixity::In));
                    self.op_dir.remove(&(name.clone(), Fixity::Post));
                }

                EvalSession::EntrySuccess
            }
        }
    }

    pub fn submit_query<'a>(&mut self, code: Code, alloc_locs: AllocVarDict<'a>) -> EvalSession<'a>
    {
        let mut heap_locs = HashMap::new();

        self.cached_query = Some(code);
        self.run_query(&alloc_locs, &mut heap_locs);

        if self.failed() {
            self.fail()
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    pub fn continue_query<'a>(&mut self, alloc_l: &AllocVarDict<'a>, heap_l: &mut HeapVarDict<'a>)
                              -> EvalSession<'a>
    {
        if !self.or_stack_is_empty() {
            let b = self.ms.b - 1;
            self.ms.p = self.ms.or_stack[b].bp;

            if let CodePtr::TopLevel(_, 0) = self.ms.p {
                return EvalSession::QueryFailure;
            }

            self.run_query(alloc_l, heap_l);

            if self.failed() {
                self.fail()
            } else {
                EvalSession::SubsequentQuerySuccess
            }
        } else {
            EvalSession::QueryFailure
        }
    }

    fn print_var(&self, r: Ref) -> String
    {
        let disp = TermFormatter {};
        let iter = HeapCellIterator::new(&self.ms, r);

        let mut printer = HeapCellPrinter::new(iter, disp);

        printer.print()
    }

    fn print_term(&self, addr: &Addr) -> String
    {
        match addr {
            &Addr::Con(ref c) =>
                format!("{}", c),
            &Addr::Lis(h) | &Addr::HeapCell(h) | &Addr::Str(h) =>
                self.print_var(Ref::HeapCell(h)),
            &Addr::StackCell(fr, sc) =>
                self.print_var(Ref::StackCell(fr, sc))
        }
    }

    pub fn heap_view(&self, var_dir: &HeapVarDict) -> String {
        let mut result = String::new();

        for (var, addr) in var_dir {
            if result != "" {
                result += "\n\r";
            }

            result += var.as_str();
            result += " = ";

            result += self.print_term(addr).as_str();
        }

        result
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.ms.b == 0
    }

    pub fn clear(&mut self) {
        self.reset();
        self.code.clear();
        self.code_dir.clear();
    }

    pub fn reset(&mut self) {
        self.ms.reset();
    }

    pub fn op_dir(&self) -> &OpDir {
        &self.op_dir
    }
}
