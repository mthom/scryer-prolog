use prolog::ast::*;
use prolog::builtins::*;
use prolog::heap_print::*;
use prolog::tabled_rc::*;

mod machine_errors;
pub(super) mod machine_state;
#[macro_use]
mod machine_state_impl;

use prolog::machine::machine_state::*;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::mem::swap;
use std::ops::Index;
use std::rc::Rc;

pub(super) struct MachineCodeIndex<'a> {
    pub(super) code_dir: &'a mut CodeDir,
    pub(super) op_dir: &'a mut OpDir,
}

pub struct Machine {
    ms: MachineState,
    call_policy: Box<CallPolicy>,
    cut_policy: Box<CutPolicy>,
    code: Code,
    pub(super) code_dir: CodeDir,
    pub(super) op_dir: OpDir,
    term_dir: TermDir,
    modules: HashMap<ClauseName, Module>,
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
            CodePtr::DirEntry(p, _) => &self.code[p]
        }
    }
}

impl<'a> SubModuleUser for MachineCodeIndex<'a> {
    fn op_dir(&mut self) -> &mut OpDir {
        self.op_dir
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: ModuleCodeIndex) {
        if let Some(ref mut code_idx) = self.code_dir.get_mut(&(name.clone(), arity)) {
            println!("warning: overwriting {}/{}", &name, arity);
            set_code_index!(code_idx, idx.0, idx.1);

            return;
        }

        self.code_dir.insert((name, arity), CodeIndex::from(idx));
    }
}

impl Machine {
    pub fn new() -> Self {
        let atom_tbl = Rc::new(RefCell::new(HashSet::new()));
        let (code, code_dir, op_dir) = default_build();

        Machine {
            ms: MachineState::new(atom_tbl),
            call_policy: Box::new(DefaultCallPolicy {}),
            cut_policy: Box::new(DefaultCutPolicy {}),
            code,
            code_dir,
            term_dir: TermDir::new(),
            op_dir,
            modules: HashMap::new(),
            cached_query: None
        }
    }

    fn remove_module(&mut self, module_name: ClauseName) {
        let iter = if let Some(submodule) = self.modules.get(&module_name) {
            submodule.module_decl.exports.iter().cloned()
        } else {
            return;
        };

        for (name, arity) in iter {
            let name = name.defrock_brackets();

            match self.code_dir.get(&(name.clone(), arity)).cloned() {
                Some(CodeIndex (ref code_idx)) => {
                    if &code_idx.borrow().1 != &module_name {
                        continue;
                    }

                    self.code_dir.remove(&(name.clone(), arity));

                    // remove or respecify ops.
                    if arity == 2 {
                        if let Some((_, _, mod_name)) = self.op_dir.get(&(name.clone(), Fixity::In)).cloned()
                        {
                            if mod_name == module_name {
                                self.op_dir.remove(&(name.clone(), Fixity::In));
                            }
                        }
                    } else if arity == 1 {
                        if let Some((_, _, mod_name)) = self.op_dir.get(&(name.clone(), Fixity::Pre)).cloned()
                        {
                            if mod_name == module_name {
                                self.op_dir.remove(&(name.clone(), Fixity::Pre));
                            }
                        }

                        if let Some((_, _, mod_name)) = self.op_dir.get(&(name.clone(), Fixity::Post)).cloned()
                        {
                            if mod_name == module_name {
                                self.op_dir.remove(&(name.clone(), Fixity::Post));
                            }
                        }
                    }
                },
                _ => {}
            };
        }
    }

    pub fn failed(&self) -> bool {
        self.ms.fail
    }

    pub fn atom_tbl(&self) -> TabledData<Atom> {
        self.ms.atom_tbl.clone()
    }

    pub fn use_qualified_module_in_toplevel(&mut self, name: ClauseName, exports: Vec<PredicateKey>)
                                            -> EvalSession
    {
        self.remove_module(name.clone());

        match self.modules.get_mut(&name) {
            Some(ref mut module) => {
                let mut indices = MachineCodeIndex { code_dir: &mut self.code_dir,
                                                     op_dir: &mut self.op_dir };

                indices.use_qualified_module(module, &exports)
            },
            None => EvalSession::from(SessionError::ModuleNotFound)
        }
    }

    pub fn use_module_in_toplevel(&mut self, name: ClauseName) -> EvalSession {
        self.remove_module(name.clone());

        match self.modules.get_mut(&name) {
            Some(ref mut module) => {
                let mut indices = MachineCodeIndex { code_dir: &mut self.code_dir,
                                                     op_dir: &mut self.op_dir };

                indices.use_module(module)
            },
            None => EvalSession::from(SessionError::ModuleNotFound)
        }
    }

    pub fn get_module(&self, name: ClauseName) -> Option<&Module> {
        self.modules.get(&name)
    }

    pub fn add_batched_code(&mut self, mut code: Code, code_dir: CodeDir) {
        self.code.append(&mut code);
        self.code_dir.extend(code_dir.into_iter());
    }

    pub fn add_batched_ops(&mut self, op_dir: OpDir) {
        self.op_dir.extend(op_dir.into_iter());
    }

    pub fn add_module(&mut self, module: Module, code: Code) {
        self.modules.insert(module.module_decl.name.clone(), module);
        self.code.extend(code.into_iter());
    }

    pub fn add_user_code(&mut self, name: ClauseName, arity: usize, code: Code, pred: Predicate)
                         -> EvalSession
    {
        match self.code_dir.get(&(name.clone(), arity)) {
            Some(&CodeIndex (ref idx)) if idx.borrow().1 != clause_name!("user") =>
                    return EvalSession::from(SessionError::ImpermissibleEntry(format!("{}/{}",
                                                                                   name,
                                                                                   arity))),
            _ => {}
        };

        let offset = self.code.len();

        self.code.extend(code.into_iter());
        self.term_dir.insert((name.clone(), arity), pred);

        let idx = self.code_dir.entry((name, arity))
            .or_insert(CodeIndex::from((offset, clause_name!("user"))));

        set_code_index!(idx, IndexPtr::Index(offset), clause_name!("user"));
        EvalSession::EntrySuccess
    }

    pub fn code_size(&self) -> usize {
        self.code.len()
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
            CodePtr::DirEntry(p, _) => &self.code[p]
        };

        match instr {
            &Line::Arithmetic(ref arith_instr) =>
                self.ms.execute_arith_instr(arith_instr),
            &Line::BuiltIn(ref built_in_instr) => {
                let code_dirs = CodeDirs::new(&self.code_dir, &self.modules);
                self.ms.execute_built_in_instr(code_dirs, &mut self.call_policy,
                                               &mut self.cut_policy, built_in_instr);
            },
            &Line::Choice(ref choice_instr) =>
                self.ms.execute_choice_instr(choice_instr, &mut self.call_policy),
            &Line::Cut(ref cut_instr) =>
                self.ms.execute_cut_instr(cut_instr, &mut self.cut_policy),
            &Line::Control(ref control_instr) => {
                let code_dirs = CodeDirs::new(&self.code_dir, &self.modules);
                self.ms.execute_ctrl_instr(code_dirs, &mut self.call_policy,
                                           &mut self.cut_policy, control_instr)
            },
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
                self.ms.execute_indexed_choice_instr(choice_instr, &mut self.call_policy),
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
            self.ms.p  = self.ms.or_stack[b].bp.clone();

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
        loop {
            self.execute_instr();

            if self.failed() {
                self.backtrack();
            }

            match self.ms.p {
                CodePtr::DirEntry(p, _) if p < self.code.len() => {},
                _ => break
            };
        }
    }

    fn record_var_places(&self, chunk_num: usize, alloc_locs: &AllocVarDict,
                         heap_locs: &mut HeapVarDict)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(p) if p > 0 => {
                    let e = self.ms.e;
                    let r = var_data.as_reg_type().reg_num();
                    let addr = self.ms.and_stack[e][r].clone();

                    heap_locs.insert(var.clone(), addr);
                },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();

                    if r.reg_num() != 0 {
                        let addr = self.ms[r].clone();
                        heap_locs.insert(var.clone(), addr);
                    }
                },
                _ => {}
            }
        }
    }

    fn run_query(&mut self, alloc_locs: &AllocVarDict, heap_locs: &mut HeapVarDict)
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
                _ => {
                    if heap_locs.is_empty() {
                        self.record_var_places(0, alloc_locs, heap_locs);
                    }

                    break;
                }
            };
        }
    }

    fn fail(&mut self, heap_locs: &HeapVarDict) -> EvalSession
    {
        if self.ms.ball.stub.len() > 0 {
            let h = self.ms.heap.h;
            self.ms.copy_and_align_ball_to_heap();

            let heap_locs = self.ms.reconstruct_dict(heap_locs, h);
            let error_str = self.ms.print_exception(Addr::HeapCell(h),
                                                    &heap_locs,
                                                    TermFormatter {},
                                                    PrinterOutputter::new())
                                .result();

            EvalSession::from(SessionError::QueryFailureWithException(error_str))
        } else {
            EvalSession::from(SessionError::QueryFailure)
        }
    }

    pub fn submit_query(&mut self, code: Code, alloc_locs: AllocVarDict) -> EvalSession
    {
        let mut heap_locs = HashMap::new();

        self.cached_query = Some(code);
        self.run_query(&alloc_locs, &mut heap_locs);

        if self.failed() {
            self.fail(&heap_locs)
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    pub fn continue_query(&mut self, alloc_l: &AllocVarDict, heap_l: &mut HeapVarDict) -> EvalSession
    {
        if !self.or_stack_is_empty() {
            let b = self.ms.b - 1;
            self.ms.p = self.ms.or_stack[b].bp.clone();

            if let CodePtr::TopLevel(_, 0) = self.ms.p {
                return EvalSession::from(SessionError::QueryFailure);
            }

            self.run_query(alloc_l, heap_l);

            if self.failed() {
                self.fail(&heap_l)
            } else {
                EvalSession::SubsequentQuerySuccess
            }
        } else {
            EvalSession::from(SessionError::QueryFailure)
        }
    }

    pub fn heap_view<Outputter>(&self, var_dir: &HeapVarDict, mut output: Outputter) -> Outputter
       where Outputter: HCValueOutputter
    {
        for (var, addr) in var_dir {
            let fmt = TermFormatter {};
            output = self.ms.print_var_eq(var.clone(), addr.clone(), var_dir, fmt, output);
        }

        output
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.ms.b == 0
    }

    pub fn clear(&mut self) {
        let mut machine = Machine::new();
        swap(self, &mut machine);
    }

    pub fn reset(&mut self) {
        self.cut_policy = Box::new(DefaultCutPolicy {});
        self.ms.reset();
    }
}
