use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::compile::*;
use prolog::heap_print::*;
use prolog::instructions::*;

mod machine_errors;
pub(super) mod machine_state;
pub(super) mod term_expansion;

#[macro_use] mod machine_state_impl;
mod system_calls;

use prolog::machine::machine_state::*;

use std::collections::HashMap;
use std::mem;
use std::ops::Index;
use std::rc::Rc;

static BUILTINS: &str = include_str!("../lib/builtins.pl");

pub struct IndexStore {
    pub(super) atom_tbl: TabledData<Atom>,
    pub(super) code_dir: CodeDir,
    pub(super) op_dir: OpDir,
    pub(super) modules: ModuleDir
}

enum RefOrOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T)
}

impl<'a, T> RefOrOwned<'a, T> {
    fn as_ref(&'a self) -> &'a T {
        match self {
            &RefOrOwned::Borrowed(r) => r,
            &RefOrOwned::Owned(ref r) => r
        }
    }
}

impl IndexStore {    
    #[inline]
    pub fn take_module(&mut self, name: ClauseName) -> Option<Module> {
        self.modules.remove(&name)
    }
    
    #[inline]
    pub fn insert_module(&mut self, module: Module) {
        self.modules.insert(module.module_decl.name.clone(), module);
    }
    
    #[inline]
    pub(super) fn new() -> Self {
        IndexStore {
            atom_tbl: TabledData::new(Rc::new("user".to_string())),
            code_dir: CodeDir::new(),
            op_dir: default_op_dir(),
            modules: ModuleDir::new(),
        }
    }

    #[inline]
    pub(super) fn copy_and_swap(&mut self, other: &mut IndexStore) {
        self.code_dir = other.code_dir.clone();
        self.op_dir = other.op_dir.clone();

        mem::swap(&mut self.code_dir, &mut other.code_dir);
        mem::swap(&mut self.op_dir, &mut other.op_dir);
        mem::swap(&mut self.modules, &mut other.modules);
    }

    fn get_internal(&self, name: ClauseName, arity: usize, in_mod: ClauseName)
                    -> Option<ModuleCodeIndex>
    {
        self.modules.get(&in_mod)
            .and_then(|ref module| module.code_dir.get(&(name, arity)))
            .cloned()
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h  = clause_name!("run_cleaners_with_handling");
        let r_wo_h = clause_name!("run_cleaners_without_handling");

        let builtins = clause_name!("builtins");

        let r_w_h  = self.get_internal(r_w_h, 0, builtins.clone()).and_then(|item| item.local());
        let r_wo_h = self.get_internal(r_wo_h, 1, builtins).and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
    }
}

pub struct CodeRepo {
    cached_query: Option<Code>,
    pub(super) goal_expanders: Code,
    pub(super) term_expanders: Code,
    pub(super) code: Code,
    pub(super) term_dir: TermDir        
}

impl CodeRepo {
    #[inline]
    fn new() -> Self {
        CodeRepo {
            cached_query: None,
            goal_expanders: Code::new(),
            term_expanders: Code::new(),
            code: Code::new(),
            term_dir: TermDir::new()               
        }
    }

    #[inline]
    fn size_of_cached_query(&self) -> usize {
        match &self.cached_query {
            &Some(ref query) => query.len(),
            _ => 0
        }
    }    
    
    fn lookup_instr<'a>(&'a self, last_call: bool, p: &CodePtr) -> Option<RefOrOwned<'a, Line>>
    {
        match p {
            &CodePtr::Local(LocalCodePtr::UserGoalExpansion(p)) =>
                if p < self.goal_expanders.len() {
                    Some(RefOrOwned::Borrowed(&self.goal_expanders[p]))
                } else {
                    None
                },
            &CodePtr::Local(LocalCodePtr::UserTermExpansion(p)) =>
                if p < self.term_expanders.len() {
                    Some(RefOrOwned::Borrowed(&self.term_expanders[p]))
                } else {
                    None
                },
            &CodePtr::Local(LocalCodePtr::TopLevel(_, p)) =>
                match &self.cached_query {
                    &Some(ref cq) => Some(RefOrOwned::Borrowed(&cq[p])),
                    &None => None
                },
            &CodePtr::Local(LocalCodePtr::DirEntry(p)) =>
                Some(RefOrOwned::Borrowed(&self.code[p])),
            &CodePtr::BuiltInClause(ref built_in, _) => {
                let call_clause = call_clause!(ClauseType::BuiltIn(built_in.clone()),
                                               built_in.arity(),
                                               0, last_call);
                Some(RefOrOwned::Owned(call_clause))
            },
            &CodePtr::CallN(arity, _) => {
                let call_clause = call_clause!(ClauseType::CallN, arity, 0, last_call);
                Some(RefOrOwned::Owned(call_clause))
            }
        }
    }
}

pub struct MachinePolicies {
    call_policy: Box<CallPolicy>,
    cut_policy: Box<CutPolicy>,
}

impl MachinePolicies {
    #[inline]
    fn new() -> Self {
        MachinePolicies {
            call_policy: Box::new(DefaultCallPolicy {}),
            cut_policy: Box::new(DefaultCutPolicy {}),
        }
    }
}

pub struct Machine {
    pub(super) machine_st: MachineState,
    pub(super) policies: MachinePolicies,
    pub(super) indices: IndexStore,    
    pub(super) code_repo: CodeRepo  
}

impl Index<LocalCodePtr> for CodeRepo {
    type Output = Line;

    fn index(&self, ptr: LocalCodePtr) -> &Self::Output {
        match ptr {
            LocalCodePtr::TopLevel(_, p) => {
                match &self.cached_query {
                    &Some(ref cq) => &cq[p],
                    &None => panic!("Out-of-bounds top level index.")
                }
            },
            LocalCodePtr::DirEntry(p) => &self.code[p],
            LocalCodePtr::UserGoalExpansion(p) => &self.goal_expanders[p],
            LocalCodePtr::UserTermExpansion(p) => &self.term_expanders[p]
        }
    }
}

impl Index<LocalCodePtr> for Machine {
    type Output = Line;

    fn index(&self, ptr: LocalCodePtr) -> &Self::Output {
        &self.code_repo[ptr]
    }
}

impl SubModuleUser for IndexStore {
    fn atom_tbl(&self) -> TabledData<Atom> {
        self.atom_tbl.clone()
    }
    
    fn op_dir(&mut self) -> &mut OpDir {
        &mut self.op_dir
    }

    fn get_code_index(&self, key: PredicateKey, module: ClauseName) -> Option<CodeIndex>
    {
        match module.as_str() {
            "user" | "builtin" => self.code_dir.get(&key).cloned(),
            _ => self.modules.get(&module).and_then(|ref module| {
                module.code_dir.get(&key).cloned().map(CodeIndex::from)
            })
        }
    }

    fn remove_code_index(&mut self, key: PredicateKey) {
        self.code_dir.remove(&key);
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: ModuleCodeIndex)
    {
        if let Some(ref mut code_idx) = self.code_dir.get_mut(&(name.clone(), arity)) {
            if !code_idx.is_undefined() {
                println!("warning: overwriting {}/{}", &name, arity);
            }

            set_code_index!(code_idx, idx.0, idx.1);
            return;
        }

        self.code_dir.insert((name, arity), CodeIndex::from(idx));
    }
}

static LISTS: &str   = include_str!("../lib/lists.pl");
static CONTROL: &str = include_str!("../lib/control.pl");
static QUEUES: &str  = include_str!("../lib/queues.pl");
static ERROR: &str   = include_str!("../lib/error.pl");
static TERMS: &str   = include_str!("../lib/terms.pl");
static DCGS: &str    = include_str!("../lib/dcgs.pl");

impl Machine {
    pub fn new() -> Self {
        let mut wam = Machine {
            machine_st: MachineState::new(),
            policies: MachinePolicies::new(),
            indices: IndexStore::new(),
            code_repo: CodeRepo::new()
        };

        let atom_tbl = wam.indices.atom_tbl.clone();
        
        compile_listing(&mut wam, BUILTINS.as_bytes(),
                        default_index_store!(atom_tbl.clone()));

        compile_user_module(&mut wam, LISTS.as_bytes());
        compile_user_module(&mut wam, CONTROL.as_bytes());
        compile_user_module(&mut wam, QUEUES.as_bytes());
        compile_user_module(&mut wam, ERROR.as_bytes());
	compile_user_module(&mut wam, TERMS.as_bytes());
        compile_user_module(&mut wam, DCGS.as_bytes());

        wam
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.machine_st.flags
    }
        
    pub fn add_batched_code(&mut self, code: Code, code_dir: CodeDir) -> Result<(), SessionError>
    {
        for (ref key, ref idx) in code_dir.iter() {
            match ClauseType::from(key.0.clone(), key.1, None) {
                ClauseType::Named(..) | ClauseType::Op(..) => {},
                _ => {
                    // ensure we don't try to overwrite the name/arity of a builtin.
                    let err_str = format!("{}/{}", key.0, key.1);
                    return Err(SessionError::CannotOverwriteBuiltIn(err_str));
                }
            };

            if let Some(ref existing_idx) = self.indices.code_dir.get(&key) {
                // ensure we don't try to overwrite an existing predicate from a different module.
                if !existing_idx.is_undefined() && !idx.is_undefined() {
                    // allow the overwriting of user-level predicates by all other predicates.
                    if existing_idx.module_name().as_str() == "user" {
                        continue;
                    }

                    if existing_idx.module_name().as_str() != idx.module_name().as_str() {
                        let err_str = format!("{}/{} from module {}", key.0, key.1,
                                              existing_idx.module_name().as_str());
                        return Err(SessionError::CannotOverwriteImport(err_str));
                    }
                }
            }
        }

        // error detection has finished, so update the master index of keys.
        for (key, idx) in code_dir {
            if let Some(ref mut master_idx) = self.indices.code_dir.get_mut(&key) {
                // ensure we don't double borrow if master_idx == idx.
                // we don't need to modify anything in that case.
                if !Rc::ptr_eq(&master_idx.0, &idx.0) {
                    set_code_index!(master_idx, idx.0.borrow().0, idx.module_name());
                }

                continue;
            }
                        
            self.indices.code_dir.insert(key.clone(), idx.clone());
        }

        self.code_repo.code.extend(code.into_iter());
        Ok(())
    }

    #[inline]
    pub fn add_batched_ops(&mut self, op_dir: OpDir) {
        self.indices.op_dir.extend(op_dir.into_iter());
    }

    #[inline]
    pub fn add_module(&mut self, module: Module, code: Code) {
        self.indices.modules.insert(module.module_decl.name.clone(), module);
        self.code_repo.code.extend(code.into_iter());
    }

    pub fn code_size(&self) -> usize {
        self.code_repo.code.len()
    }

    fn fail(&mut self, heap_locs: &HeapVarDict) -> EvalSession
    {
        if self.machine_st.ball.stub.len() > 0 {
            let h = self.machine_st.heap.h;
            self.machine_st.copy_and_align_ball_to_heap();

            let error_str = self.machine_st.print_exception(Addr::HeapCell(h),
                                                            &heap_locs,
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

        self.code_repo.cached_query = Some(code);
        self.machine_st.run_query(&mut self.indices, &mut self.policies, &self.code_repo, &alloc_locs, &mut heap_locs);

        if self.machine_st.fail {
            self.fail(&heap_locs)
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    pub fn continue_query(&mut self, alloc_l: &AllocVarDict, heap_l: &mut HeapVarDict) -> EvalSession
    {
        if !self.or_stack_is_empty() {
            let b = self.machine_st.b - 1;
            self.machine_st.p = self.machine_st.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.machine_st.p {
                return EvalSession::from(SessionError::QueryFailure);
            }

            self.machine_st.run_query(&mut self.indices, &mut self.policies, &self.code_repo,
                                      alloc_l, heap_l);
            
            if self.machine_st.fail {
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
        let mut sorted_vars: Vec<(&Rc<Var>, &Addr)> = var_dir.iter().collect();
        sorted_vars.sort_by_key(|ref v| v.0);

        for (var, addr) in sorted_vars {            
            output = self.machine_st.print_var_eq(var.clone(), addr.clone(), var_dir, output);
        }

        output
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.machine_st.b == 0
    }

    pub fn clear(&mut self) {
        let mut machine = Machine::new();
        mem::swap(self, &mut machine);
    }

    pub fn reset(&mut self) {
        self.policies.cut_policy = Box::new(DefaultCutPolicy {});
        self.machine_st.reset();
    }
}


impl MachineState {    
    fn execute_instr(&mut self, indices: &mut IndexStore, policies: &mut MachinePolicies,
                     code_repo: &CodeRepo)
    {
        let instr = match code_repo.lookup_instr(self.last_call, &self.p) {
            Some(instr) => instr,
            None => return
        };

        match instr.as_ref() {
            &Line::Arithmetic(ref arith_instr) =>
                self.execute_arith_instr(arith_instr),
            &Line::Choice(ref choice_instr) =>
                self.execute_choice_instr(choice_instr, &mut policies.call_policy),
            &Line::Cut(ref cut_instr) =>
                self.execute_cut_instr(cut_instr, &mut policies.cut_policy),
            &Line::Control(ref control_instr) => 
                self.execute_ctrl_instr(indices, &mut policies.call_policy,
                                        &mut policies.cut_policy, control_instr),            
            &Line::Fact(ref fact) => {
                for fact_instr in fact {
                    if self.fail {
                        break;
                    }

                    self.execute_fact_instr(&fact_instr);
                }

                self.p += 1;
            },
            &Line::Indexing(ref indexing_instr) =>
                self.execute_indexing_instr(&indexing_instr),
            &Line::IndexedChoice(ref choice_instr) =>
                self.execute_indexed_choice_instr(choice_instr, &mut policies.call_policy),
            &Line::Query(ref query) => {
                for query_instr in query {
                    if self.fail {
                        break;
                    }

                    self.execute_query_instr(&query_instr);
                }

                self.p += 1;
            }
        }
    }

    fn backtrack(&mut self)
    {
        if self.b > 0 {
            let b = self.b - 1;

            self.b0 = self.or_stack[b].b0;
            self.p  = self.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, p)) = self.p {
                self.fail = p == 0;
            } else {
                self.fail = false;
            }
        } else {
            self.p = CodePtr::Local(LocalCodePtr::TopLevel(0, 0));
        }
    }

    fn query_stepper(&mut self, indices: &mut IndexStore, policies: &mut MachinePolicies, code_repo: &CodeRepo)
    {
        loop {
            self.execute_instr(indices, policies, code_repo);

            if self.fail {
                self.backtrack();
            }

            match self.p {
                CodePtr::Local(LocalCodePtr::DirEntry(p)) if p < code_repo.code.len() => {},
                CodePtr::Local(LocalCodePtr::UserTermExpansion(p)) if p < code_repo.term_expanders.len() => {},
                CodePtr::Local(LocalCodePtr::UserTermExpansion(_)) => self.fail = true,
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(p)) if p < code_repo.goal_expanders.len() => {},
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(_)) => self.fail = true,
                CodePtr::Local(_) => break,
                _ => {}
            };
        }
    }

    fn record_var_places(&self, chunk_num: usize, alloc_locs: &AllocVarDict, heap_locs: &mut HeapVarDict)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(p) if p > 0 => {
                    let e = self.e;
                    let r = var_data.as_reg_type().reg_num();
                    let addr = self.and_stack[e][r].clone();

                    heap_locs.insert(var.clone(), addr);
                },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();

                    if r.reg_num() != 0 {
                        let addr = self[r].clone();
                        heap_locs.insert(var.clone(), addr);
                    }
                },
                _ => {}
            }
        }
    }

    pub(super)
    fn run_query(&mut self, indices: &mut IndexStore,
                 policies: &mut MachinePolicies, code_repo: &CodeRepo,
                 alloc_locs: &AllocVarDict, heap_locs: &mut HeapVarDict)
    {
        let end_ptr = top_level_code_ptr!(0, code_repo.size_of_cached_query());

        while self.p < end_ptr {
            if let CodePtr::Local(LocalCodePtr::TopLevel(mut cn, p)) = self.p {
                match &code_repo[LocalCodePtr::TopLevel(cn, p)] {
                    &Line::Control(ref ctrl_instr) if ctrl_instr.is_jump_instr() => {
                        self.record_var_places(cn, alloc_locs, heap_locs);
                        cn += 1;
                    },
                    _ => {}
                }

                self.p = top_level_code_ptr!(cn, p);
            }

            self.query_stepper(indices, policies, code_repo);

            match self.p {
                CodePtr::Local(LocalCodePtr::TopLevel(_, p)) if p > 0 => {},
                _ => {
                    if heap_locs.is_empty() {
                        self.record_var_places(0, alloc_locs, heap_locs);
                    }

                    break;
                }
            };
        }
    }    
}

