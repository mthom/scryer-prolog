use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::clause_types::*;
use prolog::fixtures::*;
use prolog::forms::*;
use prolog::heap_print::*;
use prolog::instructions::*;

pub mod machine_indices;
pub mod heap;
mod and_stack;
mod or_stack;
mod attributed_variables;
mod copier;
mod dynamic_database;
pub mod machine_errors;
pub mod toplevel;
pub mod compile;
pub(super) mod code_repo;
pub mod modules;
pub(super) mod machine_state;
pub(super) mod term_expansion;

#[macro_use] mod machine_state_impl;
mod system_calls;

use prolog::machine::attributed_variables::*;
use prolog::machine::compile::*;
use prolog::machine::code_repo::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::machine::modules::*;
use prolog::machine::toplevel::*;

use std::collections::{HashMap, VecDeque};
use std::mem;
use std::ops::Index;
use std::rc::Rc;

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
            LocalCodePtr::InSituDirEntry(p) => &self.in_situ_code[p],
            LocalCodePtr::TopLevel(_, p) => &self.cached_query[p],
            LocalCodePtr::DirEntry(p) => &self.code[p],
            LocalCodePtr::UserGoalExpansion(p) => &self.goal_expanders[p],
            LocalCodePtr::UserTermExpansion(p) => &self.term_expanders[p],
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

    fn remove_code_index(&mut self, key: PredicateKey)
    {
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

    fn use_qualified_module(&mut self, code_repo: &mut CodeRepo, flags: MachineFlags,
                            submodule: &Module, exports: &Vec<PredicateKey>)
                            -> Result<(), SessionError>
    {
        use_qualified_module(self, submodule, exports)?;
        submodule.dump_expansions(code_repo, flags).map_err(SessionError::from)
    }

    fn use_module(&mut self, code_repo: &mut CodeRepo, flags: MachineFlags, submodule: &Module)
                  -> Result<(), SessionError>
    {
        use_module(self, submodule)?;

        if !submodule.inserted_expansions {
            submodule.dump_expansions(code_repo, flags).map_err(SessionError::from)
        } else {
            Ok(())
        }
    }
}

static BUILTINS: &str = include_str!("../lib/builtins.pl");
static LISTS: &str    = include_str!("../lib/lists.pl");
static QUEUES: &str   = include_str!("../lib/queues.pl");
static ERROR: &str    = include_str!("../lib/error.pl");
static BETWEEN: &str  = include_str!("../lib/between.pl");
static TERMS: &str    = include_str!("../lib/terms.pl");
static DCGS: &str     = include_str!("../lib/dcgs.pl");
static ATTS: &str     = include_str!("../lib/atts.pl");
static DIF: &str      = include_str!("../lib/dif.pl");
static FREEZE: &str   = include_str!("../lib/freeze.pl");
static REIF: &str     = include_str!("../lib/reif.pl");

impl Machine {
    fn compile_special_forms(&mut self) {
        match compile_special_form(self, VERIFY_ATTRS.as_bytes()) {
            Ok(code) => {
                self.machine_st.attr_var_init.verify_attrs_loc = self.code_repo.code.len();
                self.code_repo.code.extend(code.into_iter());
            },
            Err(_) => panic!("Machine::compile_special_forms() failed at VERIFY_ATTRS")
        }

        match compile_special_form(self, PROJECT_ATTRS.as_bytes()) {
            Ok(code) => {
                self.machine_st.attr_var_init.project_attrs_loc = self.code_repo.code.len();
                self.code_repo.code.extend(code.into_iter());
            },
            Err(_) => panic!("Machine::compile_special_forms() failed at PROJECT_ATTRS")
        }
    }

    fn compile_libraries(&mut self) {
        compile_user_module(self, LISTS.as_bytes());
        compile_user_module(self, QUEUES.as_bytes());
        compile_user_module(self, ERROR.as_bytes());
        compile_user_module(self, BETWEEN.as_bytes());
	compile_user_module(self, TERMS.as_bytes());
        compile_user_module(self, DCGS.as_bytes());
        compile_user_module(self, ATTS.as_bytes());
        compile_user_module(self, DIF.as_bytes());
        compile_user_module(self, FREEZE.as_bytes());
        compile_user_module(self, REIF.as_bytes());
    }

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

        wam.compile_libraries();
        wam.compile_special_forms();

        wam
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.machine_st.flags
    }

    pub fn check_dynamic_clause_overwrite(&self, name: ClauseName, arity: usize, module: ClauseName)
                                          -> Result<(), SessionError>
    {
        if let Some(info) = self.indices.dynamic_code_dir.get(&(name.clone(), arity)) {
            if info.module_src != module {
                let err_str = format!("{}/{}", name.as_str(), arity);
                let err_str = clause_name!(err_str, self.indices.atom_tbl());

                return Err(SessionError::CannotOverwriteDynamicClause(err_str));
            }
        }

        Ok(())
    }

    pub fn check_toplevel_code(&self, indices: &IndexStore, dynamic_clause_map: &DynamicClauseMap)
                               -> Result<(), SessionError>
    {
        for (key, idx) in &indices.code_dir {
            match ClauseType::from(key.0.clone(), key.1, None) {
                ClauseType::Named(..) | ClauseType::Op(..) => {},
                _ => {
                    // ensure we don't try to overwrite the name/arity of a builtin.
                    let err_str = format!("{}/{}", key.0, key.1);
                    let err_str = clause_name!(err_str, self.indices.atom_tbl());
                    
                    return Err(SessionError::CannotOverwriteBuiltIn(err_str));
                }
            };

            if dynamic_clause_map.contains_key(&key) {
                let module = idx.0.borrow().1.clone();
                self.check_dynamic_clause_overwrite(key.0.clone(), key.1, module)?;
            }
            
            if let Some(ref existing_idx) = self.indices.code_dir.get(&key) {
                // ensure we don't try to overwrite an existing predicate from a different module.
                if !existing_idx.is_undefined() && !idx.is_undefined() {
                    // allow the overwriting of user-level predicates by all other predicates.
                    if existing_idx.module_name().as_str() == "user" {
                        continue;
                    }

                    if existing_idx.module_name() != idx.module_name() {
                        let err_str = format!("{}/{} from module {}", key.0, key.1,
                                              existing_idx.module_name().as_str());
                        let err_str = clause_name!(err_str, self.indices.atom_tbl());
                        
                        return Err(SessionError::CannotOverwriteImport(err_str));
                    }
                }
            }
        }

        Ok(())
    }
    
    pub fn add_batched_code(&mut self, code: Code, code_dir: CodeDir)
    {
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

            self.indices.code_dir.insert(key, idx);
        }

        self.code_repo.code.extend(code.into_iter());
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

    fn fail(&mut self) -> EvalSession
    {
        if self.machine_st.ball.stub.len() > 0 {
            let h = self.machine_st.heap.h;
            self.machine_st.copy_and_align_ball_to_heap(0);

            let err_str = self.machine_st.print_exception(Addr::HeapCell(h),
                                                          &HeapVarDict::new(),
                                                          PrinterOutputter::new())
                .result();

            let err_str = clause_name!(err_str, self.indices.atom_tbl());            
            EvalSession::from(SessionError::QueryFailureWithException(err_str))
        } else {
            EvalSession::from(SessionError::QueryFailure)
        }
    }

    pub fn submit_query(&mut self, code: Code, alloc_locs: AllocVarDict) -> EvalSession
    {
        let mut heap_locs = HashMap::new();

        self.code_repo.cached_query = code;
        self.run_query(&alloc_locs, &mut heap_locs);

        if self.machine_st.fail {
            self.fail()
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs, heap_locs)
        }
    }

    fn record_var_places(&self, chunk_num: usize, alloc_locs: &AllocVarDict,
                         heap_locs: &mut HeapVarDict)
    {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(p) if p > 0 =>
                    if !heap_locs.contains_key(var) {
                        let e = self.machine_st.e;
                        let r = var_data.as_reg_type().reg_num();
                        let addr = self.machine_st.and_stack[e][r].clone();

                        heap_locs.insert(var.clone(), addr);
                    },
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();

                    if r.reg_num() != 0 {
                        let addr = self.machine_st[r].clone();
                        heap_locs.insert(var.clone(), addr);
                    }
                },
                _ => {}
            }
        }
    }

    pub(super)
    fn run_query(&mut self, alloc_locs: &AllocVarDict, heap_locs: &mut HeapVarDict)
    {
        let end_ptr = top_level_code_ptr!(0, self.code_repo.size_of_cached_query());

        while self.machine_st.p < end_ptr {
            if let CodePtr::Local(LocalCodePtr::TopLevel(mut cn, p)) = self.machine_st.p {
                match &self.code_repo[LocalCodePtr::TopLevel(cn, p)] {
                    &Line::Control(ref ctrl_instr) if ctrl_instr.is_jump_instr() => {
                        self.record_var_places(cn, alloc_locs, heap_locs);
                        cn += 1;
                    },
                    _ => {}
                }

                self.machine_st.p = top_level_code_ptr!(cn, p);
            }

            self.machine_st.query_stepper(&mut self.indices, &mut self.policies, &mut self.code_repo);

            match self.machine_st.p {
                CodePtr::Local(LocalCodePtr::TopLevel(_, p)) if p > 0 => {},
                CodePtr::DynamicTransaction(trans_type, p) => {
                    // self.code_repo.cached_query is about to be overwritten by the term expander,
                    // so hold onto it locally and restore it after the compiler has finished.
                    let cached_query = mem::replace(&mut self.code_repo.cached_query, vec![]);
                    self.dynamic_transaction(trans_type, p);

                    if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.machine_st.p {
                        if heap_locs.is_empty() {
                            self.record_var_places(0, alloc_locs, heap_locs);
                        }

                        self.code_repo.cached_query = cached_query;
                        break;
                    }

                    self.code_repo.cached_query = cached_query;
                },
                _ => {
                    if heap_locs.is_empty() {
                        self.record_var_places(0, alloc_locs, heap_locs);
                    }

                    break;
                }
            };
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

            self.run_query(alloc_l, heap_l);

            if self.machine_st.fail {
                self.fail()
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
            &Line::Fact(ref fact_instr) => {
                self.execute_fact_instr(&fact_instr);
                self.p += 1;
            },
            &Line::Indexing(ref indexing_instr) =>
                self.execute_indexing_instr(&indexing_instr),
            &Line::IndexedChoice(ref choice_instr) =>
                self.execute_indexed_choice_instr(choice_instr, &mut policies.call_policy),
            &Line::Query(ref query_instr) => {
                self.execute_query_instr(&query_instr);
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

    fn query_stepper(&mut self, indices: &mut IndexStore, policies: &mut MachinePolicies,
                     code_repo: &mut CodeRepo)
    {
        loop {
            self.execute_instr(indices, policies, code_repo);

            if self.fail {
                self.backtrack();
            }

            match self.p {
                CodePtr::Local(LocalCodePtr::DirEntry(p))
                    if p < code_repo.code.len() => {},
                CodePtr::Local(LocalCodePtr::UserTermExpansion(p))
                    if p < code_repo.term_expanders.len() => {},
                CodePtr::Local(LocalCodePtr::UserTermExpansion(_)) =>
                    self.fail = true,
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(p))
                    if p < code_repo.goal_expanders.len() => {},
                CodePtr::Local(LocalCodePtr::UserGoalExpansion(_)) =>
                    self.fail = true,
                CodePtr::Local(LocalCodePtr::InSituDirEntry(p))
                    if p < code_repo.in_situ_code.len() => {},
                CodePtr::Local(_) | CodePtr::DynamicTransaction(..) =>
                    break,
                CodePtr::VerifyAttrInterrupt(p) =>
                    self.verify_attr_interrupt(p),
                _ => {}
            }
        }
    }
}
