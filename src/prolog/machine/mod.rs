use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::clause_types::*;
use prolog::fixtures::*;
use prolog::forms::*;
use prolog::heap_print::*;
use prolog::instructions::*;
use prolog::read::*;
use prolog::write::{next_keypress, ContinueResult};

mod and_stack;
mod attributed_variables;
pub(super) mod code_repo;
pub mod compile;
mod copier;
mod dynamic_database;
pub mod heap;
pub mod machine_errors;
pub mod machine_indices;
pub(super) mod machine_state;
pub mod modules;
mod or_stack;
pub(super) mod term_expansion;
pub mod toplevel;

#[macro_use]
mod machine_state_impl;
mod system_calls;

use prolog::machine::attributed_variables::*;
use prolog::machine::code_repo::*;
use prolog::machine::compile::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::machine::modules::*;
use prolog::machine::toplevel::stream_to_toplevel;
use prolog::read::PrologStream;

use indexmap::IndexMap;

use std::collections::VecDeque;
use std::fs::File;
use std::io::{stdout, Read, Write};
use std::mem;
use std::ops::Index;
use std::rc::Rc;

use termion::raw::IntoRawMode;

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
    pub(super) code_repo: CodeRepo,
    pub(super) toplevel_idx: usize,
    pub(super) prolog_stream: ParsingStream<Box<Read>>,
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

    fn get_code_index(&self, key: PredicateKey, module: ClauseName) -> Option<CodeIndex> {
        match module.as_str() {
            "user" | "builtin" => self.code_dir.get(&key).cloned(),
            _ => self
                .modules
                .get(&module)
                .and_then(|ref module| module.code_dir.get(&key).cloned().map(CodeIndex::from)),
        }
    }

    fn remove_code_index(&mut self, key: PredicateKey) {
        self.code_dir.remove(&key);
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: CodeIndex) {
        if let Some(ref code_idx) = self.code_dir.get(&(name.clone(), arity)) {
            if !code_idx.is_undefined() {
                println!("warning: overwriting {}/{}", &name, arity);
            }

            let (p, module_name) = idx.0.borrow().clone();
            set_code_index!(code_idx, p, module_name);
            return;
        }

        self.code_dir.insert((name, arity), idx);
    }

    fn use_qualified_module(
        &mut self,
        code_repo: &mut CodeRepo,
        flags: MachineFlags,
        submodule: &Module,
        exports: &Vec<PredicateKey>,
    ) -> Result<(), SessionError> {
        use_qualified_module(self, submodule, exports)?;
        submodule
            .dump_expansions(code_repo, flags)
            .map_err(SessionError::from)
    }

    fn use_module(
        &mut self,
        code_repo: &mut CodeRepo,
        flags: MachineFlags,
        submodule: &Module,
    ) -> Result<(), SessionError> {
        use_module(self, submodule)?;

        if !submodule.inserted_expansions {
            submodule
                .dump_expansions(code_repo, flags)
                .map_err(SessionError::from)
        } else {
            Ok(())
        }
    }
}

static BUILTINS: &str = include_str!("../lib/builtins.pl");
static ERROR: &str = include_str!("../lib/error.pl");
static LISTS: &str = include_str!("../lib/lists.pl");
static NON_ISO: &str = include_str!("../lib/non_iso.pl");
static TOPLEVEL: &str = include_str!("../toplevel.pl");

impl Machine {
    fn compile_special_forms(&mut self) {
        match compile_special_form(self, parsing_stream(VERIFY_ATTRS.as_bytes())) {
            Ok(code) => {
                self.machine_st.attr_var_init.verify_attrs_loc = self.code_repo.code.len();
                self.code_repo.code.extend(code.into_iter());
            }
            Err(_) => panic!("Machine::compile_special_forms() failed at VERIFY_ATTRS"),
        }

        match compile_special_form(self, parsing_stream(PROJECT_ATTRS.as_bytes())) {
            Ok(code) => {
                self.machine_st.attr_var_init.project_attrs_loc = self.code_repo.code.len();
                self.code_repo.code.extend(code.into_iter());
            }
            Err(_) => panic!("Machine::compile_special_forms() failed at PROJECT_ATTRS"),
        }
    }

    fn compile_top_level(&mut self) {
        self.toplevel_idx = self.code_repo.code.len();
        compile_user_module(self, parsing_stream(TOPLEVEL.as_bytes()));
    }

    fn compile_scryerrc(&mut self) {
        let mut path = match dirs::home_dir() {
            Some(path) => path,
            None => return,
        };

        path.push(".scryerrc");

        if path.is_file() {
            let file_src = match File::open(&path) {
                Ok(file_handle) => parsing_stream(file_handle),
                Err(_) => return,
            };

            compile_user_module(self, file_src);
        }
    }

    #[cfg(test)]
    pub fn reset(&mut self) {
        self.prolog_stream = readline::input_stream();
        self.policies.cut_policy = Box::new(DefaultCutPolicy {});
        self.machine_st.reset();
    }

    pub fn run_toplevel(&mut self) {
        self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(self.toplevel_idx));
        self.run_query(&AllocVarDict::new());
    }

    pub fn new(prolog_stream: PrologStream) -> Self {
        let mut wam = Machine {
            machine_st: MachineState::new(),
            policies: MachinePolicies::new(),
            indices: IndexStore::new(),
            code_repo: CodeRepo::new(),
            toplevel_idx: 0,
            prolog_stream,
        };

        let atom_tbl = wam.indices.atom_tbl.clone();

        compile_listing(
            &mut wam,
            parsing_stream(BUILTINS.as_bytes()),
            default_index_store!(atom_tbl.clone()),
        );

        wam.compile_special_forms();
        wam.compile_top_level();

        compile_user_module(&mut wam, parsing_stream(ERROR.as_bytes()));
        compile_user_module(&mut wam, parsing_stream(LISTS.as_bytes()));
        compile_user_module(&mut wam, parsing_stream(NON_ISO.as_bytes()));

        wam.compile_scryerrc();

        wam
    }

    #[inline]
    pub fn machine_flags(&self) -> MachineFlags {
        self.machine_st.flags
    }

    pub fn check_toplevel_code(&self, indices: &IndexStore) -> Result<(), SessionError> {
        for (key, idx) in &indices.code_dir {
            match ClauseType::from(key.0.clone(), key.1, None) {
                ClauseType::Named(..) | ClauseType::Op(..) => {}
                _ => {
                    // ensure we don't try to overwrite the name/arity of a builtin.
                    let err_str = format!("{}/{}", key.0, key.1);
                    let err_str = clause_name!(err_str, self.indices.atom_tbl());

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

                    if existing_idx.module_name() != idx.module_name() {
                        let err_str = format!(
                            "{}/{} from module {}",
                            key.0,
                            key.1,
                            existing_idx.module_name().as_str()
                        );
                        let err_str = clause_name!(err_str, self.indices.atom_tbl());

                        return Err(SessionError::CannotOverwriteImport(err_str));
                    }
                }
            }
        }

        Ok(())
    }

    pub fn add_batched_code(&mut self, code: Code, code_dir: CodeDir) {
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
        self.indices
            .modules
            .insert(module.module_decl.name.clone(), module);
        self.code_repo.code.extend(code.into_iter());
    }

    pub fn submit_query(&mut self, code: Code, alloc_locs: AllocVarDict) -> EvalSession {
        self.code_repo.cached_query = code;
        self.run_query(&alloc_locs);

        if self.machine_st.fail {
            EvalSession::QueryFailure
        } else {
            EvalSession::InitialQuerySuccess(alloc_locs)
        }
    }

    pub fn throw_session_error(&mut self, err: SessionError, key: PredicateKey) {
        let h = self.machine_st.heap.h;

        let err = MachineError::session_error(h, err);
        let stub = MachineError::functor_stub(key.0, key.1);
        let err = self.machine_st.error_form(err, stub);

        self.machine_st.throw_exception(err);
        return;
    }

    fn handle_toplevel_command(&mut self, code_ptr: REPLCodePtr, p: LocalCodePtr) {
        match code_ptr {
            REPLCodePtr::CompileBatch => {
                #[cfg(feature = "readline_rs_compat")]
                readline::set_line_mode(readline::LineMode::Multi);

                let src = readline::input_stream();

                #[cfg(feature = "readline_rs_compat")]
                readline::set_line_mode(readline::LineMode::Single);

                match compile_user_module(self, src) {
                    EvalSession::Error(e) => self.throw_session_error(e, (clause_name!("repl"), 0)),
                    _ => {}
                };
            }
            REPLCodePtr::SubmitQueryAndPrintResults => {
                let term = self.machine_st[temp_v!(1)].clone();
                let stub = MachineError::functor_stub(clause_name!("repl"), 0);

                let s = match self.machine_st.try_from_list(temp_v!(2), stub) {
                    Ok(addrs) => {
                        let mut var_dict = HeapVarDict::new();

                        for addr in addrs {
                            match addr {
                                Addr::Str(s) => {
                                    let var_atom = match self.machine_st.heap[s + 1].as_addr(s + 1)
                                    {
                                        Addr::Con(Constant::Atom(var_atom, _)) => {
                                            Rc::new(var_atom.to_string())
                                        }
                                        _ => unreachable!(),
                                    };

                                    let var_addr = self.machine_st.heap[s + 2].as_addr(s + 2);
                                    var_dict.insert(var_atom, var_addr);
                                }
                                _ => unreachable!(),
                            };
                        }

                        self.machine_st.heap_locs = var_dict;
                        let term_output = self.machine_st.print_query(term, &self.indices.op_dir);

                        term_output.result()
                    }
                    Err(err_stub) => {
                        self.machine_st.throw_exception(err_stub);
                        return;
                    }
                };

                let stream = parsing_stream(s.as_bytes());

                let snapshot = self.machine_st.sink_to_snapshot();
                self.machine_st.reset();

                let result = match stream_to_toplevel(stream, self) {
                    Ok(packet) => compile_term(self, packet),
                    Err(e) => EvalSession::from(e),
                };

                self.handle_eval_session(result, snapshot);
            }
        }

        self.machine_st.p = CodePtr::Local(p);
    }

    fn propagate_exception_to_toplevel(&mut self, snapshot: MachineState) {
        let ball = self.machine_st.ball.take();

        self.machine_st.absorb_snapshot(snapshot);
        self.machine_st.ball = ball;

        let stub = self.machine_st.copy_and_align_ball();
        self.machine_st.throw_exception(stub);

        return;
    }

    fn handle_eval_session(&mut self, result: EvalSession, snapshot: MachineState) {
        match result {
            EvalSession::InitialQuerySuccess(alloc_locs) => loop {
                let bindings = {
                    let output = PrinterOutputter::new();
                    self.toplevel_heap_view(output).result()
                };

                let attr_goals = self.attribute_goals();

                if !(self.machine_st.b > 0) {
                    if bindings.is_empty() {
                        let space = if requires_space(&attr_goals, ".") {
                            " "
                        } else {
                            ""
                        };

                        if !attr_goals.is_empty() {
                            println!("{}{}.", attr_goals, space);
                        } else {
                            println!("true.");
                        }

                        self.machine_st.absorb_snapshot(snapshot);
                        return;
                    }
                } else if bindings.is_empty() && attr_goals.is_empty() {
                    print!("true");
                    stdout().flush().unwrap();
                }

                let mut raw_stdout = stdout().into_raw_mode().unwrap();

                if !attr_goals.is_empty() {
                    if bindings.is_empty() {
                        write!(raw_stdout, "{}", attr_goals).unwrap();
                    } else {
                        write!(raw_stdout, "{}, {}", bindings, attr_goals).unwrap();
                    }
                } else if !bindings.is_empty() {
                    write!(raw_stdout, "{}", bindings).unwrap();
                }

                if self.machine_st.b > 0 {
                    raw_stdout.flush().unwrap();

                    let result = match next_keypress() {
                        ContinueResult::ContinueQuery => {
                            write!(raw_stdout, " ;\r\n").unwrap();
                            self.continue_query(&alloc_locs)
                        }
                        ContinueResult::Conclude => {
                            write!(raw_stdout, " ...\r\n").unwrap();
                            self.machine_st.absorb_snapshot(snapshot);
                            return;
                        }
                    };

                    let mut raw_stdout = stdout().into_raw_mode().unwrap();

                    match result {
                        EvalSession::QueryFailure => {
                            if self.machine_st.ball.stub.len() > 0 {
                                self.propagate_exception_to_toplevel(snapshot);
                                return;
                            } else {
                                write!(raw_stdout, "false.\r\n").unwrap();
                                raw_stdout.flush().unwrap();

                                self.machine_st.absorb_snapshot(snapshot);
                                return;
                            }
                        }
                        EvalSession::Error(err) => {
                            self.machine_st.absorb_snapshot(snapshot);
                            self.throw_session_error(err, (clause_name!("repl"), 0));
                            return;
                        }
                        _ => {}
                    }
                } else {
                    if bindings.is_empty() && attr_goals.is_empty() {
                        write!(raw_stdout, "true.\r\n").unwrap();
                    } else {
                        let space = if !attr_goals.is_empty() {
                            if requires_space(&attr_goals, ".") {
                                " "
                            } else {
                                ""
                            }
                        } else {
                            if requires_space(&bindings, ".") {
                                " "
                            } else {
                                ""
                            }
                        };

                        write!(raw_stdout, "{}.\r\n", space).unwrap();
                    }

                    break;
                }
            },
            EvalSession::Error(err) => {
                self.machine_st.absorb_snapshot(snapshot);
                self.throw_session_error(err, (clause_name!("repl"), 0));
                return;
            }
            EvalSession::QueryFailure => {
                if self.machine_st.ball.stub.len() > 0 {
                    return self.propagate_exception_to_toplevel(snapshot);
                } else {
                    println!("false.");
                }
            }
            _ => {}
        }

        self.machine_st.absorb_snapshot(snapshot);
    }

    pub(super) fn run_query(&mut self, alloc_locs: &AllocVarDict) {
        let end_ptr = top_level_code_ptr!(0, self.code_repo.size_of_cached_query());

        while self.machine_st.p < end_ptr {
            if let CodePtr::Local(LocalCodePtr::TopLevel(mut cn, p)) = self.machine_st.p {
                match &self.code_repo[LocalCodePtr::TopLevel(cn, p)] {
                    &Line::Control(ref ctrl_instr) if ctrl_instr.is_jump_instr() => {
                        self.machine_st.record_var_places(cn, alloc_locs);
                        cn += 1;
                    }
                    _ => {}
                }

                self.machine_st.p = top_level_code_ptr!(cn, p);
            }

            self.machine_st.query_stepper(
                &mut self.indices,
                &mut self.policies,
                &mut self.code_repo,
                &mut self.prolog_stream,
            );

            match self.machine_st.p {
                CodePtr::Local(LocalCodePtr::TopLevel(_, p)) if p > 0 => {}
                CodePtr::REPL(code_ptr, p) => self.handle_toplevel_command(code_ptr, p),
                CodePtr::DynamicTransaction(trans_type, p) => {
                    // self.code_repo.cached_query is about to be overwritten by the term expander,
                    // so hold onto it locally and restore it after the compiler has finished.
                    self.machine_st.fail = false;
                    let cached_query = mem::replace(&mut self.code_repo.cached_query, vec![]);
                    self.dynamic_transaction(trans_type, p);

                    if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.machine_st.p {
                        if self.machine_st.heap_locs.is_empty() {
                            self.machine_st.record_var_places(0, alloc_locs);
                        }

                        self.code_repo.cached_query = cached_query;
                        break;
                    }

                    self.code_repo.cached_query = cached_query;
                }
                _ => {
                    if self.machine_st.heap_locs.is_empty() {
                        self.machine_st.record_var_places(0, alloc_locs);
                    }

                    break;
                }
            };
        }
    }

    pub fn continue_query(&mut self, alloc_locs: &AllocVarDict) -> EvalSession {
        if !self.or_stack_is_empty() {
            let b = self.machine_st.b - 1;
            self.machine_st.p = self.machine_st.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.machine_st.p {
                self.machine_st.fail = true;
                return EvalSession::QueryFailure;
            }

            self.run_query(alloc_locs);

            if self.machine_st.fail {
                EvalSession::QueryFailure
            } else {
                EvalSession::SubsequentQuerySuccess
            }
        } else {
            EvalSession::QueryFailure
        }
    }

    pub fn toplevel_heap_view<Outputter>(&self, mut output: Outputter) -> Outputter
    where
        Outputter: HCValueOutputter,
    {
        let mut sorted_vars: Vec<_> = self.machine_st.heap_locs.iter().collect();
        sorted_vars.sort_by_key(|ref v| v.0);

        for (var, addr) in sorted_vars {
            let addr = self.machine_st.store(self.machine_st.deref(addr.clone()));
            output = self
                .machine_st
                .print_var_eq(var.clone(), addr, &self.indices.op_dir, output);
        }

        output
    }

    #[cfg(test)]
    pub fn test_heap_view<Outputter>(&self, mut output: Outputter) -> Outputter
    where
        Outputter: HCValueOutputter,
    {
        let mut sorted_vars: Vec<(&Rc<Var>, &Addr)> = self.machine_st.heap_locs.iter().collect();
        sorted_vars.sort_by_key(|ref v| v.0);

        for (var, addr) in sorted_vars {
            output = self.machine_st.print_var_eq(
                var.clone(),
                addr.clone(),
                &self.indices.op_dir,
                output,
            );
        }

        output
    }

    pub fn or_stack_is_empty(&self) -> bool {
        self.machine_st.b == 0
    }
}

impl MachineState {
    fn record_var_places(&mut self, chunk_num: usize, alloc_locs: &AllocVarDict) {
        for (var, var_data) in alloc_locs {
            match var_data {
                &VarData::Perm(p) if p > 0 => {
                    if !self.heap_locs.contains_key(var) {
                        let e = self.e;
                        let r = var_data.as_reg_type().reg_num();
                        let addr = self.and_stack[e][r].clone();

                        self.heap_locs.insert(var.clone(), addr);
                    }
                }
                &VarData::Temp(cn, _, _) if cn == chunk_num => {
                    let r = var_data.as_reg_type();

                    if r.reg_num() != 0 {
                        let addr = self[r].clone();
                        self.heap_locs.insert(var.clone(), addr);
                    }
                }
                _ => {}
            }
        }
    }

    fn print_query(&mut self, addr: Addr, op_dir: &OpDir) -> PrinterOutputter {
        let flags = self.flags;

        let mut output = {
            self.flags = MachineFlags {
                double_quotes: DoubleQuotes::Atom,
            };

            let output = PrinterOutputter::new();
            let mut printer = HCPrinter::from_heap_locs(&self, op_dir, output);

            printer.quoted = true;
            printer.numbervars = false;
            printer.drop_toplevel_spec();

            printer.see_all_locs();
            printer.print(addr)
        };

        self.flags = flags;

        output.append(".");
        output
    }

    fn dispatch_instr(
        &mut self,
        instr: &Line,
        indices: &mut IndexStore,
        policies: &mut MachinePolicies,
        code_repo: &CodeRepo,
        prolog_stream: &mut PrologStream,
    ) {
        match instr {
            &Line::Arithmetic(ref arith_instr) => self.execute_arith_instr(arith_instr),
            &Line::Choice(ref choice_instr) => {
                self.execute_choice_instr(choice_instr, &mut policies.call_policy)
            }
            &Line::Cut(ref cut_instr) => {
                self.execute_cut_instr(cut_instr, &mut policies.cut_policy)
            }
            &Line::Control(ref control_instr) => self.execute_ctrl_instr(
                indices,
                code_repo,
                &mut policies.call_policy,
                &mut policies.cut_policy,
                prolog_stream,
                control_instr,
            ),
            &Line::Fact(ref fact_instr) => {
                self.execute_fact_instr(&fact_instr);
                self.p += 1;
            }
            &Line::Indexing(ref indexing_instr) => self.execute_indexing_instr(&indexing_instr),
            &Line::IndexedChoice(ref choice_instr) => {
                self.execute_indexed_choice_instr(choice_instr, &mut policies.call_policy)
            }
            &Line::Query(ref query_instr) => {
                self.execute_query_instr(&query_instr);
                self.p += 1;
            }
        }
    }

    fn execute_instr(
        &mut self,
        indices: &mut IndexStore,
        policies: &mut MachinePolicies,
        code_repo: &CodeRepo,
        prolog_stream: &mut PrologStream,
    ) {
        let instr = match code_repo.lookup_instr(self.last_call, &self.p) {
            Some(instr) => instr,
            None => return,
        };

        self.dispatch_instr(instr.as_ref(), indices, policies, code_repo, prolog_stream);
    }

    fn backtrack(&mut self) {
        if self.b > 0 {
            let b = self.b - 1;

            self.b0 = self.or_stack[b].b0;
            self.p = self.or_stack[b].bp.clone();

            if let CodePtr::Local(LocalCodePtr::TopLevel(_, p)) = self.p {
                self.fail = p == 0;
            } else {
                self.fail = false;
            }
        } else {
            self.p = CodePtr::Local(LocalCodePtr::TopLevel(0, 0));
        }
    }

    fn check_machine_index(&mut self, code_repo: &CodeRepo) -> bool {
        match self.p {
            CodePtr::Local(LocalCodePtr::DirEntry(p)) if p < code_repo.code.len() => {}
            CodePtr::Local(LocalCodePtr::UserTermExpansion(p))
                if p < code_repo.term_expanders.len() => {}
            CodePtr::Local(LocalCodePtr::UserTermExpansion(_)) => self.fail = true,
            CodePtr::Local(LocalCodePtr::UserGoalExpansion(p))
                if p < code_repo.goal_expanders.len() => {}
            CodePtr::Local(LocalCodePtr::UserGoalExpansion(_)) => self.fail = true,
            CodePtr::Local(LocalCodePtr::InSituDirEntry(p)) if p < code_repo.in_situ_code.len() => {
            }
            CodePtr::Local(_) | CodePtr::REPL(..) => return false,
            CodePtr::DynamicTransaction(..) => {
                // prevent use of dynamic transactions from
                // succeeding in expansions. self.fail will be toggled
                // back to false later.
                self.fail = true;
                return false;
            }
            _ => {}
        }

        true
    }

    // return true iff verify_attr_interrupt is called.
    fn verify_attr_stepper(
        &mut self,
        indices: &mut IndexStore,
        policies: &mut MachinePolicies,
        code_repo: &mut CodeRepo,
        prolog_stream: &mut PrologStream,
    ) -> bool {
        loop {
            let instr = match code_repo.lookup_instr(self.last_call, &self.p) {
                Some(instr) => {
                    if instr.as_ref().is_head_instr() {
                        instr
                    } else {
                        let cp = self.p.local();
                        self.run_verify_attr_interrupt(cp);
                        return true;
                    }
                }
                None => return false,
            };

            self.dispatch_instr(instr.as_ref(), indices, policies, code_repo, prolog_stream);

            if self.fail {
                self.backtrack();
            }

            if !self.check_machine_index(code_repo) {
                return false;
            }
        }
    }

    fn run_verify_attr_interrupt(&mut self, cp: LocalCodePtr) {
        let p = self.attr_var_init.verify_attrs_loc;

        self.attr_var_init.cp = cp;
        self.verify_attr_interrupt(p);
    }

    fn query_stepper(
        &mut self,
        indices: &mut IndexStore,
        policies: &mut MachinePolicies,
        code_repo: &mut CodeRepo,
        prolog_stream: &mut PrologStream,
    ) {
        loop {
            self.execute_instr(indices, policies, code_repo, prolog_stream);

            if self.fail {
                self.backtrack();
            }

            match self.p {
                CodePtr::VerifyAttrInterrupt(_) => {
                    self.p = CodePtr::Local(self.attr_var_init.cp + 1);

                    if !self.verify_attr_stepper(indices, policies, code_repo, prolog_stream) {
                        if self.fail {
                            break;
                        }

                        let cp = self.p.local();
                        self.run_verify_attr_interrupt(cp);
                    }
                }
                _ => {
                    if !self.check_machine_index(code_repo) {
                        break;
                    }
                }
            }
        }
    }
}
