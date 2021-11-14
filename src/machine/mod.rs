pub mod arithmetic_ops;
pub mod attributed_variables;
pub mod code_repo;
pub mod code_walker;
#[macro_use]
pub mod loader;
pub mod compile;
pub mod copier;
pub mod gc;
pub mod heap;
pub mod load_state;
pub mod machine_errors;
pub mod machine_indices;
pub mod machine_state;
pub mod machine_state_impl;
pub mod mock_wam;
pub mod partial_string;
pub mod preprocessor;
pub mod stack;
pub mod streams;
pub mod system_calls;
pub mod term_stream;

use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::code_repo::*;
use crate::machine::compile::*;
use crate::machine::heap::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::streams::*;
use crate::types::*;

use indexmap::IndexMap;

use lazy_static::lazy_static;

use std::env;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;

lazy_static! {
    pub static ref INTERRUPT: AtomicBool = AtomicBool::new(false);
}

#[derive(Debug)]
pub struct Machine {
    pub(super) machine_st: MachineState,
    pub(super) inner_heap: Heap,
    pub(super) policies: MachinePolicies,
    pub(super) indices: IndexStore,
    pub(super) code_repo: CodeRepo,
    pub(super) user_input: Stream,
    pub(super) user_output: Stream,
    pub(super) user_error: Stream,
    pub(super) load_contexts: Vec<LoadContext>,
}

#[derive(Debug)]
pub(crate) struct MachinePolicies {
    call_policy: Box<dyn CallPolicy>,
    cut_policy: Box<dyn CutPolicy>,
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

impl Default for MachinePolicies {
    #[inline]
    fn default() -> Self {
        MachinePolicies::new()
    }
}

#[derive(Debug)]
pub struct LoadContext {
    pub(super) path: PathBuf,
    pub(super) stream: Stream,
    pub(super) module: Atom,
}

impl LoadContext {
    #[inline]
    fn new(path: &str, stream: Stream) -> Self {
        let mut path_buf = PathBuf::from(path);

        if path_buf.is_relative() {
            let mut current_dir = current_dir();
            current_dir.push(path_buf);
            path_buf = current_dir;
        }

        LoadContext {
            path: path_buf,
            stream,
            module: atom!("user"),
        }
    }
}

#[inline]
fn current_dir() -> PathBuf {
    env::current_dir().unwrap_or(PathBuf::from("./"))
}

include!(concat!(env!("OUT_DIR"), "/libraries.rs"));

pub struct MachinePreludeView<'a> {
    pub indices: &'a mut IndexStore,
    pub code_repo: &'a mut CodeRepo,
    pub load_contexts: &'a mut Vec<LoadContext>,
}

impl Machine {
    #[inline]
    pub fn prelude_view_and_machine_st(&mut self) -> (MachinePreludeView, &mut MachineState) {
        (
            MachinePreludeView {
                indices: &mut self.indices,
                code_repo: &mut self.code_repo,
                load_contexts: &mut self.load_contexts,
            },
            &mut self.machine_st
        )
    }

    pub fn throw_session_error(&mut self, err: SessionError, key: PredicateKey) {
        let err = self.machine_st.session_error(err);
        let stub = functor_stub(key.0, key.1);
        let err = self.machine_st.error_form(err, stub);

        self.machine_st.throw_exception(err);
        return;
    }
}

impl Machine {
    fn run_module_predicate(&mut self, module_name: Atom, key: PredicateKey) {
        if let Some(module) = self.indices.modules.get(&module_name) {
            if let Some(ref code_index) = module.code_dir.get(&key) {
                let p = code_index.local().unwrap();

                self.machine_st.cp = LocalCodePtr::Halt;
                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p));

                return self.run_query();
            }
        }

        unreachable!();
    }

    pub fn load_file(&mut self, path: &str, stream: Stream) {
        self.machine_st.registers[1] = stream_as_cell!(stream);
        self.machine_st.registers[2] = atom_as_cell!(
            self.machine_st.atom_tbl.build_with(path)
        );

        self.run_module_predicate(atom!("loader"), (atom!("file_load"), 2));
    }

    fn load_top_level(&mut self) {
        let mut path_buf = current_dir();

        path_buf.push("src/toplevel.pl");

        let path = path_buf.to_str().unwrap();
        let toplevel_stream = Stream::from_static_string(
            include_str!("../toplevel.pl"),
            &mut self.machine_st.arena,
        );

        self.load_file(path, toplevel_stream);

        if let Some(toplevel) = self.indices.modules.get(&atom!("$toplevel")) {
            load_module(
                &mut self.indices.code_dir,
                &mut self.indices.op_dir,
                &mut self.indices.meta_predicates,
                &CompilationTarget::User,
                toplevel,
            );
        } else {
            unreachable!()
        }
    }

    fn load_special_forms(&mut self) {
        let mut path_buf = current_dir();
        path_buf.push("machine/attributed_variables.pl");

        bootstrapping_compile(
            Stream::from_static_string(
                include_str!("attributed_variables.pl"),
                &mut self.machine_st.arena,
            ),
            self,
            ListingSource::from_file_and_path(
                atom!("attributed_variables"),
                path_buf,
            ),
        )
        .unwrap();

        let mut path_buf = current_dir();
        path_buf.push("machine/project_attributes.pl");

        bootstrapping_compile(
            Stream::from_static_string(
                include_str!("project_attributes.pl"),
                &mut self.machine_st.arena,
            ),
            self,
            ListingSource::from_file_and_path(atom!("project_attributes"), path_buf),
        )
        .unwrap();

        if let Some(module) = self.indices.modules.get(&atom!("$atts")) {
            if let Some(code_index) = module.code_dir.get(&(atom!("driver"), 2)) {
                self.machine_st.attr_var_init.verify_attrs_loc = code_index.local().unwrap();
            }
        }
    }

    pub fn run_top_level(&mut self) {
        let mut arg_pstrs = vec![];

        for arg in env::args() {
            arg_pstrs.push(put_complete_string(
                &mut self.machine_st.heap,
                &arg,
                &mut self.machine_st.atom_tbl,
            ));
        }

        self.machine_st.registers[1] = heap_loc_as_cell!(
            iter_to_heap_list(&mut self.machine_st.heap, arg_pstrs.into_iter())
        );

        self.run_module_predicate(atom!("$toplevel"), (atom!("$repl"), 1));
    }

    pub(crate) fn configure_modules(&mut self) {
        fn update_call_n_indices(loader: &Module, target_code_dir: &mut CodeDir) {
            for arity in 1..66 {
                let key = (atom!("call"), arity);

                match loader.code_dir.get(&key) {
                    Some(src_code_index) => {
                        let target_code_index = target_code_dir
                            .entry(key)
                            .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined));

                        target_code_index.set(src_code_index.get());
                    }
                    None => {
                        unreachable!();
                    }
                }
            }
        }

        if let Some(loader) = self.indices.modules.swap_remove(&atom!("loader")) {
            if let Some(builtins) = self.indices.modules.get_mut(&atom!("builtins")) {
                // Import loader's exports into the builtins module so they will be
                // implicitly included in every further module.
                load_module(
                    &mut builtins.code_dir,
                    &mut builtins.op_dir,
                    &mut builtins.meta_predicates,
                    &CompilationTarget::Module(atom!("builtins")),
                    &loader,
                );

                for export in &loader.module_decl.exports {
                    builtins.module_decl.exports.push(export.clone());
                }

                for arity in 10..66 {
                    builtins
                        .module_decl
                        .exports
                        .push(ModuleExport::PredicateKey((atom!("call"), arity)));
                }
            }

            for (_, target_module) in self.indices.modules.iter_mut() {
                update_call_n_indices(&loader, &mut target_module.code_dir);
            }

            update_call_n_indices(&loader, &mut self.indices.code_dir);

            self.indices.modules.insert(atom!("loader"), loader);
        } else {
            unreachable!()
        }
    }

    pub fn new() -> Self {
        use ref_thread_local::RefThreadLocal;

        let mut machine_st = MachineState::new();

        let user_input = Stream::stdin(&mut machine_st.arena);
        let user_output = Stream::stdout(&mut machine_st.arena);
        let user_error = Stream::stderr(&mut machine_st.arena);

        let mut wam = Machine {
            machine_st,
            inner_heap: Heap::new(),
            policies: MachinePolicies::new(),
            indices: IndexStore::new(),
            code_repo: CodeRepo::new(),
            user_input,
            user_output,
            user_error,
            load_contexts: vec![],
        };

        let mut lib_path = current_dir();

        lib_path.pop();
        lib_path.push("lib");

        bootstrapping_compile(
            Stream::from_static_string(
                LIBRARIES.borrow()["ops_and_meta_predicates"],
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(
                atom!("ops_and_meta_predicates.pl"),
                lib_path.clone(),
            ),
        )
        .unwrap();

        bootstrapping_compile(
            Stream::from_static_string(
                LIBRARIES.borrow()["builtins"],
                &mut wam.machine_st.arena,
            ),
            &mut wam,
            ListingSource::from_file_and_path(atom!("builtins.pl"), lib_path.clone()),
        )
        .unwrap();

        if let Some(builtins) = wam.indices.modules.get(&atom!("builtins")) {
            load_module(
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                builtins,
            );
        } else {
            unreachable!()
        }

        lib_path.pop(); // remove the "lib" at the end

        bootstrapping_compile(
            Stream::from_static_string(include_str!("../loader.pl"), &mut wam.machine_st.arena),
            &mut wam,
            ListingSource::from_file_and_path(atom!("loader.pl"), lib_path.clone()),
        )
        .unwrap();

        wam.configure_modules();

        if let Some(loader) = wam.indices.modules.get(&atom!("loader")) {
            load_module(
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                loader,
            );
        } else {
            unreachable!()
        }

        wam.load_special_forms();
        wam.load_top_level();
        wam.configure_streams();

        wam
    }

    pub(crate) fn configure_streams(&mut self) {
        self.user_input.options_mut().set_alias_to_atom_opt(Some(atom!("user_input")));

        self.indices
            .stream_aliases
            .insert(atom!("user_input"), self.user_input);

        self.indices.streams.insert(self.user_input);

        self.user_output.options_mut().set_alias_to_atom_opt(Some(atom!("user_output")));

        self.indices
            .stream_aliases
            .insert(atom!("user_output"), self.user_output);

        self.indices.streams.insert(self.user_output);
    }

    fn handle_toplevel_command(&mut self, code_ptr: REPLCodePtr, p: LocalCodePtr) {
        match code_ptr {
            REPLCodePtr::AddDiscontiguousPredicate => {
                self.add_discontiguous_predicate();
            }
            REPLCodePtr::AddDynamicPredicate => {
                self.add_dynamic_predicate();
            }
            REPLCodePtr::AddMultifilePredicate => {
                self.add_multifile_predicate();
            }
            REPLCodePtr::AddGoalExpansionClause => {
                self.add_goal_expansion_clause();
            }
            REPLCodePtr::AddTermExpansionClause => {
                self.add_term_expansion_clause();
            }
            REPLCodePtr::AddInSituFilenameModule => {
                self.add_in_situ_filename_module();
            }
            REPLCodePtr::ClauseToEvacuable => {
                self.clause_to_evacuable();
            }
            REPLCodePtr::ScopedClauseToEvacuable => {
                self.scoped_clause_to_evacuable();
            }
            REPLCodePtr::ConcludeLoad => {
                self.conclude_load();
            }
            REPLCodePtr::PopLoadContext => {
                self.pop_load_context();
            }
            REPLCodePtr::PushLoadContext => {
                self.push_load_context();
            }
            REPLCodePtr::PopLoadStatePayload => {
                self.pop_load_state_payload();
            }
            REPLCodePtr::UseModule => {
                self.use_module();
            }
            REPLCodePtr::LoadCompiledLibrary => {
                self.load_compiled_library();
            }
            REPLCodePtr::DeclareModule => {
                self.declare_module();
            }
            REPLCodePtr::PushLoadStatePayload => {
                self.push_load_state_payload();
            }
            REPLCodePtr::LoadContextSource => {
                self.load_context_source();
            }
            REPLCodePtr::LoadContextFile => {
                self.load_context_file();
            }
            REPLCodePtr::LoadContextDirectory => {
                self.load_context_directory();
            }
            REPLCodePtr::LoadContextModule => {
                self.load_context_module();
            }
            REPLCodePtr::LoadContextStream => {
                self.load_context_stream();
            }
            REPLCodePtr::MetaPredicateProperty => {
                self.meta_predicate_property();
            }
            REPLCodePtr::BuiltInProperty => {
                self.builtin_property();
            }
            REPLCodePtr::MultifileProperty => {
                self.multifile_property();
            }
            REPLCodePtr::DiscontiguousProperty => {
                self.discontiguous_property();
            }
            REPLCodePtr::DynamicProperty => {
                self.dynamic_property();
            }
            REPLCodePtr::Assertz => {
                self.compile_assert(AppendOrPrepend::Append);
            }
            REPLCodePtr::Asserta => {
                self.compile_assert(AppendOrPrepend::Prepend);
            }
            REPLCodePtr::Retract => {
                self.retract_clause();
            }
            REPLCodePtr::AbolishClause => {
                self.abolish_clause();
            }
            REPLCodePtr::IsConsistentWithTermQueue => {
                self.is_consistent_with_term_queue();
            }
            REPLCodePtr::FlushTermQueue => {
                self.flush_term_queue();
            }
            REPLCodePtr::RemoveModuleExports => {
                self.remove_module_exports();
            }
            REPLCodePtr::AddNonCountedBacktracking => {
                self.add_non_counted_backtracking();
            }
        }

        self.machine_st.p = CodePtr::Local(p);
    }

    pub(crate) fn run_query(&mut self) {
        while !self.machine_st.p.is_halt() {
            self.machine_st.query_stepper(
                &mut self.indices,
                &mut self.policies,
                &mut self.code_repo,
                &mut self.user_input,
                &mut self.user_output,
            );

            match self.machine_st.p {
                CodePtr::REPL(code_ptr, p) => {
                    self.handle_toplevel_command(code_ptr, p);

                    if self.machine_st.fail {
                        self.machine_st.backtrack();
                    }
                }
                _ => {
                    break;
                }
            };
        }
    }
}

impl MachineState {
    fn dispatch_instr(
        &mut self,
        instr: &Line,
        indices: &mut IndexStore,
        policies: &mut MachinePolicies,
        code_repo: &CodeRepo,
        user_input: &mut Stream,
        user_output: &mut Stream,
    ) {
        match instr {
            &Line::Arithmetic(ref arith_instr) => self.execute_arith_instr(arith_instr),
            &Line::Choice(ref choice_instr) => self.execute_choice_instr(
                choice_instr,
                code_repo,
                &mut policies.call_policy,
                &mut indices.global_variables,
            ),
            &Line::Cut(ref cut_instr) => {
                self.execute_cut_instr(cut_instr, &mut policies.cut_policy)
            }
            &Line::Control(ref control_instr) => self.execute_ctrl_instr(
                indices,
                code_repo,
                &mut policies.call_policy,
                &mut policies.cut_policy,
                user_input,
                user_output,
                control_instr,
            ),
            &Line::Fact(ref fact_instr) => {
                self.execute_fact_instr(&fact_instr);
                self.p += 1;
            }
            &Line::IndexingCode(ref indexing_lines) => {
                self.execute_indexing_instr(indexing_lines, code_repo)
            }
            &Line::IndexedChoice(ref choice_instr) => self.execute_indexed_choice_instr(
                choice_instr,
                &mut policies.call_policy,
                &mut indices.global_variables,
            ),
            &Line::DynamicIndexedChoice(_) => self.execute_dynamic_indexed_choice_instr(
                code_repo,
                &mut policies.call_policy,
                &mut indices.global_variables,
            ),
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
        user_input: &mut Stream,
        user_output: &mut Stream,
    ) {
        let instr = match code_repo.lookup_instr(self.last_call, &self.p) {
            Some(instr) => instr,
            None => return,
        };

        self.dispatch_instr(
            instr.as_ref(),
            indices,
            policies,
            code_repo,
            user_input,
            user_output,
        );
    }

    fn backtrack(&mut self) {
        let b = self.b;

        self.b0 = self.stack.index_or_frame(b).prelude.b0;
        self.p = CodePtr::Local(self.stack.index_or_frame(b).prelude.bp);

        self.pdl.clear();
        self.fail = false;
    }

    fn check_machine_index(&mut self, code_repo: &CodeRepo) -> bool {
        match self.p {
            CodePtr::Local(LocalCodePtr::DirEntry(p)) |
            CodePtr::Local(LocalCodePtr::IndexingBuf(p, ..))
                if p < code_repo.code.len() => {}
            CodePtr::Local(LocalCodePtr::Halt) | CodePtr::REPL(..) => {
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
        user_input: &mut Stream,
        user_output: &mut Stream,
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

            self.dispatch_instr(
                instr.as_ref(),
                indices,
                policies,
                code_repo,
                user_input,
                user_output,
            );

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
        user_input: &mut Stream,
        user_output: &mut Stream,
    ) {
        loop {
            self.execute_instr(indices, policies, code_repo, user_input, user_output);

            if self.fail {
                self.backtrack();
            }

            match self.p {
                CodePtr::VerifyAttrInterrupt(_) => {
                    self.p = CodePtr::Local(self.attr_var_init.cp);

                    let instigating_p = CodePtr::Local(self.attr_var_init.instigating_p);
                    let instigating_instr = code_repo
                        .lookup_instr(false, &instigating_p)
                        .unwrap();

                    if !instigating_instr.as_ref().is_head_instr() {
                        let cp = self.p.local();
                        self.run_verify_attr_interrupt(cp);
                    } else if !self.verify_attr_stepper(
                        indices,
                        policies,
                        code_repo,
                        user_input,
                        user_output,
                    ) {
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
