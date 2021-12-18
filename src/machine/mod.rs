pub mod arithmetic_ops;
pub mod attributed_variables;
pub mod code_repo;
pub mod code_walker;
#[macro_use]
pub mod loader;
pub mod compile;
pub mod copier;
pub mod dispatch;
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

use crate::arena::*;
use crate::atom_table::*;
use crate::clause_types::*;
use crate::forms::*;
use crate::machine::code_repo::*;
use crate::machine::compile::*;
use crate::machine::copier::*;
use crate::machine::heap::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::stack::*;
use crate::machine::streams::*;
use crate::parser::ast::*;
use crate::parser::rug::{Integer, Rational};
use crate::types::*;

use indexmap::IndexMap;
use lazy_static::lazy_static;
use ordered_float::OrderedFloat;

use std::cmp::Ordering;
use std::env;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;

lazy_static! {
    pub static ref INTERRUPT: AtomicBool = AtomicBool::new(false);
}

#[derive(Debug)]
pub struct Machine {
    pub(super) machine_st: MachineState,
    pub(super) indices: IndexStore,
    pub(super) code_repo: CodeRepo,
    pub(super) user_input: Stream,
    pub(super) user_output: Stream,
    pub(super) user_error: Stream,
    pub(super) load_contexts: Vec<LoadContext>,
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

        self.indices
            .stream_aliases
            .insert(atom!("user_error"), self.user_error);

        self.indices.streams.insert(self.user_error);
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
            self.query_stepper();

            match self.machine_st.p {
                CodePtr::REPL(code_ptr, p) => {
                    self.handle_toplevel_command(code_ptr, p);

                    if self.machine_st.fail {
                        self.backtrack();
                    }
                }
                _ => {
                    break;
                }
            };
        }
    }

    fn execute_instr(&mut self) {
        let instr = match self.code_repo.lookup_instr(&self.machine_st, &self.machine_st.p) {
            Some(instr) => instr,
            None => return,
        };

        self.dispatch_instr(instr);
    }

    fn backtrack(&mut self) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);

        self.machine_st.b0 = or_frame.prelude.b0;
        self.machine_st.p = CodePtr::Local(or_frame.prelude.bp);

        self.machine_st.oip = or_frame.prelude.boip;
        self.machine_st.iip = or_frame.prelude.biip;

        self.machine_st.pdl.clear();
        self.machine_st.fail = false;
    }

    fn check_machine_index(&mut self) -> bool {
        match self.machine_st.p {
            CodePtr::Local(LocalCodePtr::DirEntry(p))
                if p < self.code_repo.code.len() => {}
            CodePtr::Local(LocalCodePtr::Halt) | CodePtr::REPL(..) => {
                return false;
            }
            _ => {}
        }

        true
    }

    // return true iff verify_attr_interrupt is called.
    fn verify_attr_stepper(&mut self) -> bool {
        loop {
            let instr = match self.code_repo.lookup_instr(&self.machine_st, &self.machine_st.p) {
                Some(instr) => {
                    if instr.as_ref(&self.code_repo.code).is_head_instr() {
                        instr
                    } else {
                        let cp = self.machine_st.p.local();
                        self.run_verify_attr_interrupt(cp);
                        return true;
                    }
                }
                None => return false,
            };

            self.dispatch_instr(instr);

            if self.machine_st.fail {
                self.backtrack();
            }

            if !self.check_machine_index() {
                return false;
            }
        }
    }

    fn run_verify_attr_interrupt(&mut self, cp: LocalCodePtr) {
        let p = self.machine_st.attr_var_init.verify_attrs_loc;

        self.machine_st.attr_var_init.cp = cp;
        self.machine_st.verify_attr_interrupt(p);
    }

    fn query_stepper(&mut self) {
        loop {
            self.execute_instr();

            if self.machine_st.fail {
                self.backtrack();
            }

            match self.machine_st.p {
                CodePtr::VerifyAttrInterrupt(_) => {
                    self.machine_st.p = CodePtr::Local(self.machine_st.attr_var_init.cp);

                    let instigating_p = CodePtr::Local(self.machine_st.attr_var_init.instigating_p);
                    let instigating_instr = self.code_repo
                        .lookup_instr(&self.machine_st, &instigating_p)
                        .unwrap();

                    if !instigating_instr.as_ref(&self.code_repo.code).is_head_instr() {
                        let cp = self.machine_st.p.local();
                        self.run_verify_attr_interrupt(cp);
                    } else if !self.verify_attr_stepper() {
                        if self.machine_st.fail {
                            break;
                        }

                        let cp = self.machine_st.p.local();
                        self.run_verify_attr_interrupt(cp);
                    }
                }
                _ => {
                    if !self.check_machine_index() {
                        break;
                    }
                }
            }
        }
    }

    pub fn execute_inlined(&mut self, inlined: &InlinedClauseType) {
        match inlined {
            &InlinedClauseType::CompareNumber(cmp, ref at_1, ref at_2) => {
                let n1 = try_or_fail!(self.machine_st, self.machine_st.get_number(at_1));
                let n2 = try_or_fail!(self.machine_st, self.machine_st.get_number(at_2));

                self.machine_st.compare_numbers(cmp, n1, n2);
            }
            &InlinedClauseType::IsAtom(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity == 0 {
                            self.machine_st.p += 1;
                        } else {
                            self.machine_st.fail = true;
                        }
                    }
                    (HeapCellValueTag::Char) => {
                        self.machine_st.p += 1;
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsAtomic(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Char | HeapCellValueTag::Fixnum | HeapCellValueTag::F64 |
                     HeapCellValueTag::Cons) => {
                        self.machine_st.p += 1;
                    }
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity == 0 {
                            self.machine_st.p += 1;
                        } else {
                            self.machine_st.fail = true;
                        }
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsInteger(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                match Number::try_from(d) {
                    Ok(Number::Fixnum(_)) => {
                        self.machine_st.p += 1;
                    }
                    Ok(Number::Integer(_)) => {
                        self.machine_st.p += 1;
                    }
                    Ok(Number::Rational(n)) => {
                        if n.denom() == &1 {
                            self.machine_st.p += 1;
                        } else {
                            self.machine_st.fail = true;
                        }
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsCompound(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Str | HeapCellValueTag::Lis |
                     HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr) => {
                        self.machine_st.p += 1;
                    }
                    (HeapCellValueTag::Atom, (_name, arity)) => {
                        if arity > 0 {
                            self.machine_st.p += 1;
                        } else {
                            self.machine_st.fail = true;
                        }
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsFloat(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                match Number::try_from(d) {
                    Ok(Number::Float(_)) => {
                        self.machine_st.p += 1;
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsNumber(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                match Number::try_from(d) {
                    Ok(Number::Fixnum(_)) => {
                        self.machine_st.p += 1;
                    }
                    Ok(Number::Integer(_)) => {
                        self.machine_st.p += 1;
                    }
                    Ok(Number::Rational(n)) => {
                        if n.denom() == &1 {
                            self.machine_st.p += 1;
                        } else {
                            self.machine_st.fail = true;
                        }
                    }
                    Ok(Number::Float(_)) => {
                        self.machine_st.p += 1;
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                }
            }
            &InlinedClauseType::IsRational(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                read_heap_cell!(d,
                    (HeapCellValueTag::Cons, ptr) => {
                        match_untyped_arena_ptr!(ptr,
                             (ArenaHeaderTag::Rational, _r) => {
                                 self.machine_st.p += 1;
                             }
                             _ => {
                                 self.machine_st.fail = true;
                             }
                        );
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                );
            }
            &InlinedClauseType::IsNonVar(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                match d.get_tag() {
                    HeapCellValueTag::AttrVar
                    | HeapCellValueTag::Var
                    | HeapCellValueTag::StackVar => {
                        self.machine_st.fail = true;
                    }
                    _ => {
                        self.machine_st.p += 1;
                    }
                }
            }
            &InlinedClauseType::IsVar(r1) => {
                let d = self.machine_st.store(self.machine_st.deref(self.machine_st[r1]));

                match d.get_tag() {
                    HeapCellValueTag::AttrVar |
                    HeapCellValueTag::Var |
                    HeapCellValueTag::StackVar => {
                        self.machine_st.p += 1;
                    }
                    _ => {
                        self.machine_st.fail = true;
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub(super) fn execute_dynamic_indexed_choice_instr(&mut self) {
        let p = self.machine_st.p.local();

        match self.find_living_dynamic(self.machine_st.oip, self.machine_st.iip) {
            Some((offset, oi, ii, is_next_clause)) => {
                self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(p.abs_loc()));
                self.machine_st.oip = oi;
                self.machine_st.iip = ii;

                match self.machine_st.dynamic_mode {
                    FirstOrNext::First if !is_next_clause => {
                        self.machine_st.p =
                            CodePtr::Local(LocalCodePtr::DirEntry(p.abs_loc() + offset));
                    }
                    FirstOrNext::First => {
                        // there's a leading DynamicElse that sets self.machine_st.cc.
                        // self.machine_st.cc = self.machine_st.global_clock;

                        // see that there is a following dynamic_else
                        // clause so we avoid generating a choice
                        // point in case there isn't.
                        match self.find_living_dynamic(oi, ii + 1) {
                            Some(_) => {
                                self.machine_st.registers[self.machine_st.num_of_args + 1] =
                                    fixnum_as_cell!(Fixnum::build_with(self.machine_st.cc as i64));

                                self.machine_st.num_of_args += 2;
                                self.machine_st.indexed_try(offset);
                                self.machine_st.num_of_args -= 2;
                            }
                            None => {
                                self.machine_st.p =
                                    CodePtr::Local(LocalCodePtr::DirEntry(p.abs_loc() + offset));
                                self.machine_st.oip = 0;
                                self.machine_st.iip = 0;
                            }
                        }
                    }
                    FirstOrNext::Next => {
                        let b = self.machine_st.b;
                        let n = self.machine_st
                            .stack
                            .index_or_frame(b)
                            .prelude
                            .univ_prelude
                            .num_cells;

                        self.machine_st.cc = cell_as_fixnum!(
                            self.machine_st.stack[stack_loc!(OrFrame, b, n-2)]
                        ).get_num() as usize;

                        if is_next_clause {
                            match self.find_living_dynamic(self.machine_st.oip, self.machine_st.iip) {
                                Some(_) => {
                                    self.retry(offset);

                                    try_or_fail!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                                None => {
                                    self.trust(offset);

                                    try_or_fail!(
                                        self.machine_st,
                                        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                                    );
                                }
                            }
                        } else {
                            self.trust(offset);

                            try_or_fail!(
                                self.machine_st,
                                (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
                            );
                        }
                    }
                }
            }
            None => {
                self.machine_st.fail = true;
            }
        }

        self.machine_st.dynamic_mode = FirstOrNext::Next;
    }

    #[inline(always)]
    fn retry_me_else(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            self.machine_st.registers[i + 1] = or_frame[i];
        }

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        or_frame.prelude.bp = self.machine_st.p.local() + offset;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;
        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;

        self.machine_st.attr_var_init.reset();
        self.machine_st.hb = self.machine_st.heap.len();
        self.machine_st.p += 1;

        self.unwind_trail(old_tr, curr_tr);

        self.machine_st.trail.truncate(self.machine_st.tr);
        self.machine_st.heap.truncate(target_h);
    }

    #[inline(always)]
    fn retry(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            self.machine_st.registers[i+1] = or_frame[i];
        }

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        // WAS: or_frame.prelude.bp = self.machine_st.p.local() + 1;
        or_frame.prelude.biip += 1;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;
        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;
        self.machine_st.attr_var_init.reset();

        self.unwind_trail(old_tr, curr_tr);

        self.machine_st.trail.truncate(self.machine_st.tr);
        self.machine_st.heap.truncate(target_h);

        self.machine_st.hb = self.machine_st.heap.len();
        self.machine_st.p = CodePtr::Local(dir_entry!(self.machine_st.p.local().abs_loc() + offset));

        self.machine_st.oip = 0;
        self.machine_st.iip = 0;
    }

    #[inline(always)]
    fn trust(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            self.machine_st.registers[i+1] = or_frame[i];
        }

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;
        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;

        self.machine_st.attr_var_init.reset();
        self.machine_st.b = or_frame.prelude.b;

        self.unwind_trail(old_tr, curr_tr);

        self.machine_st.trail.truncate(self.machine_st.tr);
        self.machine_st.stack.truncate(b);
        self.machine_st.heap.truncate(target_h);

        self.machine_st.hb = self.machine_st.heap.len();
        self.machine_st.p = CodePtr::Local(dir_entry!(self.machine_st.p.local().abs_loc() + offset));

        self.machine_st.oip = 0;
        self.machine_st.iip = 0;
    }

    #[inline(always)]
    fn trust_me(&mut self) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.univ_prelude.num_cells;

        for i in 0..n {
            self.machine_st.registers[i+1] = or_frame[i];
        }

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;
        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;

        self.machine_st.attr_var_init.reset();
        self.machine_st.b = or_frame.prelude.b;

        self.unwind_trail(old_tr, curr_tr);

        self.machine_st.trail.truncate(self.machine_st.tr);
        self.machine_st.stack.truncate(b);
        self.machine_st.heap.truncate(target_h);

        self.machine_st.hb = self.machine_st.heap.len();
        self.machine_st.p += 1;
    }

    #[inline(always)]
    fn context_call(&mut self, name: Atom, arity: usize, idx: CodeIndex) -> CallResult {
        if self.machine_st.last_call {
            self.try_execute(name, arity, idx)
        } else {
            self.try_call(name, arity, idx)
        }
    }

    #[inline(always)]
    fn try_call(&mut self, name: Atom, arity: usize, idx: CodeIndex) -> CallResult {
        match idx.get() {
            IndexPtr::DynamicUndefined => {
                self.machine_st.fail = true;
                return Ok(());
            }
            IndexPtr::Undefined => {
                return Err(self.machine_st.throw_undefined_error(name, arity));
            }
            IndexPtr::DynamicIndex(compiled_tl_index) => {
                self.machine_st.dynamic_mode = FirstOrNext::First;
                self.machine_st.call_at_index(arity, dir_entry!(compiled_tl_index));
            }
            IndexPtr::Index(compiled_tl_index) => {
                self.machine_st.call_at_index(arity, dir_entry!(compiled_tl_index));
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn try_execute(&mut self, name: Atom, arity: usize, idx: CodeIndex) -> CallResult {
        match idx.get() {
            IndexPtr::DynamicUndefined => {
                self.machine_st.fail = true;
                return Ok(());
            }
            IndexPtr::Undefined => {
                return Err(self.machine_st.throw_undefined_error(name, arity));
            }
            IndexPtr::DynamicIndex(compiled_tl_index) => {
                self.machine_st.dynamic_mode = FirstOrNext::First;
                self.machine_st.execute_at_index(arity, dir_entry!(compiled_tl_index));
            }
            IndexPtr::Index(compiled_tl_index) => {
                self.machine_st.execute_at_index(arity, dir_entry!(compiled_tl_index))
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn call_builtin(&mut self, ct: &BuiltInClauseType) -> CallResult {
        match ct {
            &BuiltInClauseType::AcyclicTerm => {
                let addr = self.machine_st.registers[1];
                self.machine_st.fail = self.machine_st.is_cyclic_term(addr);
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Arg => {
                self.machine_st.try_arg()?;
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Compare => {
                let stub_gen = || functor_stub(atom!("compare"), 3);

                let a1 = self.machine_st.store(self.machine_st.deref(self.machine_st.registers[1]));
                let a2 = self.machine_st.registers[2];
                let a3 = self.machine_st.registers[3];

                read_heap_cell!(a1,
                    (HeapCellValueTag::Str, s) => {
                        let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                            .get_name_and_arity();

                        match name {
                            atom!(">") | atom!("<") | atom!("=") if arity == 2 => {
                            }
                            _ => {
                                let err = self.machine_st.domain_error(DomainErrorType::Order, a1);
                                return Err(self.machine_st.error_form(err, stub_gen()));
                            }
                        }
                    }
                    (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                    }
                    _ => {
                        let err = self.machine_st.type_error(ValidType::Atom, a1);
                        return Err(self.machine_st.error_form(err, stub_gen()));
                    }
                );

                let atom = match compare_term_test!(self.machine_st, a2, a3) {
                    Some(Ordering::Greater) => {
                        atom!(">")
                    }
                    Some(Ordering::Equal) => {
                        atom!("=")
                    }
                    None | Some(Ordering::Less) => {
                        atom!("<")
                    }
                };

                self.machine_st.unify_atom(atom, a1);
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::CompareTerm(qt) => {
                self.machine_st.compare_term(qt);
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Read => {
                let stream = self.machine_st.get_stream_or_alias(
                    self.machine_st.registers[1],
                    &self.indices.stream_aliases,
                    atom!("read"),
                    2,
                )?;

                match self.machine_st.read(stream, &self.indices.op_dir) {
                    Ok(offset) => {
                        let value = self.machine_st.registers[2];
                        unify_fn!(&mut self.machine_st, value, heap_loc_as_cell!(offset.heap_loc));
                    }
                    Err(ParserError::UnexpectedEOF) => {
                        let value = self.machine_st.registers[2];
                        self.machine_st.unify_atom(atom!("end_of_file"), value);
                    }
                    Err(e) => {
                        let stub = functor_stub(atom!("read"), 2);
                        let err = self.machine_st.syntax_error(e);

                        return Err(self.machine_st.error_form(err, stub));
                    }
                };

                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::CopyTerm => {
                self.machine_st.copy_term(AttrVarPolicy::DeepCopy);
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Eq => {
                let a1 = self.machine_st.registers[1];
                let a2 = self.machine_st.registers[2];

                self.machine_st.fail = self.machine_st.eq_test(a1, a2);
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Ground => {
                self.machine_st.fail = self.machine_st.ground_test();
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Functor => {
                self.machine_st.try_functor()?;
                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::NotEq => {
                let a1 = self.machine_st.registers[1];
                let a2 = self.machine_st.registers[2];

                self.machine_st.fail =
                    if let Some(Ordering::Equal) = compare_term_test!(self.machine_st, a1, a2) {
                        true
                    } else {
                        false
                    };

                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Sort => {
                self.machine_st.check_sort_errors()?;

                let stub_gen = || functor_stub(atom!("sort"), 2);
                let mut list = self.machine_st.try_from_list(self.machine_st.registers[1], stub_gen)?;

                list.sort_unstable_by(|v1, v2| {
                    compare_term_test!(self.machine_st, *v1, *v2).unwrap_or(Ordering::Less)
                });

                list.dedup_by(|v1, v2| {
                    compare_term_test!(self.machine_st, *v1, *v2) == Some(Ordering::Equal)
                });

                let heap_addr = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.machine_st.heap, list.into_iter())
                );

                let r2 = self.machine_st.registers[2];
                unify_fn!(&mut self.machine_st, r2, heap_addr);

                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::KeySort => {
                self.machine_st.check_keysort_errors()?;

                let stub_gen = || functor_stub(atom!("keysort"), 2);
                let list = self.machine_st.try_from_list(self.machine_st.registers[1], stub_gen)?;

                let mut key_pairs = Vec::with_capacity(list.len());

                for val in list {
                    let key = self.machine_st.project_onto_key(val)?;
                    key_pairs.push((key, val));
                }

                key_pairs.sort_by(|a1, a2| {
                    compare_term_test!(self.machine_st, a1.0, a2.0).unwrap_or(Ordering::Less)
                });

                let key_pairs = key_pairs.into_iter().map(|kp| kp.1);
                let heap_addr = heap_loc_as_cell!(
                    iter_to_heap_list(&mut self.machine_st.heap, key_pairs)
                );

                let r2 = self.machine_st.registers[2];
                unify_fn!(&mut self.machine_st, r2, heap_addr);

                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
            &BuiltInClauseType::Is(r, ref at) => {
                let n1 = self.machine_st.store(self.machine_st.deref(self.machine_st[r]));
                let n2 = self.machine_st.get_number(at)?;

                match n2 {
                    Number::Fixnum(n) => self.machine_st.unify_fixnum(n, n1),
                    Number::Float(n) => {
                        // TODO: argghh.. deal with it.
                        let n = arena_alloc!(n, &mut self.machine_st.arena);
                        self.machine_st.unify_f64(n, n1)
                    }
                    Number::Integer(n) => self.machine_st.unify_big_int(n, n1),
                    Number::Rational(n) => self.machine_st.unify_rational(n, n1),
                }

                return_from_clause!(self.machine_st.last_call, self.machine_st)
            }
        }
    }

    #[inline(always)]
    fn call_clause_type(&mut self, module_name: Atom, key: PredicateKey) -> CallResult {
        let (name, arity) = key;

        match ClauseType::from(name, arity) {
            ClauseType::BuiltIn(built_in) => {
                self.machine_st.setup_built_in_call(built_in);
                self.call_builtin(&built_in)?;
            }
            ClauseType::CallN => {
                self.machine_st.handle_internal_call_n(arity);

                if self.machine_st.fail {
                    return Ok(());
                }

                self.machine_st.p = CodePtr::CallN(
                    arity,
                    self.machine_st.p.local(),
                    self.machine_st.last_call,
                );
            }
            ClauseType::Inlined(inlined) => {
                self.execute_inlined(&inlined);

                if self.machine_st.last_call {
                    self.machine_st.p = CodePtr::Local(self.machine_st.cp);
                }
            }
            ClauseType::Named(..) if module_name == atom!("user") => {
                return if let Some(idx) = self.indices.code_dir.get(&(name, arity)).cloned() {
                    self.context_call(name, arity, idx)
                } else {
                    Err(self.machine_st.throw_undefined_error(name, arity))
                };
            }
            ClauseType::Named(..) => {
                return if let Some(module) = self.indices.modules.get(&module_name) {
                    if let Some(idx) = module.code_dir.get(&(name, arity)).cloned() {
                        self.context_call(name, arity, idx)
                    } else {
                        Err(self.machine_st.throw_undefined_error(name, arity))
                    }
                } else {
                    let stub = functor_stub(name, arity);
                    let err = self.machine_st.module_resolution_error(module_name, name, arity);

                    Err(self.machine_st.error_form(err, stub))
                };
            }
            ClauseType::System(_) => {
                let (name, arity) = key;
                let name = functor!(name);

                let stub = functor_stub(atom!("call"), arity + 1);
                let err = self.machine_st.type_error(ValidType::Callable, name);

                return Err(self.machine_st.error_form(err, stub));
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn call_n(&mut self, module_name: Atom, arity: usize) -> CallResult {
        if let Some(key) = self.machine_st.setup_call_n(arity) {
            self.call_clause_type(module_name, key)?;
        }

        (self.machine_st.increment_call_count_fn)(&mut self.machine_st)
    }

    #[inline(always)]
    fn run_cleaners(&mut self) -> bool {
        use std::sync::Once;

        static CLEANER_INIT: Once = Once::new();

        static mut RCWH: usize = 0;
        static mut RCWOH: usize = 0;

        let (r_c_w_h, r_c_wo_h) = unsafe {
            CLEANER_INIT.call_once(|| {
                let r_c_w_h_atom = atom!("run_cleaners_with_handling");
                let r_c_wo_h_atom = atom!("run_cleaners_without_handling");
                let iso_ext = atom!("iso_ext");

                RCWH = self.indices.get_predicate_code_index(r_c_w_h_atom, 0, iso_ext)
                           .and_then(|item| item.local())
                           .unwrap();
                RCWOH = self.indices.get_predicate_code_index(r_c_wo_h_atom, 1, iso_ext)
                            .and_then(|item| item.local())
                            .unwrap();
            });

            (RCWH, RCWOH)
        };

        if let Some(&(_, b_cutoff, prev_block)) = self.machine_st.cont_pts.last() {
            if self.machine_st.b < b_cutoff {
                let (idx, arity) = if self.machine_st.block > prev_block {
                    (dir_entry!(r_c_w_h), 0)
                } else {
                    self.machine_st.registers[1] = fixnum_as_cell!(
                        Fixnum::build_with(b_cutoff as i64)
                    );

                    (dir_entry!(r_c_wo_h), 1)
                };

                if self.machine_st.last_call {
                    self.machine_st.execute_at_index(arity, idx);
                } else {
                    self.machine_st.call_at_index(arity, idx);
                }

                return true;
            }
        }

        false
    }

    pub(super) fn unwind_trail(&mut self, a1: usize, a2: usize) {
        // the sequence is reversed to respect the chronology of trail
        // additions, now that deleted attributes can be undeleted by
        // backtracking.
        for i in (a1..a2).rev() {
            let h = self.machine_st.trail[i].get_value() as usize;

            match self.machine_st.trail[i].get_tag() {
                TrailEntryTag::TrailedHeapVar => {
                    self.machine_st.heap[h] = heap_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedStackVar => {
                    self.machine_st.stack[h] = stack_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVar => {
                    self.machine_st.heap[h] = attr_var_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVarHeapLink => {
                    self.machine_st.heap[h] = heap_loc_as_cell!(h);
                }
                TrailEntryTag::TrailedAttrVarListLink => {
                    let l = self.machine_st.trail[i + 1].get_value();
                    self.machine_st.heap[h] = list_loc_as_cell!(l);
                }
                TrailEntryTag::TrailedBlackboardEntry => {
                    let key = Atom::from(h);

                    match self.indices.global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = None,
                        None => unreachable!(),
                    }
                }
                TrailEntryTag::TrailedBlackboardOffset => {
                    let key = Atom::from(h);
                    let value_cell = HeapCellValue::from(u64::from(self.machine_st.trail[i + 1]));

                    match self.indices.global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = Some(value_cell),
                        None => unreachable!(),
                    }
                }
                TrailEntryTag::TrailedAttachedValue => {
                }
            }
        }
    }
}
