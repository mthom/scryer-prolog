use crate::prolog_parser::ast::*;
use crate::prolog_parser::tabled_rc::*;

use crate::clause_types::*;
use crate::forms::*;
use crate::heap_print::*;
use crate::instructions::*;
use crate::machine::heap::*;
use crate::read::*;

mod attributed_variables;
pub(super) mod code_repo;
pub mod code_walker;
pub mod compile;
mod copier;
mod dynamic_database;
pub mod heap;
pub mod machine_errors;
pub mod machine_indices;
pub(super) mod machine_state;
pub mod modules;
pub mod partial_string;
mod raw_block;
mod stack;
pub(crate) mod streams;
pub(super) mod term_expansion;
pub mod toplevel;

#[macro_use]
mod arithmetic_ops;
#[macro_use]
mod machine_state_impl;
mod system_calls;

use crate::machine::attributed_variables::*;
use crate::machine::code_repo::*;
use crate::machine::compile::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::*;
use crate::machine::modules::*;
use crate::machine::streams::*;
use crate::machine::toplevel::*;

use crate::indexmap::IndexMap;

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fs::File;
use std::mem;
use std::ops::Index;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::AtomicBool;

#[derive(Debug)]
pub struct MachinePolicies {
    call_policy: Box<dyn CallPolicy>,
    cut_policy: Box<dyn CutPolicy>,
}

lazy_static! {
    pub static ref INTERRUPT: AtomicBool = AtomicBool::new(false);
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
pub struct Machine {
    pub(super) machine_st: MachineState,
    pub(super) inner_heap: Heap,
    pub(super) policies: MachinePolicies,
    pub(super) indices: IndexStore,
    pub(super) code_repo: CodeRepo,
    pub(super) toplevel_idx: usize,
    pub(super) current_input_stream: Stream,
    pub(super) current_output_stream: Stream,
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

    fn get_code_index(&self, key: PredicateKey, module_name: ClauseName) -> Option<CodeIndex> {
        match module_name.as_str() {
            "user" => {
                self.code_dir.get(&key).cloned()
            }
            _ => {
                match self.in_situ_module_dir.get(&module_name) {
                    Some(ref module_stub) => {
                        match module_stub.in_situ_code_dir.get(&key) {
                            Some(p) => {
                                return Some(CodeIndex::new(
                                    IndexPtr::InSituDirEntry(*p),
                                    module_name.clone()
                                ));
                            }
                            None => {
                            }
                        }
                    }
                    None => {
                    }
                };

                self.modules
                    .get(&module_name)
                    .and_then(|ref module| {
                        module.code_dir.get(&key).cloned()
                    })
            }
        }
    }

    fn remove_code_index(&mut self, key: PredicateKey) {
        self.code_dir.remove(&key);
    }

    fn insert_dir_entry(&mut self, name: ClauseName, arity: usize, idx: CodeIndex) {
        if let Some(ref code_idx) = self.code_dir.get(&(name.clone(), arity)) {
            if !code_idx.is_undefined() {
                match (name.as_str(), arity) {
                    ("term_expansion", 2) => {
                    }
                    ("goal_expansion", 2) => {
                    }
                    _ => {
                        println!("Warning: overwriting {}/{}", &name, arity);
                    }
                }
            }

            let (p, module_name) = idx.0.borrow().clone();
            set_code_index!(code_idx, p, module_name);
            return;
        }

        self.code_dir.insert((name.clone(), arity), idx.clone());
    }

    fn use_qualified_module(
        &mut self,
        code_repo: &mut CodeRepo,
        _: MachineFlags,
        submodule: &Module,
        exports: &Vec<ModuleExport>,
    ) -> Result<(), SessionError> {
        use_qualified_module(self, submodule, exports)?;
        submodule
            .dump_expansions(code_repo)
            .map_err(SessionError::from)
    }

    fn use_module(
        &mut self,
        code_repo: &mut CodeRepo,
        _: MachineFlags,
        submodule: &Module,
    ) -> Result<(), SessionError> {
        use_module(self, submodule)?;

        if !submodule.inserted_expansions {
            submodule
                .dump_expansions(code_repo)
                .map_err(SessionError::from)
        } else {
            Ok(())
        }
    }
}

#[inline]
fn current_dir() -> std::path::PathBuf {
    let mut path_buf = std::path::PathBuf::from(PROJECT_DIR);

    // file!() always produces a path relative to PROJECT_DIR.
    path_buf = path_buf.join(std::path::PathBuf::from(file!()));

    path_buf.pop();
    path_buf
}

include!(concat!(env!("OUT_DIR"), "/libraries.rs"));

static TOPLEVEL: &str = include_str!("../toplevel.pl");

impl Machine {
    fn compile_special_forms(&mut self)
    {
        let current_dir = current_dir();

        let verify_attrs_src = ListingSource::from_file_and_path(
            clause_name!("attributed_variables.pl"),
            current_dir.clone(),
        );

        match compile_special_form(
            self,
            Stream::from(VERIFY_ATTRS),
            verify_attrs_src,
        )
        {
            Ok(p) => {
                self.machine_st.attr_var_init.verify_attrs_loc = p;
            }
            Err(_) =>
                panic!("Machine::compile_special_forms() failed at VERIFY_ATTRS"),
        }

        let project_attrs_src = ListingSource::from_file_and_path(
            clause_name!("project_attributes.pl"),
            current_dir,
        );

        match compile_special_form(
            self,
            Stream::from(PROJECT_ATTRS),
            project_attrs_src,
        )
        {
            Ok(p) => {
                self.machine_st.attr_var_init.project_attrs_loc = p;
            }
            Err(e) =>
                panic!("Machine::compile_special_forms() failed at PROJECT_ATTRS: {}", e),
        }
    }

    fn compile_top_level(&mut self) -> Result<(), SessionError>
    {
        self.toplevel_idx = self.code_repo.code.len();

        let mut current_dir = current_dir();
        current_dir.pop();

        let top_lvl_src = ListingSource::from_file_and_path(
            clause_name!("toplevel.pl"),
            current_dir,
        );

        compile_user_module(
            self,
            Stream::from(TOPLEVEL),
            true,
            top_lvl_src,
        );

        if let Some(module) = self.indices.take_module(clause_name!("$toplevel")) {
            self.indices.use_module(
                &mut self.code_repo,
                self.machine_st.flags,
                &module,
            )?;

            Ok(self.indices.insert_module(module))
        } else {
            let err = ExistenceError::ModuleSource(ModuleSource::File(
                clause_name!("$toplevel"),
            ));

            Err(SessionError::ExistenceError(err))
        }
    }

    fn compile_scryerrc(&mut self) {
        let mut path = match dirs::home_dir() {
            Some(path) => path,
            None => return,
        };

        path.push(".scryerrc");

        if path.is_file() {
            let file_src = match File::open(&path) {
                Ok(file_handle) => Stream::from_file_as_input(
                    clause_name!(".scryerrc"),
                    file_handle,
                ),
                Err(_) => return,
            };

            let rc_src = ListingSource::from_file_and_path(
                clause_name!(".scryerrc"),
                path.to_path_buf(),
            );

            compile_user_module(self, file_src, true, rc_src);
        }
    }

    #[cfg(test)]
    pub fn reset(&mut self) {
        self.current_input_stream = readline::input_stream();
        self.policies.cut_policy = Box::new(DefaultCutPolicy {});
        self.machine_st.reset();
    }

    pub fn run_init_code(&mut self, code: Code) -> bool {
	    let old_machine_st = self.sink_to_snapshot();
	    self.machine_st.reset();

	    self.code_repo.cached_query = code;
	    self.run_query();

        let result = self.machine_st.fail;
	    self.absorb_snapshot(old_machine_st);

        !result
    }

    pub fn run_top_level(&mut self) {
        use std::env;

        let mut arg_pstrs = vec![];

        for arg in env::args() {
            arg_pstrs.push(self.machine_st.heap.put_complete_string(&arg));
        }

        let list_addr = Addr::HeapCell(self.machine_st.heap.to_list(arg_pstrs.into_iter()));
        self.machine_st[temp_v!(1)] = list_addr;

        loop {
            self.machine_st.p = CodePtr::Local(LocalCodePtr::DirEntry(self.toplevel_idx));
            self.run_query();
        }
    }

    pub fn new(current_input_stream: Stream, current_output_stream: Stream) -> Self
    {
        let mut wam = Machine {
            machine_st: MachineState::new(),
            inner_heap: Heap::new(),
            policies: MachinePolicies::new(),
            indices: IndexStore::new(),
            code_repo: CodeRepo::new(),
            toplevel_idx: 0,
            current_input_stream,
            current_output_stream,
        };

        let atom_tbl = wam.indices.atom_tbl.clone();
        let mut lib_path = current_dir();

        lib_path.pop();
        lib_path.push("lib");

        wam.indices.add_term_and_goal_expansion_indices();

        compile_listing(
            &mut wam,
            Stream::from(BUILTINS),
            default_index_store!(atom_tbl.clone()),
            true,
            ListingSource::from_file_and_path(
                clause_name!("builtins.pl"),
                lib_path.clone(),
            ),
        );

        wam.compile_special_forms();

        compile_user_module(&mut wam,
                            Stream::from(ERROR),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("error"),
                                lib_path.clone(),
                            )
        );

        compile_user_module(&mut wam,
                            Stream::from(PAIRS),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("pairs"),
                                lib_path.clone(),
                            )
        );

        compile_user_module(&mut wam,
                            Stream::from(LISTS),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("lists"),
                                lib_path.clone(),
                            ),
        );

        compile_user_module(&mut wam,
                            Stream::from(ISO_EXT),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("iso_ext"),
                                lib_path.clone(),
                            )
        );

        compile_user_module(&mut wam,
                            Stream::from(SI),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("si"),
                                lib_path.clone(),
                            )
        );

        compile_user_module(&mut wam,
                            Stream::from(CHARSIO),
                            true,
                            ListingSource::from_file_and_path(
                                clause_name!("si"),
                                lib_path.clone(),
                            )
        );

        if wam.compile_top_level().is_err() {
            panic!("Loading '$toplevel' module failed");
        }

        wam.compile_scryerrc();
        wam.configure_streams();

        wam
    }

    pub fn configure_streams(&mut self) {
        self.current_input_stream.options.alias = Some(clause_name!("user_input"));

        self.indices.stream_aliases.insert(
            clause_name!("user_input"),
            self.current_input_stream.clone(),
        );

        self.indices.streams.insert(
            self.current_input_stream.clone()
        );

        self.current_output_stream.options.alias = Some(clause_name!("user_output"));

        self.indices.stream_aliases.insert(
            clause_name!("user_output"),
            self.current_output_stream.clone(),
        );

        self.indices.streams.insert(
            self.current_output_stream.clone()
        );
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

    pub(crate) fn add_batched_code_dir(&mut self, code_dir: CodeDir) {
        // error detection has finished, so update the master index of keys.
        for (key, idx) in code_dir {
            if let Some(ref master_idx) = self.indices.code_dir.get(&key) {
                // ensure we don't double borrow if master_idx == idx.
                // we don't need to modify anything in that case.
                if !Rc::ptr_eq(&master_idx.0, &idx.0) {
                    set_code_index!(master_idx, idx.0.borrow().0, idx.module_name());
                }

                continue;
            }

            self.indices.code_dir.insert(key, idx);
        }
    }

    #[inline]
    pub(crate) fn add_batched_ops(&mut self, op_dir: OpDir) {
        self.indices.op_dir.extend(op_dir.into_iter());
    }

    pub(crate) fn add_in_situ_module_dir(&mut self, module_dir: ModuleDir) {
        for (module_name, module_skeleton) in module_dir {
            match self.indices.modules.get_mut(&module_name) {
                Some(ref mut module) => {
                    for (key, idx) in module_skeleton.code_dir {
                        if let Some(existing_idx) = module.code_dir.get(&key) {
                            set_code_index!(existing_idx, idx.0.borrow().0, module_name.clone());
                        } else {
                            module.code_dir.insert(key, idx);
                        }
                    }
                }
                None => {
                    self.add_module(module_skeleton);
                }
            }
        }
    }

    #[inline]
    pub fn add_module(&mut self, module: Module) {
        self.indices
            .modules
            .insert(module.module_decl.name.clone(), module);
    }

    fn throw_session_error(&mut self, err: SessionError, key: PredicateKey) {
        let h = self.machine_st.heap.h();

        let err = MachineError::session_error(h, err);
        let stub = MachineError::functor_stub(key.0, key.1);
        let err = self.machine_st.error_form(err, stub);

        self.machine_st.throw_exception(err);
        return;
    }

    fn extract_module_export_list(&mut self) -> Result<Vec<ModuleExport>, ParserError>
    {
	    let mut export_list = self.machine_st[temp_v!(2)].clone();
	    let mut exports = vec![];

	    while let Addr::Lis(l) = self.machine_st.store(self.machine_st.deref(export_list)) {
	        match &self.machine_st.heap[l] {
		        &HeapCellValue::Addr(Addr::Str(s)) => {
                    match &self.machine_st.heap[s] {
                        HeapCellValue::NamedStr(arity, ref name, _)
                            if *arity == 2 && name.as_str() == "/" => {
		                        let name = match &self.machine_st.heap[s+1] {
			                        &HeapCellValue::Atom(ref name, _) =>
			                            name.clone(),
			                        _ =>
			                            unreachable!()
		                        };

		                        let arity = match &self.machine_st.heap[s+2] {
			                        &HeapCellValue::Integer(ref arity) =>
			                            arity.to_usize().unwrap(),
                                    &HeapCellValue::Addr(Addr::Fixnum(n)) =>
                                        usize::try_from(n).unwrap(),
			                        _ =>
			                            unreachable!()
		                        };

		                        exports.push(ModuleExport::PredicateKey((name, arity)));
                            }
                        HeapCellValue::NamedStr(arity, ref name, _)
                            if *arity == 3 && name.as_str() == "op" => {
                                let name = match &self.machine_st.heap[s+3] {
			                        &HeapCellValue::Atom(ref name, _) =>
			                            name.clone(),
			                        _ =>
			                            unreachable!()
		                        };

                                let spec = match &self.machine_st.heap[s+2] {
			                        &HeapCellValue::Atom(ref name, _) =>
			                            name.clone(),
			                        _ =>
			                            unreachable!()
		                        };

		                        let prec = match &self.machine_st.heap[s+1] {
			                        &HeapCellValue::Integer(ref arity) =>
			                            arity.to_usize().unwrap(),
                                    &HeapCellValue::Addr(Addr::Fixnum(n)) =>
                                        usize::try_from(n).unwrap(),
			                        _ =>
			                            unreachable!()
		                        };

                                exports.push(ModuleExport::OpDecl(to_op_decl(
                                    prec,
                                    spec.as_str(),
                                    name,
                                )?));
                            }
                        _ => unreachable!()
                    }
		        }
		        _ => unreachable!()
	        }

	        export_list = self.machine_st.heap[l+1].as_addr(l+1);
	    }

	    Ok(exports)
    }

    fn use_module(&mut self, to_src: impl Fn(ClauseName) -> ModuleSource)
    {
	    // the term expander will overwrite the cached query, so save it here.
	    let cached_query = mem::replace(&mut self.code_repo.cached_query, vec![]);

	    let module_spec = self.machine_st[temp_v!(1)].clone();
	    let (name, is_path) = {
            let addr = self.machine_st.store(self.machine_st.deref(module_spec));

            match self.machine_st.heap.index_addr(&addr).as_ref() {
                HeapCellValue::Atom(name, _) =>
                    (name.clone(), name.as_str().contains('/')),
                HeapCellValue::Addr(Addr::Char(c)) =>
                    (clause_name!(c.to_string(), self.indices.atom_tbl), false),
                HeapCellValue::Addr(addr @ Addr::PStrLocation(..)) => {
                    let mut heap_pstr_iter = self.machine_st.heap_pstr_iter(*addr);
                    let filename = heap_pstr_iter.to_string();
                    let is_path = filename.contains('/');

                    (clause_name!(filename, self.indices.atom_tbl), is_path)
                }
	            _ =>
                    unreachable!(),
            }
	    };

	    let load_result = match to_src(name) {
	        ModuleSource::Library(name) =>
                if is_path {
                    load_library(self, name, false)
                } else {
                    if let Some(module) = self.indices.take_module(name.clone()) {
                        self.indices.remove_module(clause_name!("user"), &module);
                        self.indices.modules.insert(name.clone(), module);

		                Ok(name)
		            } else {
		                load_library(self, name, false)
		            }
                }
	        ModuleSource::File(name) =>
                load_module_from_file(self, PathBuf::from(name.as_str()), false)
	    };

	    let result = load_result.and_then(|name| {
            let module = self.indices.take_module(name.clone()).unwrap();

            if !module.is_impromptu_module {
                self.indices.use_module(&mut self.code_repo, self.machine_st.flags, &module)?;
            }

            Ok(self.indices.insert_module(module))
        });

	    self.code_repo.cached_query = cached_query;

	    if let Err(e) = result {
	        self.throw_session_error(e, (clause_name!("use_module"), 1));
	    }
    }

    fn use_qualified_module(&mut self, to_src: impl Fn(ClauseName) -> ModuleSource)
    {
	    // the term expander will overwrite the cached query, so save it here.
	    let cached_query = mem::replace(&mut self.code_repo.cached_query, vec![]);

	    let module_spec = self.machine_st[temp_v!(1)].clone();
	    let (name, is_path) = {
            let addr = self.machine_st.store(self.machine_st.deref(module_spec));

            match self.machine_st.heap.index_addr(&addr).as_ref() {
                HeapCellValue::Atom(name, _) =>
                    (name.clone(), name.as_str().contains('/')),
                HeapCellValue::Addr(Addr::Char(c)) =>
                    (clause_name!(c.to_string(), self.indices.atom_tbl), false),
                HeapCellValue::Addr(addr @ Addr::PStrLocation(..)) => {
                    let mut heap_pstr_iter = self.machine_st.heap_pstr_iter(*addr);
                    let filename = heap_pstr_iter.to_string();
                    let is_path = filename.contains('/');

                    (clause_name!(filename, self.indices.atom_tbl), is_path)
                }
	            _ =>
                    unreachable!(),
            }
	    };

	    let exports = match self.extract_module_export_list() {
            Ok(exports) => exports,
            Err(e) => {
                self.throw_session_error(SessionError::from(e), (clause_name!("use_module"), 2));
                return;
            }
        };

	    let load_result = match to_src(name) {
	        ModuleSource::Library(name) =>
                if is_path {
                    load_library(self, name, false)
                } else {
                    if let Some(module) = self.indices.take_module(name.clone()) {
                        self.indices.remove_module(clause_name!("user"), &module);
                        self.indices.modules.insert(name.clone(), module);

		                Ok(name)
		            } else {
		                load_library(self, name, false)
		            }
                },
	        ModuleSource::File(name) =>
                load_module_from_file(self, PathBuf::from(name.as_str()), false)
	    };

	    let result = load_result.and_then(|name| {
	        let module = self.indices.take_module(name.clone()).unwrap();

            if !module.is_impromptu_module {
	            self.indices.use_qualified_module(&mut self.code_repo,
					                              self.machine_st.flags,
					                              &module,
					                              &exports)?;
            }

	        Ok(self.indices.insert_module(module))
        });

	    self.code_repo.cached_query = cached_query;

	    if let Err(e) = result {
	        self.throw_session_error(e, (clause_name!("use_module"), 2));
	    }
    }

    fn handle_toplevel_command(&mut self, code_ptr: REPLCodePtr, p: LocalCodePtr) {
        match code_ptr {
            REPLCodePtr::CompileBatch => {
                let user_src = ListingSource::User;

                let src = readline::input_stream();
                readline::set_prompt(false);

                if let EvalSession::Error(e) = compile_user_module(self, src, false, user_src) {
                    self.throw_session_error(e, (clause_name!("repl"), 0));
                }
            }
	        REPLCodePtr::UseModule =>
		        self.use_module(ModuleSource::Library),
	        REPLCodePtr::UseModuleFromFile =>
		        self.use_module(ModuleSource::File),
	        REPLCodePtr::UseQualifiedModule =>
		        self.use_qualified_module(ModuleSource::Library),
	        REPLCodePtr::UseQualifiedModuleFromFile =>
		        self.use_qualified_module(ModuleSource::File)
        }

        self.machine_st.p = CodePtr::Local(p);
    }

    fn sink_to_snapshot(&mut self) -> MachineState {
        let mut snapshot = MachineState::with_small_heap();

        snapshot.hb = self.machine_st.hb;
        snapshot.e = self.machine_st.e;
        snapshot.b = self.machine_st.b;
        snapshot.b0 = self.machine_st.b0;
        snapshot.s = self.machine_st.s.clone();
        snapshot.tr = self.machine_st.tr;
        snapshot.num_of_args = self.machine_st.num_of_args;

        snapshot.fail = self.machine_st.fail;
        snapshot.trail = mem::replace(&mut self.machine_st.trail, vec![]);
        snapshot.heap = self.machine_st.heap.take();
        snapshot.mode = self.machine_st.mode;
        snapshot.stack = self.machine_st.stack.take();
        snapshot.registers = mem::replace(&mut self.machine_st.registers, vec![]);
        snapshot.block = self.machine_st.block;

        snapshot.ball = self.machine_st.ball.take();
        snapshot.lifted_heap = self.machine_st.lifted_heap.take();

        snapshot
    }

    fn absorb_snapshot(&mut self, mut snapshot: MachineState) {
        self.machine_st.hb = snapshot.hb;
        self.machine_st.e = snapshot.e;
        self.machine_st.b = snapshot.b;
        self.machine_st.b0 = snapshot.b0;
        self.machine_st.s = snapshot.s;
        self.machine_st.tr = snapshot.tr;
        self.machine_st.num_of_args = snapshot.num_of_args;

        self.machine_st.fail = snapshot.fail;
        self.machine_st.trail = mem::replace(&mut snapshot.trail, vec![]);

        self.inner_heap = self.machine_st.heap.take();
        self.inner_heap.truncate(0);

        self.machine_st.heap = snapshot.heap.take();
        self.machine_st.mode = snapshot.mode;
        self.machine_st.stack = snapshot.stack;
        self.machine_st.registers = mem::replace(&mut snapshot.registers, vec![]);
        self.machine_st.block = snapshot.block;

        self.machine_st.ball = snapshot.ball.take();
        self.machine_st.lifted_heap = snapshot.lifted_heap.take();
    }

    pub(super) fn run_query(&mut self) {
	    self.machine_st.cp = LocalCodePtr::TopLevel(0, self.code_repo.size_of_cached_query());
        let end_ptr = CodePtr::Local(self.machine_st.cp);

        while self.machine_st.p < end_ptr {
            self.machine_st.query_stepper(
                &mut self.indices,
                &mut self.policies,
                &mut self.code_repo,
                &mut self.current_input_stream,
                &mut self.current_output_stream,
            );

            match self.machine_st.p {
                CodePtr::Local(LocalCodePtr::TopLevel(_, p)) if p > 0 => {
                }
                CodePtr::REPL(code_ptr, p) => {
                    self.handle_toplevel_command(code_ptr, p)
                }
                CodePtr::DynamicTransaction(trans_type, p) => {
                    // self.code_repo.cached_query is about to be overwritten by the term expander,
                    // so hold onto it locally and restore it after the compiler has finished.
                    self.machine_st.fail = false;
                    let cached_query = mem::replace(&mut self.code_repo.cached_query, vec![]);

                    self.dynamic_transaction(trans_type, p);
                    self.code_repo.cached_query = cached_query;

                    if let CodePtr::Local(LocalCodePtr::TopLevel(_, 0)) = self.machine_st.p {
                        break;
                    }
                }
                _ =>
                    break
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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) {
        match instr {
            &Line::Arithmetic(ref arith_instr) => {
                self.execute_arith_instr(arith_instr)
            }
            &Line::Choice(ref choice_instr) => {
                self.execute_choice_instr(choice_instr, &mut policies.call_policy)
            }
            &Line::Cut(ref cut_instr) => {
                self.execute_cut_instr(cut_instr, &mut policies.cut_policy)
            }
            &Line::Control(ref control_instr) => {
                self.execute_ctrl_instr(
                    indices,
                    code_repo,
                    &mut policies.call_policy,
                    &mut policies.cut_policy,
                    current_input_stream,
                    current_output_stream,
                    control_instr,
                )
            }
            &Line::Fact(ref fact_instr) => {
                self.execute_fact_instr(&fact_instr);
                self.p += 1;
            }
            &Line::Indexing(ref indexing_instr) => {
                self.execute_indexing_instr(&indexing_instr)
            }
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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
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
            current_input_stream,
            current_output_stream,
        );
    }

    fn backtrack(&mut self) {
        if self.b > 0 {
            let b = self.b;

            self.b0 = self.stack.index_or_frame(b).prelude.b0;
            self.p = CodePtr::Local(self.stack.index_or_frame(b).prelude.bp);

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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
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
                current_input_stream,
                current_output_stream,
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
        current_input_stream: &mut Stream,
        current_output_stream: &mut Stream,
    ) {
        loop {
            self.execute_instr(
                indices,
                policies,
                code_repo,
                current_input_stream,
                current_output_stream,
            );

            if self.fail {
                self.backtrack();
            }

            match self.p {
                CodePtr::VerifyAttrInterrupt(_) => {
                    self.p = CodePtr::Local(self.attr_var_init.cp);

                    let instigating_p = CodePtr::Local(self.attr_var_init.instigating_p);
                    let instigating_instr = code_repo.lookup_instr(false, &instigating_p).unwrap();

                    if !instigating_instr.as_ref().is_head_instr() {
                        let cp = self.p.local();
                        self.run_verify_attr_interrupt(cp);
                    } else if !self.verify_attr_stepper(
                        indices,
                        policies,
                        code_repo,
                        current_input_stream,
                        current_output_stream,
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
