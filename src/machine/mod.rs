pub mod args;
pub mod arithmetic_ops;
pub mod attributed_variables;
pub mod code_walker;
#[macro_use]
pub mod loader;
pub mod compile;
pub mod copier;
pub mod disjuncts;
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
pub mod unify;

use crate::arena::*;
use crate::arithmetic::*;
use crate::atom_table::*;
#[cfg(feature = "ffi")]
use crate::ffi::ForeignFunctionTable;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::args::*;
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
use crate::parser::dashu::{Integer, Rational};
use crate::types::*;

use indexmap::IndexMap;
use lazy_static::lazy_static;
use ordered_float::OrderedFloat;

use std::cmp::Ordering;
use std::env;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use tokio::runtime::Runtime;

lazy_static! {
    pub static ref INTERRUPT: AtomicBool = AtomicBool::new(false);
}

#[derive(Debug)]
pub struct Machine {
    pub(super) machine_st: MachineState,
    pub(super) indices: IndexStore,
    pub(super) code: Code,
    pub(super) user_input: Stream,
    pub(super) user_output: Stream,
    pub(super) user_error: Stream,
    pub(super) load_contexts: Vec<LoadContext>,
    pub(super) runtime: Runtime,
    #[cfg(feature = "ffi")]
    pub(super) foreign_function_table: ForeignFunctionTable,
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

pub static BREAK_FROM_DISPATCH_LOOP_LOC: usize = 0;
pub static INSTALL_VERIFY_ATTR_INTERRUPT: usize = 1;
pub static VERIFY_ATTR_INTERRUPT_LOC: usize = 2;

pub struct MachinePreludeView<'a> {
    pub indices: &'a mut IndexStore,
    pub code: &'a mut Code,
    pub load_contexts: &'a mut Vec<LoadContext>,
}

pub(crate) fn import_builtin_impls(code_dir: &CodeDir, builtins: &mut Module) {
    let keys = [
        (atom!("@>"), 2),
        (atom!("@<"), 2),
        (atom!("@>="), 2),
        (atom!("@=<"), 2),
        (atom!("=="), 2),
        (atom!("\\=="), 2),
        (atom!(">"), 2),
        (atom!("<"), 2),
        (atom!(">="), 2),
        (atom!("=<"), 2),
        (atom!("=:="), 2),
        (atom!("=\\="), 2),
        (atom!("is"), 2),
        (atom!("acyclic_term"), 1),
        (atom!("arg"), 3),
        (atom!("compare"), 3),
        (atom!("copy_term"), 2),
        (atom!("functor"), 3),
        (atom!("ground"), 1),
        (atom!("keysort"), 2),
        (atom!("read"), 1),
        (atom!("sort"), 2),
        (atom!("$call"), 1),
        (atom!("$call"), 2),
        (atom!("$call"), 3),
        (atom!("$call"), 4),
        (atom!("$call"), 5),
        (atom!("$call"), 6),
        (atom!("$call"), 7),
        (atom!("$call"), 8),
        (atom!("$call"), 9),
        (atom!("atom"), 1),
        (atom!("atomic"), 1),
        (atom!("compound"), 1),
        (atom!("integer"), 1),
        (atom!("number"), 1),
        (atom!("rational"), 1),
        (atom!("float"), 1),
        (atom!("nonvar"), 1),
        (atom!("var"), 1),
    ];

    for key in keys {
        let idx = code_dir.get(&key).unwrap();
        builtins.code_dir.insert(key, idx.clone());
        builtins
            .module_decl
            .exports
            .push(ModuleExport::PredicateKey(key));
    }
}

#[inline]
pub(crate) fn get_structure_index(value: HeapCellValue) -> Option<CodeIndex> {
    read_heap_cell!(value,
        (HeapCellValueTag::Cons, cons_ptr) => {
             match_untyped_arena_ptr!(cons_ptr,
                 (ArenaHeaderTag::IndexPtr, ip) => {
                     return Some(CodeIndex::from(ip));
                 }
                 _ => {}
             );
        }
        _ => {
        }
    );

    None
}

impl Machine {
    #[inline]
    pub fn prelude_view_and_machine_st(&mut self) -> (MachinePreludeView, &mut MachineState) {
        (
            MachinePreludeView {
                indices: &mut self.indices,
                code: &mut self.code,
                load_contexts: &mut self.load_contexts,
            },
            &mut self.machine_st,
        )
    }

    pub fn throw_session_error(&mut self, err: SessionError, key: PredicateKey) {
        let err = self.machine_st.session_error(err);
        let stub = functor_stub(key.0, key.1);
        let err = self.machine_st.error_form(err, stub);

        self.machine_st.throw_exception(err);
    }

    fn run_module_predicate(
        &mut self,
        module_name: Atom,
        key: PredicateKey,
    ) -> std::process::ExitCode {
        if let Some(module) = self.indices.modules.get(&module_name) {
            if let Some(ref code_index) = module.code_dir.get(&key) {
                let p = code_index.local().unwrap();

                self.machine_st.cp = BREAK_FROM_DISPATCH_LOOP_LOC;
                self.machine_st.p = p;

                return self.dispatch_loop();
            }
        }

        unreachable!();
    }

    pub fn load_file(&mut self, path: &str, stream: Stream) {
        self.machine_st.registers[1] = stream_as_cell!(stream);
        self.machine_st.registers[2] =
            atom_as_cell!(AtomTable::build_with(&self.machine_st.atom_tbl, path));

        self.run_module_predicate(atom!("loader"), (atom!("file_load"), 2));
    }

    fn load_top_level(&mut self) {
        let mut path_buf = current_dir();

        path_buf.push("src/toplevel.pl");

        let path = path_buf.to_str().unwrap();
        let toplevel_stream =
            Stream::from_static_string(include_str!("../toplevel.pl"), &mut self.machine_st.arena);

        self.load_file(path, toplevel_stream);

        if let Some(toplevel) = self.indices.modules.get(&atom!("$toplevel")) {
            load_module(
                &mut self.machine_st,
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

        let stream = Stream::from_static_string(
            include_str!("attributed_variables.pl"),
            &mut self.machine_st.arena,
        );

        self.load_file(path_buf.to_str().unwrap(), stream);

        let mut path_buf = current_dir();
        path_buf.push("machine/project_attributes.pl");

        let stream = Stream::from_static_string(
            include_str!("project_attributes.pl"),
            &mut self.machine_st.arena,
        );

        self.load_file(path_buf.to_str().unwrap(), stream);

        if let Some(module) = self.indices.modules.get(&atom!("$atts")) {
            if let Some(code_index) = module.code_dir.get(&(atom!("driver"), 2)) {
                self.machine_st.attr_var_init.verify_attrs_loc = code_index.local().unwrap();
            }
        }
    }

    pub fn run_top_level(&mut self) -> std::process::ExitCode {
        let mut arg_pstrs = vec![];

        for arg in env::args() {
            arg_pstrs.push(put_complete_string(
                &mut self.machine_st.heap,
                &arg,
                &self.machine_st.atom_tbl,
            ));
        }

        self.machine_st.registers[1] = heap_loc_as_cell!(iter_to_heap_list(
            &mut self.machine_st.heap,
            arg_pstrs.into_iter()
        ));

        self.run_module_predicate(atom!("$toplevel"), (atom!("$repl"), 1))
    }

    pub(crate) fn configure_modules(&mut self) {
        fn update_call_n_indices(
            loader: &Module,
            target_code_dir: &mut CodeDir,
            arena: &mut Arena,
        ) {
            for arity in 1..66 {
                let key = (atom!("call"), arity);

                match loader.code_dir.get(&key) {
                    Some(src_code_index) => {
                        let target_code_index = target_code_dir
                            .entry(key)
                            .or_insert_with(|| CodeIndex::new(IndexPtr::undefined(), arena));

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
                    &mut self.machine_st,
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
                update_call_n_indices(
                    &loader,
                    &mut target_module.code_dir,
                    &mut self.machine_st.arena,
                );
            }

            update_call_n_indices(
                &loader,
                &mut self.indices.code_dir,
                &mut self.machine_st.arena,
            );

            self.indices.modules.insert(atom!("loader"), loader);
        } else {
            unreachable!()
        }
    }

    pub(crate) fn add_impls_to_indices(&mut self) {
        let impls_offset = self.code.len() + 3;

        self.code.extend(
            vec![
                Instruction::BreakFromDispatchLoop,
                Instruction::InstallVerifyAttr,
                Instruction::VerifyAttrInterrupt,
                Instruction::ExecuteTermGreaterThan,
                Instruction::ExecuteTermLessThan,
                Instruction::ExecuteTermGreaterThanOrEqual,
                Instruction::ExecuteTermLessThanOrEqual,
                Instruction::ExecuteTermEqual,
                Instruction::ExecuteTermNotEqual,
                Instruction::ExecuteNumberGreaterThan(ar_reg!(temp_v!(1)), ar_reg!(temp_v!(2))),
                Instruction::ExecuteNumberLessThan(ar_reg!(temp_v!(1)), ar_reg!(temp_v!(2))),
                Instruction::ExecuteNumberGreaterThanOrEqual(
                    ar_reg!(temp_v!(1)),
                    ar_reg!(temp_v!(2)),
                ),
                Instruction::ExecuteNumberLessThanOrEqual(ar_reg!(temp_v!(1)), ar_reg!(temp_v!(2))),
                Instruction::ExecuteNumberEqual(ar_reg!(temp_v!(1)), ar_reg!(temp_v!(2))),
                Instruction::ExecuteNumberNotEqual(ar_reg!(temp_v!(1)), ar_reg!(temp_v!(2))),
                Instruction::ExecuteIs(temp_v!(1), ar_reg!(temp_v!(2))),
                Instruction::ExecuteAcyclicTerm,
                Instruction::ExecuteArg,
                Instruction::ExecuteCompare,
                Instruction::ExecuteCopyTerm,
                Instruction::ExecuteFunctor,
                Instruction::ExecuteGround,
                Instruction::ExecuteKeySort,
                Instruction::ExecuteSort,
                Instruction::ExecuteN(1),
                Instruction::ExecuteN(2),
                Instruction::ExecuteN(3),
                Instruction::ExecuteN(4),
                Instruction::ExecuteN(5),
                Instruction::ExecuteN(6),
                Instruction::ExecuteN(7),
                Instruction::ExecuteN(8),
                Instruction::ExecuteN(9),
                Instruction::ExecuteIsAtom(temp_v!(1)),
                Instruction::ExecuteIsAtomic(temp_v!(1)),
                Instruction::ExecuteIsCompound(temp_v!(1)),
                Instruction::ExecuteIsInteger(temp_v!(1)),
                Instruction::ExecuteIsNumber(temp_v!(1)),
                Instruction::ExecuteIsRational(temp_v!(1)),
                Instruction::ExecuteIsFloat(temp_v!(1)),
                Instruction::ExecuteIsNonVar(temp_v!(1)),
                Instruction::ExecuteIsVar(temp_v!(1)),
            ]
            .into_iter(),
        );

        for (p, instr) in self.code[impls_offset..].iter().enumerate() {
            let key = instr.to_name_and_arity();
            self.indices.code_dir.insert(
                key,
                CodeIndex::new(
                    IndexPtr::index(p + impls_offset),
                    &mut self.machine_st.arena,
                ),
            );
        }
    }

    pub fn new() -> Self {
        use ref_thread_local::RefThreadLocal;

        let args = MachineArgs::new();
        let mut machine_st = MachineState::new();

        let user_input = Stream::stdin(&mut machine_st.arena, args.add_history);
        let user_output = Stream::stdout(&mut machine_st.arena);
        let user_error = Stream::stderr(&mut machine_st.arena);

        #[cfg(not(target_os = "wasi"))]
        let runtime = tokio::runtime::Runtime::new().unwrap();
        #[cfg(target_os = "wasi")]
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let mut wam = Machine {
            machine_st,
            indices: IndexStore::new(),
            code: vec![],
            user_input,
            user_output,
            user_error,
            load_contexts: vec![],
            runtime,
            #[cfg(feature = "ffi")]
            foreign_function_table: Default::default(),
        };

        let mut lib_path = current_dir();

        lib_path.pop();
        lib_path.push("lib");

        wam.add_impls_to_indices();

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
            Stream::from_static_string(LIBRARIES.borrow()["builtins"], &mut wam.machine_st.arena),
            &mut wam,
            ListingSource::from_file_and_path(atom!("builtins.pl"), lib_path.clone()),
        )
        .unwrap();

        if let Some(builtins) = wam.indices.modules.get_mut(&atom!("builtins")) {
            load_module(
                &mut wam.machine_st,
                &mut wam.indices.code_dir,
                &mut wam.indices.op_dir,
                &mut wam.indices.meta_predicates,
                &CompilationTarget::User,
                builtins,
            );

            import_builtin_impls(&wam.indices.code_dir, builtins);
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
                &mut wam.machine_st,
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
        self.user_input
            .options_mut()
            .set_alias_to_atom_opt(Some(atom!("user_input")));

        self.indices
            .stream_aliases
            .insert(atom!("user_input"), self.user_input);

        self.indices.streams.insert(self.user_input);

        self.user_output
            .options_mut()
            .set_alias_to_atom_opt(Some(atom!("user_output")));

        self.indices
            .stream_aliases
            .insert(atom!("user_output"), self.user_output);

        self.indices.streams.insert(self.user_output);

        self.indices
            .stream_aliases
            .insert(atom!("user_error"), self.user_error);

        self.indices.streams.insert(self.user_error);
    }

    #[inline(always)]
    pub(crate) fn run_verify_attr_interrupt(&mut self, arity: usize) {
        let p = self.machine_st.attr_var_init.verify_attrs_loc;
        self.machine_st.verify_attr_interrupt(p, arity);
    }

    fn next_clause_applicable(&mut self, mut offset: usize) -> bool {
        loop {
            match &self.code[offset] {
                Instruction::IndexingCode(indexing_lines) => {
                    let mut oip = 0;
                    let mut cell = empty_list_as_cell!();

                    loop {
                        let indexing_code_ptr = match &indexing_lines[oip] {
                            &IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                arg,
                                v,
                                c,
                                l,
                                s,
                            )) => {
                                cell = self.deref_register(arg);
                                self.machine_st
                                    .select_switch_on_term_index(cell, v, c, l, s)
                            }
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnConstant(hm)) => {
                                let lit = self.machine_st.constant_to_literal(cell);
                                hm.get(&lit).cloned().unwrap_or(IndexingCodePtr::Fail)
                            }
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnStructure(hm)) => {
                                self.machine_st.select_switch_on_structure_index(cell, hm)
                            }
                            _ => {
                                offset += 1;
                                break;
                            }
                        };

                        match indexing_code_ptr {
                            IndexingCodePtr::External(_) | IndexingCodePtr::DynamicExternal(_) => {
                                offset += 1;
                                break;
                            }
                            IndexingCodePtr::Internal(i) => oip += i,
                            IndexingCodePtr::Fail => return false,
                        }
                    }
                }
                &Instruction::GetConstant(Level::Shallow, lit, RegType::Temp(t)) => {
                    let cell = self.deref_register(t);

                    if cell.is_var() {
                        offset += 1;
                    } else if lit.get_tag() == HeapCellValueTag::CStr {
                        read_heap_cell!(cell,
                            (HeapCellValueTag::CStr) => {
                                if cell == lit {
                                    offset += 1;
                                } else {
                                    return false;
                                }
                            }
                            (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                                offset += 1;
                            }
                            (HeapCellValueTag::Str, s) => {
                                let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s])
                                    .get_name_and_arity();

                                if name == atom!(".") && arity == 2 {
                                    offset += 1;
                                } else {
                                    return false;
                                }
                            }
                            _ => {
                                return false;
                            }
                        );
                    } else {
                        self.machine_st.write_literal_to_var(cell, lit);

                        if self.machine_st.fail {
                            self.machine_st.fail = false;
                            return false;
                        } else {
                            offset += 1;
                        }
                    }
                }
                &Instruction::GetList(Level::Shallow, RegType::Temp(t)) => {
                    let cell = self.deref_register(t);

                    read_heap_cell!(cell,
                        (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc | HeapCellValueTag::CStr) => {
                            offset += 1;
                        }
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s]).get_name_and_arity();

                            if name == atom!(".") && arity == 2 {
                                offset += 1;
                            } else {
                                return false;
                            }
                        }
                        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                            offset += 1;
                        }
                        _ => {
                            return false;
                        }
                    );
                }
                &Instruction::GetStructure(Level::Shallow, name, arity, RegType::Temp(t)) => {
                    let cell = self.deref_register(t);

                    read_heap_cell!(cell,
                        (HeapCellValueTag::Str, s) => {
                            if (name, arity) == cell_as_atom_cell!(self.machine_st.heap[s]).get_name_and_arity() {
                                offset += 1;
                            } else {
                                return false;
                            }
                        }
                        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                            offset += 1;
                        }
                        _ => {
                            return false;
                        }
                    );
                }
                &Instruction::GetPartialString(
                    Level::Shallow,
                    string,
                    RegType::Temp(t),
                    has_tail,
                ) => {
                    let cell = self.deref_register(t);

                    read_heap_cell!(cell,
                        (HeapCellValueTag::CStr, cstr) => {
                            if !has_tail && string != cstr {
                                return false;
                            }

                            offset += 1;
                        }
                        (HeapCellValueTag::Lis | HeapCellValueTag::PStrLoc) => {
                            offset += 1;
                        }
                        (HeapCellValueTag::Str, s) => {
                            let (name, arity) = cell_as_atom_cell!(self.machine_st.heap[s]).get_name_and_arity();

                            if name == atom!(".") && arity == 2 {
                                offset += 1;
                            } else {
                                return false;
                            }
                        }
                        (HeapCellValueTag::AttrVar | HeapCellValueTag::Var | HeapCellValueTag::StackVar) => {
                            offset += 1;
                        }
                        _ => {
                            return false;
                        }
                    );
                }
                Instruction::GetConstant(..)
                | Instruction::GetList(..)
                | Instruction::GetStructure(..)
                | Instruction::GetPartialString(..)
                | &Instruction::UnifyVoid(..)
                | &Instruction::UnifyConstant(..)
                | &Instruction::GetVariable(..)
                | &Instruction::GetValue(..)
                | &Instruction::UnifyVariable(..)
                | &Instruction::UnifyValue(..)
                | &Instruction::UnifyLocalValue(..) => {
                    offset += 1;
                }
                _ => {
                    break;
                }
            }
        }

        true
    }

    fn next_applicable_clause(&mut self, mut offset: usize) -> Option<usize> {
        while !self.next_clause_applicable(self.machine_st.p + offset + 1) {
            match &self.code[self.machine_st.p + offset] {
                &Instruction::DefaultRetryMeElse(o)
                | &Instruction::RetryMeElse(o)
                | &Instruction::DynamicElse(.., NextOrFail::Next(o))
                | &Instruction::DynamicInternalElse(.., NextOrFail::Next(o)) => offset += o,
                _ => {
                    return None;
                }
            }
        }

        Some(offset)
    }

    fn next_inner_applicable_clause(&mut self) -> Option<u32> {
        let mut inner_offset = 1u32;

        loop {
            match &self.code[self.machine_st.p] {
                Instruction::IndexingCode(indexing_lines) => {
                    match &indexing_lines[self.machine_st.oip as usize] {
                        IndexingLine::IndexedChoice(indexed_choice) => {
                            match &indexed_choice[(self.machine_st.iip + inner_offset) as usize] {
                                &IndexedChoiceInstruction::Retry(o)
                                | &IndexedChoiceInstruction::DefaultRetry(o) => {
                                    if self.next_clause_applicable(self.machine_st.p + o) {
                                        return Some(inner_offset);
                                    }

                                    inner_offset += 1;
                                }
                                &IndexedChoiceInstruction::Trust(o)
                                | &IndexedChoiceInstruction::DefaultTrust(o) => {
                                    return if self.next_clause_applicable(self.machine_st.p + o) {
                                        Some(inner_offset)
                                    } else {
                                        None
                                    };
                                }
                                _ => unreachable!(),
                            }
                        }
                        IndexingLine::DynamicIndexedChoice(indexed_choice) => {
                            let idx = (self.machine_st.iip + inner_offset) as usize;
                            let o = indexed_choice[idx];

                            if idx + 1 == indexed_choice.len() {
                                return if self.next_clause_applicable(self.machine_st.p + o) {
                                    Some(inner_offset)
                                } else {
                                    None
                                };
                            } else {
                                if self.next_clause_applicable(self.machine_st.p + o) {
                                    return Some(inner_offset);
                                }

                                inner_offset += 1;
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    #[inline(always)]
    pub(super) fn try_me_else(&mut self, offset: usize) {
        if let Some(offset) = self.next_applicable_clause(offset) {
            let n = self.machine_st.num_of_args;
            let b = self.machine_st.stack.allocate_or_frame(n);
            let or_frame = self.machine_st.stack.index_or_frame_mut(b);

            or_frame.prelude.num_cells = n;
            or_frame.prelude.e = self.machine_st.e;
            or_frame.prelude.cp = self.machine_st.cp;
            or_frame.prelude.b = self.machine_st.b;
            or_frame.prelude.bp = self.machine_st.p + offset;
            or_frame.prelude.boip = 0;
            or_frame.prelude.biip = 0;
            or_frame.prelude.tr = self.machine_st.tr;
            or_frame.prelude.h = self.machine_st.heap.len();
            or_frame.prelude.b0 = self.machine_st.b0;
            or_frame.prelude.attr_var_queue_len =
                self.machine_st.attr_var_init.attr_var_queue.len();

            self.machine_st.b = b;

            for i in 0..n {
                or_frame[i] = self.machine_st.registers[i + 1];
            }

            self.machine_st.hb = self.machine_st.heap.len();
        }

        self.machine_st.p += 1;
    }

    #[inline(always)]
    pub(super) fn indexed_try(&mut self, offset: usize) {
        if let Some(iip_offset) = self.next_inner_applicable_clause() {
            let n = self.machine_st.num_of_args;
            let b = self.machine_st.stack.allocate_or_frame(n);
            let or_frame = self.machine_st.stack.index_or_frame_mut(b);

            or_frame.prelude.num_cells = n;
            or_frame.prelude.e = self.machine_st.e;
            or_frame.prelude.cp = self.machine_st.cp;
            or_frame.prelude.b = self.machine_st.b;
            or_frame.prelude.bp = self.machine_st.p;
            or_frame.prelude.boip = self.machine_st.oip;
            or_frame.prelude.biip = self.machine_st.iip + iip_offset; // 1
            or_frame.prelude.tr = self.machine_st.tr;
            or_frame.prelude.h = self.machine_st.heap.len();
            or_frame.prelude.b0 = self.machine_st.b0;
            or_frame.prelude.attr_var_queue_len =
                self.machine_st.attr_var_init.attr_var_queue.len();

            self.machine_st.b = b;

            for i in 0..n {
                or_frame[i] = self.machine_st.registers[i + 1];
            }

            self.machine_st.hb = self.machine_st.heap.len();

            self.machine_st.oip = 0;
            self.machine_st.iip = 0;
        }

        self.machine_st.p += offset;
    }

    #[inline(always)]
    fn retry_me_else(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.num_cells;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;

        for i in 0..n {
            self.machine_st.registers[i + 1] = or_frame[i];
        }

        self.unwind_trail(old_tr, curr_tr);

        if let Some(offset) = self.next_applicable_clause(offset) {
            let or_frame = self.machine_st.stack.index_or_frame_mut(b);

            self.machine_st.num_of_args = n;
            self.machine_st.e = or_frame.prelude.e;
            self.machine_st.cp = or_frame.prelude.cp;

            or_frame.prelude.bp = self.machine_st.p + offset;

            let target_h = or_frame.prelude.h;
            let attr_var_queue_len = or_frame.prelude.attr_var_queue_len;

            self.machine_st.tr = or_frame.prelude.tr;
            self.reset_attr_var_state(attr_var_queue_len);

            self.machine_st.hb = target_h;

            self.machine_st.trail.truncate(self.machine_st.tr);
            self.machine_st.heap.truncate(target_h);

            self.machine_st.p += 1;
        } else {
            self.trust_me_epilogue();
        }
    }

    #[inline(always)]
    fn retry(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame_mut(b);
        let n = or_frame.prelude.num_cells;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;

        for i in 0..n {
            self.machine_st.registers[i + 1] = or_frame[i];
        }

        self.unwind_trail(old_tr, curr_tr);

        if let Some(iip_offset) = self.next_inner_applicable_clause() {
            let or_frame = self.machine_st.stack.index_or_frame_mut(b);

            self.machine_st.num_of_args = n;
            self.machine_st.e = or_frame.prelude.e;
            self.machine_st.cp = or_frame.prelude.cp;

            or_frame.prelude.biip += iip_offset;

            let target_h = or_frame.prelude.h;
            let attr_var_queue_len = or_frame.prelude.attr_var_queue_len;

            self.machine_st.tr = or_frame.prelude.tr;
            self.machine_st.trail.truncate(self.machine_st.tr);

            self.reset_attr_var_state(attr_var_queue_len);

            self.machine_st.hb = target_h;
            self.machine_st.p += offset;

            self.machine_st.heap.truncate(target_h);

            self.machine_st.oip = 0;
            self.machine_st.iip = 0;
        } else {
            self.trust_epilogue(offset);
        }
    }

    #[inline(always)]
    fn trust(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.num_cells;

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;

        for i in 0..n {
            self.machine_st.registers[i + 1] = or_frame[i];
        }

        self.unwind_trail(old_tr, curr_tr);
        self.trust_epilogue(offset);
    }

    #[inline(always)]
    fn trust_epilogue(&mut self, offset: usize) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.num_cells;

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;
        self.machine_st.trail.truncate(self.machine_st.tr);

        self.machine_st.b = or_frame.prelude.b;

        self.reset_attr_var_state(or_frame.prelude.attr_var_queue_len);

        self.machine_st.hb = target_h;
        self.machine_st.p = self.machine_st.p + offset;

        self.machine_st.stack.truncate(b);
        self.machine_st.heap.truncate(target_h);

        self.machine_st.oip = 0;
        self.machine_st.iip = 0;
    }

    #[inline(always)]
    fn trust_me(&mut self) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.num_cells;

        for i in 0..n {
            self.machine_st.registers[i + 1] = or_frame[i];
        }

        let old_tr = or_frame.prelude.tr;
        let curr_tr = self.machine_st.tr;

        self.unwind_trail(old_tr, curr_tr);

        self.trust_me_epilogue();
    }

    #[inline(always)]
    fn trust_me_epilogue(&mut self) {
        let b = self.machine_st.b;
        let or_frame = self.machine_st.stack.index_or_frame(b);
        let n = or_frame.prelude.num_cells;

        self.machine_st.num_of_args = n;
        self.machine_st.e = or_frame.prelude.e;
        self.machine_st.cp = or_frame.prelude.cp;

        let target_h = or_frame.prelude.h;

        self.machine_st.tr = or_frame.prelude.tr;
        self.machine_st.b = or_frame.prelude.b;

        self.reset_attr_var_state(or_frame.prelude.attr_var_queue_len);

        self.machine_st.hb = target_h;
        self.machine_st.p += 1;

        self.machine_st.trail.truncate(self.machine_st.tr);
        self.machine_st.stack.truncate(b);
        self.machine_st.heap.truncate(target_h);
    }

    #[inline(always)]
    fn undefined_procedure(&mut self, name: Atom, arity: usize) -> CallResult {
        match self.machine_st.flags.unknown {
            Unknown::Error => Err(self.machine_st.throw_undefined_error(name, arity)),
            Unknown::Fail => {
                self.machine_st.fail = true;
                Ok(())
            }
            Unknown::Warn => {
                println!(
                    "warning: predicate {}/{} is undefined",
                    name.as_str(),
                    arity
                );
                self.machine_st.fail = true;
                Ok(())
            }
        }
    }

    #[inline(always)]
    fn try_call(&mut self, name: Atom, arity: usize, idx: IndexPtr) -> CallResult {
        let compiled_tl_index = idx.p() as usize;

        match idx.tag() {
            IndexPtrTag::DynamicUndefined => {
                self.machine_st.fail = true;
            }
            IndexPtrTag::Undefined => {
                return self.undefined_procedure(name, arity);
            }
            IndexPtrTag::DynamicIndex => {
                self.machine_st.dynamic_mode = FirstOrNext::First;
                self.machine_st.call_at_index(arity, compiled_tl_index);
            }
            IndexPtrTag::Index => {
                self.machine_st.call_at_index(arity, compiled_tl_index);
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn try_execute(&mut self, name: Atom, arity: usize, idx: IndexPtr) -> CallResult {
        let compiled_tl_index = idx.p() as usize;

        match idx.tag() {
            IndexPtrTag::DynamicUndefined => {
                self.machine_st.fail = true;
            }
            IndexPtrTag::Undefined => {
                return self.undefined_procedure(name, arity);
            }
            IndexPtrTag::DynamicIndex => {
                self.machine_st.dynamic_mode = FirstOrNext::First;
                self.machine_st.execute_at_index(arity, compiled_tl_index);
            }
            IndexPtrTag::Index => self.machine_st.execute_at_index(arity, compiled_tl_index),
        }

        Ok(())
    }

    #[inline(always)]
    fn call_clause(&mut self, module_name: Atom, key: PredicateKey) -> CallResult {
        let (name, arity) = key;

        if module_name == atom!("user") {
            if let Some(idx) = self.indices.code_dir.get(&(name, arity)).cloned() {
                self.try_call(name, arity, idx.get())
            } else {
                Err(self.machine_st.throw_undefined_error(name, arity))
            }
        } else {
            if let Some(module) = self.indices.modules.get(&module_name) {
                if let Some(idx) = module.code_dir.get(&(name, arity)).cloned() {
                    self.try_call(name, arity, idx.get())
                } else {
                    self.undefined_procedure(name, arity)
                }
            } else {
                let stub = functor_stub(name, arity);
                let err = self
                    .machine_st
                    .module_resolution_error(module_name, name, arity);

                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    #[inline(always)]
    fn execute_clause(&mut self, module_name: Atom, key: PredicateKey) -> CallResult {
        let (name, arity) = key;

        if module_name == atom!("user") {
            if let Some(idx) = self.indices.code_dir.get(&(name, arity)).cloned() {
                self.try_execute(name, arity, idx.get())
            } else {
                self.undefined_procedure(name, arity)
            }
        } else {
            if let Some(module) = self.indices.modules.get(&module_name) {
                if let Some(idx) = module.code_dir.get(&(name, arity)).cloned() {
                    self.try_execute(name, arity, idx.get())
                } else {
                    self.undefined_procedure(name, arity)
                }
            } else {
                let stub = functor_stub(name, arity);
                let err = self
                    .machine_st
                    .module_resolution_error(module_name, name, arity);

                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    #[inline(always)]
    fn call_n(&mut self, module_name: Atom, arity: usize) -> CallResult {
        let key = self.machine_st.setup_call_n(arity)?;
        self.call_clause(module_name, key)
    }

    #[inline(always)]
    fn execute_n(&mut self, module_name: Atom, arity: usize) -> CallResult {
        let key = self.machine_st.setup_call_n(arity)?;
        self.execute_clause(module_name, key)
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

                RCWH = self
                    .indices
                    .get_predicate_code_index(r_c_w_h_atom, 0, iso_ext)
                    .and_then(|item| item.local())
                    .unwrap();
                RCWOH = self
                    .indices
                    .get_predicate_code_index(r_c_wo_h_atom, 1, iso_ext)
                    .and_then(|item| item.local())
                    .unwrap();
            });

            (RCWH, RCWOH)
        };

        if let Some(&(_, b_cutoff, prev_block)) = self.machine_st.cont_pts.last() {
            if self.machine_st.b < b_cutoff {
                let (idx, arity) = if self.machine_st.effective_block() > prev_block {
                    (r_c_w_h, 0)
                } else {
                    self.machine_st.registers[1] =
                        fixnum_as_cell!(Fixnum::build_with(b_cutoff as i64));

                    (r_c_wo_h, 1)
                };

                self.machine_st.call_at_index(arity, idx);
                return true;
            }
        }

        false
    }

    pub(super) fn unwind_trail(&mut self, a1: usize, a2: usize) {
        // the sequence is reversed to respect the chronology of trail
        // additions now that deleted attributes can be undeleted by
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
                TrailEntryTag::TrailedAttrVarListLink => {
                    let l = self.machine_st.trail[i + 1].get_value() as usize;

                    if l < self.machine_st.hb {
                        if h == l {
                            self.machine_st.heap[h] = heap_loc_as_cell!(h);
                        } else {
                            read_heap_cell!(self.machine_st.heap[l],
                                (HeapCellValueTag::Var) => {
                                    self.machine_st.heap[h] = list_loc_as_cell!(l);
                                }
                                _ => {
                                    self.machine_st.heap[h] = heap_loc_as_cell!(l);
                                }
                            );
                        }
                    } else {
                        self.machine_st.heap[h] = heap_loc_as_cell!(h);
                    }
                }
                TrailEntryTag::TrailedBlackboardEntry => {
                    let key = Atom::from(h as u64);

                    match self.indices.global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = None,
                        None => unreachable!(),
                    }
                }
                TrailEntryTag::TrailedBlackboardOffset => {
                    let key = Atom::from(h as u64);
                    let value_cell = HeapCellValue::from(u64::from(self.machine_st.trail[i + 1]));

                    match self.indices.global_variables.get_mut(&key) {
                        Some((_, ref mut loc)) => *loc = Some(value_cell),
                        None => unreachable!(),
                    }
                }
                TrailEntryTag::TrailedAttachedValue => {}
            }
        }
    }
}
