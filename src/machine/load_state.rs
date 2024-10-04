use crate::forms::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::preprocessor::*;
use crate::machine::term_stream::*;
use crate::machine::*;
use crate::parser::ast::*;

use fxhash::FxBuildHasher;
use indexmap::IndexSet;

use std::collections::VecDeque;
use std::fs::File;
use std::mem;

pub(super) type ModuleOpExports = Vec<(OpDecl, Option<OpDesc>)>;

pub(super) fn set_code_index(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    key: PredicateKey,
    mut code_index: CodeIndex,
    code_ptr: IndexPtr,
) {
    let record = match compilation_target {
        CompilationTarget::User => {
            if IndexPtrTag::Undefined == code_index.get().tag() {
                code_index.set(code_ptr);
                RetractionRecord::AddedUserPredicate(key)
            } else {
                let replaced = code_index.replace(code_ptr);
                RetractionRecord::ReplacedUserPredicate(key, replaced)
            }
        }
        CompilationTarget::Module(ref module_name) => {
            if IndexPtrTag::Undefined == code_index.get().tag() {
                code_index.set(code_ptr);
                RetractionRecord::AddedModulePredicate(*module_name, key)
            } else {
                let replaced = code_index.replace(code_ptr);
                RetractionRecord::ReplacedModulePredicate(*module_name, key, replaced)
            }
        }
    };

    retraction_info.push_record(record);
}

fn add_op_decl_as_module_export<'a, LS: LoadState<'a>>(
    payload: &mut LS::LoaderFieldType,
    module_op_dir: &mut OpDir,
    wam_op_dir: &mut OpDir,
    op_decl: &OpDecl,
) {
    /*
    insert the operator at top-level so it can
    inform the parser. it will be retracted
    from the user-level op_dir when the load
    succeeds.
    */

    match op_decl.insert_into_op_dir(wam_op_dir) {
        Some(op_desc) => {
            payload
                .retraction_info
                .push_record(RetractionRecord::ReplacedUserOp(*op_decl, op_desc));

            payload.module_op_exports.push((*op_decl, Some(op_desc)));
        }
        None => {
            payload
                .retraction_info
                .push_record(RetractionRecord::AddedUserOp(*op_decl));
            payload.module_op_exports.push((*op_decl, None));
        }
    }

    let compilation_target = payload.compilation_target;
    add_op_decl(
        &mut payload.retraction_info,
        &compilation_target,
        module_op_dir,
        op_decl,
    );
}

pub(super) fn add_op_decl(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    op_dir: &mut OpDir,
    op_decl: &OpDecl,
) {
    match op_decl.insert_into_op_dir(op_dir) {
        Some(op_desc) => match &compilation_target {
            CompilationTarget::User => {
                retraction_info.push_record(RetractionRecord::ReplacedUserOp(*op_decl, op_desc));
            }
            CompilationTarget::Module(ref module_name) => {
                retraction_info.push_record(RetractionRecord::ReplacedModuleOp(
                    *module_name,
                    *op_decl,
                    op_desc,
                ));
            }
        },
        None => match &compilation_target {
            CompilationTarget::User => {
                retraction_info.push_record(RetractionRecord::AddedUserOp(*op_decl));
            }
            CompilationTarget::Module(ref module_name) => {
                retraction_info
                    .push_record(RetractionRecord::AddedModuleOp(*module_name, *op_decl));
            }
        },
    }
}

pub(super) fn import_module_exports<'a, LS: LoadState<'a>>(
    payload: &mut LS::LoaderFieldType,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                let key = (*name, *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key, meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key).cloned() {
                    let arena = &mut LS::machine_st(payload).arena;

                    let target_code_index = *code_dir
                        .entry(key)
                        .or_insert_with(|| CodeIndex::default(arena));

                    set_code_index(
                        &mut payload.retraction_info,
                        compilation_target,
                        key,
                        target_code_index,
                        src_code_index.get(),
                    );

                    if src_code_index.is_dynamic_undefined() {
                        code_dir.insert(key, src_code_index);
                    }
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name,
                        key,
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl(
                    &mut payload.retraction_info,
                    compilation_target,
                    op_dir,
                    op_decl,
                );
            }
        }
    }

    Ok(())
}

fn import_module_exports_into_module<'a, LS: LoadState<'a>>(
    payload: &mut LS::LoaderFieldType,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
    wam_op_dir: &mut OpDir,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                let key = (*name, *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key, meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let arena = &mut LS::machine_st(payload).arena;

                    let target_code_index = *code_dir
                        .entry(key)
                        .or_insert_with(|| CodeIndex::default(arena));

                    set_code_index(
                        &mut payload.retraction_info,
                        compilation_target,
                        key,
                        target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name,
                        (*name, *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl_as_module_export::<LS>(payload, op_dir, wam_op_dir, op_decl);
            }
        }
    }

    Ok(())
}

fn import_qualified_module_exports<'a, LS: LoadState<'a>>(
    payload: &mut LS::LoaderFieldType,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    exports: &IndexSet<ModuleExport>,
    wam_prelude: &mut MachinePreludeView,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        if !exports.contains(export) {
            continue;
        }

        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                let key = (*name, *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    wam_prelude
                        .indices
                        .meta_predicates
                        .insert(key, meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let arena = &mut LS::machine_st(payload).arena;

                    let target_code_index = *wam_prelude
                        .indices
                        .code_dir
                        .entry(key)
                        .or_insert_with(|| CodeIndex::new(IndexPtr::undefined(), arena));

                    set_code_index(
                        &mut payload.retraction_info,
                        compilation_target,
                        key,
                        target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name,
                        (*name, *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl(
                    &mut payload.retraction_info,
                    compilation_target,
                    &mut wam_prelude.indices.op_dir,
                    op_decl,
                );
            }
        }
    }

    Ok(())
}

fn import_qualified_module_exports_into_module<'a, LS: LoadState<'a>>(
    payload: &mut LS::LoaderFieldType,
    imported_module: &Module,
    exports: &IndexSet<ModuleExport>,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
    wam_op_dir: &mut OpDir,
) -> Result<(), SessionError> {
    let payload_compilation_target = payload.compilation_target;

    for export in imported_module.module_decl.exports.iter() {
        if !exports.contains(export) {
            continue;
        }

        match export {
            ModuleExport::PredicateKey((name, arity)) => {
                let key = (*name, *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key, meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let arena = &mut LS::machine_st(payload).arena;

                    let target_code_index = *code_dir
                        .entry(key)
                        .or_insert_with(|| CodeIndex::new(IndexPtr::undefined(), arena));

                    set_code_index(
                        &mut payload.retraction_info,
                        &payload_compilation_target,
                        key,
                        target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name,
                        (*name, *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl_as_module_export::<LS>(payload, op_dir, wam_op_dir, op_decl);
            }
        }
    }

    Ok(())
}

impl<'a, LS: LoadState<'a>> Loader<'a, LS> {
    pub(super) fn retract_local_clauses_impl(
        &mut self,
        compilation_target: CompilationTarget,
        key: PredicateKey,
        clause_locs: &VecDeque<usize>,
    ) {
        let result_opt = self
            .wam_prelude
            .indices
            .get_predicate_skeleton_mut(&compilation_target, &key)
            .map(|skeleton| {
                (
                    clause_locs
                        .iter()
                        .map(|clause_clause_loc| {
                            skeleton.target_pos_of_clause_clause_loc(*clause_clause_loc)
                        })
                        .collect(),
                    skeleton.core.is_dynamic,
                )
            });

        if let Some((clause_target_poses, is_dynamic)) = result_opt {
            self.retract_local_clauses_by_locs(
                compilation_target,
                key,
                clause_target_poses,
                is_dynamic,
            );
        }
    }

    pub(super) fn retract_local_clauses_by_locs(
        &mut self,
        compilation_target: CompilationTarget,
        key: PredicateKey,
        mut clause_target_poses: Vec<Option<usize>>,
        is_dynamic: bool,
    ) {
        let old_compilation_target =
            mem::replace(&mut self.payload.compilation_target, compilation_target);

        while let Some(target_pos_opt) = clause_target_poses.pop() {
            match target_pos_opt {
                Some(target_pos) if is_dynamic => {
                    self.retract_dynamic_clause(key, target_pos);
                }
                Some(target_pos) => {
                    self.retract_clause(key, target_pos);
                }
                None => {
                    // Here because the clause was been removed
                    // earlier, e.g., by retract, without updating the
                    // local skeleton. In this case, do nothing.
                }
            }
        }

        self.payload.compilation_target = old_compilation_target;
    }

    pub(super) fn retract_local_clause_clauses(
        &mut self,
        clause_clause_compilation_target: CompilationTarget,
        clause_locs: &VecDeque<usize>,
    ) {
        let key = (atom!("$clause"), 2);
        let listing_src_file_name = self.listing_src_file_name();

        match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
            self.payload.compilation_target,
            clause_clause_compilation_target,
            listing_src_file_name,
            key,
        ) {
            Some(skeleton) => {
                let payload_compilation_target = self.payload.compilation_target;

                self.payload.retraction_info.push_record(
                    RetractionRecord::RemovedLocalSkeletonClauseLocations(
                        payload_compilation_target,
                        clause_clause_compilation_target,
                        key,
                        std::mem::take(&mut skeleton.clause_clause_locs),
                    ),
                );

                skeleton.reset();
            }
            None => {
                // The local skeleton might be removed when reloading
                // or redefining a module, in which case no retraction
                // record is necessary.
            }
        };

        self.retract_local_clauses_impl(clause_clause_compilation_target, key, clause_locs);
    }

    pub(super) fn try_term_to_tl(
        &mut self,
        term: Term,
        preprocessor: &mut Preprocessor,
    ) -> Result<PredicateClause, SessionError> {
        let tl = preprocessor.try_term_to_tl(self, term)?;

        Ok(match tl {
            TopLevel::Fact(fact, var_data) => PredicateClause::Fact(fact, var_data),
            TopLevel::Rule(rule, var_data) => PredicateClause::Rule(rule, var_data),
        })
    }

    #[inline]
    pub(super) fn remove_module_op_exports(&mut self) {
        for (mut op_decl, record) in self.payload.module_op_exports.drain(0..) {
            op_decl.remove(&mut self.wam_prelude.indices.op_dir);

            if let Some(op_desc) = record {
                op_decl.op_desc = op_desc;
                op_decl.insert_into_op_dir(&mut self.wam_prelude.indices.op_dir);
            }
        }
    }

    pub(super) fn remove_replaced_in_situ_module(&mut self, module_name: Atom) {
        let mut removed_module = match self.wam_prelude.indices.modules.swap_remove(&module_name) {
            Some(module) => module,
            None => return,
        };

        let mut skipped_local_predicates = IndexSet::with_hasher(FxBuildHasher::default());

        for ((local_compilation_target, key), skeleton) in
            removed_module.local_extensible_predicates.iter()
        {
            skipped_local_predicates.insert(key);

            if skeleton.is_multifile {
                continue;
            }

            if let Some(code_index) = removed_module.code_dir.get_mut(key) {
                if let Some(global_skeleton) = self
                    .wam_prelude
                    .indices
                    .get_predicate_skeleton(local_compilation_target, key)
                {
                    let old_index_ptr = code_index.replace(if global_skeleton.core.is_dynamic {
                        IndexPtr::dynamic_undefined()
                    } else {
                        IndexPtr::undefined()
                    });

                    self.payload.retraction_info.push_record(
                        RetractionRecord::ReplacedModulePredicate(module_name, *key, old_index_ptr),
                    );
                }
            }
        }

        for (key, code_index) in removed_module.code_dir.iter_mut() {
            if skipped_local_predicates.contains(key) {
                continue;
            }

            if !code_index.is_undefined() && !code_index.is_dynamic_undefined() {
                let old_index_ptr = code_index.replace(IndexPtr::undefined());

                self.payload.retraction_info.push_record(
                    RetractionRecord::ReplacedModulePredicate(module_name, *key, old_index_ptr),
                );
            }
        }

        for (key, skeleton) in removed_module.extensible_predicates.drain(..) {
            self.payload
                .retraction_info
                .push_record(RetractionRecord::RemovedSkeleton(
                    CompilationTarget::Module(module_name),
                    key,
                    skeleton,
                ));
        }

        self.wam_prelude
            .indices
            .modules
            .insert(module_name, removed_module);
    }

    pub(super) fn remove_module_exports(&mut self, module_name: Atom) {
        let removed_module = match self.wam_prelude.indices.modules.swap_remove(&module_name) {
            Some(module) => module,
            None => return,
        };

        fn remove_module_exports(
            removed_module: &Module,
            code_dir: &mut CodeDir,
            op_dir: &mut OpDir,
            retraction_info: &mut RetractionInfo,
            predicate_retractor: impl Fn(PredicateKey, IndexPtr) -> RetractionRecord,
            op_retractor: impl Fn(OpDecl, OpDesc) -> RetractionRecord,
        ) {
            for export in removed_module.module_decl.exports.iter() {
                match export {
                    ModuleExport::PredicateKey(ref key) => {
                        match (removed_module.code_dir.get(key), code_dir.get_mut(key)) {
                            (Some(module_code_index), Some(target_code_index))
                                if module_code_index.get() == target_code_index.get() =>
                            {
                                let old_index_ptr =
                                    target_code_index.replace(IndexPtr::undefined());
                                retraction_info
                                    .push_record(predicate_retractor(*key, old_index_ptr));
                            }
                            _ => {}
                        }
                    }
                    ModuleExport::OpDecl(op_decl) => {
                        let op_dir_value_opt = op_dir
                            .swap_remove(&(op_decl.name, op_decl.op_desc.get_spec().fixity()));

                        if let Some(op_desc) = op_dir_value_opt {
                            retraction_info.push_record(op_retractor(*op_decl, op_desc));
                        }
                    }
                }
            }
        }

        match self.payload.compilation_target {
            CompilationTarget::User => {
                remove_module_exports(
                    &removed_module,
                    &mut self.wam_prelude.indices.code_dir,
                    &mut self.wam_prelude.indices.op_dir,
                    &mut self.payload.retraction_info,
                    RetractionRecord::ReplacedUserPredicate,
                    RetractionRecord::ReplacedUserOp,
                );
            }
            CompilationTarget::Module(target_module_name) if target_module_name != module_name => {
                let predicate_retractor = |key, index_ptr| {
                    RetractionRecord::ReplacedModulePredicate(module_name, key, index_ptr)
                };

                let op_retractor = |op_decl, op_desc| {
                    RetractionRecord::ReplacedModuleOp(module_name, op_decl, op_desc)
                };

                if let Some(module) = self
                    .wam_prelude
                    .indices
                    .modules
                    .get_mut(&target_module_name)
                {
                    remove_module_exports(
                        &removed_module,
                        &mut module.code_dir,
                        &mut module.op_dir,
                        &mut self.payload.retraction_info,
                        predicate_retractor,
                        op_retractor,
                    );
                } else {
                    unreachable!()
                }
            }
            CompilationTarget::Module(_) => {}
        };

        self.wam_prelude
            .indices
            .modules
            .insert(module_name, removed_module);
    }

    fn get_or_insert_local_code_index(
        &mut self,
        module_name: Atom,
        key: PredicateKey,
    ) -> CodeIndex {
        match self.wam_prelude.indices.modules.get_mut(&module_name) {
            Some(ref mut module) => *module.code_dir.entry(key).or_insert_with(|| {
                CodeIndex::new(
                    IndexPtr::undefined(),
                    &mut LS::machine_st(&mut self.payload).arena,
                )
            }),
            None => {
                self.add_dynamically_generated_module(module_name);

                match self.wam_prelude.indices.modules.get_mut(&module_name) {
                    Some(ref mut module) => *module.code_dir.entry(key).or_insert_with(|| {
                        CodeIndex::new(
                            IndexPtr::undefined(),
                            &mut LS::machine_st(&mut self.payload).arena,
                        )
                    }),
                    None => {
                        unreachable!()
                    }
                }
            }
        }
    }

    pub(super) fn get_or_insert_code_index(
        &mut self,
        key: PredicateKey,
        compilation_target: CompilationTarget,
    ) -> CodeIndex {
        let arena = &mut LS::machine_st(&mut self.payload).arena;

        match compilation_target {
            CompilationTarget::User => *self
                .wam_prelude
                .indices
                .code_dir
                .entry(key)
                .or_insert_with(|| CodeIndex::new(IndexPtr::undefined(), arena)),
            CompilationTarget::Module(module_name) => {
                self.get_or_insert_local_code_index(module_name, key)
            }
        }
    }

    pub(super) fn get_or_insert_qualified_code_index(
        &mut self,
        module_name: Atom,
        key: PredicateKey,
    ) -> CodeIndex {
        let arena = &mut LS::machine_st(&mut self.payload).arena;

        if module_name == atom!("user") {
            return *self
                .wam_prelude
                .indices
                .code_dir
                .entry(key)
                .or_insert_with(|| CodeIndex::new(IndexPtr::undefined(), arena));
        } else {
            self.get_or_insert_local_code_index(module_name, key)
        }
    }

    #[inline]
    pub(super) fn add_extensible_predicate(
        &mut self,
        key: PredicateKey,
        skeleton: PredicateSkeleton,
        compilation_target: CompilationTarget,
    ) {
        match compilation_target {
            CompilationTarget::User => {
                self.wam_prelude
                    .indices
                    .extensible_predicates
                    .insert(key, skeleton);

                let record =
                    RetractionRecord::AddedExtensiblePredicate(CompilationTarget::User, key);

                self.payload.retraction_info.push_record(record);
            }
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.wam_prelude.indices.modules.get_mut(&module_name) {
                    module.extensible_predicates.insert(key, skeleton);

                    let record = RetractionRecord::AddedExtensiblePredicate(
                        CompilationTarget::Module(module_name),
                        key,
                    );

                    self.payload.retraction_info.push_record(record);
                } else {
                    unreachable!()
                }
            }
        }
    }

    #[inline]
    pub(super) fn add_local_extensible_predicate(
        &mut self,
        local_compilation_target: CompilationTarget,
        key: PredicateKey,
        skeleton: LocalPredicateSkeleton,
    ) {
        let src_compilation_target = match self.listing_src_file_name() {
            Some(filename) => CompilationTarget::Module(filename),
            None => self.payload.compilation_target,
        };

        match src_compilation_target {
            CompilationTarget::User => {
                self.wam_prelude
                    .indices
                    .local_extensible_predicates
                    .insert((local_compilation_target, key), skeleton);
            }
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.wam_prelude.indices.modules.get_mut(&module_name) {
                    module
                        .local_extensible_predicates
                        .insert((local_compilation_target, key), skeleton);
                } else {
                    unreachable!()
                }
            }
        }
    }

    pub(super) fn add_op_decl(&mut self, op_decl: &OpDecl) {
        let listing_src_file_name = self.listing_src_file_name();
        let payload_compilation_target = self.payload.compilation_target;

        match payload_compilation_target {
            CompilationTarget::User => {
                if let Some(filename) = listing_src_file_name {
                    if let Some(ref mut module) =
                        self.wam_prelude.indices.modules.get_mut(&filename)
                    {
                        op_decl.insert_into_op_dir(&mut module.op_dir);
                    }
                }

                add_op_decl(
                    &mut self.payload.retraction_info,
                    &payload_compilation_target,
                    &mut self.wam_prelude.indices.op_dir,
                    op_decl,
                );
            }
            CompilationTarget::Module(ref module_name) => {
                match self.wam_prelude.indices.modules.get_mut(module_name) {
                    Some(ref mut module) => {
                        add_op_decl_as_module_export::<LS>(
                            &mut self.payload,
                            &mut module.op_dir,
                            &mut self.wam_prelude.indices.op_dir,
                            op_decl,
                        );
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
        }
    }

    pub(super) fn get_clause_type(&mut self, name: Atom, arity: usize) -> ClauseType {
        let arena = &mut LS::machine_st(&mut self.payload).arena;

        match ClauseType::from(name, arity, arena) {
            ClauseType::Named(arity, name, _) => {
                let payload_compilation_target = self.payload.compilation_target;

                let idx = self.get_or_insert_code_index((name, arity), payload_compilation_target);

                ClauseType::Named(arity, name, idx)
            }
            ct => ct,
        }
    }

    pub(super) fn get_qualified_clause_type(
        &mut self,
        module_name: Atom,
        name: Atom,
        arity: usize,
    ) -> ClauseType {
        let arena = &mut LS::machine_st(&mut self.payload).arena;

        match ClauseType::from(name, arity, arena) {
            ClauseType::Named(arity, name, _) => {
                let key = (name, arity);
                let idx = self.get_or_insert_qualified_code_index(module_name, key);

                ClauseType::Named(arity, name, idx)
            }
            ct => ct,
        }
    }

    pub(super) fn get_meta_specs(&self, name: Atom, arity: usize) -> Option<&Vec<MetaSpec>> {
        self.wam_prelude.indices.get_meta_predicate_spec(
            name,
            arity,
            &self.payload.compilation_target,
        )
    }

    pub(super) fn add_meta_predicate_record(
        &mut self,
        module_name: Atom,
        name: Atom,
        meta_specs: Vec<MetaSpec>,
    ) {
        let arity = meta_specs.len();
        let key = (name, arity);

        match module_name {
            atom!("user") => {
                match self
                    .wam_prelude
                    .indices
                    .meta_predicates
                    .insert(key, meta_specs)
                {
                    Some(old_meta_specs) => {
                        self.payload.retraction_info.push_record(
                            RetractionRecord::ReplacedMetaPredicate(
                                module_name,
                                key.0,
                                old_meta_specs,
                            ),
                        );
                    }
                    None => {
                        self.payload
                            .retraction_info
                            .push_record(RetractionRecord::AddedMetaPredicate(module_name, key));
                    }
                }
            }
            _ => match self.wam_prelude.indices.modules.get_mut(&module_name) {
                Some(ref mut module) => match module.meta_predicates.insert(key, meta_specs) {
                    Some(old_meta_specs) => {
                        self.payload.retraction_info.push_record(
                            RetractionRecord::ReplacedMetaPredicate(
                                module_name,
                                key.0,
                                old_meta_specs,
                            ),
                        );
                    }
                    None => {
                        self.payload
                            .retraction_info
                            .push_record(RetractionRecord::AddedMetaPredicate(module_name, key));
                    }
                },
                None => {
                    self.add_dynamically_generated_module(module_name);

                    if let Some(module) = self.wam_prelude.indices.modules.get_mut(&module_name) {
                        module.meta_predicates.insert(key, meta_specs);
                    } else {
                        unreachable!()
                    }

                    self.payload
                        .retraction_info
                        .push_record(RetractionRecord::AddedMetaPredicate(module_name, key));
                }
            },
        }
    }

    pub(super) fn add_dynamically_generated_module(&mut self, module_name: Atom) {
        let module_decl = ModuleDecl {
            name: module_name,
            exports: vec![],
        };

        let listing_src = ListingSource::DynamicallyGenerated;
        let mut module = Module::new(module_decl, listing_src);

        self.import_builtins_in_module(
            module_name,
            &mut module.code_dir,
            &mut module.op_dir,
            &mut module.meta_predicates,
        );

        self.payload
            .retraction_info
            .push_record(RetractionRecord::AddedModule(module_name));

        self.wam_prelude.indices.modules.insert(module_name, module);
    }

    fn import_builtins_in_module(
        &mut self,
        module_name: Atom,
        code_dir: &mut CodeDir,
        op_dir: &mut OpDir,
        meta_predicates: &mut MetaPredicateDir,
    ) {
        if let Some(builtins) = self.wam_prelude.indices.modules.get(&atom!("builtins")) {
            let module_compilation_target = CompilationTarget::Module(module_name);

            if CompilationTarget::Module(atom!("builtins")) == self.payload.compilation_target {
                return;
            }

            import_module_exports::<LS>(
                &mut self.payload,
                &module_compilation_target,
                builtins,
                code_dir,
                op_dir,
                meta_predicates,
            )
            .unwrap();
        }
    }

    pub(crate) fn reset_in_situ_module(
        &mut self,
        module_decl: ModuleDecl,
        listing_src: &ListingSource,
    ) {
        let module_name = module_decl.name;

        self.remove_module_exports(module_name);
        self.remove_replaced_in_situ_module(module_name);

        if let Some(module) = self.wam_prelude.indices.modules.get_mut(&module_name) {
            let old_module_decl = mem::replace(&mut module.module_decl, module_decl.clone());

            let local_extensible_predicates = mem::replace(
                &mut module.local_extensible_predicates,
                LocalExtensiblePredicates::with_hasher(FxBuildHasher::default()),
            );

            for ((compilation_target, key), skeleton) in local_extensible_predicates.iter() {
                self.retract_local_clauses_impl(
                    *compilation_target,
                    *key,
                    &skeleton.clause_clause_locs,
                );

                let is_dynamic = self
                    .wam_prelude
                    .indices
                    .get_predicate_skeleton(compilation_target, key)
                    .map(|skeleton| skeleton.core.is_dynamic)
                    .unwrap_or(false);

                if is_dynamic {
                    let clause_clause_compilation_target = match compilation_target {
                        CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
                        module => *module,
                    };

                    self.retract_local_clause_clauses(
                        clause_clause_compilation_target,
                        &skeleton.clause_clause_locs,
                    );
                }
            }

            self.payload
                .retraction_info
                .push_record(RetractionRecord::ReplacedModule(
                    old_module_decl,
                    listing_src.clone(),
                    local_extensible_predicates,
                ));
        }
    }

    pub(crate) fn add_module(
        &mut self,
        module_decl: ModuleDecl,
        listing_src: ListingSource,
    ) -> Result<(), SessionError> {
        let module_name = module_decl.name;

        if let Some(module) = self.wam_prelude.indices.modules.get(&module_name) {
            if let ListingSource::DynamicallyGenerated = module.listing_src {
            } else {
                LS::err_on_builtin_module_overwrite(module_name)?;
            }
        }

        self.reset_in_situ_module(module_decl.clone(), &listing_src);

        let mut module = match self.wam_prelude.indices.modules.swap_remove(&module_name) {
            Some(mut module) => {
                module.listing_src = listing_src;
                module
            }
            None => {
                self.payload
                    .retraction_info
                    .push_record(RetractionRecord::AddedModule(module_name));

                Module::new(module_decl, listing_src)
            }
        };

        self.import_builtins_in_module(
            module_name,
            &mut module.code_dir,
            &mut module.op_dir,
            &mut module.meta_predicates,
        );

        for export in &module.module_decl.exports {
            if let ModuleExport::OpDecl(ref op_decl) = export {
                add_op_decl_as_module_export::<LS>(
                    &mut self.payload,
                    &mut module.op_dir,
                    &mut self.wam_prelude.indices.op_dir,
                    op_decl,
                );
            }
        }

        if let Some(load_context) = self.wam_prelude.load_contexts.last_mut() {
            load_context.module = module_name;
        }

        self.wam_prelude.indices.modules.insert(module_name, module);

        Ok(())
    }

    pub(super) fn import_module(&mut self, module_name: Atom) -> Result<(), SessionError> {
        if let Some(module) = self.wam_prelude.indices.modules.swap_remove(&module_name) {
            let payload_compilation_target = self.payload.compilation_target;

            match &payload_compilation_target {
                CompilationTarget::User => {
                    import_module_exports::<LS>(
                        &mut self.payload,
                        &payload_compilation_target,
                        &module,
                        &mut self.wam_prelude.indices.code_dir,
                        &mut self.wam_prelude.indices.op_dir,
                        &mut self.wam_prelude.indices.meta_predicates,
                    )?;
                }
                CompilationTarget::Module(ref defining_module_name) => {
                    match self
                        .wam_prelude
                        .indices
                        .modules
                        .get_mut(defining_module_name)
                    {
                        Some(ref mut target_module) => {
                            import_module_exports_into_module::<LS>(
                                &mut self.payload,
                                &payload_compilation_target,
                                &module,
                                &mut target_module.code_dir,
                                &mut target_module.op_dir,
                                &mut target_module.meta_predicates,
                                &mut self.wam_prelude.indices.op_dir,
                            )?;
                        }
                        None => {
                            // we find ourselves here because we're trying to import
                            // a module into itself as it is being defined.
                            self.wam_prelude.indices.modules.insert(module_name, module);
                            return Err(SessionError::ModuleCannotImportSelf(module_name));
                        }
                    }
                }
            }

            self.wam_prelude.indices.modules.insert(module_name, module);
            Ok(())
        } else {
            Err(SessionError::ExistenceError(ExistenceError::Module(
                module_name,
            )))
        }
    }

    pub(super) fn import_qualified_module(
        &mut self,
        module_name: Atom,
        exports: IndexSet<ModuleExport>,
    ) -> Result<(), SessionError> {
        if let Some(module) = self.wam_prelude.indices.modules.swap_remove(&module_name) {
            let payload_compilation_target = self.payload.compilation_target;

            let result = match &payload_compilation_target {
                CompilationTarget::User => import_qualified_module_exports::<LS>(
                    &mut self.payload,
                    &payload_compilation_target,
                    &module,
                    &exports,
                    &mut self.wam_prelude,
                ),
                CompilationTarget::Module(ref defining_module_name) => {
                    match self
                        .wam_prelude
                        .indices
                        .modules
                        .get_mut(defining_module_name)
                    {
                        Some(ref mut target_module) => {
                            import_qualified_module_exports_into_module::<LS>(
                                &mut self.payload,
                                &module,
                                &exports,
                                &mut target_module.code_dir,
                                &mut target_module.op_dir,
                                &mut target_module.meta_predicates,
                                &mut self.wam_prelude.indices.op_dir,
                            )
                        }
                        None => Err(SessionError::ModuleCannotImportSelf(module_name)),
                    }
                }
            };

            self.wam_prelude.indices.modules.insert(module_name, module);
            result
        } else {
            Err(SessionError::ExistenceError(ExistenceError::Module(
                module_name,
            )))
        }
    }

    pub(crate) fn use_module(&mut self, module_src: ModuleSource) -> Result<(), SessionError> {
        let (stream, listing_src) = match module_src {
            ModuleSource::File(filename) => {
                let mut path_buf = PathBuf::from(&*filename.as_str());
                path_buf.set_extension("pl");

                let file = File::open(&path_buf)?;

                (
                    Stream::from_file_as_input(
                        filename,
                        file,
                        &mut LS::machine_st(&mut self.payload).arena,
                    ),
                    ListingSource::File(filename, path_buf),
                )
            }
            ModuleSource::Library(library) => match libraries::get(&library.as_str()) {
                Some(code) => {
                    if let Some(module) = self.wam_prelude.indices.modules.get(&library) {
                        if let ListingSource::DynamicallyGenerated = &module.listing_src {
                            (
                                Stream::from_static_string(
                                    code,
                                    &mut LS::machine_st(&mut self.payload).arena,
                                ),
                                ListingSource::User,
                            )
                        } else {
                            return self.import_module(library);
                        }
                    } else {
                        (
                            Stream::from_static_string(
                                code,
                                &mut LS::machine_st(&mut self.payload).arena,
                            ),
                            ListingSource::User,
                        )
                    }
                }
                None => {
                    return self.import_module(library);
                }
            },
        };

        let compilation_target = {
            let term_stream = BootstrappingTermStream::from_char_reader(
                stream,
                LS::machine_st(&mut self.payload),
                listing_src,
            );

            let subloader: Loader<'_, BootstrappingLoadState> = Loader {
                payload: BootstrappingLoadState(LoadStatePayload::new(
                    self.wam_prelude.code.len(),
                    term_stream,
                )),
                wam_prelude: MachinePreludeView {
                    indices: self.wam_prelude.indices,
                    code: self.wam_prelude.code,
                    load_contexts: self.wam_prelude.load_contexts,
                },
            };

            subloader.load()?
        };

        match compilation_target {
            CompilationTarget::User => {
                // nothing to do.
                Ok(())
            }
            CompilationTarget::Module(module_name) => self.import_module(module_name),
        }
    }

    pub(crate) fn use_qualified_module(
        &mut self,
        module_src: ModuleSource,
        exports: IndexSet<ModuleExport>,
    ) -> Result<(), SessionError> {
        let (stream, listing_src) = match module_src {
            ModuleSource::File(filename) => {
                let mut path_buf = PathBuf::from(&*filename.as_str());
                path_buf.set_extension("pl");
                let file = File::open(&path_buf)?;

                (
                    Stream::from_file_as_input(
                        filename,
                        file,
                        &mut LS::machine_st(&mut self.payload).arena,
                    ),
                    ListingSource::File(filename, path_buf),
                )
            }
            ModuleSource::Library(library) => match libraries::get(&library.as_str()) {
                Some(code) => {
                    if self.wam_prelude.indices.modules.contains_key(&library) {
                        return self.import_qualified_module(library, exports);
                    } else {
                        (
                            Stream::from_static_string(
                                code,
                                &mut LS::machine_st(&mut self.payload).arena,
                            ),
                            ListingSource::User,
                        )
                    }
                }
                None => {
                    return self.import_qualified_module(library, exports);
                }
            },
        };

        let compilation_target = {
            let term_stream = BootstrappingTermStream::from_char_reader(
                stream,
                LS::machine_st(&mut self.payload),
                listing_src,
            );

            let subloader: Loader<'_, BootstrappingLoadState> = Loader {
                payload: BootstrappingLoadState(LoadStatePayload::new(
                    self.wam_prelude.code.len(),
                    term_stream,
                )),
                wam_prelude: MachinePreludeView {
                    indices: self.wam_prelude.indices,
                    code: self.wam_prelude.code,
                    load_contexts: self.wam_prelude.load_contexts,
                },
            };

            subloader.load()?
        };

        match compilation_target {
            CompilationTarget::User => {
                // nothing to do.
                Ok(())
            }
            CompilationTarget::Module(module_name) => {
                self.import_qualified_module(module_name, exports)
            }
        }
    }
}
