use crate::machine::machine_indices::*;
use crate::machine::preprocessor::*;
use crate::machine::term_stream::*;
use crate::machine::*;

use prolog_parser::clause_name;

use indexmap::IndexSet;
use ref_thread_local::RefThreadLocal;
use slice_deque::{sdeq, SliceDeque};

type ModuleOpExports = Vec<(OpDecl, Option<(usize, Specifier)>)>;

/*
 * We will want to borrow these fields from Loader separately, without
 * restricting access to other fields by borrowing them mutably.
 */
pub(super) struct LoadState<'a> {
    pub(super) compilation_target: CompilationTarget,
    pub(super) module_op_exports: ModuleOpExports,
    pub(super) retraction_info: RetractionInfo,
    pub(super) wam: &'a mut Machine,
}

pub(super) fn set_code_index(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    key: PredicateKey,
    code_index: &CodeIndex,
    code_ptr: IndexPtr,
) {
    let record = match compilation_target {
        CompilationTarget::User => {
            if IndexPtr::Undefined == code_index.get() {
                code_index.set(code_ptr);
                RetractionRecord::AddedUserPredicate(key)
            } else {
                let replaced = code_index.replace(code_ptr);
                RetractionRecord::ReplacedUserPredicate(key, replaced)
            }
        }
        CompilationTarget::Module(ref module_name) => {
            if IndexPtr::Undefined == code_index.get() {
                code_index.set(code_ptr);
                RetractionRecord::AddedModulePredicate(module_name.clone(), key)
            } else {
                let replaced = code_index.replace(code_ptr);
                RetractionRecord::ReplacedModulePredicate(module_name.clone(), key, replaced)
            }
        }
    };

    retraction_info.push_record(record);
}

fn add_op_decl_as_module_export(
    module_op_dir: &mut OpDir,
    compilation_target: &CompilationTarget,
    retraction_info: &mut RetractionInfo,
    wam_op_dir: &mut OpDir,
    module_op_exports: &mut ModuleOpExports,
    op_decl: &OpDecl,
) {
    /*
    insert the operator at top-level so it can
    inform the parser. it will be retracted
    from the user-level op_dir when the load
    succeeds.
    */

    match op_decl.insert_into_op_dir(wam_op_dir) {
        Some((prec, spec)) => {
            retraction_info.push_record(RetractionRecord::ReplacedUserOp(
                op_decl.clone(),
                prec,
                spec,
            ));

            module_op_exports.push((op_decl.clone(), Some((prec, spec))));
        }
        None => {
            retraction_info.push_record(RetractionRecord::AddedUserOp(op_decl.clone()));
            module_op_exports.push((op_decl.clone(), None));
        }
    }

    add_op_decl(retraction_info, compilation_target, module_op_dir, op_decl);
}

pub(super) fn add_op_decl(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    op_dir: &mut OpDir,
    op_decl: &OpDecl,
) {
    match op_decl.insert_into_op_dir(op_dir) {
        Some((prec, spec)) => match &compilation_target {
            CompilationTarget::User => {
                retraction_info.push_record(RetractionRecord::ReplacedUserOp(
                    op_decl.clone(),
                    prec,
                    spec,
                ));
            }
            CompilationTarget::Module(ref module_name) => {
                retraction_info.push_record(RetractionRecord::ReplacedModuleOp(
                    module_name.clone(),
                    op_decl.clone(),
                    prec,
                    spec,
                ));
            }
        },
        None => match &compilation_target {
            CompilationTarget::User => {
                retraction_info.push_record(RetractionRecord::AddedUserOp(op_decl.clone()));
            }
            CompilationTarget::Module(ref module_name) => {
                retraction_info.push_record(RetractionRecord::AddedModuleOp(
                    module_name.clone(),
                    op_decl.clone(),
                ));
            }
        },
    }
}

pub(super) fn import_module_exports(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        match export {
            ModuleExport::PredicateKey((ref name, arity)) => {
                let key = (name.clone(), *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key.clone(), meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let target_code_index = code_dir
                        .entry(key.clone())
                        .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                        .clone();

                    set_code_index(
                        retraction_info,
                        compilation_target,
                        key,
                        &target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name.clone(),
                        (name.clone(), *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl(retraction_info, compilation_target, op_dir, op_decl);
            }
        }
    }

    Ok(())
}

fn import_module_exports_into_module(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
    wam_op_dir: &mut OpDir,
    module_op_exports: &mut ModuleOpExports,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        match export {
            ModuleExport::PredicateKey((ref name, arity)) => {
                let key = (name.clone(), *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key.clone(), meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let target_code_index = code_dir
                        .entry(key.clone())
                        .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                        .clone();

                    set_code_index(
                        retraction_info,
                        compilation_target,
                        key,
                        &target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name.clone(),
                        (name.clone(), *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl_as_module_export(
                    op_dir,
                    compilation_target,
                    retraction_info,
                    wam_op_dir,
                    module_op_exports,
                    op_decl,
                );
            }
        }
    }

    Ok(())
}

fn import_qualified_module_exports(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    exports: &IndexSet<ModuleExport>,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        if !exports.contains(export) {
            continue;
        }

        match export {
            ModuleExport::PredicateKey((ref name, arity)) => {
                let key = (name.clone(), *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key.clone(), meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let target_code_index = code_dir
                        .entry(key.clone())
                        .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                        .clone();

                    set_code_index(
                        retraction_info,
                        compilation_target,
                        key,
                        &target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name.clone(),
                        (name.clone(), *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl(retraction_info, compilation_target, op_dir, op_decl);
            }
        }
    }

    Ok(())
}

fn import_qualified_module_exports_into_module(
    retraction_info: &mut RetractionInfo,
    compilation_target: &CompilationTarget,
    imported_module: &Module,
    exports: &IndexSet<ModuleExport>,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicates: &mut MetaPredicateDir,
    wam_op_dir: &mut OpDir,
    module_op_exports: &mut ModuleOpExports,
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        if !exports.contains(export) {
            continue;
        }

        match export {
            ModuleExport::PredicateKey((ref name, arity)) => {
                let key = (name.clone(), *arity);

                if let Some(meta_specs) = imported_module.meta_predicates.get(&key) {
                    meta_predicates.insert(key.clone(), meta_specs.clone());
                }

                if let Some(src_code_index) = imported_module.code_dir.get(&key) {
                    let target_code_index = code_dir
                        .entry(key.clone())
                        .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                        .clone();

                    set_code_index(
                        retraction_info,
                        compilation_target,
                        key,
                        &target_code_index,
                        src_code_index.get(),
                    );
                } else {
                    return Err(SessionError::ModuleDoesNotContainExport(
                        imported_module.module_decl.name.clone(),
                        (name.clone(), *arity),
                    ));
                }
            }
            ModuleExport::OpDecl(ref op_decl) => {
                add_op_decl_as_module_export(
                    op_dir,
                    compilation_target,
                    retraction_info,
                    wam_op_dir,
                    module_op_exports,
                    op_decl,
                );
            }
        }
    }

    Ok(())
}

impl<'a> LoadState<'a> {
    pub(super) fn retract_local_clauses(
        &mut self,
        compilation_target: CompilationTarget,
        key: PredicateKey,
        clause_locs: &SliceDeque<usize>,
    ) {
        let result_opt = self
            .wam
            .indices
            .get_predicate_skeleton(&compilation_target, &key)
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
        let old_compilation_target = mem::replace(&mut self.compilation_target, compilation_target);

        while let Some(target_pos_opt) = clause_target_poses.pop() {
            match target_pos_opt {
                Some(target_pos) if is_dynamic => {
                    self.retract_dynamic_clause(key.clone(), target_pos);
                }
                Some(target_pos) => {
                    self.retract_clause(key.clone(), target_pos);
                }
                None => {
                    // Here because the clause was been removed
                    // earlier, e.g., by retract, without updating the
                    // local skeleton. In this case, do nothing.
                }
            }
        }

        self.compilation_target = old_compilation_target;
    }

    pub(super) fn retract_local_clause_clauses(
        &mut self,
        clause_clause_compilation_target: CompilationTarget,
        clause_locs: &SliceDeque<usize>,
    ) {
        let key = (clause_name!("$clause"), 2);

        match self.wam.indices.get_local_predicate_skeleton_mut(
            self.compilation_target.clone(),
            clause_clause_compilation_target.clone(),
            self.listing_src_file_name(),
            key.clone(),
        ) {
            Some(skeleton) => {
                self.retraction_info.push_record(
                    RetractionRecord::RemovedLocalSkeletonClauseLocations(
                        self.compilation_target.clone(),
                        clause_clause_compilation_target.clone(),
                        key.clone(),
                        mem::replace(&mut skeleton.clause_clause_locs, sdeq![]),
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

        self.retract_local_clauses(clause_clause_compilation_target, key, &clause_locs);
    }

    pub(super) fn try_term_to_tl(
        &mut self,
        term: Term,
        preprocessor: &mut Preprocessor,
    ) -> Result<PredicateClause, SessionError> {
        let tl = preprocessor.try_term_to_tl(self, term, CutContext::BlocksCuts)?;

        Ok(match tl {
            TopLevel::Fact(fact) => PredicateClause::Fact(fact),
            TopLevel::Rule(rule) => PredicateClause::Rule(rule),
            TopLevel::Query(_) => return Err(SessionError::QueryCannotBeDefinedAsFact),
            _ => unreachable!(),
        })
    }

    #[inline]
    pub(super) fn remove_module_op_exports(&mut self) {
        for (mut op_decl, record) in self.module_op_exports.drain(0..) {
            op_decl.remove(&mut self.wam.indices.op_dir);

            if let Some((prec, spec)) = record {
                op_decl.prec = prec;
                op_decl.spec = spec;
                op_decl.insert_into_op_dir(&mut self.wam.indices.op_dir);
            }
        }
    }

    pub(super) fn remove_replaced_in_situ_module(&mut self, module_name: ClauseName) {
        let removed_module = match self.wam.indices.modules.remove(&module_name) {
            Some(module) => module,
            None => return,
        };

        for (key, code_index) in &removed_module.code_dir {
            match removed_module
                .local_extensible_predicates
                .get(&(CompilationTarget::User, key.clone()))
            {
                Some(skeleton) if skeleton.is_multifile => continue,
                _ => {}
            }

            if code_index.get() != IndexPtr::Undefined {
                let old_index_ptr = code_index.replace(IndexPtr::Undefined);

                self.retraction_info
                    .push_record(RetractionRecord::ReplacedModulePredicate(
                        module_name.clone(),
                        key.clone(),
                        old_index_ptr,
                    ));
            }
        }

        self.wam.indices.modules.insert(module_name, removed_module);
    }

    pub(super) fn remove_module_exports(&mut self, module_name: ClauseName) {
        let removed_module = match self.wam.indices.modules.remove(&module_name) {
            Some(module) => module,
            None => return,
        };

        fn remove_module_exports(
            removed_module: &Module,
            code_dir: &mut CodeDir,
            op_dir: &mut OpDir,
            retraction_info: &mut RetractionInfo,
            predicate_retractor: impl Fn(PredicateKey, IndexPtr) -> RetractionRecord,
            op_retractor: impl Fn(OpDecl, usize, Specifier) -> RetractionRecord,
        ) {
            for export in removed_module.module_decl.exports.iter() {
                match export {
                    ModuleExport::PredicateKey(ref key) => {
                        match (removed_module.code_dir.get(key), code_dir.get(key)) {
                            (Some(module_code_index), Some(target_code_index))
                                if module_code_index.get() == target_code_index.get() =>
                            {
                                let old_index_ptr = target_code_index.replace(IndexPtr::Undefined);

                                retraction_info
                                    .push_record(predicate_retractor(key.clone(), old_index_ptr));
                            }
                            _ => {}
                        }
                    }
                    ModuleExport::OpDecl(op_decl) => {
                        let op_dir_value_opt =
                            op_dir.remove(&(op_decl.name.clone(), op_decl.fixity()));

                        if let Some(op_dir_value) = op_dir_value_opt {
                            let (prec, spec) = op_dir_value.shared_op_desc().get();

                            retraction_info.push_record(op_retractor(op_decl.clone(), prec, spec));
                        }
                    }
                }
            }
        }

        match &self.compilation_target {
            CompilationTarget::User => {
                remove_module_exports(
                    &removed_module,
                    &mut self.wam.indices.code_dir,
                    &mut self.wam.indices.op_dir,
                    &mut self.retraction_info,
                    RetractionRecord::ReplacedUserPredicate,
                    RetractionRecord::ReplacedUserOp,
                );
            }
            CompilationTarget::Module(ref target_module_name)
                if target_module_name.as_str() != module_name.as_str() =>
            {
                let predicate_retractor = |key, index_ptr| {
                    RetractionRecord::ReplacedModulePredicate(module_name.clone(), key, index_ptr)
                };

                let op_retractor = |op_decl, prec, spec| {
                    RetractionRecord::ReplacedModuleOp(module_name.clone(), op_decl, prec, spec)
                };

                if let Some(module) = self.wam.indices.modules.get_mut(target_module_name) {
                    remove_module_exports(
                        &removed_module,
                        &mut module.code_dir,
                        &mut module.op_dir,
                        &mut self.retraction_info,
                        predicate_retractor,
                        op_retractor,
                    );
                } else {
                    unreachable!()
                }
            }
            CompilationTarget::Module(_) => {}
        };

        self.wam.indices.modules.insert(module_name, removed_module);
    }

    fn get_or_insert_local_code_index(
        &mut self,
        module_name: ClauseName,
        key: PredicateKey,
    ) -> CodeIndex {
        match self.wam.indices.modules.get_mut(&module_name) {
            Some(ref mut module) => module
                .code_dir
                .entry(key)
                .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                .clone(),
            None => {
                self.add_dynamically_generated_module(&module_name);

                match self.wam.indices.modules.get_mut(&module_name) {
                    Some(ref mut module) => module
                        .code_dir
                        .entry(key)
                        .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                        .clone(),
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
        match compilation_target {
            CompilationTarget::User => self
                .wam
                .indices
                .code_dir
                .entry(key)
                .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                .clone(),
            CompilationTarget::Module(module_name) => {
                self.get_or_insert_local_code_index(module_name, key)
            }
        }
    }

    pub(super) fn get_or_insert_qualified_code_index(
        &mut self,
        module_name: ClauseName,
        key: PredicateKey,
    ) -> CodeIndex {
        if module_name.as_str() == "user" {
            return self
                .wam
                .indices
                .code_dir
                .entry(key)
                .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                .clone();
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
                self.wam
                    .indices
                    .extensible_predicates
                    .insert(key.clone(), skeleton);

                let record =
                    RetractionRecord::AddedExtensiblePredicate(CompilationTarget::User, key);

                self.retraction_info.push_record(record);
            }
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.wam.indices.modules.get_mut(&module_name) {
                    module.extensible_predicates.insert(key.clone(), skeleton);

                    let record = RetractionRecord::AddedExtensiblePredicate(
                        CompilationTarget::Module(module_name),
                        key,
                    );

                    self.retraction_info.push_record(record);
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
            None => self.compilation_target.clone(),
        };

        match src_compilation_target {
            CompilationTarget::User => {
                self.wam
                    .indices
                    .local_extensible_predicates
                    .insert((local_compilation_target.clone(), key.clone()), skeleton);
            }
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.wam.indices.modules.get_mut(&module_name) {
                    module
                        .local_extensible_predicates
                        .insert((local_compilation_target.clone(), key.clone()), skeleton);
                } else {
                    unreachable!()
                }
            }
        }
    }

    pub(super) fn add_op_decl(&mut self, op_decl: &OpDecl) {
        match &self.compilation_target {
            CompilationTarget::User => {
                if let Some(filename) = self.listing_src_file_name() {
                    match self.wam.indices.modules.get_mut(&filename) {
                        Some(ref mut module) => {
                            op_decl.insert_into_op_dir(&mut module.op_dir);
                        }
                        None => {}
                    }
                }

                add_op_decl(
                    &mut self.retraction_info,
                    &self.compilation_target,
                    &mut self.wam.indices.op_dir,
                    op_decl,
                );
            }
            CompilationTarget::Module(ref module_name) => {
                match self.wam.indices.modules.get_mut(module_name) {
                    Some(ref mut module) => {
                        add_op_decl_as_module_export(
                            &mut module.op_dir,
                            &self.compilation_target,
                            &mut self.retraction_info,
                            &mut self.wam.indices.op_dir,
                            &mut self.module_op_exports,
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

    pub(super) fn get_clause_type(
        &mut self,
        name: ClauseName,
        arity: usize,
        fixity: Option<SharedOpDesc>,
    ) -> ClauseType {
        match ClauseType::from(name, arity, fixity) {
            ClauseType::Named(name, arity, _) => {
                let idx = self.get_or_insert_code_index(
                    (name.clone(), arity),
                    self.compilation_target.clone(),
                );

                ClauseType::Named(name, arity, idx)
            }
            ClauseType::Op(name, fixity, _) => {
                let idx = self.get_or_insert_code_index(
                    (name.clone(), arity),
                    self.compilation_target.clone(),
                );

                ClauseType::Op(name, fixity, idx)
            }
            ct => ct,
        }
    }

    pub(super) fn get_qualified_clause_type(
        &mut self,
        module_name: ClauseName,
        name: ClauseName,
        arity: usize,
        fixity: Option<SharedOpDesc>,
    ) -> ClauseType {
        match ClauseType::from(name, arity, fixity) {
            ClauseType::Named(name, arity, _) => {
                let key = (name.clone(), arity);
                let idx = self.get_or_insert_qualified_code_index(module_name, key);

                ClauseType::Named(name, arity, idx)
            }
            ClauseType::Op(name, fixity, _) => {
                let key = (name.clone(), arity);
                let idx = self.get_or_insert_qualified_code_index(module_name, key);

                ClauseType::Op(name, fixity, idx)
            }
            ct => ct,
        }
    }

    pub(super) fn add_meta_predicate_record(
        &mut self,
        module_name: ClauseName,
        name: ClauseName,
        meta_specs: Vec<MetaSpec>,
    ) {
        let arity = meta_specs.len();
        let key = (name, arity);

        match module_name.as_str() {
            "user" => {
                match self
                    .wam
                    .indices
                    .meta_predicates
                    .insert(key.clone(), meta_specs)
                {
                    Some(old_meta_specs) => {
                        self.retraction_info
                            .push_record(RetractionRecord::ReplacedMetaPredicate(
                                module_name.clone(),
                                key.0,
                                old_meta_specs,
                            ));
                    }
                    None => {
                        self.retraction_info
                            .push_record(RetractionRecord::AddedMetaPredicate(
                                module_name.clone(),
                                key,
                            ));
                    }
                }
            }
            _ => {
                match self.wam.indices.modules.get_mut(&module_name) {
                    Some(ref mut module) => {
                        match module.meta_predicates.insert(key.clone(), meta_specs) {
                            Some(old_meta_specs) => {
                                self.retraction_info.push_record(
                                    RetractionRecord::ReplacedMetaPredicate(
                                        module_name.clone(),
                                        key.0,
                                        old_meta_specs,
                                    ),
                                );
                            }
                            None => {
                                self.retraction_info.push_record(
                                    RetractionRecord::AddedMetaPredicate(module_name.clone(), key),
                                );
                            }
                        }
                    }
                    None => {
                        self.add_dynamically_generated_module(&module_name);

                        if let Some(module) = self.wam.indices.modules.get_mut(&module_name) {
                            module.meta_predicates.insert(key.clone(), meta_specs);
                        } else {
                            unreachable!()
                        }

                        self.retraction_info
                            .push_record(RetractionRecord::AddedMetaPredicate(
                                module_name.clone(),
                                key,
                            ));
                    }
                }
            }
        }
    }

    pub(super) fn add_dynamically_generated_module(&mut self, module_name: &ClauseName) {
        let module_decl = ModuleDecl {
            name: module_name.clone(),
            exports: vec![],
        };

        let listing_src = ListingSource::DynamicallyGenerated;
        let mut module = Module::new(module_decl, listing_src);

        self.import_builtins_in_module(
            module_name.clone(),
            &mut module.code_dir,
            &mut module.op_dir,
            &mut module.meta_predicates,
        );

        self.retraction_info
            .push_record(RetractionRecord::AddedModule(module_name.clone()));

        self.wam.indices.modules.insert(module_name.clone(), module);
    }

    fn import_builtins_in_module(
        &mut self,
        module_name: ClauseName,
        code_dir: &mut CodeDir,
        op_dir: &mut OpDir,
        meta_predicates: &mut MetaPredicateDir,
    ) {
        if let Some(builtins) = self.wam.indices.modules.get(&clause_name!("builtins")) {
            let module_compilation_target = CompilationTarget::Module(module_name);

            if CompilationTarget::Module(clause_name!("builtins")) == self.compilation_target {
                return;
            }

            import_module_exports(
                &mut self.retraction_info,
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
        let module_name = module_decl.name.clone();

        self.remove_module_exports(module_name.clone());
        self.remove_replaced_in_situ_module(module_name.clone());

        match self.wam.indices.modules.get_mut(&module_name) {
            Some(module) => {
                let old_module_decl = mem::replace(&mut module.module_decl, module_decl.clone());

                let local_extensible_predicates = mem::replace(
                    &mut module.local_extensible_predicates,
                    LocalExtensiblePredicates::new(),
                );

                for ((compilation_target, key), skeleton) in local_extensible_predicates.iter() {
                    self.retract_local_clauses(
                        compilation_target.clone(),
                        key.clone(),
                        &skeleton.clause_clause_locs,
                    );

                    let is_dynamic = self
                        .wam
                        .indices
                        .get_predicate_skeleton(compilation_target, key)
                        .map(|skeleton| skeleton.core.is_dynamic)
                        .unwrap_or(false);

                    if is_dynamic {
                        let clause_clause_compilation_target = match compilation_target {
                            CompilationTarget::User => {
                                CompilationTarget::Module(clause_name!("builtins"))
                            }
                            module => module.clone(),
                        };

                        self.retract_local_clause_clauses(
                            clause_clause_compilation_target,
                            &skeleton.clause_clause_locs,
                        );
                    }
                }

                self.retraction_info
                    .push_record(RetractionRecord::ReplacedModule(
                        old_module_decl,
                        listing_src.clone(),
                        local_extensible_predicates,
                    ));
            }
            None => {}
        }
    }

    pub(crate) fn add_module(&mut self, module_decl: ModuleDecl, listing_src: ListingSource) {
        self.reset_in_situ_module(module_decl.clone(), &listing_src);
        let module_name = module_decl.name.clone();

        let mut module = match self.wam.indices.modules.remove(&module_name) {
            Some(mut module) => {
                module.listing_src = listing_src;
                module
            }
            None => {
                self.retraction_info
                    .push_record(RetractionRecord::AddedModule(module_name.clone()));

                Module::new(module_decl, listing_src)
            }
        };

        self.import_builtins_in_module(
            module_name.clone(),
            &mut module.code_dir,
            &mut module.op_dir,
            &mut module.meta_predicates,
        );

        for export in &module.module_decl.exports {
            if let ModuleExport::OpDecl(ref op_decl) = export {
                add_op_decl_as_module_export(
                    &mut module.op_dir,
                    &self.compilation_target, // this is a Module.
                    &mut self.retraction_info,
                    &mut self.wam.indices.op_dir,
                    &mut self.module_op_exports,
                    op_decl,
                );
            }
        }

        if let Some(load_context) = self.wam.load_contexts.last_mut() {
            load_context.module = module_name.clone();
        }

        self.wam.indices.modules.insert(module_name, module);
    }

    pub(super) fn import_module(&mut self, module_name: ClauseName) -> Result<(), SessionError> {
        if let Some(module) = self.wam.indices.modules.remove(&module_name) {
            match &self.compilation_target {
                CompilationTarget::User => {
                    import_module_exports(
                        &mut self.retraction_info,
                        &self.compilation_target,
                        &module,
                        &mut self.wam.indices.code_dir,
                        &mut self.wam.indices.op_dir,
                        &mut self.wam.indices.meta_predicates,
                    )?;
                }
                CompilationTarget::Module(ref defining_module_name) => {
                    match self.wam.indices.modules.get_mut(defining_module_name) {
                        Some(ref mut target_module) => {
                            import_module_exports_into_module(
                                &mut self.retraction_info,
                                &self.compilation_target,
                                &module,
                                &mut target_module.code_dir,
                                &mut target_module.op_dir,
                                &mut target_module.meta_predicates,
                                &mut self.wam.indices.op_dir,
                                &mut self.module_op_exports,
                            )?;
                        }
                        None => {
                            // we find ourselves here because we're trying to import
                            // a module into itself as it is being defined.
                            self.wam.indices.modules.insert(module_name.clone(), module);
                            return Err(SessionError::ModuleCannotImportSelf(module_name));
                        }
                    }
                }
            }

            self.wam.indices.modules.insert(module_name, module);
            Ok(())
        } else {
            Err(SessionError::ExistenceError(ExistenceError::Module(
                module_name,
            )))
        }
    }

    pub(super) fn import_qualified_module(
        &mut self,
        module_name: ClauseName,
        exports: IndexSet<ModuleExport>,
    ) -> Result<(), SessionError> {
        if let Some(module) = self.wam.indices.modules.remove(&module_name) {
            match &self.compilation_target {
                CompilationTarget::User => {
                    import_qualified_module_exports(
                        &mut self.retraction_info,
                        &self.compilation_target,
                        &module,
                        &exports,
                        &mut self.wam.indices.code_dir,
                        &mut self.wam.indices.op_dir,
                        &mut self.wam.indices.meta_predicates,
                    )?;
                }
                CompilationTarget::Module(ref defining_module_name) => {
                    match self.wam.indices.modules.get_mut(defining_module_name) {
                        Some(ref mut target_module) => {
                            import_qualified_module_exports_into_module(
                                &mut self.retraction_info,
                                &self.compilation_target,
                                &module,
                                &exports,
                                &mut target_module.code_dir,
                                &mut target_module.op_dir,
                                &mut target_module.meta_predicates,
                                &mut self.wam.indices.op_dir,
                                &mut self.module_op_exports,
                            )?;
                        }
                        None => {
                            // we find ourselves here because we're trying to import
                            // a module into itself as it is being defined.
                            self.wam.indices.modules.insert(module_name.clone(), module);
                            return Err(SessionError::ModuleCannotImportSelf(module_name));
                        }
                    }
                }
            }

            self.wam.indices.modules.insert(module_name, module);
            Ok(())
        } else {
            Err(SessionError::ExistenceError(ExistenceError::Module(
                module_name,
            )))
        }
    }

    pub(crate) fn use_module(&mut self, module_src: ModuleSource) -> Result<(), SessionError> {
        let (stream, listing_src) = match module_src {
            ModuleSource::File(filename) => {
                let mut path_buf = PathBuf::from(filename.as_str());
                path_buf.set_extension("pl");
                let file = File::open(&path_buf)?;

                (
                    Stream::from_file_as_input(filename.clone(), file),
                    ListingSource::File(filename, path_buf),
                )
            }
            ModuleSource::Library(library) => match LIBRARIES.borrow().get(library.as_str()) {
                Some(code) => {
                    if let Some(ref module) = self.wam.indices.modules.get(&library) {
                        if let ListingSource::DynamicallyGenerated = &module.listing_src {
                            (Stream::from(*code), ListingSource::User)
                        } else {
                            return self.import_module(library);
                        }
                    } else {
                        (Stream::from(*code), ListingSource::User)
                    }
                }
                None => {
                    return self.import_module(library);
                }
            },
        };

        let compilation_target = {
            let stream = &mut parsing_stream(stream)?;

            let ts = BootstrappingTermStream::from_prolog_stream(
                stream,
                self.wam.machine_st.atom_tbl.clone(),
                self.wam.machine_st.flags,
                listing_src,
            );

            let subloader = Loader::new(ts, self.wam);
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
                let mut path_buf = PathBuf::from(filename.as_str());
                path_buf.set_extension("pl");
                let file = File::open(&path_buf)?;

                (
                    Stream::from_file_as_input(filename.clone(), file),
                    ListingSource::File(filename, path_buf),
                )
            }
            ModuleSource::Library(library) => match LIBRARIES.borrow().get(library.as_str()) {
                Some(code) => {
                    if self.wam.indices.modules.contains_key(&library) {
                        return self.import_qualified_module(library, exports);
                    } else {
                        (Stream::from(*code), ListingSource::User)
                    }
                }
                None => {
                    return self.import_qualified_module(library, exports);
                }
            },
        };

        let compilation_target = {
            let stream = &mut parsing_stream(stream)?;

            let ts = BootstrappingTermStream::from_prolog_stream(
                stream,
                self.wam.machine_st.atom_tbl.clone(),
                self.wam.machine_st.flags,
                listing_src,
            );

            let subloader = Loader::new(ts, self.wam);
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

    #[inline]
    pub(super) fn composite_op_dir(&self) -> CompositeOpDir {
        match &self.compilation_target {
            CompilationTarget::User => CompositeOpDir::new(&self.wam.indices.op_dir, None),
            CompilationTarget::Module(ref module_name) => {
                match self.wam.indices.modules.get(module_name) {
                    Some(ref module) => {
                        CompositeOpDir::new(&self.wam.indices.op_dir, Some(&module.op_dir))
                    }
                    None => {
                        unreachable!()
                    }
                }
            }
        }
    }
}
