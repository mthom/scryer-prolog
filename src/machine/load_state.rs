use crate::machine::machine_indices::*;
use crate::machine::*;
use prolog_parser::clause_name;

use crate::machine::term_stream::*;
use indexmap::IndexSet;

use ref_thread_local::RefThreadLocal;

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
                // TODO: emit warning about overwriting previous record
                let replaced = code_index.replace(code_ptr);
                RetractionRecord::ReplacedUserPredicate(key, replaced)
            }
        }
        CompilationTarget::Module(ref module_name) => {
            if IndexPtr::Undefined == code_index.get() {
                code_index.set(code_ptr);
                RetractionRecord::AddedModulePredicate(module_name.clone(), key)
            } else {
                // TODO: emit warning about overwriting previous record
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
) -> Result<(), SessionError> {
    for export in imported_module.module_decl.exports.iter() {
        if !exports.contains(export) {
            continue;
        }

        match export {
            ModuleExport::PredicateKey((ref name, arity)) => {
                let key = (name.clone(), *arity);

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
    #[inline]
    pub(super) fn increment_clause_assert_margin(&mut self, incr: usize) {
        match &self.compilation_target {
            CompilationTarget::User => {}
            CompilationTarget::Module(ref module_name) => {
                self.retraction_info
                    .push_record(RetractionRecord::IncreasedClauseAssertMargin(
                        module_name.clone(),
                        incr,
                    ));

                self.wam
                    .indices
                    .modules
                    .get_mut(module_name)
                    .map(|module| module.clause_assert_margin += incr);
            }
        }
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
                let mut module = Module::new(
                    ModuleDecl {
                        name: module_name.clone(),
                        exports: vec![],
                    },
                    ListingSource::DynamicallyGenerated,
                );

                let code_index = module
                    .code_dir
                    .entry(key)
                    .or_insert_with(|| CodeIndex::new(IndexPtr::Undefined))
                    .clone();

                self.retraction_info
                    .push_record(RetractionRecord::AddedModule(module_name.clone()));

                self.wam.indices.modules.insert(module_name, module);
                code_index
            }
        }
    }

    pub(super) fn get_or_insert_code_index(&mut self, key: PredicateKey) -> CodeIndex {
        match self.compilation_target.clone() {
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
    ) {
        match &self.compilation_target {
            CompilationTarget::User => {
                self.wam
                    .indices
                    .extensible_predicates
                    .insert(key.clone(), skeleton);

                self.retraction_info
                    .push_record(RetractionRecord::AddedUserExtensiblePredicate(key));
            }
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.wam.indices.modules.get_mut(module_name) {
                    module.extensible_predicates.insert(key.clone(), skeleton);

                    self.retraction_info.push_record(
                        RetractionRecord::AddedModuleExtensiblePredicate(module_name.clone(), key),
                    );
                } else {
                    unreachable!()
                }
            }
        }
    }

    pub(super) fn add_op_decl(&mut self, op_decl: &OpDecl) {
        match &self.compilation_target {
            CompilationTarget::User => {
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
                let idx = self.get_or_insert_code_index((name.clone(), arity));
                ClauseType::Named(name, arity, idx)
            }
            ClauseType::Op(name, fixity, _) => {
                let idx = self.get_or_insert_code_index((name.clone(), arity));
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
                        let module_decl = ModuleDecl {
                            name: module_name.clone(),
                            exports: vec![],
                        };

                        let listing_src = ListingSource::DynamicallyGenerated;
                        let mut module = Module::new(module_decl, listing_src);

                        module.meta_predicates.insert(key.clone(), meta_specs);

                        self.retraction_info
                            .push_record(RetractionRecord::AddedMetaPredicate(
                                module_name.clone(),
                                key,
                            ));

                        self.retraction_info
                            .push_record(RetractionRecord::AddedModule(module_name.clone()));

                        self.wam.indices.modules.insert(module_name, module);
                    }
                }
            }
        }
    }

    fn import_builtins_in_module(
        &mut self,
        code_dir: &mut CodeDir,
        op_dir: &mut OpDir,
        meta_predicates: &mut MetaPredicateDir,
    ) {
        if let Some(builtins) = self.wam.indices.modules.get(&clause_name!("builtins")) {
            import_module_exports(
                &mut self.retraction_info,
                &self.compilation_target,
                builtins,
                code_dir,
                op_dir,
                meta_predicates,
            ).unwrap();
        }
    }

    pub(crate) fn add_module(&mut self, module_decl: ModuleDecl, listing_src: ListingSource) {
        let module_name = module_decl.name.clone();

        let mut module = match self.wam.indices.modules.remove(&module_name) {
            Some(mut module) => {
                let old_module_decl = mem::replace(&mut module.module_decl, module_decl);

                self.retraction_info
                    .push_record(RetractionRecord::ReplacedModule(
                        old_module_decl,
                        listing_src.clone(),
                    ));

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

    fn import_qualified_module(
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
