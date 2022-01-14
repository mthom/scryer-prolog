use crate::parser::ast::*;

use crate::arena::*;
use crate::atom_table::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::loader::*;
use crate::machine::machine_state::*;
use crate::machine::streams::Stream;

use fxhash::FxBuildHasher;
use indexmap::IndexMap;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::Deref;
use std::rc::Rc;

use crate::types::*;
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct OrderedOpDirKey(pub(crate) Atom, pub(crate) Fixity);

pub(crate) type OssifiedOpDir = IndexMap<(Atom, Fixity), (usize, Specifier)>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DBRef {
    NamedPred(Atom, usize),
    Op(Atom, Fixity, TypedArenaPtr<OssifiedOpDir>),
}

// 7.2
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermOrderCategory {
    Variable,
    FloatingPoint,
    Integer,
    Atom,
    Compound,
}

impl PartialEq<Ref> for HeapCellValue {
    fn eq(&self, r: &Ref) -> bool {
        self.as_var() == Some(*r)
    }
}

impl PartialOrd<Ref> for HeapCellValue {
    fn partial_cmp(&self, r: &Ref) -> Option<Ordering> {
        read_heap_cell!(*self,
            (HeapCellValueTag::StackVar, s1) => {
                match r.get_tag() {
                    RefTag::StackCell => {
                        let s2 = r.get_value() as usize;
                        s1.partial_cmp(&s2)
                    }
                    _ => Some(Ordering::Greater),
                }
            }
            (HeapCellValueTag::AttrVar | HeapCellValueTag::Var, h1) => {
            // _ if self.is_ref() => {
            //     let h1 = self.get_value();

                match r.get_tag() {
                    RefTag::StackCell => Some(Ordering::Less),
                    _ => {
                        let h2 = r.get_value() as usize;
                        h1.partial_cmp(&h2)
                    }
                }
            }
            _ => {
                None
            }
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IndexPtr {
    DynamicUndefined, // a predicate, declared as dynamic, whose location in code is as yet undefined.
    DynamicIndex(usize),
    Index(usize),
    Undefined,
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct CodeIndex(pub(crate) Rc<Cell<IndexPtr>>);

impl Deref for CodeIndex {
    type Target = Cell<IndexPtr>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl CodeIndex {
    #[inline]
    pub(super) fn new(ptr: IndexPtr) -> Self {
        CodeIndex(Rc::new(Cell::new(ptr)))
    }

    #[inline]
    pub(crate) fn is_undefined(&self) -> bool {
        match self.0.get() {
            IndexPtr::Undefined => true, // | &IndexPtr::DynamicUndefined => true,
            _ => false,
        }
    }

    pub(crate) fn local(&self) -> Option<usize> {
        match self.0.get() {
            IndexPtr::Index(i) => Some(i),
            IndexPtr::DynamicIndex(i) => Some(i),
            _ => None,
        }
    }
}

impl Default for CodeIndex {
    fn default() -> Self {
        CodeIndex(Rc::new(Cell::new(IndexPtr::Undefined)))
    }
}

pub(crate) type HeapVarDict = IndexMap<Rc<String>, HeapCellValue, FxBuildHasher>;
pub(crate) type AllocVarDict = IndexMap<Rc<String>, VarData, FxBuildHasher>;

pub(crate) type GlobalVarDir = IndexMap<Atom, (Ball, Option<HeapCellValue>), FxBuildHasher>;

pub(crate) type StreamAliasDir = IndexMap<Atom, Stream, FxBuildHasher>;
pub(crate) type StreamDir = BTreeSet<Stream>;

pub(crate) type MetaPredicateDir = IndexMap<PredicateKey, Vec<MetaSpec>, FxBuildHasher>;

pub(crate) type ExtensiblePredicates = IndexMap<PredicateKey, PredicateSkeleton, FxBuildHasher>;

pub(crate) type LocalExtensiblePredicates =
    IndexMap<(CompilationTarget, PredicateKey), LocalPredicateSkeleton, FxBuildHasher>;

pub(crate) type CodeDir = IndexMap<PredicateKey, CodeIndex, FxBuildHasher>;

#[derive(Debug)]
pub struct IndexStore {
    pub(super) code_dir: CodeDir,
    pub(super) extensible_predicates: ExtensiblePredicates,
    pub(super) local_extensible_predicates: LocalExtensiblePredicates,
    pub(super) global_variables: GlobalVarDir,
    pub(super) meta_predicates: MetaPredicateDir,
    pub(super) modules: ModuleDir,
    pub(super) op_dir: OpDir,
    pub(super) streams: StreamDir,
    pub(super) stream_aliases: StreamAliasDir,
}

impl IndexStore {
    pub(crate) fn get_predicate_skeleton_mut(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
    ) -> Option<&mut PredicateSkeleton> {
        match compilation_target {
            CompilationTarget::User => self.extensible_predicates.get_mut(key),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get_mut(module_name) {
                    module.extensible_predicates.get_mut(key)
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn get_predicate_skeleton(
        &self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
    ) -> Option<&PredicateSkeleton> {
        match compilation_target {
            CompilationTarget::User => self.extensible_predicates.get(key),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get(module_name) {
                    module.extensible_predicates.get(key)
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn get_local_predicate_skeleton_mut(
        &mut self,
        mut src_compilation_target: CompilationTarget,
        local_compilation_target: CompilationTarget,
        listing_src_file_name: Option<Atom>,
        key: PredicateKey,
    ) -> Option<&mut LocalPredicateSkeleton> {
        if let Some(filename) = listing_src_file_name {
            src_compilation_target = CompilationTarget::Module(filename);
        }

        match src_compilation_target {
            CompilationTarget::User => self
                .local_extensible_predicates
                .get_mut(&(local_compilation_target, key)),
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.modules.get_mut(&module_name) {
                    module
                        .local_extensible_predicates
                        .get_mut(&(local_compilation_target, key))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn get_local_predicate_skeleton(
        &self,
        mut src_compilation_target: CompilationTarget,
        local_compilation_target: CompilationTarget,
        listing_src_file_name: Option<Atom>,
        key: PredicateKey,
    ) -> Option<&LocalPredicateSkeleton> {
        if let Some(filename) = listing_src_file_name {
            src_compilation_target = CompilationTarget::Module(filename);
        }

        match src_compilation_target {
            CompilationTarget::User => self
                .local_extensible_predicates
                .get(&(local_compilation_target, key)),
            CompilationTarget::Module(module_name) => {
                if let Some(module) = self.modules.get(&module_name) {
                    module
                        .local_extensible_predicates
                        .get(&(local_compilation_target, key))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn remove_predicate_skeleton(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
    ) -> Option<PredicateSkeleton> {
        match compilation_target {
            CompilationTarget::User => self.extensible_predicates.remove(key),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get_mut(module_name) {
                    module.extensible_predicates.remove(key)
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn get_predicate_code_index(
        &self,
        name: Atom,
        arity: usize,
        module: Atom,
    ) -> Option<CodeIndex> {
        if module == atom!("user") {
            match ClauseType::from(name, arity) {
                ClauseType::Named(arity, name, _) => self.code_dir.get(&(name, arity)).cloned(),
                _ => None,
            }
        } else {
            self.modules
                .get(&module)
                .and_then(|module| match ClauseType::from(name, arity) {
                    ClauseType::Named(arity, name, _) => {
                        module.code_dir.get(&(name, arity)).cloned()
                    }
                    _ => None,
                })
        }
    }

    pub(crate) fn get_meta_predicate_spec(
        &self,
        name: Atom,
        arity: usize,
        compilation_target: &CompilationTarget,
    ) -> Option<&Vec<MetaSpec>> {
        match compilation_target {
            CompilationTarget::User => self.meta_predicates.get(&(name, arity)),
            CompilationTarget::Module(ref module_name) => match self.modules.get(module_name) {
                Some(ref module) => module
                    .meta_predicates
                    .get(&(name.clone(), arity))
                    .or_else(|| self.meta_predicates.get(&(name, arity))),
                None => self.meta_predicates.get(&(name, arity)),
            },
        }
    }

    pub(crate) fn is_dynamic_predicate(
        &self,
        module_name: Atom,
        key: PredicateKey,
    ) -> bool {
        match module_name {
            atom!("user") => self
                .extensible_predicates
                .get(&key)
                .map(|skeleton| skeleton.core.is_dynamic)
                .unwrap_or(false),
            _ => match self.modules.get(&module_name) {
                Some(ref module) => module
                    .extensible_predicates
                    .get(&key)
                    .map(|skeleton| skeleton.core.is_dynamic)
                    .unwrap_or(false),
                None => false,
            },
        }
    }

    #[inline]
    pub(super) fn new() -> Self {
        index_store!(
            CodeDir::with_hasher(FxBuildHasher::default()),
            default_op_dir(),
            ModuleDir::with_hasher(FxBuildHasher::default())
        )
    }
}
