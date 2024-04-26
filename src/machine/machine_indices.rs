use crate::parser::ast::*;

use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::loader::*;
use crate::machine::machine_state::*;
use crate::machine::streams::Stream;
use crate::machine::ClauseType;

use fxhash::FxBuildHasher;
use indexmap::{IndexMap, IndexSet};
use scryer_modular_bitfield::specifiers::*;
use scryer_modular_bitfield::{bitfield, BitfieldSpecifier};

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::{Deref, DerefMut};

use crate::types::*;
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct OrderedOpDirKey(pub(crate) Atom, pub(crate) Fixity);

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

#[derive(BitfieldSpecifier, Copy, Clone, Debug, PartialEq)]
#[bits = 7]
pub enum IndexPtrTag {
    DynamicUndefined = 0b1000101, // a predicate, declared as dynamic, whose location in code is as yet undefined.
    DynamicIndex = 0b1000110,
    Index = 0b1000111,
    Undefined = 0b1001000,
}

#[bitfield]
#[derive(Debug, Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IndexPtr {
    pub p: B56,
    #[allow(unused)]
    m: bool,
    pub tag: IndexPtrTag,
}

impl IndexPtr {
    #[inline(always)]
    pub(crate) fn dynamic_undefined() -> Self {
        IndexPtr::new()
            .with_p(0)
            .with_m(false)
            .with_tag(IndexPtrTag::DynamicUndefined)
    }

    #[inline(always)]
    pub(crate) fn undefined() -> Self {
        IndexPtr::new()
            .with_p(0)
            .with_m(false)
            .with_tag(IndexPtrTag::Undefined)
    }

    #[inline(always)]
    pub(crate) fn dynamic_index(p: usize) -> Self {
        IndexPtr::new()
            .with_p(p as u64)
            .with_m(false)
            .with_tag(IndexPtrTag::DynamicIndex)
    }

    #[inline(always)]
    pub(crate) fn index(p: usize) -> Self {
        IndexPtr::new()
            .with_p(p as u64)
            .with_m(false)
            .with_tag(IndexPtrTag::Index)
    }

    #[inline(always)]
    pub(crate) fn is_undefined(&self) -> bool {
        matches!(self.tag(), IndexPtrTag::Undefined)
    }

    #[inline(always)]
    pub(crate) fn is_dynamic_undefined(&self) -> bool {
        matches!(self.tag(), IndexPtrTag::DynamicUndefined)
    }
}

#[derive(Debug, Clone, Copy, Ord, Hash, PartialOrd, Eq, PartialEq)]
pub struct CodeIndex(TypedArenaPtr<IndexPtr>);

#[cfg(target_pointer_width = "32")]
const_assert!(std::mem::align_of::<CodeIndex>() == 4);

#[cfg(target_pointer_width = "64")]
const_assert!(std::mem::align_of::<CodeIndex>() == 8);

impl Deref for CodeIndex {
    type Target = TypedArenaPtr<IndexPtr>;

    #[inline(always)]
    fn deref(&self) -> &TypedArenaPtr<IndexPtr> {
        &self.0
    }
}

impl DerefMut for CodeIndex {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut TypedArenaPtr<IndexPtr> {
        &mut self.0
    }
}

impl From<CodeIndex> for UntypedArenaPtr {
    #[inline(always)]
    fn from(ptr: CodeIndex) -> UntypedArenaPtr {
        UntypedArenaPtr::build_with(ptr.0.as_ptr() as usize)
    }
}

impl From<UntypedArenaPtr> for CodeIndex {
    #[inline(always)]
    fn from(ptr: UntypedArenaPtr) -> CodeIndex {
        CodeIndex(TypedArenaPtr::new(ptr.get_ptr() as *mut IndexPtr))
    }
}

impl From<TypedArenaPtr<IndexPtr>> for CodeIndex {
    #[inline(always)]
    fn from(ptr: TypedArenaPtr<IndexPtr>) -> CodeIndex {
        CodeIndex(ptr)
    }
}

impl CodeIndex {
    #[inline]
    pub(crate) fn new(ptr: IndexPtr, arena: &mut Arena) -> Self {
        CodeIndex(arena_alloc!(ptr, arena))
    }

    #[inline(always)]
    pub(crate) fn default(arena: &mut Arena) -> Self {
        CodeIndex::new(IndexPtr::undefined(), arena)
    }

    pub(crate) fn local(&self) -> Option<usize> {
        match self.0.tag() {
            IndexPtrTag::Index => Some(self.0.p() as usize),
            IndexPtrTag::DynamicIndex => Some(self.0.p() as usize),
            _ => None,
        }
    }

    #[inline(always)]
    pub(crate) fn get(&self) -> IndexPtr {
        *self.0.deref()
    }

    #[inline(always)]
    pub(crate) fn set(&mut self, value: IndexPtr) {
        *self.0.deref_mut() = value;
    }

    #[inline(always)]
    pub(crate) fn get_tag(self) -> IndexPtrTag {
        self.0.tag()
    }

    #[inline(always)]
    pub(crate) fn replace(&mut self, value: IndexPtr) -> IndexPtr {
        std::mem::replace(self.0.deref_mut(), value)
    }

    #[inline(always)]
    pub(crate) fn as_ptr(&self) -> *const IndexPtr {
        self.0.as_ptr()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VarKey {
    AnonVar(usize),
    VarPtr(VarPtr),
}

impl VarKey {
    #[allow(clippy::inherent_to_string)]
    #[inline]
    pub(crate) fn to_string(&self) -> String {
        match self {
            VarKey::AnonVar(h) => format!("_{}", h),
            VarKey::VarPtr(var) => var.borrow().to_string(),
        }
    }

    #[inline(always)]
    pub(crate) fn is_anon(&self) -> bool {
        matches!(self, VarKey::AnonVar(_))
    }
}

pub(crate) type HeapVarDict = IndexMap<VarKey, HeapCellValue, FxBuildHasher>;

pub(crate) type GlobalVarDir = IndexMap<Atom, (Ball, Option<HeapCellValue>), FxBuildHasher>;

pub(crate) type StreamAliasDir = IndexMap<Atom, Stream, FxBuildHasher>;
pub(crate) type StreamDir = BTreeSet<Stream>;

pub(crate) type MetaPredicateDir = IndexMap<PredicateKey, Vec<MetaSpec>, FxBuildHasher>;

pub(crate) type ExtensiblePredicates = IndexMap<PredicateKey, PredicateSkeleton, FxBuildHasher>;

pub(crate) type LocalExtensiblePredicates =
    IndexMap<(CompilationTarget, PredicateKey), LocalPredicateSkeleton, FxBuildHasher>;

pub(crate) type CodeDir = IndexMap<PredicateKey, CodeIndex, FxBuildHasher>;

pub(crate) type GoalExpansionIndices = IndexSet<PredicateKey, FxBuildHasher>;

#[derive(Debug)]
pub struct IndexStore {
    pub(super) code_dir: CodeDir,
    pub(super) extensible_predicates: ExtensiblePredicates,
    pub(super) local_extensible_predicates: LocalExtensiblePredicates,
    pub(super) global_variables: GlobalVarDir,
    pub(super) goal_expansion_indices: GoalExpansionIndices,
    pub(super) meta_predicates: MetaPredicateDir,
    pub(super) modules: ModuleDir,
    pub(super) op_dir: OpDir,
    pub(super) streams: StreamDir,
    pub(super) stream_aliases: StreamAliasDir,
}

impl IndexStore {
    pub(crate) fn builtin_property(&self, key: PredicateKey) -> bool {
        let (name, arity) = key;

        if !ClauseType::is_inbuilt(name, arity) {
            self.modules
                .get(&(atom!("builtins")))
                .map(|module| module.code_dir.contains_key(&(name, arity)))
                .unwrap_or(false)
        } else {
            true
        }
    }

    #[inline(always)]
    pub(crate) fn goal_expansion_defined(&self, key: PredicateKey, module_name: Atom) -> bool {
        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match key {
            _ if self.goal_expansion_indices.contains(&key) => true,
            _ => self
                .get_meta_predicate_spec(key.0, key.1, &compilation_target)
                .map(|meta_specs| {
                    meta_specs.iter().find(|meta_spec| {
                        matches!(
                            meta_spec,
                            MetaSpec::Colon | MetaSpec::RequiresExpansionWithArgument(_)
                        )
                    })
                })
                .map(|meta_spec_opt| meta_spec_opt.is_some())
                .unwrap_or(false),
        }
    }

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
            self.code_dir.get(&(name, arity)).cloned()
        } else {
            self.modules
                .get(&module)
                .and_then(|module| module.code_dir.get(&(name, arity)).cloned())
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
                Some(module) => module
                    .meta_predicates
                    .get(&(name, arity))
                    .or_else(|| self.meta_predicates.get(&(name, arity))),
                None => self.meta_predicates.get(&(name, arity)),
            },
        }
    }

    pub(crate) fn is_dynamic_predicate(&self, module_name: Atom, key: PredicateKey) -> bool {
        match module_name {
            atom!("user") => self
                .extensible_predicates
                .get(&key)
                .map(|skeleton| skeleton.core.is_dynamic)
                .unwrap_or(false),
            _ => match self.modules.get(&module_name) {
                Some(module) => module
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
