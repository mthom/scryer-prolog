#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

use crate::parser::ast::*;

use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::machine::loader::*;
use crate::machine::machine_state::*;
use crate::machine::streams::{Stream, StreamOptions};
use crate::machine::ClauseType;
use crate::machine::MachineStubGen;
use crate::offset_table::*;

use fxhash::FxBuildHasher;
use indexmap::{IndexMap, IndexSet};
use scryer_modular_bitfield::specifiers::*;
use scryer_modular_bitfield::{bitfield, BitfieldSpecifier};

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::Deref;

use crate::types::*;

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
pub struct CodeIndex(CodeIndexOffset);

#[cfg(target_pointer_width = "32")]
const_assert!(std::mem::align_of::<CodeIndex>() == 4);

#[cfg(target_pointer_width = "64")]
const_assert!(std::mem::align_of::<CodeIndex>() == 8);

impl From<CodeIndex> for HeapCellValue {
    #[inline(always)]
    fn from(idx: CodeIndex) -> HeapCellValue {
        HeapCellValue::from(idx.as_ptr())
    }
}

impl From<CodeIndexOffset> for CodeIndex {
    #[inline(always)]
    fn from(offset: CodeIndexOffset) -> CodeIndex {
        CodeIndex(offset)
    }
}

impl CodeIndex {
    #[inline]
    pub(crate) fn new(ptr: IndexPtr, arena: &mut Arena) -> Self {
        unsafe { CodeIndex(arena.code_index_tbl.build_with(ptr)) }
    }

    #[inline(always)]
    pub(crate) fn default(arena: &mut Arena) -> Self {
        CodeIndex::new(IndexPtr::undefined(), arena)
    }

    pub(crate) fn local(&self) -> Option<usize> {
        match self.0.as_ptr().tag() {
            IndexPtrTag::Index => Some(self.get().p() as usize),
            IndexPtrTag::DynamicIndex => Some(self.get().p() as usize),
            _ => None,
        }
    }

    #[inline(always)]
    pub(crate) fn get(&self) -> IndexPtr {
        *self.as_ptr().deref()
    }

    #[inline(always)]
    pub(crate) fn set(&mut self, value: IndexPtr) {
        self.as_ptr().set(value);
    }

    #[inline(always)]
    pub(crate) fn get_tag(self) -> IndexPtrTag {
        self.get().tag()
    }

    #[inline(always)]
    pub(crate) fn replace(&mut self, value: IndexPtr) -> IndexPtr {
        self.as_ptr().replace(value)
    }

    #[inline(always)]
    pub(crate) fn as_ptr(&self) -> CodeIndexPtr {
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
    streams: StreamDir,
    stream_aliases: StreamAliasDir,
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
            CompilationTarget::User => self.extensible_predicates.swap_remove(key),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get_mut(module_name) {
                    module.extensible_predicates.swap_remove(key)
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

    pub(crate) fn add_stream(
        &mut self,
        stream: Stream,
        stub_name: Atom,
        stub_arity: usize,
    ) -> Result<(), MachineStubGen> {
        if let Some(alias) = stream.options().get_alias() {
            if self.stream_aliases.contains_key(&alias) {
                return Err(Box::new(move |machine_st| {
                    machine_st.occupied_alias_permission_error(alias, stub_name, stub_arity)
                }));
            }

            self.stream_aliases.insert(alias, stream);
        }

        self.streams.insert(stream);

        Ok(())
    }

    pub(crate) fn remove_stream(&mut self, stream: Stream) {
        if let Some(alias) = stream.options().get_alias() {
            debug_assert_eq!(self.stream_aliases.get(&alias), Some(&stream));
            assert!(!is_protected_alias(alias));

            self.stream_aliases.swap_remove(&alias);
        }
        self.streams.remove(&stream);
    }

    pub(crate) fn update_stream_options<F: Fn(&mut StreamOptions)>(
        &mut self,
        mut stream: Stream,
        callback: F,
    ) {
        if let Some(prev_alias) = stream.options().get_alias() {
            debug_assert_eq!(self.stream_aliases.get(&prev_alias), Some(&stream));
        }
        let options = stream.options_mut();
        let prev_alias = options.get_alias();

        callback(options);

        if options.get_alias() != prev_alias {
            if prev_alias.map(is_protected_alias).unwrap_or(false)
                || options
                    .get_alias()
                    .map(|alias| self.has_stream(alias))
                    .unwrap_or(false)
            {
                // user_input, user_output and user_error cannot be realiased,
                // and realiasing cannot shadow an existing stream.
                options.set_alias_to_atom_opt(prev_alias);
                return;
            }

            if let Some(prev_alias) = prev_alias {
                self.stream_aliases.swap_remove(&prev_alias);
            }
            if let Some(new_alias) = options.get_alias() {
                self.stream_aliases.insert(new_alias, stream);
            }
        }
    }

    pub(crate) fn has_stream(&self, alias: Atom) -> bool {
        self.stream_aliases.contains_key(&alias)
    }

    /// ## Warning
    ///
    /// The returned stream's options should only be modified through
    /// [`IndexStore::update_stream_options`], to avoid breaking the
    /// invariants of [`IndexStore`].
    pub(crate) fn get_stream(&self, alias: Atom) -> Option<Stream> {
        self.stream_aliases.get(&alias).copied()
    }

    pub(crate) fn iter_streams<'a, R: std::ops::RangeBounds<Stream>>(
        &'a self,
        range: R,
    ) -> impl Iterator<Item = Stream> + 'a {
        self.streams.range(range).into_iter().copied()
    }

    /// Forcibly sets `alias` to `stream`.
    /// If there was a previous stream with that alias, it will lose that alias.
    ///
    /// Consider using [`add_stream`](Self::add_stream) if you wish to instead
    /// return an error when stream aliases conflict.
    pub(crate) fn set_stream(&mut self, alias: Atom, mut stream: Stream) {
        if let Some(mut prev_stream) = self.get_stream(alias) {
            if prev_stream == stream {
                // Nothing to do, as the stream is already present
                return;
            }

            prev_stream.options_mut().set_alias_to_atom_opt(None);
        }

        stream.options_mut().set_alias_to_atom_opt(Some(alias));

        self.stream_aliases.insert(alias, stream);
        self.streams.insert(stream);
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

/// A stream is said to have a "protected" alias if modifying its
/// alias would cause breakage in other parts of the code.
///
/// A stream with a protected alias cannot be realiased through
/// [`IndexStore::update_stream_options`]. Instead, one has to use
/// [`IndexStore::set_stream`] to do so.
fn is_protected_alias(alias: Atom) -> bool {
    alias == atom!("user_input") || alias == atom!("user_output") || alias == atom!("user_error")
}
