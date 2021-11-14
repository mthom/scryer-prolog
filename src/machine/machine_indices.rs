use crate::parser::ast::*;

use crate::arena::*;
use crate::atom_table::*;
use crate::clause_types::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::instructions::*;

use crate::machine::code_repo::CodeRepo;
use crate::machine::heap::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::MachineStub;
use crate::machine::machine_state::*;
use crate::machine::streams::Stream;

use indexmap::IndexMap;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::ops::{Add, AddAssign, Deref, Sub, SubAssign};
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

// the position-dependent heap template:

/*
        read_heap_cell!(
            (HeapCellValueTag::AttrVar, n) => {
            }
            (HeapCellValueTag::Lis, n) => {
            }
            (HeapCellValueTag::Var, n) => {
            }
            (HeapCellValueTag::Str, n) => {
            }
            (HeapCellValueTag::PStrOffset, n) => {
            }
            _ => {
            }
        )
*/

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
            (HeapCellValueTag::Var | HeapCellValueTag::AttrVar, h1) => {
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
/*
impl HeapCellValue {
    #[inline]
    pub fn as_constant_index(self, machine_st: &MachineState) -> Option<Literal> {
        read_heap_cell!(self,
            (HeapCellValueTag::Char, c) => Some(Literal::Char(c)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    Some(Literal::Atom(name))
                } else {
                    None
                }
            }
            (HeapCellValueTag::Fixnum, n) => {
                Some(Literal::Fixnum(n))
            }
            (HeapCellValueTag::F64, f) => {
                Some(Literal::Float(f))
            }
            (HeapCellValueTag::Cons, ptr) => {
                match_untyped_arena_ptr!(ptr,
                     (ArenaHeaderTag::Integer, n) => {
                         Some(Literal::Integer(n))
                     }
                     (ArenaHeaderTag::Rational, r) => {
                         Some(Literal::Rational(r))
                     }
                     _ => {
                         None
                     }
                )
            }
        )
    }
}
*/
/*
impl Ord for Ref {
    fn cmp(&self, other: &Ref) -> Ordering {
        match (self, other) {
            (Ref::AttrVar(h1), Ref::AttrVar(h2))
            | (Ref::HeapCell(h1), Ref::HeapCell(h2))
            | (Ref::HeapCell(h1), Ref::AttrVar(h2))
            | (Ref::AttrVar(h1), Ref::HeapCell(h2)) => h1.cmp(&h2),
            (Ref::StackCell(fr1, sc1), Ref::StackCell(fr2, sc2)) => {
                fr1.cmp(&fr2).then_with(|| sc1.cmp(&sc2))
            }
            (Ref::StackCell(..), _) => Ordering::Greater,
            (_, Ref::StackCell(..)) => Ordering::Less,
        }
    }
}

impl PartialEq<Ref> for Addr {
    fn eq(&self, r: &Ref) -> bool {
        self.as_var() == Some(*r)
    }
}

impl Addr {
    #[inline]
    pub(crate) fn is_heap_bound(&self) -> bool {
        match self {
            Addr::Char(_)
            | Addr::EmptyList
            | Addr::CutPoint(_)
            | Addr::Usize(_)
            | Addr::Fixnum(_)
            | Addr::Float(_) => false,
            _ => true,
        }
    }

    #[inline]
    pub(crate) fn is_ref(&self) -> bool {
        match self {
            Addr::HeapCell(_) | Addr::StackCell(_, _) | Addr::AttrVar(_) => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn as_var(&self) -> Option<Ref> {
        match self {
            &Addr::AttrVar(h) => Some(Ref::AttrVar(h)),
            &Addr::HeapCell(h) => Some(Ref::HeapCell(h)),
            &Addr::StackCell(fr, sc) => Some(Ref::StackCell(fr, sc)),
            _ => None,
        }
    }

    pub(crate) fn is_protected(&self, e: usize) -> bool {
        match self {
            &Addr::StackCell(addr, _) if addr >= e => false,
            _ => true,
        }
    }
}

impl SubAssign<usize> for Addr {
    fn sub_assign(&mut self, rhs: usize) {
        *self = self.clone() - rhs;
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum TrailRef {
    Ref(Ref),
    AttrVarHeapLink(usize),
    AttrVarListLink(usize, usize),
    BlackboardEntry(usize),
    BlackboardOffset(usize, usize), // key atom heap location, key value heap location
}

impl From<Ref> for TrailRef {
    fn from(r: Ref) -> Self {
        TrailRef::Ref(r)
    }
}
*/
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

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum REPLCodePtr {
    AddDiscontiguousPredicate,
    AddDynamicPredicate,
    AddMultifilePredicate,
    AddGoalExpansionClause,
    AddTermExpansionClause,
    AddInSituFilenameModule,
    ClauseToEvacuable,
    ScopedClauseToEvacuable,
    ConcludeLoad,
    DeclareModule,
    LoadCompiledLibrary,
    LoadContextSource,
    LoadContextFile,
    LoadContextDirectory,
    LoadContextModule,
    LoadContextStream,
    PopLoadContext,
    PopLoadStatePayload,
    PushLoadContext,
    PushLoadStatePayload,
    UseModule,
    BuiltInProperty,
    MetaPredicateProperty,
    MultifileProperty,
    DiscontiguousProperty,
    DynamicProperty,
    AbolishClause,
    Asserta,
    Assertz,
    Retract,
    IsConsistentWithTermQueue,
    FlushTermQueue,
    RemoveModuleExports,
    AddNonCountedBacktracking,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CodePtr {
    BuiltInClause(BuiltInClauseType, LocalCodePtr), // local is the successor call.
    CallN(usize, LocalCodePtr, bool),               // arity, local, last call.
    Local(LocalCodePtr),
    REPL(REPLCodePtr, LocalCodePtr), // the REPL code, the return pointer.
    VerifyAttrInterrupt(usize), // location of the verify attribute interrupt code in the CodeDir.
}

impl CodePtr {
    pub(crate) fn local(&self) -> LocalCodePtr {
        match self {
            &CodePtr::BuiltInClause(_, ref local)
            | &CodePtr::CallN(_, ref local, _)
            | &CodePtr::Local(ref local) => local.clone(),
            &CodePtr::VerifyAttrInterrupt(p) => LocalCodePtr::DirEntry(p),
            &CodePtr::REPL(_, p) => p, // | &CodePtr::DynamicTransaction(_, p) => p,
        }
    }

    #[inline]
    pub(crate) fn is_halt(&self) -> bool {
        if let CodePtr::Local(LocalCodePtr::Halt) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LocalCodePtr {
    DirEntry(usize), // offset
    Halt,
    IndexingBuf(usize, usize, usize), // DirEntry offset, first internal offset, second internal offset
                                      // TopLevel(usize, usize), // chunk_num, offset
}

impl LocalCodePtr {
    pub fn assign_if_local(&mut self, cp: CodePtr) {
        match cp {
            CodePtr::Local(local) => *self = local,
            _ => {}
        }
    }

    #[inline]
    pub fn abs_loc(&self) -> usize {
        match self {
            LocalCodePtr::DirEntry(ref p) => *p,
            LocalCodePtr::IndexingBuf(ref p, ..) => *p,
            LocalCodePtr::Halt => unreachable!(),
        }
    }

    pub(crate) fn is_reset_cont_marker(&self, code_repo: &CodeRepo, last_call: bool) -> bool {
        match code_repo.lookup_instr(last_call, &CodePtr::Local(*self)) {
            Some(line) => match line.as_ref() {
                Line::Control(ControlInstruction::CallClause(ref ct, ..)) => {
                    if let ClauseType::System(SystemClauseType::ResetContinuationMarker) = *ct {
                        return true;
                    }
                }
                _ => {}
            },
            None => {}
        }

        false
    }

    pub(crate) fn as_functor(&self) -> MachineStub {
        match self {
            LocalCodePtr::DirEntry(p) => {
                functor!(atom!("dir_entry"), [fixnum(*p)])
            }
            LocalCodePtr::Halt => {
                functor!(atom!("halt"))
            }
            LocalCodePtr::IndexingBuf(p, o, i) => {
                functor!(
                    atom!("indexed_buf"),
                    [fixnum(*p), fixnum(*o), fixnum(*i)]
                )
            }
        }
    }
}

impl Default for CodePtr {
    #[inline]
    fn default() -> Self {
        CodePtr::Local(LocalCodePtr::default())
    }
}

impl Default for LocalCodePtr {
    #[inline]
    fn default() -> Self {
        LocalCodePtr::DirEntry(0)
    }
}

impl Add<usize> for LocalCodePtr {
    type Output = LocalCodePtr;

    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        match self {
            LocalCodePtr::DirEntry(p) => LocalCodePtr::DirEntry(p + rhs),
            LocalCodePtr::Halt => unreachable!(),
            LocalCodePtr::IndexingBuf(p, o, i) => LocalCodePtr::IndexingBuf(p, o, i + rhs),
        }
    }
}

impl Sub<usize> for LocalCodePtr {
    type Output = Option<LocalCodePtr>;

    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        match self {
            LocalCodePtr::DirEntry(p) => p.checked_sub(rhs).map(LocalCodePtr::DirEntry),
            LocalCodePtr::Halt => unreachable!(),
            LocalCodePtr::IndexingBuf(p, o, i) => i
                .checked_sub(rhs)
                .map(|r| LocalCodePtr::IndexingBuf(p, o, r)),
        }
    }
}

impl SubAssign<usize> for LocalCodePtr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        match self {
            LocalCodePtr::DirEntry(ref mut p) => *p -= rhs,
            LocalCodePtr::Halt | LocalCodePtr::IndexingBuf(..) => unreachable!(),
        }
    }
}

impl AddAssign<usize> for LocalCodePtr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut LocalCodePtr::DirEntry(ref mut i)
            | &mut LocalCodePtr::IndexingBuf(_, _, ref mut i) => *i += rhs,
            &mut LocalCodePtr::Halt => unreachable!(),
        }
    }
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            p @ CodePtr::REPL(..) | p @ CodePtr::VerifyAttrInterrupt(_) => p,
            CodePtr::Local(local) => CodePtr::Local(local + rhs),
            CodePtr::BuiltInClause(_, local) | CodePtr::CallN(_, local, _) => {
                CodePtr::Local(local + rhs)
            }
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::VerifyAttrInterrupt(_) => {}
            &mut CodePtr::Local(ref mut local) => *local += rhs,
            _ => *self = CodePtr::Local(self.local() + rhs),
        }
    }
}

impl SubAssign<usize> for CodePtr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        match self {
            CodePtr::Local(ref mut local) => *local -= rhs,
            _ => unreachable!(),
        }
    }
}

pub(crate) type HeapVarDict = IndexMap<Rc<String>, HeapCellValue>;
pub(crate) type AllocVarDict = IndexMap<Rc<String>, VarData>;

pub(crate) type GlobalVarDir = IndexMap<Atom, (Ball, Option<HeapCellValue>)>;

pub(crate) type StreamAliasDir = IndexMap<Atom, Stream>;
pub(crate) type StreamDir = BTreeSet<Stream>;

pub(crate) type MetaPredicateDir = IndexMap<PredicateKey, Vec<MetaSpec>>;

pub(crate) type ExtensiblePredicates = IndexMap<PredicateKey, PredicateSkeleton>;

pub(crate) type LocalExtensiblePredicates =
    IndexMap<(CompilationTarget, PredicateKey), LocalPredicateSkeleton>;

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
                ClauseType::Named(name, arity, _) => self.code_dir.get(&(name, arity)).cloned(),
                _ => None,
            }
        } else {
            self.modules
                .get(&module)
                .and_then(|module| match ClauseType::from(name, arity) {
                    ClauseType::Named(name, arity, _) => {
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
        index_store!(CodeDir::new(), default_op_dir(), ModuleDir::new())
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h = atom!("run_cleaners_with_handling");
        let r_wo_h = atom!("run_cleaners_without_handling");
        let iso_ext = atom!("iso_ext");

        let r_w_h = self
            .get_predicate_code_index(r_w_h, 0, iso_ext)
            .and_then(|item| item.local());
        let r_wo_h = self
            .get_predicate_code_index(r_wo_h, 1, iso_ext)
            .and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
    }
}

pub(crate) type CodeDir = IndexMap<PredicateKey, CodeIndex>;

pub(crate) enum RefOrOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T),
}

impl<'a, T: 'a + fmt::Debug> fmt::Debug for RefOrOwned<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RefOrOwned::Borrowed(ref borrowed) => write!(f, "Borrowed({:?})", borrowed),
            &RefOrOwned::Owned(ref owned) => write!(f, "Owned({:?})", owned),
        }
    }
}

impl<'a, T> RefOrOwned<'a, T> {
    pub(crate) fn as_ref(&'a self) -> &'a T {
        match self {
            &RefOrOwned::Borrowed(r) => r,
            &RefOrOwned::Owned(ref r) => r,
        }
    }
}
