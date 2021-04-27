use prolog_parser::ast::*;
use prolog_parser::clause_name;

use crate::clause_types::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::instructions::*;
use crate::machine::code_repo::CodeRepo;
use crate::machine::heap::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::raw_block::RawBlockTraits;
use crate::machine::streams::Stream;
use crate::machine::term_stream::LoadStatePayload;
use crate::machine::CompilationTarget;
use crate::rug::{Integer, Rational};
use ordered_float::OrderedFloat;

use indexmap::IndexMap;

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryFrom;
use std::fmt;
// use std::mem;
use std::net::TcpListener;
use std::ops::{Add, AddAssign, Deref, Sub, SubAssign};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct OrderedOpDirKey(pub(crate) ClauseName, pub(crate) Fixity);

pub(crate) type OssifiedOpDir = BTreeMap<OrderedOpDirKey, (usize, Specifier)>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DBRef {
    NamedPred(ClauseName, usize, Option<SharedOpDesc>),
    Op(
        usize,
        Specifier,
        ClauseName,
        Rc<OssifiedOpDir>,
        SharedOpDesc,
    ),
}

// 7.2
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TermOrderCategory {
    Variable,
    FloatingPoint,
    Integer,
    Atom,
    Compound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Addr {
    AttrVar(usize),
    Char(char),
    Con(usize),
    CutPoint(usize),
    EmptyList,
    Fixnum(isize),
    Float(OrderedFloat<f64>),
    Lis(usize),
    LoadStatePayload(usize),
    HeapCell(usize),
    PStrLocation(usize, usize), // location of pstr in heap, offset into string in bytes.
    StackCell(usize, usize),
    Str(usize),
    Stream(usize),
    TcpListener(usize),
    Usize(usize),
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd)]
pub(crate) enum Ref {
    AttrVar(usize),
    HeapCell(usize),
    StackCell(usize, usize),
}

impl Ref {
    pub(crate) fn as_addr(self) -> Addr {
        match self {
            Ref::AttrVar(h) => Addr::AttrVar(h),
            Ref::HeapCell(h) => Addr::HeapCell(h),
            Ref::StackCell(fr, sc) => Addr::StackCell(fr, sc),
        }
    }
}

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

// for use crate::in MachineState::bind.
impl PartialOrd<Ref> for Addr {
    fn partial_cmp(&self, r: &Ref) -> Option<Ordering> {
        match self {
            &Addr::StackCell(fr, sc) => match *r {
                Ref::AttrVar(_) | Ref::HeapCell(_) => Some(Ordering::Greater),
                Ref::StackCell(fr1, sc1) => {
                    if fr1 < fr || (fr1 == fr && sc1 < sc) {
                        Some(Ordering::Greater)
                    } else if fr1 == fr && sc1 == sc {
                        Some(Ordering::Equal)
                    } else {
                        Some(Ordering::Less)
                    }
                }
            },
            &Addr::HeapCell(h) | &Addr::AttrVar(h) => match r {
                Ref::StackCell(..) => Some(Ordering::Less),
                Ref::AttrVar(h1) | Ref::HeapCell(h1) => h.partial_cmp(h1),
            },
            _ => None,
        }
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

    pub(super) fn order_category(&self, heap: &Heap) -> Option<TermOrderCategory> {
        match Number::try_from((*self, heap)) {
            Ok(Number::Integer(_)) | Ok(Number::Fixnum(_)) | Ok(Number::Rational(_)) => {
                Some(TermOrderCategory::Integer)
            }
            Ok(Number::Float(_)) => Some(TermOrderCategory::FloatingPoint),
            _ => match self {
                Addr::HeapCell(_) | Addr::AttrVar(_) | Addr::StackCell(..) => {
                    Some(TermOrderCategory::Variable)
                }
                Addr::Float(_) => Some(TermOrderCategory::FloatingPoint),
                &Addr::Con(h) => match &heap[h] {
                    HeapCellValue::Atom(..) => Some(TermOrderCategory::Atom),
                    HeapCellValue::DBRef(_) => None,
                    _ => {
                        unreachable!()
                    }
                },
                Addr::Char(_) | Addr::EmptyList => Some(TermOrderCategory::Atom),
                Addr::Fixnum(_) | Addr::Usize(_) => Some(TermOrderCategory::Integer),
                Addr::Lis(_) | Addr::PStrLocation(..) | Addr::Str(_) => {
                    Some(TermOrderCategory::Compound)
                }
                Addr::CutPoint(_)
                | Addr::LoadStatePayload(_)
                | Addr::Stream(_)
                | Addr::TcpListener(_) => None,
            },
        }
    }

    pub(crate) fn as_constant_index(&self, machine_st: &MachineState) -> Option<Constant> {
        match self {
            &Addr::Char(c) => Some(Constant::Char(c)),
            &Addr::Con(h) => match &machine_st.heap[h] {
                &HeapCellValue::Atom(ref name, _) if name.is_char() => {
                    Some(Constant::Char(name.as_str().chars().next().unwrap()))
                }
                &HeapCellValue::Atom(ref name, _) => Some(Constant::Atom(name.clone(), None)),
                &HeapCellValue::Integer(ref n) => Some(Constant::Integer(n.clone())),
                &HeapCellValue::Rational(ref n) => Some(Constant::Rational(n.clone())),
                _ => None,
            },
            &Addr::EmptyList => Some(Constant::EmptyList),
            &Addr::Fixnum(n) => Some(Constant::Fixnum(n)),
            &Addr::Float(f) => Some(Constant::Float(f)),
            &Addr::Usize(n) => Some(Constant::Usize(n)),
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

impl Add<usize> for Addr {
    type Output = Addr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            Addr::Stream(h) => Addr::Stream(h + rhs),
            Addr::Con(h) => Addr::Con(h + rhs),
            Addr::Lis(a) => Addr::Lis(a + rhs),
            Addr::AttrVar(h) => Addr::AttrVar(h + rhs),
            Addr::HeapCell(h) => Addr::HeapCell(h + rhs),
            Addr::Str(s) => Addr::Str(s + rhs),
            Addr::PStrLocation(h, n) => Addr::PStrLocation(h + rhs, n),
            _ => self,
        }
    }
}

impl Sub<i64> for Addr {
    type Output = Addr;

    fn sub(self, rhs: i64) -> Self::Output {
        if rhs < 0 {
            match self {
                Addr::Stream(h) => Addr::Stream(h + rhs.abs() as usize),
                Addr::Con(h) => Addr::Con(h + rhs.abs() as usize),
                Addr::Lis(a) => Addr::Lis(a + rhs.abs() as usize),
                Addr::AttrVar(h) => Addr::AttrVar(h + rhs.abs() as usize),
                Addr::HeapCell(h) => Addr::HeapCell(h + rhs.abs() as usize),
                Addr::Str(s) => Addr::Str(s + rhs.abs() as usize),
                Addr::PStrLocation(h, n) => Addr::PStrLocation(h + rhs.abs() as usize, n),
                _ => self,
            }
        } else {
            self.sub(rhs as usize)
        }
    }
}

impl Sub<usize> for Addr {
    type Output = Addr;

    fn sub(self, rhs: usize) -> Self::Output {
        match self {
            Addr::Stream(h) => Addr::Stream(h - rhs),
            Addr::Con(h) => Addr::Con(h - rhs),
            Addr::Lis(a) => Addr::Lis(a - rhs),
            Addr::AttrVar(h) => Addr::AttrVar(h - rhs),
            Addr::HeapCell(h) => Addr::HeapCell(h - rhs),
            Addr::Str(s) => Addr::Str(s - rhs),
            Addr::PStrLocation(h, n) => Addr::PStrLocation(h - rhs, n),
            _ => self,
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

#[derive(Debug)]
pub(crate) enum HeapCellValue {
    Addr(Addr),
    Atom(ClauseName, Option<SharedOpDesc>),
    DBRef(DBRef),
    Integer(Rc<Integer>),
    LoadStatePayload(Box<LoadStatePayload>),
    NamedStr(usize, ClauseName, Option<SharedOpDesc>), // arity, name, precedence/Specifier if it has one.
    Rational(Rc<Rational>),
    PartialString(PartialString, bool), // the partial string, a bool indicating whether it came from a Constant.
    Stream(Stream),
    TcpListener(TcpListener),
}

impl HeapCellValue {
    #[inline]
    pub(crate) fn as_addr(&self, focus: usize) -> Addr {
        match self {
            HeapCellValue::Addr(ref a) => *a,
            HeapCellValue::Atom(..)
            | HeapCellValue::DBRef(..)
            | HeapCellValue::Integer(..)
            | HeapCellValue::Rational(..) => Addr::Con(focus),
            HeapCellValue::LoadStatePayload(_) => Addr::LoadStatePayload(focus),
            HeapCellValue::NamedStr(_, _, _) => Addr::Str(focus),
            HeapCellValue::PartialString(..) => Addr::PStrLocation(focus, 0),
            HeapCellValue::Stream(_) => Addr::Stream(focus),
            HeapCellValue::TcpListener(_) => Addr::TcpListener(focus),
        }
    }

    #[inline]
    pub(crate) fn context_free_clone(&self) -> HeapCellValue {
        match self {
            &HeapCellValue::Addr(addr) => HeapCellValue::Addr(addr),
            &HeapCellValue::Atom(ref name, ref op) => HeapCellValue::Atom(name.clone(), op.clone()),
            &HeapCellValue::DBRef(ref db_ref) => HeapCellValue::DBRef(db_ref.clone()),
            &HeapCellValue::Integer(ref n) => HeapCellValue::Integer(n.clone()),
            &HeapCellValue::LoadStatePayload(_) => {
                HeapCellValue::Atom(clause_name!("$live_term_stream"), None)
            }
            &HeapCellValue::NamedStr(arity, ref name, ref op) => {
                HeapCellValue::NamedStr(arity, name.clone(), op.clone())
            }
            &HeapCellValue::Rational(ref r) => HeapCellValue::Rational(r.clone()),
            &HeapCellValue::PartialString(ref pstr, has_tail) => {
                HeapCellValue::PartialString(pstr.clone(), has_tail)
            }
            &HeapCellValue::Stream(ref stream) => HeapCellValue::Stream(stream.clone()),
            &HeapCellValue::TcpListener(_) => {
                HeapCellValue::Atom(clause_name!("$tcp_listener"), None)
            }
        }
    }
}

impl From<Addr> for HeapCellValue {
    #[inline]
    fn from(value: Addr) -> HeapCellValue {
        HeapCellValue::Addr(value)
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum IndexPtr {
    DynamicUndefined, // a predicate, declared as dynamic, whose location in code is as yet undefined.
    DynamicIndex(usize),
    Index(usize),
    Undefined,
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct CodeIndex(pub(crate) Rc<Cell<IndexPtr>>);

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
pub(crate) enum REPLCodePtr {
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

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum CodePtr {
    BuiltInClause(BuiltInClauseType, LocalCodePtr), // local is the successor call.
    CallN(usize, LocalCodePtr, bool),               // arity, local, last call.
    Local(LocalCodePtr),
    // DynamicTransaction(DynamicTransactionType, LocalCodePtr), // the type of transaction, the return pointer.
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
pub(crate) enum LocalCodePtr {
    DirEntry(usize), // offset
    Halt,
    IndexingBuf(usize, usize, usize), // DirEntry offset, first internal offset, second internal offset
                                      // TopLevel(usize, usize), // chunk_num, offset
}

impl LocalCodePtr {
    pub(crate) fn assign_if_local(&mut self, cp: CodePtr) {
        match cp {
            CodePtr::Local(local) => *self = local,
            _ => {}
        }
    }

    #[inline]
    pub(crate) fn abs_loc(&self) -> usize {
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

    pub(crate) fn as_functor<T: RawBlockTraits>(&self, heap: &mut HeapTemplate<T>) -> Addr {
        let addr = Addr::HeapCell(heap.h());

        match self {
            LocalCodePtr::DirEntry(p) => {
                heap.append(functor!("dir_entry", [integer(*p)]));
            }
            LocalCodePtr::Halt => {
                heap.append(functor!("halt"));
            }
            /*
            LocalCodePtr::TopLevel(chunk_num, offset) => {
                heap.append(functor!(
                    "top_level",
                    [integer(*chunk_num), integer(*offset)]
                ));
            }
            */
            LocalCodePtr::IndexingBuf(p, o, i) => {
                heap.append(functor!(
                    "indexed_buf",
                    [integer(*p), integer(*o), integer(*i)]
                ));
            }
        }

        addr
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
            &mut LocalCodePtr::DirEntry(ref mut p) /* |
            &mut LocalCodePtr::TopLevel(_, ref mut p) */    => *p += rhs,
            &mut LocalCodePtr::IndexingBuf(_, _, ref mut i) => *i += rhs,
            &mut LocalCodePtr::Halt => unreachable!(),
        }
    }
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            p @ CodePtr::REPL(..) | p @ CodePtr::VerifyAttrInterrupt(_) => {
                // |
                // p @ CodePtr::DynamicTransaction(..) => {
                p
            }
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

pub(crate) type HeapVarDict = IndexMap<Rc<Var>, Addr>;
pub(crate) type AllocVarDict = IndexMap<Rc<Var>, VarData>;

pub(crate) type GlobalVarDir = IndexMap<ClauseName, (Ball, Option<Addr>)>;

pub(crate) type StreamAliasDir = IndexMap<ClauseName, Stream>;
pub(crate) type StreamDir = BTreeSet<Stream>;

pub(crate) type MetaPredicateDir = IndexMap<PredicateKey, Vec<MetaSpec>>;

pub(crate) type ExtensiblePredicates = IndexMap<PredicateKey, PredicateSkeleton>;

pub(crate) type LocalExtensiblePredicates =
    IndexMap<(CompilationTarget, PredicateKey), LocalPredicateSkeleton>;

#[derive(Debug)]
pub(crate) struct IndexStore {
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

impl Default for IndexStore {
    #[inline]
    fn default() -> Self {
        index_store!(CodeDir::new(), default_op_dir(), ModuleDir::new())
    }
}

impl IndexStore {
    pub(crate) fn get_predicate_skeleton_mut(
        &mut self,
        compilation_target: &CompilationTarget,
        key: &PredicateKey,
    ) -> Option<&mut PredicateSkeleton> {
        match (key.0.as_str(), key.1) {
            //            ("term_expansion", 2) => self.extensible_predicates.get_mut(key),
            _ => match compilation_target {
                CompilationTarget::User => self.extensible_predicates.get_mut(key),
                CompilationTarget::Module(ref module_name) => {
                    if let Some(module) = self.modules.get_mut(module_name) {
                        module.extensible_predicates.get_mut(key)
                    } else {
                        None
                    }
                }
            },
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
        listing_src_file_name: Option<ClauseName>,
        key: PredicateKey,
    ) -> Option<&mut LocalPredicateSkeleton> {
        if let Some(filename) = listing_src_file_name {
            src_compilation_target = CompilationTarget::Module(filename);
        }

        match src_compilation_target {
            CompilationTarget::User => self
                .local_extensible_predicates
                .get_mut(&(local_compilation_target, key)),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get_mut(module_name) {
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
        listing_src_file_name: Option<ClauseName>,
        key: PredicateKey,
    ) -> Option<&LocalPredicateSkeleton> {
        if let Some(filename) = listing_src_file_name {
            src_compilation_target = CompilationTarget::Module(filename);
        }

        match src_compilation_target {
            CompilationTarget::User => self
                .local_extensible_predicates
                .get(&(local_compilation_target, key)),
            CompilationTarget::Module(ref module_name) => {
                if let Some(module) = self.modules.get(module_name) {
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
        name: ClauseName,
        arity: usize,
        module: ClauseName,
        op_spec: Option<SharedOpDesc>,
    ) -> Option<CodeIndex> {
        if module.as_str() == "user" {
            match ClauseType::from(name, arity, op_spec) {
                ClauseType::Named(name, arity, _) => self.code_dir.get(&(name, arity)).cloned(),
                ClauseType::Op(name, spec, ..) => self.code_dir.get(&(name, spec.arity())).cloned(),
                _ => None,
            }
        } else {
            self.modules.get(&module).and_then(|module| {
                match ClauseType::from(name, arity, op_spec) {
                    ClauseType::Named(name, arity, _) => {
                        module.code_dir.get(&(name, arity)).cloned()
                    }
                    ClauseType::Op(name, spec, ..) => {
                        module.code_dir.get(&(name, spec.arity())).cloned()
                    }
                    _ => None,
                }
            })
        }
    }

    pub(crate) fn get_meta_predicate_spec(
        &self,
        name: ClauseName,
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

    pub(crate) fn is_dynamic_predicate(&self, module_name: ClauseName, key: PredicateKey) -> bool {
        match module_name.as_str() {
            "user" => self
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
        IndexStore::default()
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h = clause_name!("run_cleaners_with_handling");
        let r_wo_h = clause_name!("run_cleaners_without_handling");
        let iso_ext = clause_name!("iso_ext");

        let r_w_h = self
            .get_predicate_code_index(r_w_h, 0, iso_ext.clone(), None)
            .and_then(|item| item.local());
        let r_wo_h = self
            .get_predicate_code_index(r_wo_h, 1, iso_ext, None)
            .and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
    }
}

pub(crate) type CodeDir = BTreeMap<PredicateKey, CodeIndex>;

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

    pub(crate) fn to_owned(self) -> T
    where
        T: Clone,
    {
        match self {
            RefOrOwned::Borrowed(item) => item.clone(),
            RefOrOwned::Owned(item) => item,
        }
    }
}
