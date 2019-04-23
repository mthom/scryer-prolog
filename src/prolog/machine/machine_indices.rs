use prolog_parser::ast::*;
use prolog_parser::tabled_rc::*;

use prolog::clause_types::*;
use prolog::fixtures::*;
use prolog::forms::*;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::mem;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrderedOpDirKey(pub ClauseName, pub Fixity);

pub type OssifiedOpDir = BTreeMap<OrderedOpDirKey, (usize, Specifier)>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum DBRef {
    BuiltInPred(ClauseName, usize, Option<SharedOpDesc>),
    NamedPred(ClauseName, usize, Option<SharedOpDesc>),
    Op(usize, Specifier, ClauseName, Rc<OssifiedOpDir>, SharedOpDesc)
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Addr {
    AttrVar(usize),
    Con(Constant),
    DBRef(DBRef),
    Lis(usize),
    HeapCell(usize),
    StackCell(usize, usize),
    Str(usize)
}

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub enum Ref {
    AttrVar(usize),
    HeapCell(usize),
    StackCell(usize, usize)
}

impl Ref {
    pub fn as_addr(self) -> Addr {
        match self {
            Ref::AttrVar(h)        => Addr::AttrVar(h),
            Ref::HeapCell(h)       => Addr::HeapCell(h),
            Ref::StackCell(fr, sc) => Addr::StackCell(fr, sc)
        }
    }
}

impl PartialEq<Ref> for Addr {
    fn eq(&self, r: &Ref) -> bool {
        self.as_var() == Some(*r)
    }
}

// for use in MachineState::bind.
impl PartialOrd<Ref> for Addr {
    fn partial_cmp(&self, r: &Ref) -> Option<Ordering> {
        match self {
            &Addr::StackCell(fr, sc) =>
                match *r {
                    Ref::AttrVar(_) | Ref::HeapCell(_) =>
                        Some(Ordering::Greater),
                    Ref::StackCell(fr1, sc1) =>
                        if fr1 < fr || (fr1 == fr && sc1 < sc) {
                            Some(Ordering::Greater)
                        } else if fr1 == fr && sc1 == sc {
                            Some(Ordering::Equal)
                        } else {
                            Some(Ordering::Less)
                        }
                },
            &Addr::HeapCell(h) | &Addr::AttrVar(h) =>
                match r {
                    &Ref::StackCell(..) => Some(Ordering::Less),
                    &Ref::AttrVar(h1) | &Ref::HeapCell(h1) => h.partial_cmp(&h1)
                },
            _ => None
        }
    }
}

impl Addr {
    pub fn is_ref(&self) -> bool {
        match self {
            &Addr::AttrVar(_) | &Addr::HeapCell(_) | &Addr::StackCell(_, _) => true,
            _ => false
        }
    }

    pub fn as_var(&self) -> Option<Ref> {
        match self {
            &Addr::AttrVar(h) => Some(Ref::AttrVar(h)),
            &Addr::HeapCell(h) => Some(Ref::HeapCell(h)),
            &Addr::StackCell(fr, sc) => Some(Ref::StackCell(fr, sc)),
            _ => None
        }
    }

    pub fn is_protected(&self, e: usize) -> bool {
        match self {
            &Addr::StackCell(addr, _) if addr >= e => false,
            _ => true
        }
    }
}

impl Add<usize> for Addr {
    type Output = Addr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            Addr::Lis(a) => Addr::Lis(a + rhs),
            Addr::AttrVar(h) => Addr::AttrVar(h + rhs),
            Addr::HeapCell(h) => Addr::HeapCell(h + rhs),
            Addr::Str(s) => Addr::Str(s + rhs),
            _ => self
        }
    }
}

impl Sub<i64> for Addr {
    type Output = Addr;

    fn sub(self, rhs: i64) -> Self::Output {
        if rhs < 0 {
            match self {
                Addr::Lis(a) => Addr::Lis(a + rhs.abs() as usize),
                Addr::AttrVar(h) => Addr::AttrVar(h + rhs.abs() as usize),
                Addr::HeapCell(h) => Addr::HeapCell(h + rhs.abs() as usize),
                Addr::Str(s) => Addr::Str(s + rhs.abs() as usize),
                _ => self
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
            Addr::Lis(a) => Addr::Lis(a - rhs),
            Addr::AttrVar(h) => Addr::AttrVar(h - rhs),
            Addr::HeapCell(h) => Addr::HeapCell(h - rhs),
            Addr::Str(s) => Addr::Str(s - rhs),
            _ => self
        }
    }
}

impl SubAssign<usize> for Addr {
    fn sub_assign(&mut self, rhs: usize) {
        *self = self.clone() - rhs;
    }
}

impl From<Ref> for Addr {
    fn from(r: Ref) -> Self {
        match r {
            Ref::AttrVar(h)        => Addr::AttrVar(h),
            Ref::HeapCell(h)       => Addr::HeapCell(h),
            Ref::StackCell(fr, sc) => Addr::StackCell(fr, sc)
        }
    }
}

#[derive(Clone)]
pub enum TrailRef {
    Ref(Ref),
    AttrVarLink(usize, Addr)
}

impl From<Ref> for TrailRef {
    fn from(r: Ref) -> Self {
        TrailRef::Ref(r)
    }
}

#[derive(Clone, PartialEq)]
pub enum HeapCellValue {
    Addr(Addr),
    NamedStr(usize, ClauseName, Option<SharedOpDesc>), // arity, name, precedence/Specifier if it has one.
}

impl HeapCellValue {
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            &HeapCellValue::Addr(ref a) => a.clone(),
            &HeapCellValue::NamedStr(_, _, _) => Addr::Str(focus)
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum IndexPtr {
    Undefined,
    Index(usize),
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct CodeIndex(pub Rc<RefCell<(IndexPtr, ClauseName)>>);

impl CodeIndex {
    #[inline]
    pub fn is_undefined(&self) -> bool {
        let index_ptr = &self.0.borrow().0;

        if let &IndexPtr::Undefined = index_ptr {
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn module_name(&self) -> ClauseName {
        self.0.borrow().1.clone()
    }

    pub fn local(&self) -> Option<usize> {
        match self.0.borrow().0 {
            IndexPtr::Index(i) => Some(i),
            _ => None
        }
    }
}

impl Default for CodeIndex {
    fn default() -> Self {
        CodeIndex(Rc::new(RefCell::new((IndexPtr::Undefined, clause_name!("")))))
    }
}

impl From<(usize, ClauseName)> for CodeIndex {
    fn from(value: (usize, ClauseName)) -> Self {
        CodeIndex(Rc::new(RefCell::new((IndexPtr::Index(value.0), value.1))))
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum DynamicAssertPlace {
    Back, Front
}

impl DynamicAssertPlace {
    #[inline]
    pub fn predicate_name(self) -> ClauseName {
        match self {
            DynamicAssertPlace::Back  => clause_name!("assertz"),
            DynamicAssertPlace::Front => clause_name!("asserta")
        }
    }

    #[inline]
    pub fn push_to_queue(self, addrs: &mut VecDeque<Addr>, new_addr: Addr) {
        match self {
            DynamicAssertPlace::Back  => addrs.push_back(new_addr),
            DynamicAssertPlace::Front => addrs.push_front(new_addr)
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum DynamicTransactionType {
    Abolish,
    Assert(DynamicAssertPlace),
    ModuleAbolish,
    ModuleAssert(DynamicAssertPlace),
    ModuleRetract,
    Retract // dynamic index of the clause to remove.
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum REPLCodePtr {
    CompileBatch,    
    SubmitQueryAndPrintResults
}

#[derive(Clone, PartialEq)]
pub enum CodePtr {
    BuiltInClause(BuiltInClauseType, LocalCodePtr), // local is the successor call.
    CallN(usize, LocalCodePtr), // arity, local.
    Local(LocalCodePtr),
    DynamicTransaction(DynamicTransactionType, LocalCodePtr), // the type of transaction, the return pointer.
    REPL(REPLCodePtr, LocalCodePtr), // the REPL code, the return pointer.
    VerifyAttrInterrupt(usize), // location of the verify attribute interrupt code in the CodeDir.    
}

impl CodePtr {
    pub fn local(&self) -> LocalCodePtr {
        match self {
            &CodePtr::BuiltInClause(_, ref local)
          | &CodePtr::CallN(_, ref local)
          | &CodePtr::Local(ref local) => local.clone(),
            &CodePtr::VerifyAttrInterrupt(p) => LocalCodePtr::DirEntry(p),
            &CodePtr::REPL(_, p)
          | &CodePtr::DynamicTransaction(_, p) => p
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum LocalCodePtr {
    DirEntry(usize), // offset.
    InSituDirEntry(usize),
    TopLevel(usize, usize), // chunk_num, offset.
    UserGoalExpansion(usize),
    UserTermExpansion(usize)
}

impl LocalCodePtr {
    pub fn assign_if_local(&mut self, cp: CodePtr) {
        match cp {
            CodePtr::Local(local) => *self = local,
            _ => {}
        }
    }
}

impl PartialOrd<CodePtr> for CodePtr {
    fn partial_cmp(&self, other: &CodePtr) -> Option<Ordering> {
        match (self, other) {
            (&CodePtr::Local(ref l1), &CodePtr::Local(ref l2)) => l1.partial_cmp(l2),
            _ => Some(Ordering::Greater)
        }
    }
}

impl PartialOrd<LocalCodePtr> for LocalCodePtr {
    fn partial_cmp(&self, other: &LocalCodePtr) -> Option<Ordering> {
        match (self, other) {
            (&LocalCodePtr::InSituDirEntry(p1), &LocalCodePtr::InSituDirEntry(ref p2))
          | (&LocalCodePtr::DirEntry(p1), &LocalCodePtr::DirEntry(ref p2))
          | (&LocalCodePtr::UserTermExpansion(p1), &LocalCodePtr::UserTermExpansion(ref p2))
          | (&LocalCodePtr::UserGoalExpansion(p1), &LocalCodePtr::UserGoalExpansion(ref p2))
          | (&LocalCodePtr::TopLevel(_, p1), &LocalCodePtr::TopLevel(_, ref p2)) =>
                p1.partial_cmp(p2),
            (_, &LocalCodePtr::TopLevel(_, _)) =>
                Some(Ordering::Less),
            _ => Some(Ordering::Greater)
        }
    }
}

impl Default for CodePtr {
    fn default() -> Self {
        CodePtr::Local(LocalCodePtr::default())
    }
}

impl Default for LocalCodePtr {
    fn default() -> Self {
        LocalCodePtr::TopLevel(0, 0)
    }
}

impl Add<usize> for LocalCodePtr {
    type Output = LocalCodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            LocalCodePtr::InSituDirEntry(p) => LocalCodePtr::InSituDirEntry(p + rhs),
            LocalCodePtr::DirEntry(p) => LocalCodePtr::DirEntry(p + rhs),
            LocalCodePtr::TopLevel(cn, p) => LocalCodePtr::TopLevel(cn, p + rhs),
            LocalCodePtr::UserTermExpansion(p) => LocalCodePtr::UserTermExpansion(p + rhs),
            LocalCodePtr::UserGoalExpansion(p) => LocalCodePtr::UserGoalExpansion(p + rhs),
        }
    }
}

impl AddAssign<usize> for LocalCodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut LocalCodePtr::InSituDirEntry(ref mut p)
          | &mut LocalCodePtr::UserGoalExpansion(ref mut p)
          | &mut LocalCodePtr::UserTermExpansion(ref mut p)
          | &mut LocalCodePtr::DirEntry(ref mut p)
          | &mut LocalCodePtr::TopLevel(_, ref mut p) => *p += rhs
        }
    }
}

impl Add<usize> for CodePtr {
    type Output = CodePtr;

    fn add(self, rhs: usize) -> Self::Output {
        match self {
            p @ CodePtr::REPL(..)
          | p @ CodePtr::VerifyAttrInterrupt(_)
          | p @ CodePtr::DynamicTransaction(..) => p,
            CodePtr::Local(local) => CodePtr::Local(local + rhs),
            CodePtr::CallN(_, local) | CodePtr::BuiltInClause(_, local) => CodePtr::Local(local + rhs)
        }
    }
}

impl AddAssign<usize> for CodePtr {
    fn add_assign(&mut self, rhs: usize) {
        match self {
            &mut CodePtr::VerifyAttrInterrupt(_) => {},
            &mut CodePtr::Local(ref mut local) => *local += rhs,
            _ => *self = CodePtr::Local(self.local() + rhs)
        }
    }
}

pub type HeapVarDict  = HashMap<Rc<Var>, Addr>;
pub type AllocVarDict = HashMap<Rc<Var>, VarData>;

#[derive(Clone)]
pub struct DynamicPredicateInfo {
    pub(super) clauses_subsection_p: usize, // a LocalCodePtr::DirEntry value.
}

impl Default for DynamicPredicateInfo {
    fn default() -> Self {
        DynamicPredicateInfo { clauses_subsection_p: 0 }
    }
}

pub type InSituCodeDir  = HashMap<PredicateKey, usize>;
// key type: module name, predicate indicator.
pub type DynamicCodeDir = HashMap<(ClauseName, ClauseName, usize), DynamicPredicateInfo>;

pub type GlobalVarDir = HashMap<ClauseName, Addr>;

pub struct IndexStore {
    pub(super) atom_tbl: TabledData<Atom>,
    pub(super) code_dir: CodeDir,
    pub(super) dynamic_code_dir: DynamicCodeDir,
    pub(super) global_variables: GlobalVarDir,
    pub(super) in_situ_code_dir: InSituCodeDir,
    pub(super) modules: ModuleDir,
    pub(super) op_dir: OpDir,
}

impl IndexStore {    
    pub fn predicate_exists(&self, name: ClauseName, module: ClauseName, arity: usize,
                            op_spec: Option<SharedOpDesc>)
                            -> bool
    {
        match self.modules.get(&module) {
            Some(module) =>
                match ClauseType::from(name, arity, op_spec) {
                    ClauseType::Named(name, arity, _) =>
                        module.code_dir.contains_key(&(name, arity)),
                    ClauseType::Op(name, spec, ..) =>
                        module.code_dir.contains_key(&(name, spec.arity())),
                    _ =>
                        true
                },
            None =>
                match ClauseType::from(name, arity, op_spec) {
                    ClauseType::Named(name, arity, _) =>
                        self.code_dir.contains_key(&(name, arity)),
                    ClauseType::Op(name, spec, ..) =>
                        self.code_dir.contains_key(&(name, spec.arity())),
                    _ =>
                        true
                }
        }
    }

    #[inline]
    pub fn remove_clause_subsection(&mut self, module: ClauseName, name: ClauseName, arity: usize)
    {
        self.dynamic_code_dir.remove(&(module, name, arity));
    }

    #[inline]
    pub fn get_clause_subsection(&self, module: ClauseName, name: ClauseName, arity: usize)
                                 -> Option<DynamicPredicateInfo>
    {
        self.dynamic_code_dir.get(&(module, name, arity)).cloned()
    }

    #[inline]
    pub fn take_module(&mut self, name: ClauseName) -> Option<Module> {
        self.modules.remove(&name)
    }

    #[inline]
    pub fn insert_module(&mut self, module: Module) {
        self.modules.insert(module.module_decl.name.clone(), module);
    }

    #[inline]
    pub(super) fn new() -> Self {
        IndexStore {
            atom_tbl: TabledData::new(Rc::new("user".to_string())),
            code_dir: CodeDir::new(),
            dynamic_code_dir: DynamicCodeDir::new(),
            global_variables: GlobalVarDir::new(),
            in_situ_code_dir: InSituCodeDir::new(),
            op_dir: default_op_dir(),
            modules: ModuleDir::new(),
//            parsing_stream: readline::parsing_stream(String::new())
        }
    }

    #[inline]
    pub(super) fn copy_and_swap(&mut self, other: &mut IndexStore) {
        self.code_dir = other.code_dir.clone();
        self.op_dir = other.op_dir.clone();

        mem::swap(&mut self.code_dir, &mut other.code_dir);
        mem::swap(&mut self.op_dir, &mut other.op_dir);
        mem::swap(&mut self.modules, &mut other.modules);
    }

    #[inline]
    fn get_internal(&self, name: ClauseName, arity: usize, in_mod: ClauseName) -> Option<CodeIndex>
    {
        self.modules.get(&in_mod)
            .and_then(|ref module| module.code_dir.get(&(name, arity)))
            .cloned()
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h  = clause_name!("run_cleaners_with_handling");
        let r_wo_h = clause_name!("run_cleaners_without_handling");

        let non_iso = clause_name!("non_iso");

        let r_w_h  = self.get_internal(r_w_h, 0, non_iso.clone()).and_then(|item| item.local());
        let r_wo_h = self.get_internal(r_wo_h, 1, non_iso).and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
    }
}

pub type CodeDir = BTreeMap<PredicateKey, CodeIndex>;
pub type TermDir = HashMap<PredicateKey, (Predicate, VecDeque<TopLevel>)>;

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum CompileTimeHook {
    GoalExpansion,
    TermExpansion,
    UserGoalExpansion,
    UserTermExpansion
}

impl CompileTimeHook {
    pub fn name(self) -> ClauseName {
        match self {
            CompileTimeHook::UserGoalExpansion
          | CompileTimeHook::GoalExpansion => clause_name!("goal_expansion"),
            CompileTimeHook::UserTermExpansion
          | CompileTimeHook::TermExpansion => clause_name!("term_expansion")
        }
    }

    #[inline]
    pub fn arity(self) -> usize {
        match self {
            CompileTimeHook::UserGoalExpansion
          | CompileTimeHook::GoalExpansion => 2,
            CompileTimeHook::UserTermExpansion
          | CompileTimeHook::TermExpansion => 2
        }
    }

    #[inline]
    pub fn user_scope(self) -> Self {
        match self {
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion =>
                CompileTimeHook::UserGoalExpansion,
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion =>
                CompileTimeHook::UserTermExpansion,
        }
    }

    #[inline]
    pub fn has_module_scope(self) -> bool {
        match self {
            CompileTimeHook::UserTermExpansion | CompileTimeHook::UserGoalExpansion => false,
            _ => true
        }
    }
}

pub(super) enum RefOrOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T)
}

impl<'a, T> RefOrOwned<'a, T> {
    pub(super)
    fn as_ref(&'a self) -> &'a T {
        match self {
            &RefOrOwned::Borrowed(r) => r,
            &RefOrOwned::Owned(ref r) => r
        }
    }
}
