use crate::prolog_parser::ast::*;
use crate::prolog_parser::tabled_rc::*;

use crate::clause_types::*;
use crate::fixtures::*;
use crate::forms::*;
use crate::machine::code_repo::CodeRepo;
use crate::machine::Ball;
use crate::machine::heap::*;
use crate::machine::machine_state::*;
use crate::machine::partial_string::*;
use crate::machine::raw_block::RawBlockTraits;
use crate::machine::streams::Stream;
use crate::instructions::*;
use crate::ordered_float::OrderedFloat;
use crate::rug::{Integer, Rational};

use crate::indexmap::IndexMap;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use std::net::TcpListener;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrderedOpDirKey(pub ClauseName, pub Fixity);

pub type OssifiedOpDir = BTreeMap<OrderedOpDirKey, (usize, Specifier)>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DBRef {
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
pub enum TermOrderCategory {
    Variable,
    FloatingPoint,
    Integer,
    Atom,
    Compound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Addr {
    AttrVar(usize),
    Char(char),
    Con(usize),
    CutPoint(usize),
    EmptyList,
    Fixnum(isize),
    Float(OrderedFloat<f64>),
    Lis(usize),
    HeapCell(usize),
    PStrLocation(usize, usize), // location of pstr in heap, offset into string in bytes.
    StackCell(usize, usize),
    Str(usize),
    Stream(usize),
    TcpListener(usize),
    Usize(usize),
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd)]
pub enum Ref {
    AttrVar(usize),
    HeapCell(usize),
    StackCell(usize, usize),
}

impl Ref {
    pub fn as_addr(self) -> Addr {
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
          | (Ref::AttrVar(h1), Ref::HeapCell(h2)) => {
                h1.cmp(&h2)
            }
            (Ref::StackCell(fr1, sc1), Ref::StackCell(fr2, sc2)) => {
                fr1.cmp(&fr2).then_with(|| sc1.cmp(&sc2))
            }
            (Ref::StackCell(..), _) => {
                Ordering::Greater
            }
            (_, Ref::StackCell(..)) => {
                Ordering::Less
            }
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
            &Addr::StackCell(fr, sc) => {
                match *r {
                    Ref::AttrVar(_) | Ref::HeapCell(_) => {
                        Some(Ordering::Greater)
                    }
                    Ref::StackCell(fr1, sc1) => {
                        if fr1 < fr || (fr1 == fr && sc1 < sc) {
                            Some(Ordering::Greater)
                        } else if fr1 == fr && sc1 == sc {
                            Some(Ordering::Equal)
                        } else {
                            Some(Ordering::Less)
                        }
                    }
                }
            }
            &Addr::HeapCell(h) | &Addr::AttrVar(h) => {
                match r {
                    Ref::StackCell(..) => {
                        Some(Ordering::Less)
                    }
                    Ref::AttrVar(h1) | Ref::HeapCell(h1) => {
                        h.partial_cmp(h1)
                    }
                }
            }
            _ => {
                None
            }
        }
    }
}

impl Addr {
    #[inline]
    pub fn is_heap_bound(&self) -> bool {
        match self {
            Addr::Char(_) | Addr::EmptyList |
            Addr::CutPoint(_) | Addr::Usize(_) | Addr::Fixnum(_) |
            Addr::Float(_) => {
                false
            }
            _ => {
                true
            }
        }
    }

    #[inline]
    pub fn is_ref(&self) -> bool {
        match self {
            Addr::HeapCell(_) | Addr::StackCell(_, _) | Addr::AttrVar(_) => {
                true
            }
            _ => {
                false
            }
        }
    }

    #[inline]
    pub fn as_var(&self) -> Option<Ref> {
        match self {
            &Addr::AttrVar(h) => Some(Ref::AttrVar(h)),
            &Addr::HeapCell(h) => Some(Ref::HeapCell(h)),
            &Addr::StackCell(fr, sc) => Some(Ref::StackCell(fr, sc)),
            _ => None,
        }
    }

    pub(super)
    fn order_category(&self, heap: &Heap) -> Option<TermOrderCategory> {
        match Number::try_from((*self, heap)) {
            Ok(Number::Integer(_)) | Ok(Number::Fixnum(_)) | Ok(Number::Rational(_)) => {
                Some(TermOrderCategory::Integer)
            }
            Ok(Number::Float(_)) => {
                Some(TermOrderCategory::FloatingPoint)
            }
            _ => {
                match self {
                    Addr::HeapCell(_) | Addr::AttrVar(_) | Addr::StackCell(..) => {
                        Some(TermOrderCategory::Variable)
                    }
                    Addr::Float(_) => {
                        Some(TermOrderCategory::FloatingPoint)
                    }
                    &Addr::Con(h) => {
                        match &heap[h] {
                            HeapCellValue::Atom(..) => {
                                Some(TermOrderCategory::Atom)
                            }
                            HeapCellValue::DBRef(_) => {
                                None
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }
                    Addr::Char(_) | Addr::EmptyList => {
                        Some(TermOrderCategory::Atom)
                    }
                    Addr::Fixnum(_) | Addr::Usize(_) => {
                        Some(TermOrderCategory::Integer)
                    }
                    Addr::Lis(_) | Addr::PStrLocation(..) | Addr::Str(_) => {
                        Some(TermOrderCategory::Compound)
                    }
                    Addr::CutPoint(_) | Addr::Stream(_) | Addr::TcpListener(_) => {
                        None
                    }
                }
            }
        }
    }

    pub fn as_constant_index(&self, machine_st: &MachineState) -> Option<Constant> {
        match self {
            &Addr::Char(c) => {
                Some(Constant::Char(c))
            }
            &Addr::Con(h) => {
                match &machine_st.heap[h] {
                    &HeapCellValue::Atom(ref name, _) if name.is_char() => {
                        Some(Constant::Char(name.as_str().chars().next().unwrap()))
                    }
                    &HeapCellValue::Atom(ref name, _) => {
                        Some(Constant::Atom(name.clone(), None))
                    }
                    &HeapCellValue::Integer(ref n) => {
                        Some(Constant::Integer(n.clone()))
                    }
                    &HeapCellValue::Rational(ref n) => {
                        Some(Constant::Rational(n.clone()))
                    }
                    _ => {
                        None
                    }
                }
            }
            &Addr::EmptyList => {
                Some(Constant::EmptyList)
            }
            &Addr::Fixnum(n) => {
                Some(Constant::Fixnum(n))
            }
            &Addr::Float(f) => {
                Some(Constant::Float(f))
            }
            &Addr::PStrLocation(h, n) => {
                let mut heap_pstr_iter =
                    machine_st.heap_pstr_iter(Addr::PStrLocation(h, n));

                let buf = heap_pstr_iter.to_string();
                let end_addr = heap_pstr_iter.focus();

                if end_addr == Addr::EmptyList {
                    Some(Constant::String(Rc::new(buf)))
                } else {
                    None
                }
            }
            &Addr::Usize(n) => {
                Some(Constant::Usize(n))
            }
            _ => {
                None
            }
        }
    }

    pub fn is_protected(&self, e: usize) -> bool {
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
pub enum TrailRef {
    Ref(Ref),
    AttrVarHeapLink(usize),
    AttrVarListLink(usize, usize),
}

impl From<Ref> for TrailRef {
    fn from(r: Ref) -> Self {
        TrailRef::Ref(r)
    }
}

#[derive(Debug)]
pub enum HeapCellValue {
    Addr(Addr),
    Atom(ClauseName, Option<SharedOpDesc>),
    DBRef(DBRef),
    Integer(Rc<Integer>),
    NamedStr(usize, ClauseName, Option<SharedOpDesc>), // arity, name, precedence/Specifier if it has one.
    Rational(Rc<Rational>),
    PartialString(PartialString, bool), // the partial string, a bool indicating whether it came from a Constant.
    Stream(Stream),
    TcpListener(TcpListener),
}

impl HeapCellValue {
    #[inline]
    pub fn as_addr(&self, focus: usize) -> Addr {
        match self {
            HeapCellValue::Addr(ref a) => {
                *a
            }
            HeapCellValue::Atom(..) | HeapCellValue::DBRef(..) | HeapCellValue::Integer(..) |
            HeapCellValue::Rational(..) => {
                Addr::Con(focus)
            }
            HeapCellValue::NamedStr(_, _, _) => {
                Addr::Str(focus)
            }
            HeapCellValue::PartialString(..) => {
                Addr::PStrLocation(focus, 0)
            }
            HeapCellValue::Stream(_) => {
                Addr::Stream(focus)
            }
            HeapCellValue::TcpListener(_) => {
                Addr::TcpListener(focus)
            }
        }
    }

    #[inline]
    pub fn context_free_clone(&self) -> HeapCellValue {
        match self {
            &HeapCellValue::Addr(addr) => {
                HeapCellValue::Addr(addr)
            }
            &HeapCellValue::Atom(ref name, ref op) => {
                HeapCellValue::Atom(name.clone(), op.clone())
            }
            &HeapCellValue::DBRef(ref db_ref) => {
                HeapCellValue::DBRef(db_ref.clone())
            }
            &HeapCellValue::Integer(ref n) => {
                HeapCellValue::Integer(n.clone())
            }
            &HeapCellValue::NamedStr(arity, ref name, ref op) => {
                HeapCellValue::NamedStr(arity, name.clone(), op.clone())
            }
            &HeapCellValue::Rational(ref r) => {
                HeapCellValue::Rational(r.clone())
            }
            &HeapCellValue::PartialString(ref pstr, has_tail) => {
                HeapCellValue::PartialString(pstr.clone(), has_tail)
            }
            &HeapCellValue::Stream(ref stream) => {
                HeapCellValue::Stream(stream.clone())
            }
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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum IndexPtr {
    DynamicUndefined, // a predicate, declared as dynamic, whose location in code is as yet undefined.
    Undefined,
    InSituDirEntry(usize),
    Index(usize),
    UserGoalExpansion,
    UserTermExpansion
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct CodeIndex(pub Rc<RefCell<(IndexPtr, ClauseName)>>);

impl CodeIndex {
    #[inline]
    pub fn new(ptr: IndexPtr, module_name: ClauseName) -> Self {
        CodeIndex(Rc::new(RefCell::new(( ptr, module_name ))))
    }

    #[inline]
    pub fn is_undefined(&self) -> bool {
        let index_ptr = &self.0.borrow().0;

        match index_ptr {
            &IndexPtr::Undefined | &IndexPtr::DynamicUndefined => true,
            _ => false
        }
    }

    #[inline]
    pub fn dynamic_undefined(module_name: ClauseName) -> Self {
        CodeIndex(Rc::new(RefCell::new((
            IndexPtr::DynamicUndefined,
            module_name
        ))))
    }

    #[inline]
    pub fn module_name(&self) -> ClauseName {
        self.0.borrow().1.clone()
    }

    pub fn local(&self) -> Option<usize> {
        match self.0.borrow().0 {
            IndexPtr::Index(i) => Some(i),
            _ => None,
        }
    }
}

impl Default for CodeIndex {
    fn default() -> Self {
        CodeIndex(Rc::new(RefCell::new((
            IndexPtr::Undefined,
            clause_name!(""),
        ))))
    }
}

impl From<(usize, ClauseName)> for CodeIndex {
    fn from(value: (usize, ClauseName)) -> Self {
        CodeIndex(Rc::new(RefCell::new((IndexPtr::Index(value.0), value.1))))
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DynamicAssertPlace {
    Back,
    Front,
}

impl DynamicAssertPlace {
    #[inline]
    pub fn predicate_name(self) -> ClauseName {
        match self {
            DynamicAssertPlace::Back => clause_name!("assertz"),
            DynamicAssertPlace::Front => clause_name!("asserta"),
        }
    }

    #[inline]
    pub fn push_to_queue(self, addrs: &mut VecDeque<Addr>, new_addr: Addr) {
        match self {
            DynamicAssertPlace::Back => addrs.push_back(new_addr),
            DynamicAssertPlace::Front => addrs.push_front(new_addr),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DynamicTransactionType {
    Abolish,
    Assert(DynamicAssertPlace),
    ModuleAbolish,
    ModuleAssert(DynamicAssertPlace),
    ModuleRetract,
    Retract, // dynamic index of the clause to remove.
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum REPLCodePtr {
    CompileBatch,
    UseModule,
    UseQualifiedModule,
    UseModuleFromFile,
    UseQualifiedModuleFromFile
}

#[derive(Debug, Clone, PartialEq)]
pub enum CodePtr {
    BuiltInClause(BuiltInClauseType, LocalCodePtr), // local is the successor call.
    CallN(usize, LocalCodePtr, bool),               // arity, local, last call.
    Local(LocalCodePtr),
    DynamicTransaction(DynamicTransactionType, LocalCodePtr), // the type of transaction, the return pointer.
    REPL(REPLCodePtr, LocalCodePtr),                          // the REPL code, the return pointer.
    VerifyAttrInterrupt(usize), // location of the verify attribute interrupt code in the CodeDir.
}

impl CodePtr {
    pub fn local(&self) -> LocalCodePtr {
        match self {
            &CodePtr::BuiltInClause(_, ref local)
          | &CodePtr::CallN(_, ref local, _)
          | &CodePtr::Local(ref local) => local.clone(),
            &CodePtr::VerifyAttrInterrupt(p) => LocalCodePtr::DirEntry(p),
            &CodePtr::REPL(_, p) | &CodePtr::DynamicTransaction(_, p) => p,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LocalCodePtr {
    DirEntry(usize), // offset.
    InSituDirEntry(usize),
    TopLevel(usize, usize), // chunk_num, offset.
    UserGoalExpansion(usize),
    UserTermExpansion(usize),
}

impl LocalCodePtr {
    pub(crate)
    fn assign_if_local(&mut self, cp: CodePtr) {
        match cp {
            CodePtr::Local(local) => *self = local,
            _ => {}
        }
    }

    pub(crate)
    fn is_reset_cont_marker(&self, code_repo: &CodeRepo, last_call: bool) -> bool {
        match code_repo.lookup_instr(last_call, &CodePtr::Local(*self)) {
            Some(line) => {
                match line.as_ref() {
                    Line::Control(ControlInstruction::CallClause(ref ct, ..)) => {
                        if let ClauseType::System(SystemClauseType::ResetContinuationMarker) = *ct {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            None => {}
        }

        false
    }

    pub(crate)
    fn as_functor<T: RawBlockTraits>(&self, heap: &mut HeapTemplate<T>) -> Addr {
        let addr = Addr::HeapCell(heap.h());

        match self {
            LocalCodePtr::DirEntry(p) => {
                heap.append(functor!(
                    "dir_entry",
                    [integer(*p)]
                ));
            }
            LocalCodePtr::InSituDirEntry(p) => {
                heap.append(functor!(
                    "in_situ_dir_entry",
                    [integer(*p)]
                ));
            }
            LocalCodePtr::TopLevel(chunk_num, offset) => {
                heap.append(functor!(
                    "top_level",
                    [integer(*chunk_num), integer(*offset)]
                ));
            }
            LocalCodePtr::UserGoalExpansion(p) => {
                heap.append(functor!(
                    "user_goal_expansion",
                    [integer(*p)]
                ));
            }
            LocalCodePtr::UserTermExpansion(p) => {
                heap.append(functor!(
                    "user_term_expansion",
                    [integer(*p)]
                ));
            }
        }

        addr
    }
}

impl PartialOrd<CodePtr> for CodePtr {
    fn partial_cmp(&self, other: &CodePtr) -> Option<Ordering> {
        match (self, other) {
            (&CodePtr::Local(ref l1), &CodePtr::Local(ref l2)) => {
                l1.partial_cmp(l2)
            }
            _ => {
                Some(Ordering::Greater)
            }
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
          | (&LocalCodePtr::TopLevel(_, p1), &LocalCodePtr::TopLevel(_, ref p2)) => {
                p1.partial_cmp(p2)
            }
            (_, &LocalCodePtr::TopLevel(_, _)) => {
                Some(Ordering::Less)
            }
            _ => {
                Some(Ordering::Greater)
            }
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

impl Sub<usize> for LocalCodePtr {
    type Output = Option<LocalCodePtr>;

    fn sub(self, rhs: usize) -> Self::Output {
        match self {
            LocalCodePtr::InSituDirEntry(p) =>
                p.checked_sub(rhs).map(LocalCodePtr::InSituDirEntry),
            LocalCodePtr::DirEntry(p) =>
                p.checked_sub(rhs).map(LocalCodePtr::DirEntry),
            LocalCodePtr::TopLevel(cn, p) =>
                p.checked_sub(rhs).map(|r| LocalCodePtr::TopLevel(cn, r)),
            LocalCodePtr::UserTermExpansion(p) =>
                p.checked_sub(rhs).map(LocalCodePtr::UserTermExpansion),
            LocalCodePtr::UserGoalExpansion(p) =>
                p.checked_sub(rhs).map(LocalCodePtr::UserGoalExpansion),
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
          | &mut LocalCodePtr::TopLevel(_, ref mut p) => *p += rhs,
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

pub type HeapVarDict = IndexMap<Rc<Var>, Addr>;
pub type AllocVarDict = IndexMap<Rc<Var>, VarData>;

#[derive(Debug, Clone)]
pub struct DynamicPredicateInfo {
    pub(super) clauses_subsection_p: usize, // a LocalCodePtr::DirEntry value.
}

impl Default for DynamicPredicateInfo {
    fn default() -> Self {
        DynamicPredicateInfo {
            clauses_subsection_p: 0,
        }
    }
}

pub type InSituCodeDir = IndexMap<PredicateKey, usize>;

// key type: module name, predicate indicator.
pub type DynamicCodeDir = IndexMap<(ClauseName, ClauseName, usize), DynamicPredicateInfo>;

pub type GlobalVarDir = IndexMap<ClauseName, (Ball, Option<usize>)>;

#[derive(Debug)]
pub(crate) struct ModuleStub {
    pub(crate) atom_tbl: TabledData<Atom>,
    pub(crate) in_situ_code_dir: InSituCodeDir,
}

impl ModuleStub {
    pub(crate) fn new(atom_tbl: TabledData<Atom>) -> Self {
        ModuleStub {
            atom_tbl,
            in_situ_code_dir: InSituCodeDir::new(),
        }
    }
}

pub(crate) type ModuleStubDir = IndexMap<ClauseName, ModuleStub>;
pub(crate) type StreamAliasDir = IndexMap<ClauseName, Stream>;
pub(crate) type StreamDir = BTreeSet<Stream>;

#[derive(Debug)]
pub struct IndexStore {
    pub(super) atom_tbl: TabledData<Atom>,
    pub(super) code_dir: CodeDir,
    pub(super) dynamic_code_dir: DynamicCodeDir,
    pub(super) global_variables: GlobalVarDir,
    pub(super) in_situ_code_dir: InSituCodeDir,
    pub(super) in_situ_module_dir: ModuleStubDir,
    pub(super) module_dir: ModuleDir,
    pub(super) modules: ModuleDir,
    pub(super) op_dir: OpDir,
    pub(super) streams: StreamDir,
    pub(super) stream_aliases: StreamAliasDir,
}

impl IndexStore {
    pub fn predicate_exists(
        &self,
        name: ClauseName,
        module: ClauseName,
        arity: usize,
        op_spec: Option<SharedOpDesc>,
    ) -> bool {
        match self.modules.get(&module) {
            Some(module) => match ClauseType::from(name, arity, op_spec) {
                ClauseType::Named(name, arity, _) => module.code_dir.contains_key(&(name, arity)),
                ClauseType::Op(name, spec, ..) => {
                    module.code_dir.contains_key(&(name, spec.arity()))
                }
                _ => true,
            },
            None => match ClauseType::from(name, arity, op_spec) {
                ClauseType::Named(name, arity, _) => self.code_dir.contains_key(&(name, arity)),
                ClauseType::Op(name, spec, ..) => self.code_dir.contains_key(&(name, spec.arity())),
                _ => true,
            },
        }
    }

    pub fn add_term_and_goal_expansion_indices(&mut self) {
        self.code_dir.insert((clause_name!("term_expansion"), 2),
                             CodeIndex(Rc::new(RefCell::new(
                                 (IndexPtr::UserTermExpansion,
                                  clause_name!("user"))
                             ))));
        self.code_dir.insert((clause_name!("goal_expansion"), 2),
                             CodeIndex(Rc::new(RefCell::new(
                                 (IndexPtr::UserGoalExpansion,
                                  clause_name!("user"))
                             ))));
    }

    #[inline]
    pub fn remove_clause_subsection(&mut self, module: ClauseName, name: ClauseName, arity: usize) {
        self.dynamic_code_dir.swap_remove(&(module, name, arity));
    }

    #[inline]
    pub fn get_clause_subsection(
        &self,
        module: ClauseName,
        name: ClauseName,
        arity: usize,
    ) -> Option<DynamicPredicateInfo> {
        self.dynamic_code_dir.get(&(module, name, arity)).cloned()
    }

    #[inline]
    pub(crate) fn take_in_situ_module_dir(&mut self) -> ModuleStubDir {
        mem::replace(&mut self.in_situ_module_dir, ModuleStubDir::new())
    }

    #[inline]
    pub fn take_in_situ_code_dir(&mut self) -> InSituCodeDir {
        mem::replace(&mut self.in_situ_code_dir, InSituCodeDir::new())
    }

    #[inline]
    pub fn take_module(&mut self, name: ClauseName) -> Option<Module> {
        self.modules.swap_remove(&name)
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
            module_dir: ModuleDir::new(),
            dynamic_code_dir: DynamicCodeDir::new(),
            global_variables: GlobalVarDir::new(),
            in_situ_code_dir: InSituCodeDir::new(),
            in_situ_module_dir: ModuleStubDir::new(),
            op_dir: default_op_dir(),
            modules: ModuleDir::new(),
            stream_aliases: StreamAliasDir::new(),
            streams: StreamDir::new(),
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
    fn get_internal(
        &self,
        name: ClauseName,
        arity: usize,
        in_mod: ClauseName,
    ) -> Option<CodeIndex> {
        self.modules
            .get(&in_mod)
            .and_then(|ref module| module.code_dir.get(&(name, arity)))
            .cloned()
    }

    pub(super) fn get_cleaner_sites(&self) -> (usize, usize) {
        let r_w_h = clause_name!("run_cleaners_with_handling");
        let r_wo_h = clause_name!("run_cleaners_without_handling");

        let iso_ext = clause_name!("iso_ext");

        let r_w_h = self
            .get_internal(r_w_h, 0, iso_ext.clone())
            .and_then(|item| item.local());
        let r_wo_h = self
            .get_internal(r_wo_h, 1, iso_ext)
            .and_then(|item| item.local());

        if let Some(r_w_h) = r_w_h {
            if let Some(r_wo_h) = r_wo_h {
                return (r_w_h, r_wo_h);
            }
        }

        return (0, 0);
    }
}

pub type CodeDir = BTreeMap<PredicateKey, CodeIndex>;
pub type TermDir = IndexMap<PredicateKey, (Predicate, VecDeque<TopLevel>)>;

#[derive(Debug)]
pub struct TermDirQuantumEntry {
    pub old_terms: (Predicate, VecDeque<TopLevel>),
    pub new_terms: (Predicate, VecDeque<TopLevel>),
    pub is_fresh: bool,
}

impl TermDirQuantumEntry {
    #[inline]
    pub fn new() -> Self {
        TermDirQuantumEntry {
            old_terms: (Predicate::new(), VecDeque::new()),
            new_terms: (Predicate::new(), VecDeque::new()),
            is_fresh: false,
        }
    }

    pub fn from(preds: &Predicate, queue: &VecDeque<TopLevel>) -> Self
    {
        let mut entry = TermDirQuantumEntry::new();
        entry.is_fresh = false;

        (entry.old_terms.0).0.extend(preds.0.iter().cloned());
        entry.old_terms.1.extend(queue.iter().cloned());

        entry
    }
}

#[derive(Debug)]
pub struct TermDirQuantum(IndexMap<PredicateKey, TermDirQuantumEntry>);

impl TermDirQuantum {
    #[inline]
    pub fn new() -> Self {
        TermDirQuantum(IndexMap::new())
    }

    #[inline]
    pub fn insert_or_refresh(&mut self, key: PredicateKey, mut entry: TermDirQuantumEntry) {
        if let Some(prev_entry) = self.get_mut(&key) {
            prev_entry.is_fresh = true;
        } else {
            entry.is_fresh = true;
            self.0.insert(key, entry);
        }
    }

    #[inline]
    pub fn insert(&mut self, key: PredicateKey, entry: TermDirQuantumEntry) {
        self.0.insert(key, entry);
    }

    #[inline]
    pub fn get_mut(&mut self, key: &PredicateKey) -> Option<&mut TermDirQuantumEntry> {
        self.0.get_mut(key)
    }

    pub fn consolidate(self) -> TermDir {
        let mut term_dir = TermDir::new();

        for (key, entry) in self.0 {
            let (preds, queue) =
                term_dir.entry(key).or_insert((Predicate::new(), VecDeque::new()));

            preds.0.extend((entry.new_terms.0).0.into_iter());
            queue.extend(entry.new_terms.1.into_iter());
        }

        term_dir
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum CompileTimeHook {
    GoalExpansion,
    TermExpansion,
    UserGoalExpansion,
    UserTermExpansion,
}

impl CompileTimeHook {
    pub fn name(self) -> ClauseName {
        match self {
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                clause_name!("goal_expansion")
            }
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                clause_name!("term_expansion")
            }
        }
    }

    #[inline]
    pub fn arity(self) -> usize {
        match self {
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => 2,
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => 2,
        }
    }

    #[inline]
    pub fn user_scope(self) -> Self {
        match self {
            CompileTimeHook::UserGoalExpansion | CompileTimeHook::GoalExpansion => {
                CompileTimeHook::UserGoalExpansion
            }
            CompileTimeHook::UserTermExpansion | CompileTimeHook::TermExpansion => {
                CompileTimeHook::UserTermExpansion
            }
        }
    }

    #[inline]
    pub fn has_module_scope(self) -> bool {
        match self {
            CompileTimeHook::UserTermExpansion | CompileTimeHook::UserGoalExpansion => false,
            _ => true,
        }
    }
}

pub enum RefOrOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T),
}

impl<'a, T: 'a + fmt::Debug> fmt::Debug for RefOrOwned<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RefOrOwned::Borrowed(ref borrowed) =>
                write!(f, "Borrowed({:?})", borrowed),
            &RefOrOwned::Owned(ref owned) => write!(f, "Owned({:?})", owned),
        }
    }
}

impl<'a, T> RefOrOwned<'a, T> {
    pub fn as_ref(&'a self) -> &'a T {
        match self {
            &RefOrOwned::Borrowed(r) => r,
            &RefOrOwned::Owned(ref r) => r,
        }
    }

    pub fn to_owned(self) -> T
    where
        T: Clone,
    {
        match self {
            RefOrOwned::Borrowed(item) => item.clone(),
            RefOrOwned::Owned(item) => item,
        }
    }
}
