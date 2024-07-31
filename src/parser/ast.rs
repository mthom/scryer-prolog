#![allow(clippy::new_without_default)] // annotating structs annotated with #[bitfield] doesn't work

use crate::arena::*;
use crate::atom_table::*;
use crate::machine::machine_indices::*;
use crate::parser::char_reader::*;
use crate::types::HeapCellValueTag;

use std::cell::{Cell, Ref, RefCell, RefMut};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{Error as IOError, ErrorKind};
use std::ops::{Deref, Neg};
use std::rc::Rc;
use std::sync::Arc;
use std::vec::Vec;

use crate::parser::dashu::{Integer, Rational};

use fxhash::FxBuildHasher;
use indexmap::IndexMap;
use scryer_modular_bitfield::error::OutOfBounds;
use scryer_modular_bitfield::prelude::*;

pub type Specifier = u32;

pub const MAX_ARITY: usize = 1023;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum OpDeclSpec {
    XFX = 0x0001,
    XFY = 0x0002,
    YFX = 0x0004,
    XF = 0x0010,
    YF = 0x0020,
    FX = 0x0040,
    FY = 0x0080,
}

pub use OpDeclSpec::*;

impl OpDeclSpec {
    pub const fn value(self) -> u32 {
        self as u32
    }

    pub fn get_spec(self) -> Atom {
        match self {
            XFX => atom!("xfx"),
            XFY => atom!("xfy"),
            YFX => atom!("yfx"),
            FX => atom!("fx"),
            FY => atom!("fy"),
            XF => atom!("xf"),
            YF => atom!("yf"),
        }
    }

    pub const fn is_prefix(self) -> bool {
        matches!(self, Self::FX | Self::FY)
    }

    pub const fn is_postfix(self) -> bool {
        matches!(self, Self::XF | Self::YF)
    }

    pub const fn is_infix(self) -> bool {
        matches!(self, Self::XFX | Self::XFY | Self::YFX)
    }

    pub const fn is_strict_left(self) -> bool {
        matches!(self, Self::XFX | Self::XFY | Self::XF)
    }

    pub const fn is_strict_right(self) -> bool {
        matches!(self, Self::XFX | Self::YFX | Self::FX)
    }

    #[inline(always)]
    pub(crate) fn fixity(self) -> Fixity {
        match self {
            XFY | XFX | YFX => Fixity::In,
            XF | YF => Fixity::Post,
            FX | FY => Fixity::Pre,
        }
    }
}

impl From<OpDeclSpec> for u8 {
    fn from(value: OpDeclSpec) -> Self {
        value as u8
    }
}

impl From<OpDeclSpec> for u32 {
    fn from(value: OpDeclSpec) -> Self {
        value as u32
    }
}

impl TryFrom<u8> for OpDeclSpec {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Ok(match value {
            0x0001 => XFX,
            0x0002 => XFY,
            0x0004 => YFX,
            0x0010 => XF,
            0x0020 => YF,
            0x0040 => FX,
            0x0080 => FY,
            _ => return Err(()),
        })
    }
}

impl TryFrom<Atom> for OpDeclSpec {
    type Error = ();

    fn try_from(value: Atom) -> Result<Self, Self::Error> {
        Ok(match value {
            atom!("xfx") => Self::XFX,
            atom!("xfy") => Self::XFY,
            atom!("yfx") => Self::YFX,
            atom!("fx") => Self::FX,
            atom!("fy") => Self::FY,
            atom!("xf") => Self::XF,
            atom!("yf") => Self::YF,
            _ => return Err(()),
        })
    }
}

pub const DELIMITER: u32 = 0x0100;
pub const TERM: u32 = 0x1000;
pub const LTERM: u32 = 0x3000;
pub const BTERM: u32 = 0x11000;

pub const NEGATIVE_SIGN: u32 = 0x0200;

#[macro_export]
macro_rules! fixnum {
    ($wrapper:tt, $n:expr, $arena:expr) => {
        Fixnum::build_with_checked($n)
            .map(<$wrapper>::Fixnum)
            .unwrap_or_else(|_| <$wrapper>::Integer(arena_alloc!(Integer::from($n), $arena)))
    };
}

macro_rules! is_term {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::TERM) != 0 || is_negate!($x)
    };
}

macro_rules! is_lterm {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::LTERM) != 0 || is_negate!($x)
    };
}

macro_rules! is_op {
    ($x:expr) => {
        $x as u32
            & ($crate::parser::ast::XF as u32
                | $crate::parser::ast::YF as u32
                | $crate::parser::ast::FX as u32
                | $crate::parser::ast::FY as u32
                | $crate::parser::ast::XFX as u32
                | $crate::parser::ast::XFY as u32
                | $crate::parser::ast::YFX as u32)
            != 0
    };
}

macro_rules! is_negate {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::NEGATIVE_SIGN) != 0
    };
}

#[macro_export]
macro_rules! is_prefix {
    ($x:expr) => {
        $x as u32 & ($crate::parser::ast::FX as u32 | $crate::parser::ast::FY as u32) != 0
    };
}

#[macro_export]
macro_rules! is_postfix {
    ($x:expr) => {
        $x as u32 & ($crate::parser::ast::XF as u32 | $crate::parser::ast::YF as u32) != 0
    };
}

#[macro_export]
macro_rules! is_infix {
    ($x:expr) => {
        ($x as u32
            & ($crate::parser::ast::XFX as u32
                | $crate::parser::ast::XFY as u32
                | $crate::parser::ast::YFX as u32))
            != 0
    };
}

#[macro_export]
macro_rules! is_xfx {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::XFX as u32) != 0
    };
}

#[macro_export]
macro_rules! is_xfy {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::XFY as u32) != 0
    };
}

#[macro_export]
macro_rules! is_yfx {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::YFX as u32) != 0
    };
}
#[macro_export]
macro_rules! is_yf {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::YF as u32) != 0
    };
}

#[macro_export]
macro_rules! is_xf {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::XF as u32) != 0
    };
}

#[macro_export]
macro_rules! is_fx {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::FX as u32) != 0
    };
}

#[macro_export]
macro_rules! is_fy {
    ($x:expr) => {
        ($x as u32 & $crate::parser::ast::FY as u32) != 0
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RegType {
    Perm(usize),
    Temp(usize),
}

impl Default for RegType {
    fn default() -> Self {
        RegType::Temp(0)
    }
}

impl RegType {
    pub fn reg_num(self) -> usize {
        match self {
            RegType::Perm(reg_num) | RegType::Temp(reg_num) => reg_num,
        }
    }

    pub fn is_perm(self) -> bool {
        matches!(self, RegType::Perm(_))
    }
}

impl fmt::Display for RegType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RegType::Perm(val) => write!(f, "Y{}", val),
            RegType::Temp(val) => write!(f, "X{}", val),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VarReg {
    ArgAndNorm(RegType, usize),
    Norm(RegType),
}

impl VarReg {
    pub fn norm(self) -> RegType {
        match self {
            VarReg::ArgAndNorm(reg, _) | VarReg::Norm(reg) => reg,
        }
    }
}

impl fmt::Display for VarReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VarReg::Norm(RegType::Perm(reg)) => write!(f, "Y{}", reg),
            VarReg::Norm(RegType::Temp(reg)) => write!(f, "X{}", reg),
            VarReg::ArgAndNorm(RegType::Perm(reg), arg) => write!(f, "Y{} A{}", reg, arg),
            VarReg::ArgAndNorm(RegType::Temp(reg), arg) => write!(f, "X{} A{}", reg, arg),
        }
    }
}

impl Default for VarReg {
    fn default() -> Self {
        VarReg::Norm(RegType::default())
    }
}

#[macro_export]
macro_rules! temp_v {
    ($x:expr) => {
        $crate::parser::ast::RegType::Temp($x)
    };
}

#[macro_export]
macro_rules! perm_v {
    ($x:expr) => {
        $crate::parser::ast::RegType::Perm($x)
    };
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GenContext {
    Head,
    Mid(usize),
    Last(usize), // Mid & Last: chunk_num
}

impl GenContext {
    #[inline]
    pub fn chunk_num(self) -> usize {
        match self {
            GenContext::Head => 0,
            GenContext::Mid(cn) | GenContext::Last(cn) => cn,
        }
    }

    #[inline]
    pub fn is_last(self) -> bool {
        matches!(self, GenContext::Last(_))
    }
}

#[bitfield]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct OpDesc {
    prec: B11,
    spec: B8,
    #[allow(unused)]
    padding: B13,
}

impl OpDesc {
    #[inline]
    pub fn build_with(prec: u16, spec: OpDeclSpec) -> Self {
        OpDesc::new().with_spec(spec as u8).with_prec(prec)
    }

    #[inline]
    pub fn get(self) -> (u16, OpDeclSpec) {
        (self.prec(), self.get_spec())
    }

    pub fn set(&mut self, prec: u16, spec: OpDeclSpec) {
        self.set_prec(prec);
        self.set_spec(spec as u8);
    }

    #[inline]
    pub fn get_prec(self) -> u16 {
        self.prec()
    }

    #[inline]
    pub fn get_spec(self) -> OpDeclSpec {
        OpDeclSpec::try_from(self.spec()).expect("OpDecl always contains a valud OpDeclSpec")
    }

    #[inline]
    pub fn arity(self) -> usize {
        if !self.get_spec().is_infix() {
            1
        } else {
            2
        }
    }
}

// name and fixity -> operator type and precedence.
pub type OpDir = IndexMap<(Atom, Fixity), OpDesc, FxBuildHasher>;

#[derive(Debug, Default, Clone, Copy)]
pub struct MachineFlags {
    pub double_quotes: DoubleQuotes,
    pub unknown: Unknown,
}

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub enum DoubleQuotes {
    Atom,
    #[default]
    Chars,
    Codes,
}

impl DoubleQuotes {
    pub fn is_chars(self) -> bool {
        matches!(self, DoubleQuotes::Chars)
    }

    pub fn is_atom(self) -> bool {
        matches!(self, DoubleQuotes::Atom)
    }

    pub fn is_codes(self) -> bool {
        matches!(self, DoubleQuotes::Codes)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Unknown {
    #[default]
    Error,
    Fail,
    Warn,
}

impl Unknown {
    pub fn is_error(self) -> bool {
        matches!(self, Unknown::Error)
    }

    pub fn is_fail(self) -> bool {
        matches!(self, Unknown::Fail)
    }

    pub fn is_warn(self) -> bool {
        matches!(self, Unknown::Warn)
    }
}

pub fn default_op_dir() -> OpDir {
    let mut op_dir = OpDir::with_hasher(FxBuildHasher::default());

    op_dir.insert((atom!(":-"), Fixity::In), OpDesc::build_with(1200, XFX));
    op_dir.insert((atom!(":-"), Fixity::Pre), OpDesc::build_with(1200, FX));
    op_dir.insert((atom!("?-"), Fixity::Pre), OpDesc::build_with(1200, FX));
    op_dir.insert((atom!(","), Fixity::In), OpDesc::build_with(1000, XFY));

    op_dir
}

#[derive(Debug, Clone)]
pub enum ArithmeticError {
    NonEvaluableFunctor(Literal, usize),
    UninstantiatedVar,
}

#[derive(Debug)]
pub enum ParserError {
    BackQuotedString(usize, usize),
    IO(IOError),
    IncompleteReduction(usize, usize),
    InvalidSingleQuotedCharacter(char),
    LexicalError(lexical::Error),
    MissingQuote(usize, usize),
    NonPrologChar(usize, usize),
    ParseBigInt(usize, usize),
    UnexpectedChar(char, usize, usize),
    // UnexpectedEOF,
    Utf8Error(usize, usize),
}

impl ParserError {
    pub fn line_and_col_num(&self) -> Option<(usize, usize)> {
        match self {
            &ParserError::BackQuotedString(line_num, col_num)
            | &ParserError::IncompleteReduction(line_num, col_num)
            | &ParserError::MissingQuote(line_num, col_num)
            | &ParserError::NonPrologChar(line_num, col_num)
            | &ParserError::ParseBigInt(line_num, col_num)
            | &ParserError::UnexpectedChar(_, line_num, col_num)
            | &ParserError::Utf8Error(line_num, col_num) => Some((line_num, col_num)),
            _ => None,
        }
    }

    pub fn as_atom(&self) -> Atom {
        match self {
            ParserError::BackQuotedString(..) => atom!("back_quoted_string"),
            ParserError::IncompleteReduction(..) => atom!("incomplete_reduction"),
            ParserError::InvalidSingleQuotedCharacter(..) => {
                atom!("invalid_single_quoted_character")
            }
            ParserError::IO(e) if e.kind() == ErrorKind::UnexpectedEof => {
                atom!("unexpected_end_of_file")
            }
            ParserError::IO(e) if e.kind() == ErrorKind::InvalidData => {
                atom!("invalid_data")
            }
            ParserError::IO(_) => atom!("input_output_error"),
            ParserError::LexicalError(_) => atom!("lexical_error"),
            ParserError::MissingQuote(..) => atom!("missing_quote"),
            ParserError::NonPrologChar(..) => atom!("non_prolog_character"),
            ParserError::ParseBigInt(..) => atom!("cannot_parse_big_int"),
            ParserError::UnexpectedChar(..) => atom!("unexpected_char"),
            ParserError::Utf8Error(..) => atom!("utf8_conversion_error"),
        }
    }

    #[inline]
    pub fn unexpected_eof() -> Self {
        ParserError::IO(std::io::Error::from(ErrorKind::UnexpectedEof))
    }

    #[inline]
    pub fn is_unexpected_eof(&self) -> bool {
        if let ParserError::IO(e) = self {
            e.kind() == ErrorKind::UnexpectedEof
        } else {
            false
        }
    }
}

impl From<lexical::Error> for ParserError {
    fn from(e: lexical::Error) -> ParserError {
        ParserError::LexicalError(e)
    }
}

impl From<IOError> for ParserError {
    fn from(e: IOError) -> ParserError {
        ParserError::IO(e)
    }
}

impl From<&IOError> for ParserError {
    fn from(error: &IOError) -> ParserError {
        if error.get_ref().filter(|e| e.is::<BadUtf8Error>()).is_some() {
            ParserError::Utf8Error(0, 0)
        } else {
            ParserError::IO(error.kind().into())
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CompositeOpDir<'a, 'b> {
    pub primary_op_dir: Option<&'b OpDir>,
    pub secondary_op_dir: &'a OpDir,
}

impl<'a, 'b> CompositeOpDir<'a, 'b> {
    #[inline]
    pub fn new(secondary_op_dir: &'a OpDir, primary_op_dir: Option<&'b OpDir>) -> Self {
        CompositeOpDir {
            primary_op_dir,
            secondary_op_dir,
        }
    }

    #[inline]
    pub(crate) fn get(&self, name: Atom, fixity: Fixity) -> Option<OpDesc> {
        let entry = if let Some(primary_op_dir) = &self.primary_op_dir {
            primary_op_dir.get(&(name, fixity))
        } else {
            None
        };

        entry
            .or_else(move || self.secondary_op_dir.get(&(name, fixity)))
            .cloned()
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum Fixity {
    In,
    Post,
    Pre,
}

#[bitfield]
#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Fixnum {
    num: B56,
    #[allow(unused)]
    f: bool,
    #[allow(unused)]
    m: bool,
    #[allow(unused)]
    tag: B6,
}

impl Fixnum {
    #[inline]
    pub fn build_with(num: i64) -> Self {
        Fixnum::new()
            .with_num(u64::from_ne_bytes(num.to_ne_bytes()) & ((1 << 56) - 1))
            .with_tag(HeapCellValueTag::Fixnum as u8)
            .with_m(false)
            .with_f(false)
    }

    #[inline]
    pub fn as_cutpoint(num: i64) -> Self {
        Fixnum::new()
            .with_num(u64::from_ne_bytes(num.to_ne_bytes()) & ((1 << 56) - 1))
            .with_tag(HeapCellValueTag::CutPoint as u8)
            .with_m(false)
            .with_f(false)
    }

    #[inline]
    pub fn get_tag(&self) -> HeapCellValueTag {
        use scryer_modular_bitfield::Specifier;
        HeapCellValueTag::from_bytes(self.tag()).unwrap()
    }

    #[inline]
    pub fn build_with_checked(num: i64) -> Result<Self, OutOfBounds> {
        const UPPER_BOUND: i64 = (1 << 55) - 1;
        const LOWER_BOUND: i64 = -(1 << 55);

        if (LOWER_BOUND..=UPPER_BOUND).contains(&num) {
            Ok(Fixnum::new()
                .with_m(false)
                .with_f(false)
                .with_tag(HeapCellValueTag::Fixnum as u8)
                .with_num(u64::from_ne_bytes(num.to_ne_bytes()) & ((1 << 56) - 1)))
        } else {
            Err(OutOfBounds {})
        }
    }

    #[inline]
    pub fn get_num(self) -> i64 {
        let n = self.num() as i64;
        let (n, overflowed) = (n << 8).overflowing_shr(8);
        debug_assert!(!overflowed);
        n
    }
}

impl Neg for Fixnum {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Fixnum::build_with(-self.get_num())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Atom(Atom),
    Char(char),
    CodeIndex(CodeIndex),
    Fixnum(Fixnum),
    Integer(TypedArenaPtr<Integer>),
    Rational(TypedArenaPtr<Rational>),
    Float(F64Offset),
    String(Atom),
}

impl From<F64Ptr> for Literal {
    #[inline(always)]
    fn from(ptr: F64Ptr) -> Literal {
        Literal::Float(ptr.as_offset())
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Atom(ref atom) => {
                write!(f, "{}", atom.flat_index())
            }
            Literal::Char(c) => write!(f, "'{}'", *c as u32),
            Literal::CodeIndex(i) => write!(f, "{:x}", i.as_ptr() as u64),
            Literal::Fixnum(n) => write!(f, "{}", n.get_num()),
            Literal::Integer(ref n) => write!(f, "{}", n),
            Literal::Rational(ref n) => write!(f, "{}", n),
            Literal::Float(ref n) => write!(f, "{}", *n),
            Literal::String(ref s) => write!(f, "\"{}\"", s.as_str()),
        }
    }
}

impl Literal {
    pub fn to_atom(&self, atom_tbl: &Arc<AtomTable>) -> Option<Atom> {
        match self {
            Literal::Atom(atom) => Some(atom.defrock_brackets(atom_tbl)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarPtr(Rc<RefCell<Var>>);

impl Hash for VarPtr {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.borrow().hash(hasher)
    }
}

impl Deref for VarPtr {
    type Target = RefCell<Var>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl VarPtr {
    #[inline(always)]
    pub(crate) fn borrow(&self) -> Ref<'_, Var> {
        self.0.borrow()
    }

    #[inline(always)]
    pub(crate) fn borrow_mut(&self) -> RefMut<'_, Var> {
        self.0.borrow_mut()
    }

    pub(crate) fn to_var_num(&self) -> Option<usize> {
        match *self.borrow() {
            Var::Generated(var_num) => Some(var_num),
            _ => None,
        }
    }

    pub(crate) fn set(&self, var: Var) {
        let mut var_ref = self.borrow_mut();
        *var_ref = var;
    }
}

impl From<Var> for VarPtr {
    #[inline(always)]
    fn from(value: Var) -> VarPtr {
        VarPtr(Rc::new(RefCell::new(value)))
    }
}

impl From<String> for VarPtr {
    #[inline(always)]
    fn from(value: String) -> VarPtr {
        VarPtr::from(Var::from(value))
    }
}

impl From<&str> for VarPtr {
    #[inline(always)]
    fn from(value: &str) -> VarPtr {
        VarPtr::from(value.to_owned())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Var {
    Generated(usize),
    InSitu(usize),
    Named(String),
}

impl From<String> for Var {
    #[inline(always)]
    fn from(value: String) -> Var {
        Var::Named(value)
    }
}

impl From<&str> for Var {
    #[inline(always)]
    fn from(value: &str) -> Var {
        Var::Named(value.to_owned())
    }
}

impl Var {
    #[inline(always)]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Var::Named(value) => Some(value),
            _ => None,
        }
    }

    #[allow(clippy::inherent_to_string)]
    #[inline(always)]
    pub fn to_string(&self) -> String {
        match self {
            Var::InSitu(n) | Var::Generated(n) => format!("_{}", n),
            Var::Named(value) => value.to_owned(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    AnonVar,
    Clause(Cell<RegType>, Atom, Vec<Term>),
    Cons(Cell<RegType>, Box<Term>, Box<Term>),
    Literal(Cell<RegType>, Literal),
    // PartialString wraps a String in anticipation of it absorbing
    // other PartialString variants in as_partial_string.
    PartialString(Cell<RegType>, String, Box<Term>),
    CompleteString(Cell<RegType>, Atom),
    Var(Cell<VarReg>, VarPtr),
}

impl Term {
    pub fn into_literal(self) -> Option<Literal> {
        match self {
            Term::Literal(_, c) => Some(c),
            _ => None,
        }
    }

    pub fn first_arg(&self) -> Option<&Term> {
        match self {
            Term::Clause(_, _, ref terms) => terms.first(),
            _ => None,
        }
    }

    pub fn set_name(&mut self, new_name: Atom) {
        match self {
            Term::Literal(_, Literal::Atom(ref mut atom)) | Term::Clause(_, ref mut atom, ..) => {
                *atom = new_name;
            }
            _ => {}
        }
    }

    pub fn name(&self) -> Option<Atom> {
        match self {
            &Term::Literal(_, Literal::Atom(ref atom)) | &Term::Clause(_, ref atom, ..) => {
                Some(*atom)
            }
            _ => None,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Term::Clause(_, _, ref child_terms, ..) => child_terms.len(),
            _ => 0,
        }
    }
}

#[inline]
pub fn source_arity(terms: &[Term]) -> usize {
    if let Some(Term::Literal(_, Literal::CodeIndex(_))) = terms.last() {
        return terms.len() - 1;
    }

    terms.len()
}

pub(crate) fn unfold_by_str_once(term: &mut Term, s: Atom) -> Option<(Term, Term)> {
    if let Term::Clause(_, ref name, ref mut subterms) = term {
        if let Some(Term::Literal(_, Literal::CodeIndex(_))) = subterms.last() {
            subterms.pop();
        }

        if name == &s && subterms.len() == 2 {
            let snd = subterms.pop().unwrap();
            let fst = subterms.pop().unwrap();

            return Some((fst, snd));
        }
    }

    None
}

pub fn unfold_by_str(mut term: Term, s: Atom) -> Vec<Term> {
    let mut terms = vec![];

    while let Some((fst, snd)) = unfold_by_str_once(&mut term, s) {
        terms.push(fst);
        term = snd;
    }

    terms.push(term);
    terms
}
