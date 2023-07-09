use crate::forms::*;
use crate::machine::*;
use crate::machine::load_state::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::*;
use crate::parser::ast::*;
use crate::parser::parser::*;
use crate::read::devour_whitespace;

use crate::predicate_queue;

use indexmap::IndexSet;

use std::collections::VecDeque;
use std::fmt;

pub struct LoadStatePayload<TS> {
    pub term_stream: TS,
    pub(super) compilation_target: CompilationTarget,
    pub(super) retraction_info: RetractionInfo,
    pub(super) module_op_exports: ModuleOpExports,
    pub(super) non_counted_bt_preds: IndexSet<PredicateKey>,
    pub(super) predicates: PredicateQueue,
    pub(super) clause_clauses: Vec<(Term, Term)>,
}

pub trait TermStream: Sized {
    fn next(&mut self, op_dir: &CompositeOpDir) -> Result<Term, CompilationError>;
    fn eof(&mut self) -> Result<bool, CompilationError>;
    fn listing_src(&self) -> &ListingSource;
}

#[derive(Debug)]
pub struct BootstrappingTermStream<'a> {
    listing_src: ListingSource,
    pub(super) parser: Parser<'a, Stream>,
}

impl<'a> BootstrappingTermStream<'a> {
    #[inline]
    pub(super) fn from_char_reader(
        stream: Stream,
        machine_st: &'a mut MachineState,
        listing_src: ListingSource,
    ) -> Self {
        let parser = Parser::new(stream, machine_st);
        Self { parser, listing_src }
    }
}

impl<'a> TermStream for BootstrappingTermStream<'a> {
    #[inline]
    fn next(&mut self, op_dir: &CompositeOpDir) -> Result<Term, CompilationError> {
        self.parser.reset();
        self.parser
            .read_term(op_dir, Tokens::Default)
            .map_err(CompilationError::from)
    }

    #[inline]
    fn eof(&mut self) -> Result<bool, CompilationError> {
        devour_whitespace(&mut self.parser) // eliminate dangling comments before checking for EOF.
            .map_err(CompilationError::from)
    }

    #[inline]
    fn listing_src(&self) -> &ListingSource {
        &self.listing_src
    }
}

pub struct LiveTermStream {
    pub(super) term_queue: VecDeque<Term>,
    pub(super) listing_src: ListingSource,
}

impl LiveTermStream {
    #[inline]
    pub(super) fn new(listing_src: ListingSource) -> Self {
        Self {
            term_queue: VecDeque::new(),
            listing_src,
        }
    }
}

impl<TS> fmt::Debug for LoadStatePayload<TS> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "LoadStatePayload")
    }
}

impl<TS> LoadStatePayload<TS> {
    pub(super) fn new(code_repo_len: usize, term_stream: TS) -> Self {
        Self {
            term_stream,
            compilation_target: CompilationTarget::default(),
            retraction_info: RetractionInfo::new(code_repo_len),
            module_op_exports: vec![],
            non_counted_bt_preds: IndexSet::new(),
            predicates: predicate_queue![],
            clause_clauses: vec![],
        }
    }
}

impl TermStream for LiveTermStream {
    #[inline]
    fn next(&mut self, _: &CompositeOpDir) -> Result<Term, CompilationError> {
        Ok(self.term_queue.pop_front().unwrap())
    }

    #[inline]
    fn eof(&mut self) -> Result<bool, CompilationError> {
        Ok(self.term_queue.is_empty())
    }

    #[inline]
    fn listing_src(&self) -> &ListingSource {
        &self.listing_src
    }
}

pub struct InlineTermStream {
}

impl TermStream for InlineTermStream {
    fn next(&mut self, _: &CompositeOpDir) -> Result<Term, CompilationError> {
	    Err(CompilationError::from(ParserError::unexpected_eof()))
    }

    fn eof(&mut self) -> Result<bool, CompilationError> {
	    Ok(true)
    }

    fn listing_src(&self) -> &ListingSource {
	    &ListingSource::User
    }
}

