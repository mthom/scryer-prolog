use crate::prolog_parser::ast::*;
use crate::prolog_parser::parser::*;

use crate::machine::*;
use crate::machine::machine_errors::CompilationError;
use crate::machine::preprocessor::*;

use indexmap::IndexSet;

use std::collections::VecDeque;
use std::fmt;

pub(crate) trait TermStream : Sized {
    type Evacuable;

    fn next(&mut self, op_dir: &CompositeOpDir) -> Result<Term, CompilationError>;
    fn eof(&mut self) -> Result<bool, CompilationError>;
    fn listing_src(&self) -> &ListingSource;
    fn evacuate<'a>(loader: Loader<'a, Self>) -> Result<Self::Evacuable, SessionError>;
}

#[derive(Debug)]
pub(super) struct BootstrappingTermStream<'a> {
    listing_src: ListingSource,
    parser: Parser<'a, Stream>,
}

impl<'a> BootstrappingTermStream<'a> {
    #[inline]
    pub(super)
    fn from_prolog_stream(
        stream: &'a mut PrologStream,
        atom_tbl: TabledData<Atom>,
        flags: MachineFlags,
        listing_src: ListingSource,
    ) -> Self {
        let parser = Parser::new(stream, atom_tbl, flags);
        Self { parser, listing_src }
    }
}

impl<'a> TermStream for BootstrappingTermStream<'a> {
    type Evacuable = CompilationTarget;

    #[inline]
    fn next(&mut self, op_dir: &CompositeOpDir) -> Result<Term, CompilationError> {
        self.parser.reset();
        self.parser.read_term(op_dir)
            .map_err(CompilationError::from)
    }

    #[inline]
    fn eof(&mut self) -> Result<bool, CompilationError> {
	    self.parser.devour_whitespace()?; // eliminate dangling comments before checking for EOF.
        Ok(self.parser.eof()?)
    }

    #[inline]
    fn listing_src(&self) -> &ListingSource {
        &self.listing_src
    }

    fn evacuate(mut loader: Loader<Self>) -> Result<Self::Evacuable, SessionError> {
        if !loader.predicates.is_empty() {
            loader.compile_and_submit()?;
        }

        loader.load_state.retraction_info.reset(
            loader.load_state.wam.code_repo.code.len(),
        );

        loader.load_state.remove_module_op_exports();

        Ok(loader.load_state.compilation_target.take())
    }
}

pub struct LiveTermStream {
    pub(super) term_queue: VecDeque<Term>,
    pub(super) listing_src: ListingSource,
}

impl LiveTermStream {
    #[inline]
    pub(super)
    fn new(listing_src: ListingSource) -> Self {
        Self {
            term_queue: VecDeque::new(),
            listing_src,
        }
    }
}

pub struct LoadStatePayload {
    pub(super) term_stream: LiveTermStream,
    pub(super) compilation_target: CompilationTarget,
    pub(super) retraction_info: RetractionInfo,
    pub(super) module_op_exports: Vec<(OpDecl, Option<(usize, Specifier)>)>,
    pub(super) non_counted_bt_preds: IndexSet<PredicateKey>,
    pub(super) preprocessor: Preprocessor,
    pub(super) predicates: Vec<PredicateClause>,
    pub(super) clause_clauses: Vec<(Term, Term)>,
}

impl fmt::Debug for LoadStatePayload {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "LoadStatePayload")
    }
}

impl LoadStatePayload {
    pub(super)
    fn new(wam: &Machine) -> Self {
        Self {
            term_stream: LiveTermStream::new(ListingSource::User),
            compilation_target: CompilationTarget::default(),
            retraction_info: RetractionInfo::new(wam.code_repo.code.len()),
            module_op_exports: vec![],
            non_counted_bt_preds: IndexSet::new(),
            preprocessor: Preprocessor::new(wam.machine_st.flags),
            predicates: vec![],
            clause_clauses: vec![],
        }
    }
}

impl TermStream for LiveTermStream {
    type Evacuable = LoadStatePayload;

    #[inline]
    fn next(&mut self, _: &CompositeOpDir) -> Result<Term, CompilationError> {
        Ok(self.term_queue.pop_front().unwrap())
    }

    #[inline]
    fn eof(&mut self) -> Result<bool, CompilationError> {
        return Ok(self.term_queue.is_empty());
    }

    #[inline]
    fn listing_src(&self) -> &ListingSource {
        &self.listing_src
    }

    #[inline]
    fn evacuate(loader: Loader<Self>) -> Result<LoadStatePayload, SessionError> {
        Ok(loader.to_load_state_payload())
    }
}
