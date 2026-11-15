#[cfg(feature = "repl")]
pub mod fallback_mode;
#[cfg(feature = "repl")]
pub mod user_interaction;

use crate::parser::ast::*;
use crate::parser::lexer::Lexer;
use crate::parser::parser::*;

use crate::arena::opt_in_buf_reader::*;
use crate::arena::stream_layout::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::iterators::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::MachineState;
use crate::types::*;

use fxhash::FxBuildHasher;

use std::collections::VecDeque;

type SubtermDeque = VecDeque<(usize, usize)>;

pub(crate) fn devour_whitespace<R: GraphemeRead>(
    lexer: &mut Lexer<'_, R>,
) -> Result<bool, ParserError> {
    match lexer.scan_for_layout() {
        Err(e) if e.is_unexpected_eof() => Ok(true),
        Err(e) => Err(e),
        Ok(_) => Ok(false),
    }
}

pub(crate) fn error_after_read_term<R>(
    err: ParserError,
    prior_num_lines_read: usize,
    parser: &Parser<R>,
) -> CompilationError {
    if err.is_unexpected_eof() {
        let location = &parser.lexer.location;

        // rough overlap with errors 8.14.1.3 k) & l) of the ISO standard here.
        // End of stream after nothing but layout text (e.g. a final clause followed by a
        // newline and trailing spaces) is a genuine end of file, not an incomplete term.
        if !parser.lexer.eof_at_token_start
            && !(location.line() == prior_num_lines_read && location.column() == 0)
        {
            return CompilationError::from(parser.lexer.incomplete_reduction());
        }
    }

    CompilationError::from(err)
}

impl MachineState {
    pub(crate) fn read(
        &mut self,
        mut inner: Stream,
        op_dir: &OpDir,
    ) -> Result<TermWriteResult, CompilationError> {
        let (term, num_lines_read) = {
            let prior_num_lines_read = inner.lines_read;
            let mut parser = Parser::new(inner, self);
            let op_dir = CompositeOpDir::new(op_dir, None);

            parser.add_lines_read(prior_num_lines_read);

            let term = parser
                .read_term(&op_dir, Tokens::Default)
                .map_err(|err| error_after_read_term(err, prior_num_lines_read, &parser))?;

            (term, parser.lines_read() - prior_num_lines_read)
        };

        inner.lines_read += num_lines_read;
        write_term_to_heap(&term, &mut self.heap)
    }
}

#[inline]
pub(crate) fn write_term_to_heap(
    term: &Term,
    heap: &mut Heap,
) -> Result<TermWriteResult, CompilationError> {
    let term_writer = TermWriter::new(heap);
    term_writer.write_term_to_heap(term)
}

#[derive(Debug)]
struct TermWriter<'a> {
    heap: &'a mut Heap,
    queue: SubtermDeque,
    var_dict: HeapVarDict,
}

#[derive(Debug)]
pub struct TermWriteResult {
    pub heap_loc: usize,
    pub var_dict: HeapVarDict,
}

impl<'a> TermWriter<'a> {
    #[inline]
    fn new(heap: &'a mut Heap) -> Self {
        TermWriter {
            heap,
            queue: SubtermDeque::new(),
            var_dict: HeapVarDict::with_hasher(FxBuildHasher::default()),
        }
    }

    #[inline]
    fn modify_head_of_queue(&mut self, term: &TermRef, h: usize) {
        if let Some((arity, site_h)) = self.queue.pop_front() {
            self.heap[site_h] = self.term_as_addr(term, h);

            if arity > 1 {
                self.queue.push_front((arity - 1, site_h + 1));
            }
        }
    }

    #[inline]
    fn push_stub_addr(&mut self) -> Result<(), CompilationError> {
        let h = self.heap.cell_len();
        self.push_cell(heap_loc_as_cell!(h))
    }

    #[inline]
    fn push_cell(&mut self, cell: HeapCellValue) -> Result<(), CompilationError> {
        Ok(self.heap.push_cell(cell)?)
    }

    fn term_as_addr(&mut self, term: &TermRef, h: usize) -> HeapCellValue {
        match term {
            &TermRef::Cons(..) => list_loc_as_cell!(h),
            &TermRef::AnonVar(_) | &TermRef::Var(..) => heap_loc_as_cell!(h),
            TermRef::PartialString(..) | TermRef::CompleteString(..) => heap_loc_as_cell!(h),
            &TermRef::Literal(_, _, literal) => HeapCellValue::from(*literal),
            &TermRef::Clause(_, _, _, subterms) if subterms.is_empty() => heap_loc_as_cell!(h),
            &TermRef::Clause(..) => str_loc_as_cell!(h),
            &TermRef::Stream(_, _, stream) => HeapCellValue::from(stream),
            &TermRef::Process(_, _, process) => HeapCellValue::from(process),
        }
    }

    fn write_term_to_heap(mut self, term: &Term) -> Result<TermWriteResult, CompilationError> {
        let heap_loc = self.heap.cell_len();

        for term in breadth_first_iter(term, RootIterationPolicy::Iterated) {
            let h = self.heap.cell_len();

            match &term {
                &TermRef::Cons(Level::Root, ..) => {
                    self.queue.push_back((2, h + 1));
                    self.push_cell(list_loc_as_cell!(h + 1))?;

                    self.push_stub_addr()?;
                    self.push_stub_addr()?;

                    continue;
                }
                &TermRef::Cons(..) => {
                    self.queue.push_back((2, h));

                    self.push_stub_addr()?;
                    self.push_stub_addr()?;
                }
                &TermRef::Clause(Level::Root, _, name, subterms) => {
                    if subterms.len() > MAX_ARITY {
                        return Err(CompilationError::ExceededMaxArity);
                    }

                    self.push_cell(if subterms.is_empty() {
                        heap_loc_as_cell!(heap_loc + 1)
                    } else {
                        str_loc_as_cell!(heap_loc + 1)
                    })?;

                    self.queue.push_back((subterms.len(), h + 2));
                    let named = atom_as_cell!(name, subterms.len());

                    self.push_cell(named)?;

                    for _ in 0..subterms.len() {
                        self.push_stub_addr()?;
                    }

                    continue;
                }
                &TermRef::Clause(_, _, name, subterms) => {
                    self.queue.push_back((subterms.len(), h + 1));
                    let named = atom_as_cell!(name, subterms.len());

                    self.push_cell(named)?;

                    for _ in 0..subterms.len() {
                        self.push_stub_addr()?;
                    }
                }
                &TermRef::AnonVar(Level::Root) | TermRef::Literal(Level::Root, ..) => {
                    let addr = self.term_as_addr(&term, h);
                    self.push_cell(addr)?;
                }
                &TermRef::Var(Level::Root, _, ref var_ptr) => {
                    let addr = self.term_as_addr(&term, h);
                    self.var_dict.insert(VarKey::VarPtr(var_ptr.clone()), addr);
                    self.push_cell(addr)?;
                }
                &TermRef::AnonVar(_) => {
                    if let Some((arity, site_h)) = self.queue.pop_front() {
                        self.var_dict
                            .insert(VarKey::AnonVar(h), heap_loc_as_cell!(site_h));

                        if arity > 1 {
                            self.queue.push_front((arity - 1, site_h + 1));
                        }
                    }

                    continue;
                }
                TermRef::CompleteString(lvl, _, src) => {
                    if let Level::Root = lvl {
                        self.push_stub_addr()?;
                    }

                    let cell = self.heap.allocate_cstr(src.as_bytes())?;

                    let new_h = self.heap.cell_len();
                    self.push_cell(cell)?;

                    if !matches!(lvl, Level::Root) {
                        self.modify_head_of_queue(&term, new_h);
                    } else {
                        self.heap[h] = cell;
                    }

                    continue;
                }
                TermRef::PartialString(lvl, _, src, _) => {
                    if let Level::Root = lvl {
                        self.push_stub_addr()?;
                    }

                    let cell = self.heap.allocate_pstr(src.as_bytes())?;

                    let tail_h = self.heap.cell_len();
                    self.push_stub_addr()?;

                    if matches!(lvl, Level::Root) {
                        self.heap[h] = cell;
                    } else {
                        self.push_cell(cell)?;
                    };

                    self.queue.push_back((1, tail_h));

                    if !matches!(lvl, Level::Root) {
                        self.modify_head_of_queue(&term, tail_h + 1);
                    }

                    continue;
                }
                TermRef::Var(.., var) => {
                    if let Some((arity, site_h)) = self.queue.pop_front() {
                        let var_key = VarKey::VarPtr(var.clone());

                        if let Some(addr) = self.var_dict.get(&var_key).cloned() {
                            self.heap[site_h] = addr;
                        } else {
                            self.var_dict.insert(var_key, heap_loc_as_cell!(site_h));
                        }

                        if arity > 1 {
                            self.queue.push_front((arity - 1, site_h + 1));
                        }
                    }

                    continue;
                }
                _ => {}
            };

            self.modify_head_of_queue(&term, h);
        }

        Ok(TermWriteResult {
            heap_loc,
            var_dict: self.var_dict,
        })
    }
}
