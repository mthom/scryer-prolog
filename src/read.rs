use crate::parser::ast::*;
use crate::parser::parser::*;

use crate::atom_table::*;
use crate::forms::*;
use crate::iterators::*;
use crate::machine::heap::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::machine_state::MachineState;
use crate::machine::streams::*;
use crate::parser::char_reader::*;
use crate::repl_helper::Helper;
use crate::types::*;

use fxhash::FxBuildHasher;

use indexmap::IndexSet;
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{Config, Editor};

use std::collections::VecDeque;
use std::io::{Cursor, Error, ErrorKind, Read};

type SubtermDeque = VecDeque<(usize, usize)>;

pub(crate) fn devour_whitespace<'a, R: CharRead>(parser: &mut Parser<'a, R>) -> Result<bool, ParserError> {
    match parser.lexer.scan_for_layout() {
        Err(e) if e.is_unexpected_eof() => {
            Ok(true)
        }
        Err(e) => Err(e),
        Ok(_) => {
            Ok(false)
        }
    }
}

pub(crate) fn error_after_read_term<R>(
    err: ParserError,
    prior_num_lines_read: usize,
    parser: &Parser<R>,
) -> CompilationError {
    if err.is_unexpected_eof() {
        let line_num = parser.lexer.line_num;
        let col_num = parser.lexer.col_num;

        // rough overlap with errors 8.14.1.3 k) & l) of the ISO standard here
        if !(line_num == prior_num_lines_read && col_num == 0) {
            return CompilationError::from(ParserError::IncompleteReduction(line_num, col_num));
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
            let prior_num_lines_read = inner.lines_read();
            let mut parser = Parser::new(inner, self);
            let op_dir = CompositeOpDir::new(op_dir, None);

            parser.add_lines_read(prior_num_lines_read);

            let term = parser.read_term(&op_dir, Tokens::Default)
                .map_err(|err| error_after_read_term(err, prior_num_lines_read, &parser))?; // CompilationError::from

            (term, parser.lines_read() - prior_num_lines_read)
        };

        inner.add_lines_read(num_lines_read);
        write_term_to_heap(&term, &mut self.heap, &mut self.atom_tbl)
    }
}

static mut PROMPT: bool = false;
static mut EMIT_NEWLINE: bool = false;

const HISTORY_FILE: &'static str = ".scryer_history";

pub(crate) fn set_emit_newline(value: bool) {
    unsafe {
        EMIT_NEWLINE = value;
    }
}

pub(crate) fn set_prompt(value: bool) {
    unsafe {
        PROMPT = value;
    }
}

#[inline]
fn get_prompt() -> &'static str {
    unsafe {
        if PROMPT {
            "?- "
        } else {
            ""
        }
    }
}

#[derive(Debug)]
pub struct ReadlineStream {
    rl: Editor<Helper, DefaultHistory>,
    pending_input: CharReader<Cursor<String>>,
    add_history: bool,
}

impl ReadlineStream {
    #[inline]
    pub fn new(pending_input: &str, add_history: bool) -> Self {
        let config = Config::builder()
            .check_cursor_position(true)
            .build();

        let helper = Helper::new();

        let mut rl = Editor::with_config(config).unwrap();
        rl.set_helper(Some(helper));

        if let Some(mut path) = dirs_next::home_dir() {
            path.push(HISTORY_FILE);
            if path.exists() && rl.load_history(&path).is_err() {
                println!("Warning: loading history failed");
            }
        }

        ReadlineStream {
            rl,
            pending_input: CharReader::new(Cursor::new(pending_input.to_owned())),
            add_history: add_history,
        }
    }

    pub fn set_atoms_for_completion(&mut self, atoms: *const IndexSet<Atom>) {
        let helper = self.rl.helper_mut().unwrap();
        helper.atoms = atoms;
    }

    #[inline]
    pub fn reset(&mut self) {
        self.pending_input.reset_buffer();

        let pending_input = self.pending_input.get_mut();

        pending_input.get_mut().clear();
        pending_input.set_position(0);
    }

    fn call_readline(&mut self) -> std::io::Result<usize> {
        match self.rl.readline(get_prompt()) {
            Ok(text) => {
                self.pending_input.reset_buffer();

                *self.pending_input.get_mut().get_mut() = text;
                self.pending_input.get_mut().set_position(0);

                unsafe {
                    if PROMPT {
                        self.rl.add_history_entry(self.pending_input.get_ref().get_ref()).unwrap();
                        self.save_history();
                        PROMPT = false;
                    }

                    if EMIT_NEWLINE {
                        if self.pending_input.get_ref().get_ref().chars().last() != Some('\n') {
                            *self.pending_input.get_mut().get_mut() += "\n";
                        }
                    }
                }

                Ok(self.pending_input.get_ref().get_ref().len())
            }
            Err(ReadlineError::Eof) => Err(Error::from(ErrorKind::UnexpectedEof)),
            Err(e) => Err(Error::new(ErrorKind::InvalidInput, e)),
        }
    }

    fn save_history(&mut self) {
        if !self.add_history {
            return;
        };
        if let Some(mut path) = dirs_next::home_dir() {
            path.push(HISTORY_FILE);
            if path.exists() {
                if self.rl.append_history(&path).is_err() {
                    println!("Warning: couldn't append history (existing file)");
                }
            } else if self.rl.save_history(&path).is_err() {
                println!("Warning: couldn't save history (new file)");
            }
        }
    }

    #[inline]
    pub(crate) fn peek_byte(&mut self) -> std::io::Result<u8> {
        let bytes = self.pending_input.refresh_buffer()?;
        let byte = bytes.iter().next().cloned();

        loop {
            match byte {
                Some(b) => {
                    return Ok(b);
                }
                None => match self.call_readline() {
                    Err(e) => {
                        return Err(e);
                    }
                    _ => {
                        set_prompt(false);
                    }
                },
            }
        }
    }
}

impl Read for ReadlineStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self.pending_input.read(buf) {
            Ok(0) => {
                self.call_readline()?;
                self.pending_input.read(buf)
            }
            result => result
        }
    }
}

impl CharRead for ReadlineStream {
    #[inline]
    fn peek_char(&mut self) -> Option<std::io::Result<char>> {
        loop {
            match self.pending_input.peek_char() {
                Some(Ok(c)) => {
                    return Some(Ok(c));
                }
                _ => {
                    match self.call_readline() {
                        Err(e) => {
                            return Some(Err(e));
                        }
                        _ => {
                            set_prompt(false);
                        }
                    }
                }
            }
        }
    }

    #[inline]
    fn consume(&mut self, nread: usize) {
        self.pending_input.consume(nread);
    }

    #[inline]
    fn put_back_char(&mut self, c: char) {
        self.pending_input.put_back_char(c);
    }
}

#[inline]
pub(crate) fn write_term_to_heap<'a, 'b>(
    term: &'a Term,
    heap: &'b mut Heap,
    atom_tbl: &mut AtomTable,
) -> Result<TermWriteResult, CompilationError> {
    let term_writer = TermWriter::new(heap, atom_tbl);
    term_writer.write_term_to_heap(term)
}

#[derive(Debug)]
struct TermWriter<'a, 'b> {
    heap: &'a mut Heap,
    atom_tbl: &'b mut AtomTable,
    queue: SubtermDeque,
    var_dict: HeapVarDict,
}

#[derive(Debug)]
pub struct TermWriteResult {
    pub heap_loc: usize,
    pub var_dict: HeapVarDict,
}

impl<'a, 'b> TermWriter<'a, 'b> {
    #[inline]
    fn new(heap: &'a mut Heap, atom_tbl: &'b mut AtomTable) -> Self {
        TermWriter {
            heap,
            atom_tbl,
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
    fn push_stub_addr(&mut self) {
        let h = self.heap.len();
        self.heap.push(heap_loc_as_cell!(h));
    }

    fn term_as_addr(&mut self, term: &TermRef, h: usize) -> HeapCellValue {
        match term {
            &TermRef::Cons(..) => list_loc_as_cell!(h),
            &TermRef::AnonVar(_) | &TermRef::Var(..) => heap_loc_as_cell!(h),
            &TermRef::CompleteString(_, _, ref src) =>
                if src.as_str().is_empty() {
                    empty_list_as_cell!()
                } else if self.heap[h].get_tag() == HeapCellValueTag::CStr {
                    heap_loc_as_cell!(h)
                } else {
                    pstr_loc_as_cell!(h)
                },
            &TermRef::PartialString(..) => pstr_loc_as_cell!(h),
            &TermRef::Literal(_, _, literal) => HeapCellValue::from(*literal),
            &TermRef::Clause(_,_,_,subterms) if subterms.len() == 0 => heap_loc_as_cell!(h),
            &TermRef::Clause(..) => str_loc_as_cell!(h),
        }
    }

    fn write_term_to_heap(mut self, term: &Term) -> Result<TermWriteResult, CompilationError> {
        let heap_loc = self.heap.len();

        for term in breadth_first_iter(term, RootIterationPolicy::Iterated) {
            let h = self.heap.len();

            match &term {
                &TermRef::Cons(Level::Root, ..) => {
                    self.queue.push_back((2, h + 1));
                    self.heap.push(list_loc_as_cell!(h + 1));

                    self.push_stub_addr();
                    self.push_stub_addr();

                    continue;
                }
                &TermRef::Cons(..) => {
                    self.queue.push_back((2, h));

                    self.push_stub_addr();
                    self.push_stub_addr();
                }
                &TermRef::Clause(Level::Root, _, name, subterms) => {
                    if subterms.len() > MAX_ARITY {
                        return Err(CompilationError::ExceededMaxArity);
                    }

                    self.heap.push(if subterms.len() == 0 {
                        heap_loc_as_cell!(heap_loc + 1)
                    } else {
                        str_loc_as_cell!(heap_loc + 1)
                    });

                    self.queue.push_back((subterms.len(), h + 2));
                    let named = atom_as_cell!(name, subterms.len());

                    self.heap.push(named);

                    for _ in 0..subterms.len() {
                        self.push_stub_addr();
                    }

                    continue;
                }
                &TermRef::Clause(_, _, name, subterms) => {
                    self.queue.push_back((subterms.len(), h + 1));
                    let named = atom_as_cell!(name, subterms.len());

                    self.heap.push(named);

                    for _ in 0..subterms.len() {
                        self.push_stub_addr();
                    }
                }
                &TermRef::AnonVar(Level::Root) | TermRef::Literal(Level::Root, ..) => {
                    let addr = self.term_as_addr(&term, h);
                    self.heap.push(addr);
                }
                &TermRef::Var(Level::Root, _, ref var_ptr) => {
                    let addr = self.term_as_addr(&term, h);
                    self.var_dict.insert(VarKey::VarPtr(var_ptr.clone()), addr);
                    self.heap.push(addr);
                }
                &TermRef::AnonVar(_) => {
                    if let Some((arity, site_h)) = self.queue.pop_front() {
                        self.var_dict.insert(VarKey::AnonVar(h), heap_loc_as_cell!(site_h));

                        if arity > 1 {
                            self.queue.push_front((arity - 1, site_h + 1));
                        }
                    }

                    continue;
                }
                &TermRef::CompleteString(_, _, ref src) => {
                    put_complete_string(self.heap, src.as_str(), self.atom_tbl);
                }
                &TermRef::PartialString(lvl, _, ref src, _) => {
                    if let Level::Root = lvl {
                        // Var tags can't refer directly to partial strings,
                        // so a PStrLoc cell must be pushed.
                        self.heap.push(pstr_loc_as_cell!(heap_loc + 1));
                    }

                    allocate_pstr(self.heap, src.as_str(), self.atom_tbl);

                    let h = self.heap.len();
                    self.queue.push_back((1, h - 1));

                    if let Level::Root = lvl {
                        continue;
                    }
                }
                &TermRef::Var(.., ref var) => {
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
