use crate::parser::ast::*;
use crate::parser::parser::*;

use crate::atom_table::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_state::{MachineState, copy_and_align_iter};
use crate::machine::streams::*;
use crate::parser::char_reader::*;
#[cfg(feature = "repl")]
use crate::repl_helper::Helper;

#[cfg(feature = "repl")]
use rustyline::error::ReadlineError;
#[cfg(feature = "repl")]
use rustyline::history::DefaultHistory;
#[cfg(feature = "repl")]
use rustyline::{Config, Editor};

use std::io::{Cursor, Read};
#[cfg(feature = "repl")]
use std::io::{Error, ErrorKind};
use std::sync::Arc;

pub(crate) fn devour_whitespace<R: CharRead>(
    parser: &mut Parser<'_, R>,
) -> Result<bool, ParserError> {
    match parser.lexer.scan_for_layout() {
        Err(e) if e.is_unexpected_eof() => Ok(true),
        Err(e) => Err(e),
        Ok(_) => Ok(false),
    }
}

pub(crate) fn error_after_read_term(
    err: ParserError,
    prior_num_lines_read: usize,
) -> CompilationError {
    if err.is_unexpected_eof() {
        let ParserErrorSrc { line_num, col_num } = err.err_src();

        // rough overlap with errors 8.14.1.3 k) & l) of the ISO standard here
        if !(line_num == prior_num_lines_read && col_num == 0) {
            return CompilationError::from(ParserError::IncompleteReduction(err.err_src()));
        }
    }

    CompilationError::from(err)
}

impl FocusedHeap {
    pub fn to_machine_heap(mut self, machine_st: &mut MachineState) -> TermWriteResult {
        let heap_len = machine_st.heap.len();
        machine_st.heap.extend(copy_and_align_iter(self.heap.drain(..), 0, heap_len as i64));

        let mut var_locs = VarLocs::default();

        for (var_loc, var_ptrs) in self.var_locs.drain(..) {
            var_locs.insert(var_loc + heap_len, var_ptrs);
        }

        TermWriteResult {
            heap_loc: self.focus + heap_len,
            var_locs,
        }
    }
}

impl MachineState {
    pub(crate) fn read<R: CharRead>(
        &mut self,
        inner: R,
        op_dir: &OpDir,
    ) -> Result<(FocusedHeap, usize), ParserError> {
        let mut parser = Parser::new(inner, self);
        let op_dir = CompositeOpDir::new(op_dir, None);

        let term_result = parser.read_term(&op_dir, Tokens::Default);
        let lines_read  = parser.lines_read();

        term_result.map(|term| (term, lines_read))
    }

    pub(crate) fn read_to_heap(
        &mut self,
        mut inner: Stream,
        op_dir: &OpDir,
    ) -> Result<TermWriteResult, CompilationError> {
        let prior_num_lines_read = inner.lines_read();
        let term = match self.read(inner, op_dir) {
            Ok((term, num_lines_read)) => {
                inner.add_lines_read(num_lines_read);
                term
            }
            Err(e) => {
                return Err(error_after_read_term(e, prior_num_lines_read));
            }
        };

        Ok(term.to_machine_heap(self))
    }
}

static mut PROMPT: bool = false;
#[cfg(feature = "repl")]
const HISTORY_FILE: &str = ".scryer_history";

pub(crate) fn set_prompt(value: bool) {
    unsafe {
        PROMPT = value;
    }
}

#[cfg(feature = "repl")]
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
    #[cfg(feature = "repl")]
    rl: Editor<Helper, DefaultHistory>,
    pending_input: CharReader<Cursor<String>>,
    #[allow(dead_code)]
    add_history: bool,
}

impl ReadlineStream {
    #[inline]
    pub fn new(pending_input: &str, add_history: bool) -> Self {
        #[cfg(feature = "repl")]
        {
            let config = Config::builder().check_cursor_position(true).build();

            let helper = Helper::new();

            let mut rl = Editor::with_config(config).unwrap();
            rl.set_helper(Some(helper));

            if let Some(mut path) = dirs_next::home_dir() {
                path.push(HISTORY_FILE);
                if path.exists() && rl.load_history(&path).is_err() {
                    println!("% Warning: loading history failed");
                }
            }

            ReadlineStream {
                rl,
                pending_input: CharReader::new(Cursor::new(pending_input.to_owned())),
                add_history,
            }
        }

        #[cfg(not(feature = "repl"))]
        {
            ReadlineStream {
                pending_input: CharReader::new(Cursor::new(pending_input.to_owned())),
                add_history,
            }
        }
    }

    #[allow(unused_variables)]
    pub fn set_atoms_for_completion(&mut self, atoms: &Arc<AtomTable>) {
        #[cfg(feature = "repl")]
        {
            let helper = self.rl.helper_mut().unwrap();
            helper.atoms = Arc::downgrade(atoms);
        }
    }

    #[inline]
    pub fn reset(&mut self) {
        self.pending_input.reset_buffer();

        let pending_input = self.pending_input.get_mut();

        pending_input.get_mut().clear();
        pending_input.set_position(0);
    }

    #[cfg(feature = "repl")]
    fn call_readline(&mut self) -> std::io::Result<usize> {
        match self.rl.readline(get_prompt()) {
            Ok(text) => {
                self.pending_input.reset_buffer();

                *self.pending_input.get_mut().get_mut() = text;
                self.pending_input.get_mut().set_position(0);

                unsafe {
                    if PROMPT {
                        self.rl
                            .add_history_entry(self.pending_input.get_ref().get_ref())
                            .unwrap();
                        self.save_history();
                        PROMPT = false;
                    }

                    if !self.pending_input.get_ref().get_ref().ends_with('\n') {
                        *self.pending_input.get_mut().get_mut() += "\n";
                    }
                }

                Ok(self.pending_input.get_ref().get_ref().len())
            }
            Err(ReadlineError::Eof) => Err(Error::from(ErrorKind::UnexpectedEof)),
            Err(e) => Err(Error::new(ErrorKind::InvalidInput, e)),
        }
    }

    #[cfg(not(feature = "repl"))]
    fn call_readline(&mut self) -> std::io::Result<usize> {
        Ok(0)
    }

    #[cfg(feature = "repl")]
    fn save_history(&mut self) {
        if !self.add_history {
            return;
        };
        if let Some(mut path) = dirs_next::home_dir() {
            path.push(HISTORY_FILE);
            if path.exists() {
                if self.rl.append_history(&path).is_err() {
                    println!("% Warning: couldn't append history (existing file)");
                }
            } else if self.rl.save_history(&path).is_err() {
                println!("% Warning: couldn't save history (new file)");
            }
        }
    }

    #[allow(dead_code)]
    #[cfg(not(feature = "repl"))]
    fn save_history(&mut self) {}

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
            result => result,
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
                _ => match self.call_readline() {
                    Err(e) => {
                        return Some(Err(e));
                    }
                    _ => {
                        set_prompt(false);
                    }
                },
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

#[derive(Debug)]
pub struct TermWriteResult {
    pub heap_loc: usize,
    pub var_locs: VarLocs,
}
