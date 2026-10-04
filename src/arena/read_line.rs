use crate::arena::opt_in_buf_reader::*;
use crate::arena::stream_insts::*;
use crate::arena::stream_layout::*;
use crate::atom_table::{Atom, AtomTable};

#[cfg(feature = "repl")]
use crate::repl_helper::Helper;
#[cfg(feature = "repl")]
use rustyline::error::ReadlineError;
#[cfg(feature = "repl")]
use rustyline::history::DefaultHistory;
#[cfg(feature = "repl")]
use rustyline::{Config, Editor};

use bstr::ByteSlice;
use compact_str::*;

use std::io::{self, BufRead, Cursor, Read, Write};
#[cfg(feature = "repl")]
use std::io::{Error, ErrorKind};
use std::sync::Arc;

static mut PROMPT: bool = false;
#[cfg(feature = "repl")]
const HISTORY_FILE: &str = ".scryer_history";

#[derive(Debug)]
pub(crate) struct ReadlineStream {
    rl: Editor<Helper, DefaultHistory>,
    pending_input: Cursor<Vec<u8>>,
    #[allow(dead_code)]
    add_history: bool,
}

pub(crate) unsafe fn set_prompt(value: bool) {
    unsafe { PROMPT = value };
}

#[cfg(feature = "repl")]
#[inline]
unsafe fn get_prompt() -> &'static str {
    if unsafe { PROMPT } { "?- " } else { "" }
}

thread_local! {
    static RAW_READ: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub struct RawReadGuard;

impl RawReadGuard {
    pub fn new() -> RawReadGuard {
        if RAW_READ.get() {
            panic!("Nested RawReadGuards");
        }
        RAW_READ.set(true);
        RawReadGuard
    }
}

impl Drop for RawReadGuard {
    fn drop(&mut self) {
        RAW_READ.set(false);
    }
}

impl ReadlineStream {
    #[inline]
    pub(crate) fn new(pending_input: &str, add_history: bool) -> Self {
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

            let pending_input = pending_input.bytes().collect();

            ReadlineStream {
                rl,
                pending_input: Cursor::new(pending_input),
                add_history,
            }
        }
        #[cfg(not(feature = "repl"))]
        {
            ReadlineStream {
                pending_input: Cursor::new(pending_input.to_owned()),
                add_history,
            }
        }
    }

    #[cfg(feature = "repl")]
    fn read_line(&mut self) -> io::Result<String> {
        if RAW_READ.get() {
            let mut text = String::new();
            let stdin = std::io::stdin();
            match stdin.read_line(&mut text) {
                Ok(_) => Ok(text),
                Err(e) => Err(e),
            }
        } else {
            match self.rl.readline(unsafe { get_prompt() }) {
                Ok(text) => Ok(text),
                Err(ReadlineError::Eof) => Err(Error::from(ErrorKind::UnexpectedEof)),
                Err(e) => Err(Error::new(ErrorKind::InvalidInput, e)),
            }
        }
    }

    #[cfg(feature = "repl")]
    fn call_readline(&mut self) -> std::io::Result<usize> {
        let text = self.read_line();

        match text {
            Ok(mut text) => {
                unsafe {
                    if PROMPT {
                        self.rl.add_history_entry(&text).unwrap();
                        self.save_history();
                        PROMPT = false;
                    }
                }

                if !text.ends_with('\n') {
                    text.push('\n');
                }

                *self.pending_input.get_mut() = text.into_bytes();
                self.pending_input.set_position(0);

                Ok(self.pending_input.get_ref().len())
            }
            Err(e) => Err(e),
        }
    }

    #[cfg(not(feature = "repl"))]
    fn call_readline(&mut self) -> std::io::Result<usize> {
        Ok(0)
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
        self.pending_input.get_mut().clear();
        self.pending_input.set_position(0);
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
}

#[cfg(feature = "repl")]
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

#[cfg(feature = "repl")]
impl Write for ReadlineStream {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::WriteToInputStream,
        ))
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::Error::new(
            ErrorKind::PermissionDenied,
            StreamError::FlushToInputStream,
        ))
    }
}

#[cfg(feature = "repl")]
impl GraphemeRead for ReadlineStream {
    fn read_grapheme(&mut self) -> io::Result<Option<CompactString>> {
        match self.peek_grapheme(0)?.map(CompactString::new) {
            Some(g) => {
                self.pending_input.consume(g.len());
                Ok(Some(g))
            }
            None => Ok(None),
        }
    }

    fn peek_grapheme(&mut self, at: usize) -> io::Result<Option<&str>> {
        loop {
            let pos = self.pending_input.position() as usize;

            if self.pending_input.get_ref().get(pos + at).is_none() {
                self.call_readline()?;
                unsafe { set_prompt(false) };
                continue;
            } else {
                break;
            }
        }

        let pos = self.pending_input.position() as usize;

        Ok(self
            .pending_input
            .get_ref()
            .get(pos + at..)
            .and_then(|slice| slice.graphemes().next()))
    }

    fn read_char(&mut self) -> io::Result<Option<char>> {
        if let Some(c) = self.peek_char()? {
            self.pending_input.consume(c.len_utf8());
            Ok(Some(c))
        } else {
            Ok(None)
        }
    }

    fn peek_char(&mut self) -> io::Result<Option<char>> {
        if let Some(g) = self.peek_grapheme(0)? {
            Ok(g.chars().next())
        } else {
            Ok(None)
        }
    }
}

impl PrologStream for ReadlineStream {
    #[inline]
    fn peek_byte(&mut self) -> io::Result<Option<u8>> {
        let buf = self.pending_input.get_ref();
        let byte = buf.iter().next().cloned();

        loop {
            match byte {
                Some(b) => {
                    return Ok(Some(b));
                }
                None => match self.call_readline() {
                    Err(e) => {
                        return Err(e);
                    }
                    _ => unsafe {
                        set_prompt(false);
                    },
                },
            }
        }
    }

    fn reset(&mut self) -> bool {
        self.reset();
        true
    }

    fn position_relative_to_end(&mut self) -> AtEndOfStream {
        let cursor_len = self.pending_input.get_ref().len() as u64;
        cursor_position(&self.pending_input, cursor_len)
    }

    fn position(&mut self) -> Option<u64> {
        Some(0)
    }

    fn mode(&self) -> Atom {
        atom!("read")
    }
}
