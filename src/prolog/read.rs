use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::TabledData;

use crate::prolog::forms::*;
use crate::prolog::iterators::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::MachineState;
use crate::prolog::machine::streams::Stream;

use std::collections::VecDeque;

type SubtermDeque = VecDeque<(usize, usize)>;

pub type PrologStream = ParsingStream<Stream>;

pub mod readline {
    use crate::prolog::machine::streams::Stream;
    use crate::prolog::rustyline::error::ReadlineError;
    use crate::prolog::rustyline::{Cmd, Editor, KeyPress};
    use std::io::{Cursor, Error, ErrorKind, Read};

    static mut PROMPT: bool = false;

    pub fn set_prompt(value: bool) {
        unsafe {
            PROMPT = value;
        }
    }

    #[inline]
    fn get_prompt() -> &'static str {
        unsafe {
            if PROMPT { "?- " } else { "" }
        }
    }

    #[derive(Debug)]
    pub struct ReadlineStream {
        rl: Editor<()>,
        pending_input: Cursor<String>,
    }

    impl ReadlineStream {
        pub fn input_stream(pending_input: String) -> Stream {
            let mut rl = Editor::<()>::new();
            rl.bind_sequence(KeyPress::Tab, Cmd::Insert(1, "\t".to_string()));
            Stream::from(ReadlineStream { rl, pending_input: Cursor::new(pending_input) })
        }

        fn call_readline(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            match self.rl.readline(get_prompt()) {
                Ok(text) => {
                    *self.pending_input.get_mut() = text;
                    self.pending_input.set_position(0);

                    unsafe {
                        if PROMPT {
                            self.rl.history_mut().add(self.pending_input.get_ref());
                            PROMPT = false;
                        }
                    }

                    *self.pending_input.get_mut() += "\n";
                    self.pending_input.read(buf)
                }
                Err(ReadlineError::Eof) => {
                    Ok(0)
                }
                Err(e) => {
                    Err(Error::new(ErrorKind::InvalidInput, e))
                }
            }
        }

        pub fn peek_byte(&mut self) -> std::io::Result<u8> {
            set_prompt(false);

            loop {
                match self.pending_input.get_ref().bytes().next() {
                    Some(b) => {
                        return Ok(b);
                    }
                    None => {
                        match self.call_readline(&mut []) {
                            Err(e) => {
                                return Err(e);
                            }
                            Ok(0) => {
                                return Err(Error::new(
                                    ErrorKind::UnexpectedEof,
                                    "end of file",
                                ));
                            }
                            _ => {
                            }
                        }
                    }
                }
            }
        }

        pub fn peek_char(&mut self) -> std::io::Result<char> {
            set_prompt(false);

            loop {
                match self.pending_input.get_ref().chars().next() {
                    Some(c) => {
                        return Ok(c);
                    }
                    None => {
                        match self.call_readline(&mut []) {
                            Err(e) => {
                                return Err(e);
                            }
                            Ok(0) => {
                                return Err(Error::new(
                                    ErrorKind::UnexpectedEof,
                                    "end of file",
                                ));
                            }
                            _ => {
                            }
                        }
                    }
                }
            }
        }
    }

    impl Read for ReadlineStream {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            match self.pending_input.read(buf) {
                Ok(0) => {
                    self.call_readline(buf)
                }
                result => {
                    result
                }
            }
        }
    }

    #[inline]
    pub fn input_stream() -> Stream {
        let input_stream = ReadlineStream::input_stream(String::from(""));
        Stream::from(input_stream)
    }
}

impl MachineState {
    pub fn read(
        &mut self,
        inner: &mut PrologStream,
        atom_tbl: TabledData<Atom>,
        op_dir: &OpDir,
    ) -> Result<TermWriteResult, ParserError> {
        let mut parser = Parser::new(inner, atom_tbl, self.flags);
        let term = parser.read_term(composite_op!(op_dir))?;

        Ok(write_term_to_heap(&term, self))
    }
}

#[inline]
pub(crate)
fn write_term_to_heap(term: &Term, machine_st: &mut MachineState) -> TermWriteResult {
    let term_writer = TermWriter::new(machine_st);
    term_writer.write_term_to_heap(term)
}

#[derive(Debug)]
struct TermWriter<'a> {
    machine_st: &'a mut MachineState,
    queue: SubtermDeque,
    var_dict: HeapVarDict,
}

#[derive(Debug)]
pub struct TermWriteResult {
    pub(crate) heap_loc: usize,
    pub(crate) var_dict: HeapVarDict,
}

impl<'a> TermWriter<'a> {
    #[inline]
    fn new(machine_st: &'a mut MachineState) -> Self {
        TermWriter {
            machine_st,
            queue: SubtermDeque::new(),
            var_dict: HeapVarDict::new(),
        }
    }

    #[inline]
    fn modify_head_of_queue(&mut self, term: &TermRef<'a>, h: usize) {
        if let Some((arity, site_h)) = self.queue.pop_front() {
            self.machine_st.heap[site_h] =
                HeapCellValue::Addr(self.term_as_addr(term, h));

            if arity > 1 {
                self.queue.push_front((arity - 1, site_h + 1));
            }
        }
    }

    #[inline]
    fn push_stub_addr(&mut self) {
        let h = self.machine_st.heap.h();
        self.machine_st.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
    }

    fn term_as_addr(&mut self, term: &TermRef<'a>, h: usize) -> Addr {
        match term {
            &TermRef::AnonVar(_) | &TermRef::Var(..) => {
                Addr::HeapCell(h)
            }
            &TermRef::Cons(..) => {
                Addr::HeapCell(h)
            }
            &TermRef::Constant(_, _, c) => {
                self.machine_st.heap.put_constant(c.clone())
            }
            &TermRef::Clause(..) => {
                Addr::Str(h)
            }
            &TermRef::PartialString(..) => {
                Addr::PStrLocation(h, 0)
            }
        }
    }

    fn write_term_to_heap(mut self, term: &'a Term) -> TermWriteResult {
        let heap_loc = self.machine_st.heap.h();

        for term in breadth_first_iter(term, true) {
            let h = self.machine_st.heap.h();

            match &term {
                &TermRef::Cons(lvl, ..) => {
                    self.queue.push_back((2, h + 1));
                    self.machine_st.heap.push(HeapCellValue::Addr(Addr::Lis(h + 1)));

                    self.push_stub_addr();
                    self.push_stub_addr();

                    if let Level::Root = lvl {
                        continue;
                    }
                }
                &TermRef::Clause(lvl, _, ref ct, subterms) => {
                    self.queue.push_back((subterms.len(), h + 1));
                    let named = HeapCellValue::NamedStr(subterms.len(), ct.name(), ct.spec());

                    self.machine_st.heap.push(named);

                    for _ in 0..subterms.len() {
                        self.push_stub_addr();
                    }

                    if let Level::Root = lvl {
                        continue;
                    }
                }
                &TermRef::AnonVar(Level::Root) | &TermRef::Constant(Level::Root, ..) => {
                    let addr = self.term_as_addr(&term, h);
                    self.machine_st.heap.push(HeapCellValue::Addr(addr));
                }
                &TermRef::Var(Level::Root, _, ref var) => {
                    let addr = self.term_as_addr(&term, h);
                    self.var_dict.insert(var.clone(), Addr::HeapCell(h));
                    self.machine_st.heap.push(HeapCellValue::Addr(addr));
                }
                &TermRef::AnonVar(_) => {
                    if let Some((arity, site_h)) = self.queue.pop_front() {
                        if arity > 1 {
                            self.queue.push_front((arity - 1, site_h + 1));
                        }
                    }

                    continue;
                }
                &TermRef::PartialString(lvl, _, ref pstr, tail) => {
                    if tail.is_some() {
                        self.machine_st.heap.allocate_pstr(&pstr);
                    } else {
                        self.machine_st.heap.put_complete_string(&pstr);
                    }

                    if let Level::Root = lvl {
                    } else if tail.is_some() {
                        let h = self.machine_st.heap.h();
                        self.queue.push_back((1, h - 1));
                    }
                }
                &TermRef::Var(_, _, ref var) => {
                    if let Some((arity, site_h)) = self.queue.pop_front() {
                        if let Some(addr) = self.var_dict.get(var).cloned() {
                            self.machine_st.heap[site_h] = HeapCellValue::Addr(addr);
                        } else {
                            self.var_dict.insert(var.clone(), Addr::HeapCell(site_h));
                        }

                        if arity > 1 {
                            self.queue.push_front((arity - 1, site_h + 1));
                        }
                    }

                    continue;
                }
                _ => {
                }
            };

            self.modify_head_of_queue(&term, h);
        }

        TermWriteResult { heap_loc, var_dict: self.var_dict }
    }
}
