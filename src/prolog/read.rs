use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::forms::*;
use prolog::iterators::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::MachineState;

use std::collections::VecDeque;
use std::io::Read;

type SubtermDeque = VecDeque<(usize, usize)>;

impl<'a> TermRef<'a> {
    fn as_addr(&self, h: usize) -> Addr {
        match self {
            &TermRef::AnonVar(_) | &TermRef::Var(..) => Addr::HeapCell(h),
            &TermRef::Cons(..) => Addr::HeapCell(h),
            &TermRef::Constant(_, _, c) => Addr::Con(c.clone()),
            &TermRef::Clause(..) => Addr::Str(h),
        }
    }
}

pub type PrologStream = ParsingStream<Box<Read>>;

#[cfg(feature = "readline_rs_compat")]
pub mod readline
{
    use prolog_parser::ast::*;
    use readline_rs_compat::readline::*;
    use std::io::{Error, Read};

    #[derive(Clone, Copy)]
    pub enum LineMode {
        Single,
        Multi
    }

    pub struct ReadlineStream {
        pending_input: String
    }

    impl ReadlineStream {
        #[inline]
        fn new(pending_input: String) -> Self {
            ReadlineStream { pending_input }
        }

        fn call_readline(&mut self, prompt: &str, buf: &mut [u8]) -> std::io::Result<usize> {
            match readline_rl(prompt) {
                Some(text) => {
                    self.pending_input += &text;
                    Ok(self.write_to_buf(buf))
                },
                None => Err(Error::last_os_error())
            }
        }

        fn split_pending(&mut self, buf: &mut [u8], split_idx: usize) -> usize {
            let (outgoing, _) = self.pending_input.split_at(split_idx);

            for (idx, b) in outgoing.bytes().enumerate() {
                buf[idx] = b;
            }

            outgoing.len()
        }

        fn write_to_buf(&mut self, buf: &mut [u8]) -> usize {
            let split_idx = std::cmp::min(self.pending_input.len(), buf.len());
            let output_len = self.split_pending(buf, split_idx);

            if split_idx < self.pending_input.len() {
                self.pending_input = self.pending_input[split_idx ..].to_string();
            } else {
                self.pending_input.clear();
            }

            output_len
        }
    }

    impl Read for ReadlineStream {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.pending_input.is_empty() {
                self.call_readline("", buf)
            } else {
                Ok(self.write_to_buf(buf))
            }
        }
    }

    static mut LINE_MODE: LineMode = LineMode::Single;
    static mut END_OF_LINE: bool = false;

    pub fn set_line_mode(mode: LineMode) {
        unsafe {
            LINE_MODE = mode;
            END_OF_LINE = false;
            rl_done = 0;
        }
    }

    unsafe extern "C" fn bind_end_chord(_: i32, _: i32) -> i32 {
        if let LineMode::Multi = LINE_MODE {
            rl_done = 1;
        }

        0
    }

    unsafe extern "C" fn bind_cr(_: i32, _: i32) -> i32 {
        if let LineMode::Single = LINE_MODE {
            insert_text_rl("\n");
            println!("");
            rl_done = 1;
        } else {
            insert_text_rl("\n");
        }

        0
    }

    pub fn readline_initialize() {
        let rc = initialize_rl(); // initialize editline.

        if rc != 0 {
            panic!("initialize_rl() failed with return code {}", rc);
        }

        bind_key_rl('\t' as i32, rl_insert); // just insert tabs when typed.
        bind_key_rl('\n' as i32, bind_cr);
        bind_key_rl('\r' as i32, bind_cr);
        bind_keyseq_rl("\\C-d", bind_end_chord);
    }

    pub fn read_batch(prompt: &str) -> Result<Vec<u8>, ::SessionError> {
        match readline_rl(prompt) {
            Some(input) => Ok(Vec::from(input.as_bytes())),
            None => Err(::SessionError::UserPrompt)
        }
    }

    #[inline]
    pub fn input_stream() -> ::PrologStream {
        let reader: Box<Read> = Box::new(ReadlineStream::new(String::from("")));
        parsing_stream(reader)
    }
}

#[cfg(not(feature = "readline_rs_compat"))]
pub mod readline
{
    use prolog_parser::ast::*;
    use std::io::{BufReader, Read, Stdin, stdin};

    struct StdinWrapper {
        buf: BufReader<Stdin>
    }

    impl Read for StdinWrapper {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.buf.read(buf)
        }
    }

    pub fn read_batch(_: &str) -> Result<Vec<u8>, ::SessionError> {
        let mut buf = vec![];

        let stdin = stdin();
        let mut stdin = stdin.lock();

        match stdin.read_to_end(&mut buf) {
            Ok(_) => Ok(buf),
            _ => Err(::SessionError::UserPrompt)
        }
    }

    #[inline]
    pub fn input_stream() -> ::PrologStream {
        let reader: Box<Read> = Box::new(StdinWrapper { buf: BufReader::new(stdin()) });
        parsing_stream(reader)
    }
}

impl MachineState {
    pub fn read(&mut self, inner: &mut PrologStream, atom_tbl: TabledData<Atom>, op_dir: &OpDir)
                -> Result<TermWriteResult, ParserError>
    {
        let mut parser = Parser::new(inner, atom_tbl, self.flags);
        let term = parser.read_term(composite_op!(op_dir))?;

        Ok(write_term_to_heap(&term, self))
    }
}

fn push_stub_addr(machine_st: &mut MachineState) {
    let h = machine_st.heap.h;
    machine_st.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
}

fn modify_head_of_queue(machine_st: &mut MachineState, queue: &mut SubtermDeque, term: TermRef, h: usize)
{
    if let Some((arity, site_h)) = queue.pop_front() {
        machine_st.heap[site_h] = HeapCellValue::Addr(term.as_addr(h));

        if arity > 1 {
            queue.push_front((arity - 1, site_h + 1));
        }
    }
}

pub struct TermWriteResult {
    pub(crate) heap_loc: usize,
    pub(crate) var_dict: HeapVarDict,
}

pub(crate)
fn write_term_to_heap(term: &Term, machine_st: &mut MachineState) -> TermWriteResult
{
    let heap_loc = machine_st.heap.h;

    let mut queue = SubtermDeque::new();
    let mut var_dict = HeapVarDict::new();

    for term in breadth_first_iter(term, true) {
        let h = machine_st.heap.h;

        match &term {
            &TermRef::Cons(lvl, ..) => {
                queue.push_back((2, h+1));
                machine_st.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));

                push_stub_addr(machine_st);
                push_stub_addr(machine_st);

                if let Level::Root = lvl {
                    continue;
                }
            },
            &TermRef::Clause(lvl, _, ref ct, subterms) => {
                queue.push_back((subterms.len(), h+1));
                let named = HeapCellValue::NamedStr(subterms.len(), ct.name(), ct.spec());

                machine_st.heap.push(named);

                for _ in 0 .. subterms.len() {
                    push_stub_addr(machine_st);
                }

                if let Level::Root = lvl {
                    continue;
                }
            },
            &TermRef::AnonVar(Level::Root) | &TermRef::Constant(Level::Root, ..) =>
                machine_st.heap.push(HeapCellValue::Addr(term.as_addr(h))),
            &TermRef::Var(Level::Root, ..) =>
                machine_st.heap.push(HeapCellValue::Addr(term.as_addr(h))),
            &TermRef::AnonVar(_) => {
                if let Some((arity, site_h)) = queue.pop_front() {
                    if arity > 1 {
                        queue.push_front((arity - 1, site_h + 1));
                    }
                }

                continue;
            },
            &TermRef::Var(_, _, ref var) => {
                if let Some((arity, site_h)) = queue.pop_front() {
                    if let Some(addr) = var_dict.get(var).cloned() {
                        machine_st.heap[site_h] = HeapCellValue::Addr(addr);
                    } else {
                        var_dict.insert(var.clone(), Addr::HeapCell(site_h));
                    }

                    if arity > 1 {
                        queue.push_front((arity - 1, site_h + 1));
                    }
                }

                continue;
            },
            _ => {}
        };

        modify_head_of_queue(machine_st, &mut queue, term, h);
    }

    TermWriteResult { heap_loc, var_dict }
}
