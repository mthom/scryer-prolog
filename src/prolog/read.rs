use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::TabledData;

use crate::prolog::forms::*;
use crate::prolog::iterators::*;
use crate::prolog::machine::heap::Heap;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::MachineState;
use crate::prolog::machine::streams::Stream;

use std::collections::VecDeque;

type SubtermDeque = VecDeque<(usize, usize)>;

impl<'a> TermRef<'a> {
    fn as_addr(&self, heap: &mut Heap, h: usize) -> Addr {
        match self {
            &TermRef::AnonVar(_) | &TermRef::Var(..) => {
                Addr::HeapCell(h)
            }
            &TermRef::Cons(..) => {
                Addr::HeapCell(h)
            }
            &TermRef::Constant(_, _, c) => {
                heap.put_constant(c.clone())
            }
            &TermRef::Clause(..) => {
                Addr::Str(h)
            }
        }
    }
}

pub type PrologStream = ParsingStream<Stream>;

pub mod readline {
    use crate::prolog::machine::streams::Stream;
    use crate::prolog::rustyline::error::ReadlineError;
    use crate::prolog::rustyline::{Cmd, Editor, KeyPress};
    use std::io::{Cursor, Read};

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
                    Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, e))
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

fn push_stub_addr(machine_st: &mut MachineState) {
    let h = machine_st.heap.h();
    machine_st.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
}

fn modify_head_of_queue(
    machine_st: &mut MachineState,
    queue: &mut SubtermDeque,
    term: TermRef,
    h: usize,
) {
    if let Some((arity, site_h)) = queue.pop_front() {
        machine_st.heap[site_h] = HeapCellValue::Addr(term.as_addr(&mut machine_st.heap, h));

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
fn write_term_to_heap(term: &Term, machine_st: &mut MachineState) -> TermWriteResult {
    let heap_loc = machine_st.heap.h();

    let mut queue = SubtermDeque::new();
    let mut var_dict = HeapVarDict::new();

    for term in breadth_first_iter(term, true) {
        let h = machine_st.heap.h();

        match &term {
            &TermRef::Cons(lvl, ..) => {
                queue.push_back((2, h + 1));
                machine_st.heap.push(HeapCellValue::Addr(Addr::Lis(h + 1)));

                push_stub_addr(machine_st);
                push_stub_addr(machine_st);

                if let Level::Root = lvl {
                    continue;
                }
            }
            &TermRef::Clause(lvl, _, ref ct, subterms) => {
                queue.push_back((subterms.len(), h + 1));
                let named = HeapCellValue::NamedStr(subterms.len(), ct.name(), ct.spec());

                machine_st.heap.push(named);

                for _ in 0..subterms.len() {
                    push_stub_addr(machine_st);
                }

                if let Level::Root = lvl {
                    continue;
                }
            }
            &TermRef::AnonVar(Level::Root) | &TermRef::Constant(Level::Root, ..)
          | &TermRef::Var(Level::Root, ..) => {
                let addr = term.as_addr(&mut machine_st.heap, h);

                if !addr.is_heap_bound() {
                    machine_st.heap.push(HeapCellValue::Addr(addr));
                }
            }
            &TermRef::AnonVar(_) => {
                if let Some((arity, site_h)) = queue.pop_front() {
                    if arity > 1 {
                        queue.push_front((arity - 1, site_h + 1));
                    }
                }

                continue;
            }
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
            }
            _ => {}
        };

        modify_head_of_queue(machine_st, &mut queue, term, h);
    }

    TermWriteResult { heap_loc, var_dict }
}
