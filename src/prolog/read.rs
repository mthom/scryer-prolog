use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::forms::*;
use prolog::iterators::*;
use prolog::machine::machine_errors::*;
use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::MachineState;

use std::collections::VecDeque;
use std::io::Read;

use readline_rs_compat::readline::*;

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

pub enum Input {
    Clear,
    Batch,
    TermString(&'static str)
}

#[derive(Clone, Copy)]
pub enum LineMode {
    Single,
    Multi
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

fn is_directive(buf: &str) -> bool {
    match buf {
        "?- [user]." | "?- [clear]." => true,
        _ => false
    }
}

unsafe extern "C" fn bind_end_chord(_: i32, _: i32) -> i32 {
    if let LineMode::Multi = LINE_MODE {
        rl_done = 1;
    }

    0
}

unsafe extern "C" fn bind_end_key(_: i32, _: i32) -> i32 {
    insert_text_rl(".");

    if let LineMode::Single = LINE_MODE {
        END_OF_LINE = true;
    }

    0
}

unsafe extern "C" fn bind_cr(_: i32, _: i32) -> i32 {    
    if END_OF_LINE {
        if let Some(buf) = rl_line_buffer_as_str() {
            if is_directive(buf) {
                println!("");
                rl_done = 1;
                return 0;
            }
        }
        
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

    bind_key_rl('.' as i32, bind_end_key);
    bind_key_rl('\n' as i32, bind_cr);
    bind_key_rl('\r' as i32, bind_cr);
    bind_keyseq_rl("\\C-d", bind_end_chord);
}

pub fn read_batch(prompt: &str) -> Result<&'static str, SessionError> {
    unsafe {
        use std::ptr::null;
        use std::mem;

        // deactivate the startup hook that emits a "?- " to the
        // beginning of the readline buffer.
        let p: *const i8 = null();
        rl_startup_hook = mem::transmute(p);
    }
    
    match readline_rl(prompt) {
        Some(input) => Ok(input),
        None => Err(SessionError::UserPrompt)
    }
}

fn read_line(prompt: &str) -> Result<&'static str, SessionError> {    
    match readline_rl(prompt) {
        Some(input) => Ok(input),
        None => Err(SessionError::UserPrompt)
    }
}

unsafe extern "C" fn insert_query_prompt() -> i32 {
    insert_text_rl("?- ");
    0
}

pub fn toplevel_read_line() -> Result<Input, SessionError>
{
    unsafe {
        rl_startup_hook = insert_query_prompt;
    }
    
    let buffer = read_line("")?;
    
    Ok(match &*buffer.trim() {
        "?- [clear]." => Input::Clear,
        "?- [user]." => {
            println!("(type Enter + Ctrl-D to terminate the stream when finished)");
            Input::Batch
        },
        _ => Input::TermString(buffer)
    })
}

impl MachineState {
    pub fn read<R: Read>(&mut self, inner: R, atom_tbl: TabledData<Atom>, op_dir: &OpDir)
                         -> Result<usize, ParserError>
    {
        let mut parser = Parser::new(inner, atom_tbl, self.flags);
        let term = parser.read_term(composite_op!(op_dir))?;

        Ok(write_term_to_heap(&term, self).heap_loc)
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

pub(crate) struct TermWriteResult {
    pub(crate) heap_loc: usize,
    pub(crate) var_dict: HeapVarDict,
}

pub(crate) fn write_term_to_heap(term: &Term, machine_st: &mut MachineState) -> TermWriteResult
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
