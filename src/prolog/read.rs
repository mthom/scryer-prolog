use prolog_parser::ast::*;
use prolog_parser::parser::*;
use prolog_parser::tabled_rc::TabledData;

use prolog::instructions::*;
use prolog::iterators::*;
use prolog::machine::machine_state::MachineState;

use std::collections::VecDeque;
use std::io::{Read, stdin};

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
    Quit,
    Clear,
    Batch,
    TermString(String)
}

pub fn toplevel_read_line() -> Result<Input, ParserError> {
    let mut buffer = String::new();

    let stdin = stdin();
    stdin.read_line(&mut buffer).unwrap();

    match &*buffer.trim() {
        "quit"   => Ok(Input::Quit),
        "clear"  => Ok(Input::Clear),
        "[user]" => {
            println!("(type Enter + Ctrl-D to terminate the stream when finished)");
            Ok(Input::Batch)
        },
        _ => Ok(Input::TermString(buffer))
    }
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
            &TermRef::Var(Level::Root, _, ref name) =>
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
