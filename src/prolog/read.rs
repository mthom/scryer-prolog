use prolog::ast::*;
use prolog::machine::machine_state::*;
use prolog::parser::parser::*;

use std::collections::VecDeque;
use std::io::stdin;

pub struct Reader<'a> {
    pub machine_st: &'a mut MachineState,
}

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

impl<'a> Reader<'a> {
    pub fn new(machine_st: &'a mut MachineState) -> Self {
        Reader { machine_st }
    }

    pub fn read_stdin(&mut self, op_dir: &'a OpDir) -> Result<usize, ParserError> {
        let mut buffer = String::new();

        let stdin = stdin();
        let flags = self.machine_st.machine_flags();

        loop {
            stdin.read_line(&mut buffer).unwrap();
            let mut parser = Parser::new(buffer.as_bytes(), self.machine_st.atom_tbl.clone(),
                                         self.machine_st.string_tbl.clone(), flags);

            match parser.read_term(op_dir) {
                Err(ParserError::UnexpectedEOF) => continue,
                Err(e) => return Err(e),
                Ok(term) => return Ok(self.write_term_to_heap(term))
            };
        }
    }

    fn push_stub_addr(&mut self) {
        let h = self.machine_st.heap.h;
        self.machine_st.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
    }

    fn modify_head_of_queue(&mut self, queue: &mut SubtermDeque, term: TermRef, h: usize) {
        if let Some((arity, site_h)) = queue.pop_front() {
            self.machine_st.heap[site_h] = HeapCellValue::Addr(term.as_addr(h));

            if arity > 1 {
                queue.push_front((arity - 1, site_h + 1));
            }
        }
    }

    fn write_term_to_heap(&mut self, term: Term) -> usize {
        let h = self.machine_st.heap.h;

        let mut queue = SubtermDeque::new();
        let mut var_dict = HeapVarDict::new();

        for term in term.breadth_first_iter(true) {
            let h = self.machine_st.heap.h;

            match &term {
                &TermRef::Cons(lvl, ..) => {
                    queue.push_back((2, h+1));
                    self.machine_st.heap.push(HeapCellValue::Addr(Addr::Lis(h+1)));

                    self.push_stub_addr();
                    self.push_stub_addr();

                    if let Level::Root = lvl {
                        continue;
                    }
                },
                &TermRef::Clause(lvl, _, ref ct, subterms) => {
                    queue.push_back((subterms.len(), h+1));
                    let named = HeapCellValue::NamedStr(subterms.len(), ct.name(),
                                                        ct.fixity());

                    self.machine_st.heap.push(named);

                    for _ in 0 .. subterms.len() {
                        self.push_stub_addr();
                    }

                    if let Level::Root = lvl {
                        continue;
                    }
                },
                &TermRef::AnonVar(Level::Root)
              | &TermRef::Var(Level::Root, ..)
              | &TermRef::Constant(Level::Root, ..) =>
                    self.machine_st.heap.push(HeapCellValue::Addr(term.as_addr(h))),
                &TermRef::AnonVar(_) =>
                    continue,
                &TermRef::Var(_, _, ref var) => {
                    if let Some((arity, site_h)) = queue.pop_front() {
                        if let Some(addr) = var_dict.get(var).cloned() {
                            self.machine_st.heap[site_h] = HeapCellValue::Addr(addr);
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

            self.modify_head_of_queue(&mut queue, term, h);
        }

        h
    }
}
