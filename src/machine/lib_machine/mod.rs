use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::atom_table;
use crate::heap_iter::{stackful_post_order_iter, NonListElider};
use crate::machine::mock_wam::CompositeOpDir;
use crate::machine::{
    ArenaHeaderTag, F64Offset, F64Ptr, Fixnum, Number, BREAK_FROM_DISPATCH_LOOP_LOC,
    LIB_QUERY_SUCCESS,
};
use crate::parser::ast::{TermWriteResult, Var};
use crate::parser::lexer::LexerParser;
use crate::parser::parser::Tokens;
use crate::types::UntypedArenaPtr;

use dashu::{Integer, Rational};
use indexmap::IndexMap;

use super::{streams::Stream, Atom, AtomCell, HeapCellValue, HeapCellValueTag, Machine};

#[cfg(test)]
mod tests;

/// Represents a leaf answer from a query.
#[derive(Debug, Clone, PartialEq)]
pub enum LeafAnswer {
    /// A `true` leaf answer.
    True,
    /// A `false` leaf answer.
    ///
    /// This means that there are no more answers for the query.
    False,
    /// An exception leaf answer.
    Exception(Term),
    /// A leaf answer with bindings.
    #[non_exhaustive]
    LeafAnswer {
        /// The bindings of variables in the query.
        bindings: BTreeMap<String, Term>,
        //residual_goals: Vec<Term>,
    },
}

impl LeafAnswer {
    /// Creates a leaf answer with no residual goals.
    pub fn from_bindings<S: Into<String>>(bindings: impl IntoIterator<Item = (S, Term)>) -> Self {
        LeafAnswer::LeafAnswer {
            bindings: bindings.into_iter().map(|(k, v)| (k.into(), v)).collect(),
        }
    }
}

/// Represents a Prolog term.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// An arbitrary precision integer.
    Integer(Integer),
    /// An arbitrary precision rational.
    Rational(Rational),
    /// A float.
    Float(f64),
    /// A Prolog atom.
    Atom(String),
    /// A Prolog string.
    ///
    /// In particular, this represents Prolog lists of characters.
    String(String),
    /// A Prolog list.
    List(Vec<Term>),
    /// A Prolog compound term.
    Compound(String, Vec<Term>),
    /// A Prolog variable.
    Var(String),
}

impl Term {
    /// Creates an integer term.
    pub fn integer(value: impl Into<Integer>) -> Self {
        Term::Integer(value.into())
    }

    /// Creates a rational term.
    pub fn rational(value: impl Into<Rational>) -> Self {
        Term::Rational(value.into())
    }

    /// Creates a float term.
    pub fn float(value: impl Into<f64>) -> Self {
        Term::Float(value.into())
    }

    /// Creates an atom term.
    pub fn atom(value: impl Into<String>) -> Self {
        Term::Atom(value.into())
    }

    /// Creates a string term.
    ///
    /// In specific, this represents a list of chars in Prolog.
    pub fn string(value: impl Into<String>) -> Self {
        Term::String(value.into())
    }

    /// Creates a list term.
    pub fn list(value: impl IntoIterator<Item = Term>) -> Self {
        Term::List(value.into_iter().collect())
    }

    /// Creates a compound term.
    pub fn compound(functor: impl Into<String>, args: impl IntoIterator<Item = Term>) -> Self {
        Term::Compound(functor.into(), args.into_iter().collect())
    }

    /// Creates a variable.
    pub fn variable(value: impl Into<String>) -> Self {
        Term::Var(value.into())
    }

    /// Creates a conjunction, giving the atom `true` if empty.
    pub fn conjunction(value: impl IntoIterator<Item = Term>) -> Self {
        Term::try_conjunction(value).unwrap_or(Term::atom("true"))
    }

    /// Creates a conjunction, giving `None` if empty.
    pub fn try_conjunction(value: impl IntoIterator<Item = Term>) -> Option<Self> {
        let mut iter = value.into_iter();
        iter.next().map(|first| {
            Term::try_conjunction(iter)
                .map(|rest| Term::compound(",", [first.clone(), rest]))
                .unwrap_or(first)
        })
    }

    /// Creates a disjunction, giving the atom `false` if empty.
    pub fn disjunction(value: impl IntoIterator<Item = Term>) -> Self {
        Term::try_disjunction(value).unwrap_or(Term::atom("false"))
    }

    /// Creates a disjunction, giving `None` if empty.
    pub fn try_disjunction(value: impl IntoIterator<Item = Term>) -> Option<Self> {
        let mut iter = value.into_iter();
        iter.next().map(|first| {
            Term::try_disjunction(iter)
                .map(|rest| Term::compound(";", [first.clone(), rest]))
                .unwrap_or(first)
        })
    }
}

/// This is an auxiliary function to turn a count into names of anonymous variables like _A, _B,
/// _AB, etc...
fn count_to_letter_code(mut count: usize) -> String {
    let mut letters = Vec::new();

    loop {
        let letter_idx = (count % 26) as u32;
        letters.push(char::from_u32('A' as u32 + letter_idx).unwrap());
        count /= 26;

        if count == 0 {
            break;
        }
    }

    letters.into_iter().chain("_".chars()).rev().collect()
}

impl Term {
    pub(crate) fn from_heapcell(
        machine: &mut Machine,
        heap_cell: HeapCellValue,
        var_names: &mut IndexMap<HeapCellValue, Var>,
    ) -> Self {
        // Adapted from MachineState::read_term_from_heap
        let mut term_stack = vec![];

        machine.machine_st.heap[0] = heap_cell;

        let mut iter = stackful_post_order_iter::<NonListElider>(
            &mut machine.machine_st.heap,
            &mut machine.machine_st.stack,
            0,
        );

        let mut anon_count: usize = 0;

        while let Some(addr) = iter.next() {
            let addr = unmark_cell_bits!(addr);

            read_heap_cell!(addr,
                (HeapCellValueTag::Lis) => {
                    let tail = term_stack.pop().unwrap();
                    let head = term_stack.pop().unwrap();

                    let list = match tail {
                        Term::Atom(atom) if atom == "[]" => match head {
                            Term::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                Term::String(a.to_string())
                            }
                            _ => Term::List(vec![head]),
                        },
                        Term::List(elems) if elems.is_empty() => match head {
                            Term::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                Term::String(a.to_string())
                            },
                            _ => Term::List(vec![head]),
                        },
                        Term::List(mut elems) => {
                            elems.insert(0, head);
                            Term::List(elems)
                        },
                        Term::String(mut elems) => match head {
                            Term::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                elems.insert(0, a.chars().next().unwrap());
                                Term::String(elems)
                            },
                            _ => {
                                let mut elems: Vec<Term> = elems
                                    .chars()
                                    .map(|x| Term::Atom(x.into()))
                                    .collect();
                                elems.insert(0, head);
                                Term::List(elems)
                            }
                        },
                        _ => {
                            Term::Compound(".".into(), vec![head, tail])
                        }
                    };
                    term_stack.push(list);
                }
                (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                    let var = var_names.get(&addr).cloned();
                    match var {
                        Some(name) => term_stack.push(Term::Var(name.to_string())),
                        _ => {
                            let anon_name = loop {
                                // Generate a name for the anonymous variable
                                let anon_name = count_to_letter_code(anon_count);

                                // Find if this name is already being used
                                var_names.sort_by(|_, a, _, b| a.cmp(b));

                                let binary_result = var_names.binary_search_by(|_,a| {
                                    let a: &String = a.as_ref();
                                    a.cmp(&anon_name)
                                });

                                match binary_result {
                                    Ok(_) => anon_count += 1, // Name already used
                                    Err(_) => {
                                        // Name not used, assign it to this variable
                                        let var = anon_name.clone();
                                        var_names.insert(addr, Var::from(var));
                                        break anon_name;
                                    },
                                }
                            };
                            term_stack.push(Term::Var(anon_name));
                        },
                    }
                }
                (HeapCellValueTag::F64, f) => {
                    term_stack.push(Term::Float((*f).into()));
                }
                (HeapCellValueTag::Fixnum, n) => {
                    term_stack.push(Term::Integer(n.into()));
                }
                (HeapCellValueTag::Cons, ptr) => {
                    if let Ok(n) = Number::try_from(addr) {
                        match n {
                            Number::Integer(i) => term_stack.push(Term::Integer((*i).clone())),
                            Number::Rational(r) => term_stack.push(Term::Rational((*r).clone())),
                            _ => { unreachable!() },
                        }
                    } else {
                        match_untyped_arena_ptr!(ptr,
                            (ArenaHeaderTag::Stream, stream) => {
                                let stream_term = if let Some(alias) = stream.options().get_alias() {
                                    Term::atom(alias.as_str().to_string())
                                } else {
                                    Term::compound("$stream", [
                                        Term::integer(stream.as_ptr() as usize)
                                    ])
                                };
                                term_stack.push(stream_term);
                            }
                            (ArenaHeaderTag::Dropped, _stream) => {
                                term_stack.push(Term::atom("$dropped_value"));
                            }
                            _ => {
                                unreachable!();
                            }
                        );
                    }
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    //let h = iter.focus().value() as usize;
                    //let mut arity = arity;

                    // Not sure why/if this is needed.
                    // Might find out with better testing later.
                    /*
                    if iter.heap.len() > h + arity + 1 {
                        let value = iter.heap[h + arity + 1];

                        if let Some(idx) = get_structure_index(value) {
                            // in the second condition, arity == 0,
                            // meaning idx cannot pertain to this atom
                            // if it is the direct subterm of a larger
                            // structure.
                            if arity > 0 || !iter.direct_subterm_of_str(h) {
                                term_stack.push(
                                    Term::Literal(Cell::default(), Literal::CodeIndex(idx))
                                );

                                arity += 1;
                            }
                        }
                    }
                    */

                    if arity == 0 {
                        let atom_name = name.as_str().to_string();
                        if atom_name == "[]" {
                            term_stack.push(Term::List(vec![]));
                        } else {
                            term_stack.push(Term::Atom(atom_name));
                        }
                    } else {
                        let subterms = term_stack
                            .drain(term_stack.len() - arity ..)
                            .collect();

                        term_stack.push(Term::Compound(name.as_str().to_string(), subterms));
                    }
                }
                (HeapCellValueTag::PStrLoc, pstr_loc) => {
                    let tail = term_stack.pop().unwrap();
                    let char_iter = iter.base_iter.heap.char_iter(pstr_loc);

                    match tail {
                        Term::Atom(atom) => {
                            if atom == "[]" {
                                term_stack.push(Term::String(atom.as_str().to_string()));
                            }
                        },
                        Term::List(l) if l.is_empty() => {
                            term_stack.push(Term::String(char_iter.collect()));
                        }
                        Term::List(l) => {
                            let mut list: Vec<Term> = char_iter
                                .map(|x| Term::Atom(x.to_string()))
                                .collect();
                            list.extend(l.into_iter());
                            term_stack.push(Term::List(list));
                        },
                        _ => {
                            let mut list: Vec<Term> = char_iter
                                .map(|x| Term::Atom(x.to_string()))
                                .collect();

                            let mut partial_list = Term::Compound(
                                ".".into(),
                                vec![
                                    list.pop().unwrap(),
                                    tail,
                                ],
                            );

                            while let Some(last) = list.pop() {
                                partial_list = Term::Compound(
                                    ".".into(),
                                    vec![
                                        last,
                                        partial_list,
                                    ],
                                );
                            }

                            term_stack.push(partial_list);
                        }
                    }
                }
                _ => {
                    unreachable!();
                }
            );
        }

        debug_assert_eq!(term_stack.len(), 1);
        term_stack.pop().unwrap()
    }
}

/// An iterator though the leaf answers of a query.
pub struct QueryState<'a> {
    machine: &'a mut Machine,
    term: TermWriteResult,
    stub_b: usize,
    var_names: IndexMap<HeapCellValue, Var>,
    called: bool,
}

impl Drop for QueryState<'_> {
    fn drop(&mut self) {
        // FIXME: This may be wrong if the iterator is not fully consumend, but from testing it
        // seems fine. Is this really ok?
        self.machine.trust_me();
    }
}

impl Iterator for QueryState<'_> {
    type Item = Result<LeafAnswer, Term>;

    fn next(&mut self) -> Option<Self::Item> {
        let var_names = &mut self.var_names;
        let term_write_result = &self.term;
        let machine = &mut self.machine;

        // No more choicepoints, end iteration
        if self.called && machine.machine_st.b <= self.stub_b {
            return None;
        }

        machine.dispatch_loop();

        self.called = true;

        if !machine.machine_st.ball.stub.is_empty() {
            // NOTE: this means an exception was thrown, at which
            // point we backtracked to the stub choice point.
            // this should halt the search for solutions as it
            // does in the Scryer top-level. the exception term is
            // contained in self.machine_st.ball.
            let h = machine.machine_st.heap.cell_len();

            if let Err(resource_err_loc) = machine
                .machine_st
                .heap
                .append(machine.machine_st.ball.stub.splice(..))
            {
                return Some(Err(Term::from_heapcell(
                    machine,
                    machine.machine_st.heap[resource_err_loc],
                    &mut IndexMap::new(),
                )));
            }

            let exception_term =
                Term::from_heapcell(machine, machine.machine_st.heap[h], &mut var_names.clone());

            if let Term::Compound(functor, args) = &exception_term {
                if functor == "error" && args.len() == 2 {
                    // We have an error
                    return Some(Err(exception_term));
                }
            }

            // We have an exception that is not an error
            return Some(Ok(LeafAnswer::Exception(exception_term)));
        }

        if machine.machine_st.p == LIB_QUERY_SUCCESS {
            if term_write_result.inverse_var_locs.is_empty() {
                self.machine.machine_st.backtrack();
                return Some(Ok(LeafAnswer::True));
            }
        } else if machine.machine_st.p == BREAK_FROM_DISPATCH_LOOP_LOC {
            return Some(Ok(LeafAnswer::False));
        }

        let mut bindings: BTreeMap<String, Term> = BTreeMap::new();
        let inverse_var_locs = &term_write_result.inverse_var_locs;

        for (var_loc, var_name) in inverse_var_locs.iter() {
            if var_name.starts_with('_') {
                let should_print = var_names.values().any(|v| v == var_name);
                if !should_print {
                    continue;
                }
            }

            let var_loc = *var_loc;
            let term =
                Term::from_heapcell(machine, heap_loc_as_cell!(var_loc), &mut var_names.clone());

            if let Term::Var(ref term_str) = term {
                if *term_str == **var_name {
                    continue;
                }

                // inverse_var_locs is in the order things appear in
                // the query. If var_name appears after term in the
                // query, switch their places.
                let var_cell = machine
                    .machine_st
                    .store(machine.machine_st.deref(machine.machine_st.heap[var_loc]));

                if (var_cell.get_value() as usize) < var_loc {
                    bindings.insert(term_str.clone(), Term::Var(var_name.to_string()));
                    continue;
                }
            }

            bindings.insert(var_name.to_string(), term);
        }

        // NOTE: there are outstanding choicepoints, backtrack
        // through them for further solutions. if
        // self.machine_st.b == stub_b we've backtracked to the stub
        // choice point, so we should break.
        self.machine.machine_st.backtrack();

        Some(Ok(LeafAnswer::LeafAnswer { bindings }))
    }
}

impl Machine {
    /// Loads a module into the [`Machine`] from a string.
    pub fn load_module_string(&mut self, module_name: &str, program: impl Into<String>) {
        let stream = Stream::from_owned_string(program.into(), &mut self.machine_st.arena);
        self.load_file(module_name, stream);
    }

    /// Consults a module into the [`Machine`] from a string.
    pub fn consult_module_string(&mut self, module_name: &str, program: impl Into<String>) {
        let stream = Stream::from_owned_string(program.into(), &mut self.machine_st.arena);
        self.machine_st.registers[1] = stream.into();
        self.machine_st.registers[2] = atom_as_cell!(&atom_table::AtomTable::build_with(
            &self.machine_st.atom_tbl,
            module_name
        ));

        self.run_module_predicate(atom!("loader"), (atom!("consult_stream"), 2));
    }

    pub(crate) fn allocate_stub_choice_point(&mut self) {
        // NOTE: create a choice point to terminate the dispatch_loop
        // if an exception is thrown.

        let stub_b = self.machine_st.stack.allocate_or_frame(0);
        let or_frame = self.machine_st.stack.index_or_frame_mut(stub_b);

        or_frame.prelude.num_cells = 0;
        or_frame.prelude.e = 0;
        or_frame.prelude.cp = 0;
        or_frame.prelude.b = 0;
        or_frame.prelude.bp = BREAK_FROM_DISPATCH_LOOP_LOC;
        or_frame.prelude.boip = 0;
        or_frame.prelude.biip = 0;
        or_frame.prelude.tr = 0;
        or_frame.prelude.h = 0;
        or_frame.prelude.b0 = 0;
        or_frame.prelude.attr_var_queue_len = 0;

        self.machine_st.b = stub_b;
        self.machine_st.hb = self.machine_st.heap.cell_len();
        self.machine_st.block = stub_b;
    }

    /// Runs a query.
    pub fn run_query(&mut self, query: impl Into<String>) -> QueryState {
        let mut parser = LexerParser::new(
            Stream::from_owned_string(query.into(), &mut self.machine_st.arena),
            &mut self.machine_st,
        );
        let op_dir = CompositeOpDir::new(&self.indices.op_dir, None);
        let term = parser
            .read_term(&op_dir, Tokens::Default)
            .expect("Failed to parse query");

        self.allocate_stub_choice_point();

        // Write term to heap
        self.machine_st.registers[1] = self.machine_st.heap[term.focus];
        self.machine_st.cp = LIB_QUERY_SUCCESS; // BREAK_FROM_DISPATCH_LOOP_LOC;

        let call_index_p = self
            .indices
            .code_dir
            .get(&(atom!("call"), 1))
            .expect("couldn't get code index")
            .local()
            .unwrap();

        let var_names: IndexMap<_, _> = term
            .inverse_var_locs
            .iter()
            .map(|(var_loc, var)| {
                let cell = self.machine_st.heap[*var_loc];
                (cell, var.clone())
            })
            .collect();

        self.machine_st.execute_at_index(1, call_index_p);

        let stub_b = self.machine_st.b;

        QueryState {
            machine: self,
            term,
            stub_b,
            var_names,
            called: false,
        }
    }
}
