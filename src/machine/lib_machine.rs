use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::atom_table;
use crate::heap_iter::{stackful_post_order_iter, NonListElider};
use crate::machine::machine_indices::VarKey;
use crate::machine::mock_wam::CompositeOpDir;
use crate::machine::{
    F64Offset, F64Ptr, Fixnum, Number, BREAK_FROM_DISPATCH_LOOP_LOC, LIB_QUERY_SUCCESS,
};
use crate::parser::ast::{Var, VarPtr};
use crate::parser::parser::{Parser, Tokens};
use crate::read::{write_term_to_heap, TermWriteResult};

use dashu::{Integer, Rational};
use indexmap::IndexMap;

use super::{streams::Stream, Atom, AtomCell, HeapCellValue, HeapCellValueTag, Machine};

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
    /// A leaf answer with bindings and residual goals.
    LeafAnswer {
        /// The bindings of variables in the query.
        ///
        /// Can be empty.
        bindings: BTreeMap<String, Term>,
        /// Residual goals.
        ///
        /// Can be empty.
        residual_goals: Vec<Term>,
    },
}

impl LeafAnswer {
    /// True if leaf answer failed.
    ///
    /// This gives [`false`] for exceptions.
    pub fn failed(&self) -> bool {
        matches!(self, LeafAnswer::False)
    }

    /// True if leaf answer may have succeeded.
    ///
    /// When a leaf answer has residual goals the success is conditional on the satisfiability of
    /// the contraints they represent. This gives [`false`] for exceptions.
    pub fn maybe_succeeded(&self) -> bool {
        matches!(self, LeafAnswer::True | LeafAnswer::LeafAnswer { .. })
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

impl From<LeafAnswer> for Term {
    fn from(value: LeafAnswer) -> Self {
        match value {
            LeafAnswer::True => Term::atom("true"),
            LeafAnswer::False => Term::atom("false"),
            LeafAnswer::Exception(inner) => match inner.clone() {
                Term::Compound(functor, args) if functor == "error" && args.len() == 2 => inner,
                _ => Term::compound("throw", [inner]),
            },
            LeafAnswer::LeafAnswer {
                bindings: _,
                residual_goals: _,
            } => {
                todo!()
            }
        }
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
        var_names: &mut IndexMap<HeapCellValue, VarPtr>,
    ) -> Self {
        // Adapted from MachineState::read_term_from_heap
        let mut term_stack = vec![];
        let iter = stackful_post_order_iter::<NonListElider>(
            &mut machine.machine_st.heap,
            &mut machine.machine_st.stack,
            heap_cell,
        );

        let mut anon_count: usize = 0;
        let var_ptr_cmp = |a, b| match a {
            Var::Named(name_a) => match b {
                Var::Named(name_b) => name_a.cmp(&name_b),
                _ => Ordering::Less,
            },
            _ => match b {
                Var::Named(_) => Ordering::Greater,
                _ => Ordering::Equal,
            },
        };

        for addr in iter {
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
                    let var = var_names.get(&addr).map(|x| x.borrow().clone());
                    match var {
                        Some(Var::Named(name)) => term_stack.push(Term::Var(name)),
                        _ => {
                            let anon_name = loop {
                                // Generate a name for the anonymous variable
                                let anon_name = count_to_letter_code(anon_count);

                                // Find if this name is already being used
                                var_names.sort_by(|_, a, _, b| {
                                    var_ptr_cmp(a.borrow().clone(), b.borrow().clone())
                                });
                                let binary_result = var_names.binary_search_by(|_,a| {
                                    let var_ptr = Var::Named(anon_name.clone());
                                    var_ptr_cmp(a.borrow().clone(), var_ptr.clone())
                                });

                                match binary_result {
                                    Ok(_) => anon_count += 1, // Name already used
                                    Err(_) => {
                                        // Name not used, assign it to this variable
                                        let var_ptr = VarPtr::from(Var::Named(anon_name.clone()));
                                        var_names.insert(addr, var_ptr);
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
                (HeapCellValueTag::Char, c) => {
                    term_stack.push(Term::Atom(c.into()));
                }
                (HeapCellValueTag::Fixnum, n) => {
                    term_stack.push(Term::Integer(n.into()));
                }
                (HeapCellValueTag::Cons) => {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(i)) => term_stack.push(Term::Integer((*i).clone())),
                        Ok(Number::Rational(r)) => term_stack.push(Term::Rational((*r).clone())),
                        _ => {}
                    }
                }
                (HeapCellValueTag::CStr, s) => {
                    term_stack.push(Term::String(s.as_str().to_string()));
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
                (HeapCellValueTag::PStr, atom) => {
                    let tail = term_stack.pop().unwrap();

                    match tail {
                        Term::Atom(atom) => {
                            if atom == "[]" {
                                term_stack.push(Term::String(atom.as_str().to_string()));
                            }
                        },
                        Term::List(l) => {
                            let mut list: Vec<Term> = atom
                                .as_str()
                                .to_string()
                                .chars()
                                .map(|x| Term::Atom(x.to_string()))
                                .collect();
                            list.extend(l.into_iter());
                            term_stack.push(Term::List(list));
                        },
                        _ => {
                            let mut list: Vec<Term> = atom
                                .as_str()
                                .to_string()
                                .chars()
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
                // I dont know if this is needed here.
                /*
                (HeapCellValueTag::PStrLoc, h) => {
                    let atom = cell_as_atom_cell!(iter.heap[h]).get_name();
                    let tail = term_stack.pop().unwrap();

                    term_stack.push(Term::PartialString(
                        Cell::default(),
                        atom.as_str().to_owned(),
                        Box::new(tail),
                    ));
                }
                */
                _ => {
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
    var_names: IndexMap<HeapCellValue, VarPtr>,
    called: bool,
}

impl Drop for QueryState<'_> {
    fn drop(&mut self) {
        // This may be wrong if the iterator is not fully consumend, but from testing it seems
        // fine.
        self.machine.trust_me();
    }
}

impl Iterator for QueryState<'_> {
    type Item = Result<LeafAnswer, String>;

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
            let error_string = self
                .machine
                .machine_st
                .ball
                .stub
                .iter()
                .filter(|h| {
                    matches!(
                        h.get_tag(),
                        HeapCellValueTag::Atom | HeapCellValueTag::Fixnum
                    )
                })
                .map(|h| match h.get_tag() {
                    HeapCellValueTag::Atom => {
                        let (name, _) = cell_as_atom_cell!(h).get_name_and_arity();
                        name.as_str().to_string()
                    }
                    HeapCellValueTag::Fixnum => h.get_value().clone().to_string(),
                    _ => unreachable!(),
                })
                .collect::<Vec<String>>()
                .join(" ");

            return Some(Err(error_string));
        }

        if machine.machine_st.p == LIB_QUERY_SUCCESS {
            if term_write_result.var_dict.is_empty() {
                self.machine.machine_st.backtrack();
                return Some(Ok(LeafAnswer::True));
            }
        } else if machine.machine_st.p == BREAK_FROM_DISPATCH_LOOP_LOC {
            return Some(Ok(LeafAnswer::False));
        }

        let mut bindings: BTreeMap<String, Term> = BTreeMap::new();

        let var_dict = &term_write_result.var_dict;

        for (var_key, term_to_be_printed) in var_dict.iter() {
            let mut var_name = var_key.to_string();
            if var_name.starts_with('_') {
                let should_print = var_names.values().any(|x| match x.borrow().clone() {
                    Var::Named(v) => v == var_name,
                    _ => false,
                });
                if !should_print {
                    continue;
                }
            }

            let mut term =
                Term::from_heapcell(machine, *term_to_be_printed, &mut var_names.clone());

            if let Term::Var(ref term_str) = term {
                if *term_str == var_name {
                    continue;
                }

                // Var dict is in the order things appear in the query. If var_name appears
                // after term in the query, switch their places.
                let var_name_idx = var_dict
                    .get_index_of(&VarKey::VarPtr(Var::Named(var_name.clone()).into()))
                    .unwrap();
                let term_idx =
                    var_dict.get_index_of(&VarKey::VarPtr(Var::Named(term_str.clone()).into()));
                if let Some(idx) = term_idx {
                    if idx < var_name_idx {
                        let new_term = Term::Var(var_name);
                        let new_var_name = term_str.into();
                        term = new_term;
                        var_name = new_var_name;
                    }
                }
            }

            bindings.insert(var_name, term);
        }

        // NOTE: there are outstanding choicepoints, backtrack
        // through them for further solutions. if
        // self.machine_st.b == stub_b we've backtracked to the stub
        // choice point, so we should break.
        self.machine.machine_st.backtrack();

        Some(Ok(LeafAnswer::LeafAnswer {
            bindings,
            residual_goals: vec![],
        }))
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
        self.machine_st.registers[1] = stream_as_cell!(stream);
        self.machine_st.registers[2] = atom_as_cell!(&atom_table::AtomTable::build_with(
            &self.machine_st.atom_tbl,
            module_name
        ));

        self.run_module_predicate(atom!("loader"), (atom!("consult_stream"), 2));
    }

    fn allocate_stub_choice_point(&mut self) {
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
        self.machine_st.hb = self.machine_st.heap.len();
        self.machine_st.block = stub_b;
    }

    /// Runs a query.
    pub fn run_query(&mut self, query: impl Into<String>) -> QueryState {
        let mut parser = Parser::new(
            Stream::from_owned_string(query.into(), &mut self.machine_st.arena),
            &mut self.machine_st,
        );
        let op_dir = CompositeOpDir::new(&self.indices.op_dir, None);
        let term = parser
            .read_term(&op_dir, Tokens::Default)
            .expect("Failed to parse query");

        self.allocate_stub_choice_point();

        // Write parsed term to heap
        let term_write_result =
            write_term_to_heap(&term, &mut self.machine_st.heap, &self.machine_st.atom_tbl)
                .expect("couldn't write term to heap");

        let var_names: IndexMap<_, _> = term_write_result
            .var_dict
            .iter()
            .map(|(var_key, cell)| match var_key {
                // NOTE: not the intention behind Var::InSitu here but
                // we can hijack it to store anonymous variables
                // without creating problems.
                VarKey::AnonVar(h) => (*cell, VarPtr::from(Var::InSitu(*h))),
                VarKey::VarPtr(var_ptr) => (*cell, var_ptr.clone()),
            })
            .collect();

        // Write term to heap
        self.machine_st.registers[1] = self.machine_st.heap[term_write_result.heap_loc];

        self.machine_st.cp = LIB_QUERY_SUCCESS; // BREAK_FROM_DISPATCH_LOOP_LOC;
        let call_index_p = self
            .indices
            .code_dir
            .get(&(atom!("call"), 1))
            .expect("couldn't get code index")
            .local()
            .unwrap();

        self.machine_st.execute_at_index(1, call_index_p);

        let stub_b = self.machine_st.b;
        QueryState {
            machine: self,
            term: term_write_result,
            stub_b,
            var_names,
            called: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{QueryMatch, QueryResolution, Term};

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn programatic_query() {
        let mut machine = Machine::new_lib();

        machine.load_module_string(
            "facts",
            String::from(
                r#"
                triple("a", "p1", "b").
                triple("a", "p2", "b").
                "#,
            ),
        );

        let query = String::from(r#"triple("a",P,"b")."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "P" => Term::from("p1"),
                }),
                QueryMatch::from(btreemap! {
                    "P" => Term::from("p2"),
                }),
            ]))
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("a","p1","b")."#)),
            Ok(QueryResolution::True)
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("x","y","z")."#)),
            Ok(QueryResolution::False)
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn failing_query() {
        let mut machine = Machine::new_lib();
        let query = String::from(r#"triple("a",P,"b")."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Err(String::from(
                "error existence_error procedure / triple 3 / triple 3"
            ))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn complex_results() {
        let mut machine = Machine::new_lib();
        machine.load_module_string(
            "facts",
            r#"
            :- discontiguous(subject_class/2).
            :- discontiguous(constructor/2).

            subject_class("Todo", c).
            constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').

            subject_class("Recipe", xyz).
            constructor(xyz, '[{action: "addLink", source: "this", predicate: "recipe://title", target: "literal://string:Meta%20Muffins"}]').
            "#.to_string());

        let result = machine.run_query(String::from(
            "subject_class(\"Todo\", C), constructor(C, Actions).",
        ));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "C" => Term::Atom("c".into()),
                    "Actions" => Term::Atom("[{action: \"addLink\", source: \"this\", predicate: \"todo://state\", target: \"todo://ready\"}]".into()),
                }
            ),]))
        );

        let result = machine.run_query(String::from(
            "subject_class(\"Recipe\", C), constructor(C, Actions).",
        ));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "C" => Term::Atom("xyz".into()),
                    "Actions" => Term::Atom("[{action: \"addLink\", source: \"this\", predicate: \"recipe://title\", target: \"literal://string:Meta%20Muffins\"}]".into()),
                }
            ),]))
        );

        let result = machine.run_query(String::from("subject_class(Class, _)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "Class" => Term::String("Todo".into())
                }),
                QueryMatch::from(btreemap! {
                    "Class" => Term::String("Recipe".into())
                }),
            ]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn empty_predicate() {
        let mut machine = Machine::new_lib();
        machine.load_module_string(
            "facts",
            r#"
            :- discontiguous(subject_class/2).
            "#
            .to_string(),
        );

        let result = machine.run_query(String::from("subject_class(X, _)."));
        assert_eq!(result, Ok(QueryResolution::False));
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn list_results() {
        let mut machine = Machine::new_lib();
        machine.load_module_string(
            "facts",
            r#"
            list([1,2,3]).
            "#
            .to_string(),
        );

        let result = machine.run_query(String::from("list(X)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => Term::List(vec![
                        Term::Integer(1.into()),
                        Term::Integer(2.into()),
                        Term::Integer(3.into()),
                    ]),
                }
            ),]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn consult() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                triple("a", "p1", "b").
                triple("a", "p2", "b").
                "#,
            ),
        );

        let query = String::from(r#"triple("a",P,"b")."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "P" => Term::from("p1"),
                }),
                QueryMatch::from(btreemap! {
                    "P" => Term::from("p2"),
                }),
            ]))
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("a","p1","b")."#)),
            Ok(QueryResolution::True)
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("x","y","z")."#)),
            Ok(QueryResolution::False)
        );

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                triple("a", "new", "b").
                "#,
            ),
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("a","p1","b")."#)),
            Ok(QueryResolution::False)
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("a","new","b")."#)),
            Ok(QueryResolution::True)
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    #[ignore = "uses old flawed interface"]
    fn integration_test() {
        let mut machine = Machine::new_lib();

        // File with test commands, i.e. program code to consult and queries to run
        let code = include_str!("./lib_integration_test_commands.txt");

        // Split the code into blocks
        let blocks = code.split("=====");

        let mut i = 0;
        let mut last_result: Option<_> = None;
        // Iterate over the blocks
        for block in blocks {
            // Trim the block to remove any leading or trailing whitespace
            let block = block.trim();

            // Skip empty blocks
            if block.is_empty() {
                continue;
            }

            // Check if the block is a query
            if let Some(query) = block.strip_prefix("query") {
                // Parse and execute the query
                let result = machine.run_query(query.to_string());
                assert!(result.is_ok());

                last_result = Some(result);
            } else if let Some(code) = block.strip_prefix("consult") {
                // Load the code into the machine
                machine.consult_module_string("facts", code.to_string());
            } else if let Some(result) = block.strip_prefix("result") {
                i += 1;
                if let Some(Ok(ref last_result)) = last_result {
                    println!("\n\n=====Result No. {i}=======\n{last_result}\n===============");
                    assert_eq!(last_result.to_string(), result.to_string().trim(),)
                }
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn findall() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                triple("a", "p1", "b").
                triple("a", "p2", "b").
                "#,
            ),
        );

        let query =
            String::from(r#"findall([Predicate, Target], triple(_,Predicate,Target), Result)."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "Result" => Term::List(
                        Vec::from([
                            Term::List([Term::from("p1"), Term::from("b")].into()),
                            Term::List([Term::from("p2"), Term::from("b")].into()),
                        ])
                    ),
                }
            ),]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn dont_return_partial_matches() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                :- discontiguous(property_resolve/2).
                subject_class("Todo", c).
                "#,
            ),
        );

        let query = String::from(r#"property_resolve(C, "isLiked"), subject_class("Todo", C)."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::False));

        let query = String::from(r#"subject_class("Todo", C), property_resolve(C, "isLiked")."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::False));
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn dont_return_partial_matches_without_discountiguous() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                a("true for a").
                b("true for b").
                "#,
            ),
        );

        let query = String::from(r#"a("true for a")."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::True));

        let query = String::from(r#"a("true for a"), b("true for b")."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::True));

        let query = String::from(r#"a("true for b"), b("true for b")."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::False));

        let query = String::from(r#"a("true for a"), b("true for a")."#);
        let output = machine.run_query(query);
        assert_eq!(output, Ok(QueryResolution::False));
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn non_existent_predicate_should_not_cause_panic_when_other_predicates_are_defined() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                triple("a", "p1", "b").
                triple("a", "p2", "b").
                "#,
            ),
        );

        let query = String::from("non_existent_predicate(\"a\",\"p1\",\"b\").");

        let result = machine.run_query(query);

        assert_eq!(
            result,
            Err(String::from("error existence_error procedure / non_existent_predicate 3 / non_existent_predicate 3"))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn atom_quoting() {
        let mut machine = Machine::new_lib();

        let query = "X = '.'.".into();

        let result = machine.run_query(query);

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => Term::Atom(".".into()),
                }
            )]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn rational_number() {
        use crate::parser::dashu::rational::RBig;
        let mut machine = Machine::new_lib();

        let query = "X is 1 rdiv 2.".into();

        let result = machine.run_query(query);

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => Term::Rational(RBig::from_parts(1.into(), 2u32.into())),
                }
            )]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn big_integer() {
        use crate::parser::dashu::integer::IBig;
        let mut machine = Machine::new_lib();

        let query = "X is 10^100.".into();

        let result = machine.run_query(query);

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => Term::Integer(IBig::from(10).pow(100)),
                }
            )]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn complicated_term() {
        let mut machine = Machine::new_lib();

        let query = "X = a(\"asdf\", [42, 2.54, asdf, a, [a,b|_], Z]).".into();

        let result = machine.run_query(query);

        let expected = Term::Structure(
            // Composite term
            "a".into(),
            vec![
                Term::String("asdf".into()), // String
                Term::List(vec![
                    Term::Integer(42.into()),  // Fixnum
                    Term::Float(2.54.into()),  // Float
                    Term::Atom("asdf".into()), // Atom
                    Term::Atom("a".into()),    // Char
                    Term::Structure(
                        // Partial string
                        ".".into(),
                        vec![
                            Term::Atom("a".into()),
                            Term::Structure(
                                ".".into(),
                                vec![
                                    Term::Atom("b".into()),
                                    Term::Var("_A".into()), // Anonymous variable
                                ],
                            ),
                        ],
                    ),
                    Term::Var("Z".into()), // Named variable
                ]),
            ],
        );

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => expected,
                }
            )]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "it takes too long to run")]
    fn issue_2341() {
        let mut machine = Machine::new_lib();

        machine.load_module_string(
            "facts",
            String::from(
                r#"
                male(stephen).
                parent(albert,edward).
                father(F,C):-parent(F,C),male(F).
                "#,
            ),
        );

        let query = String::from(r#"father(F,C)."#);
        let output = machine.run_query(query);

        assert_eq!(output, Ok(QueryResolution::False));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn query_iterator_determinism() {
        let mut machine = Machine::new_lib();

        {
            let mut iterator = machine.run_query_iter("X = 1.".into());

            iterator.next();
            assert_eq!(iterator.next(), None);
        }

        {
            let mut iterator = machine.run_query_iter("X = 1 ; false.".into());

            iterator.next();

            assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
            assert_eq!(iterator.next(), None);
        }

        {
            let mut iterator = machine.run_query_iter("false.".into());

            assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
            assert_eq!(iterator.next(), None);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn query_iterator_backtracking_when_no_variables() {
        let mut machine = Machine::new_lib();

        let mut iterator = machine.run_query_iter("true;false.".into());

        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::True)));
        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn differentiate_anonymous_variables() {
        let mut machine = Machine::new_lib();

        let result = machine.run_query("A = [_,_], _B = 1 ; B = [_,_].".into());

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "A" => Term::List(vec![Term::Var("_A".into()), Term::Var("_C".into())]),
                    "_B" => Term::Integer(1.into()),
                }),
                QueryMatch::from(btreemap! {
                    "B" => Term::List(vec![Term::Var("_A".into()), Term::Var("_C".into())]),
                }),
            ]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn order_of_variables_in_binding() {
        let mut machine = Machine::new_lib();

        let result = machine.run_query("X = Y, Z = W.".into());

        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![QueryMatch::from(
                btreemap! {
                    "X" => Term::Var("Y".into()),
                    "Z" => Term::Var("W".into()),
                }
            ),]))
        );
    }
}
