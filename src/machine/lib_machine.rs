use std::collections::BTreeMap;

use crate::atom_table;
use crate::machine::machine_indices::VarKey;
use crate::machine::mock_wam::CompositeOpDir;
use crate::machine::{BREAK_FROM_DISPATCH_LOOP_LOC, LIB_QUERY_SUCCESS};
use crate::parser::ast::{Var, VarPtr};
use crate::parser::parser::{Parser, Tokens};
use crate::read::{write_term_to_heap, TermWriteResult};
use indexmap::IndexMap;

use super::{
    streams::Stream, Atom, AtomCell, HeapCellValue, HeapCellValueTag, Machine, MachineConfig,
    QueryResolutionLine, QueryResult, Value,
};

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
    type Item = Result<QueryResolutionLine, String>;

    fn next(&mut self) -> Option<Self::Item> {
        let var_names = &self.var_names;
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
                return Some(Ok(QueryResolutionLine::True));
            }
        } else if machine.machine_st.p == BREAK_FROM_DISPATCH_LOOP_LOC {
            return Some(Ok(QueryResolutionLine::False));
        }

        let mut bindings: BTreeMap<String, Value> = BTreeMap::new();

        for (var_key, term_to_be_printed) in &term_write_result.var_dict {
            if var_key.to_string().starts_with('_') {
                continue;
            }

            let term = Value::from_heapcell(machine, *term_to_be_printed, var_names);

            if let Value::Var(ref term_str) = term {
                if *term_str == var_key.to_string() {
                    continue;
                }
            }

            bindings.insert(var_key.to_string(), term);
        }

        // NOTE: there are outstanding choicepoints, backtrack
        // through them for further solutions. if
        // self.machine_st.b == stub_b we've backtracked to the stub
        // choice point, so we should break.
        self.machine.machine_st.backtrack();

        Some(Ok(QueryResolutionLine::Match(bindings)))
    }
}

impl Machine {
    pub fn new_lib() -> Self {
        Machine::new(MachineConfig::in_memory())
    }

    pub fn load_module_string(&mut self, module_name: &str, program: String) {
        let stream = Stream::from_owned_string(program, &mut self.machine_st.arena);
        self.load_file(module_name, stream);
    }

    pub fn consult_module_string(&mut self, module_name: &str, program: String) {
        let stream = Stream::from_owned_string(program, &mut self.machine_st.arena);
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

    pub fn run_query(&mut self, query: String) -> QueryResult {
        self.run_query_iter(query).collect()
    }

    pub fn run_query_iter(&mut self, query: String) -> QueryState {
        let mut parser = Parser::new(
            Stream::from_owned_string(query, &mut self.machine_st.arena),
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
    use crate::machine::{QueryMatch, QueryResolution, Value};

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
                    "P" => Value::from("p1"),
                }),
                QueryMatch::from(btreemap! {
                    "P" => Value::from("p2"),
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
                    "C" => Value::Atom("c".into()),
                    "Actions" => Value::Atom("[{action: \"addLink\", source: \"this\", predicate: \"todo://state\", target: \"todo://ready\"}]".into()),
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
                    "C" => Value::Atom("xyz".into()),
                    "Actions" => Value::Atom("[{action: \"addLink\", source: \"this\", predicate: \"recipe://title\", target: \"literal://string:Meta%20Muffins\"}]".into()),
                }
            ),]))
        );

        let result = machine.run_query(String::from("subject_class(Class, _)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "Class" => Value::String("Todo".into())
                }),
                QueryMatch::from(btreemap! {
                    "Class" => Value::String("Recipe".into())
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
                    "X" => Value::List(vec![
                        Value::Integer(1.into()),
                        Value::Integer(2.into()),
                        Value::Integer(3.into()),
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
                    "P" => Value::from("p1"),
                }),
                QueryMatch::from(btreemap! {
                    "P" => Value::from("p2"),
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
                    "Result" => Value::List(
                        Vec::from([
                            Value::List([Value::from("p1"), Value::from("b")].into()),
                            Value::List([Value::from("p2"), Value::from("b")].into()),
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
                    "X" => Value::Atom(".".into()),
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
                    "X" => Value::Rational(RBig::from_parts(1.into(), 2u32.into())),
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
                    "X" => Value::Integer(IBig::from(10).pow(100)),
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

        let expected = Value::Structure(
            // Composite term
            "a".into(),
            vec![
                Value::String("asdf".into()), // String
                Value::List(vec![
                    Value::Integer(42.into()),  // Fixnum
                    Value::Float(2.54.into()),  // Float
                    Value::Atom("asdf".into()), // Atom
                    Value::Atom("a".into()),    // Char
                    Value::Structure(
                        // Partial string
                        ".".into(),
                        vec![
                            Value::Atom("a".into()),
                            Value::Structure(
                                ".".into(),
                                vec![
                                    Value::Atom("b".into()),
                                    Value::AnonVar, // Anonymous variable
                                ],
                            ),
                        ],
                    ),
                    Value::Var("Z".into()), // Named variable
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

            assert_eq!(iterator.next(), Some(Ok(QueryResolutionLine::False)));
            assert_eq!(iterator.next(), None);
        }

        {
            let mut iterator = machine.run_query_iter("false.".into());

            assert_eq!(iterator.next(), Some(Ok(QueryResolutionLine::False)));
            assert_eq!(iterator.next(), None);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn query_iterator_backtracking_when_no_variables() {
        let mut machine = Machine::new_lib();

        let mut iterator = machine.run_query_iter("true;false.".into());

        assert_eq!(iterator.next(), Some(Ok(QueryResolutionLine::True)));
        assert_eq!(iterator.next(), Some(Ok(QueryResolutionLine::False)));
        assert_eq!(iterator.next(), None);
    }
}
