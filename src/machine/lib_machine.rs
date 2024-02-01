use std::collections::BTreeMap;
use std::sync::Arc;

use crate::atom_table;
use crate::heap_print::{HCPrinter, HCValueOutputter, PrinterOutputter};
use crate::machine::machine_indices::VarKey;
use crate::machine::mock_wam::CompositeOpDir;
use crate::machine::{BREAK_FROM_DISPATCH_LOOP_LOC, LIB_QUERY_SUCCESS};
use crate::parser::ast::{Var, VarPtr};
use crate::parser::parser::{Parser, Tokens};
use crate::read::write_term_to_heap;
use indexmap::IndexMap;

use super::{
    streams::Stream, Atom, AtomCell, HeapCellValue, HeapCellValueTag, Machine, MachineConfig,
    QueryResolution, QueryResolutionLine, QueryResult, Value,
};

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
    }

    pub fn run_query(&mut self, query: String) -> QueryResult {
        // println!("Query: {}", query);
        // Parse the query so we can analyze and then call the term
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

        let mut matches: Vec<QueryResolutionLine> = Vec::new();
        // Call the term
        loop {
            self.dispatch_loop();

            //println!("b: {}", self.machine_st.b);
            //println!("stub_b: {}", stub_b);
            //println!("fail: {}", self.machine_st.fail);

            if !self.machine_st.ball.stub.is_empty() {
                // NOTE: this means an exception was thrown, at which
                // point we backtracked to the stub choice point.
                // this should halt the search for solutions as it
                // does in the Scryer top-level. the exception term is
                // contained in self.machine_st.ball.
                let error_string = self
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

                return Err(error_string);
            }

            /*
            if self.machine_st.fail {
                // NOTE: only print results on success
                self.machine_st.fail = false;
                println!("fail!");
                matches.push(QueryResolutionLine::False);
                break;
            };
            */

            if self.machine_st.p == LIB_QUERY_SUCCESS {
                if term_write_result.var_dict.is_empty() {
                    matches.push(QueryResolutionLine::True);
                    break;
                }
            } else if self.machine_st.p == BREAK_FROM_DISPATCH_LOOP_LOC {
                // NOTE: only print results on success
                // self.machine_st.fail = false;
                // println!("b == stub_b");
                matches.push(QueryResolutionLine::False);
                break;
            }

            let mut bindings: BTreeMap<String, Value> = BTreeMap::new();

            for (var_key, term_to_be_printed) in &term_write_result.var_dict {
                if var_key.to_string().starts_with('_') {
                    continue;
                }
                let mut printer = HCPrinter::new(
                    &mut self.machine_st.heap,
                    Arc::clone(&self.machine_st.atom_tbl),
                    &mut self.machine_st.stack,
                    &self.indices.op_dir,
                    PrinterOutputter::new(),
                    *term_to_be_printed,
                );

                printer.ignore_ops = false;
                printer.numbervars = true;
                printer.quoted = true;
                printer.max_depth = 1000; // NOTE: set this to 0 for unbounded depth
                printer.double_quotes = true;
                printer.var_names = var_names.clone();

                let outputter = printer.print();

                let output: String = outputter.result();
                // println!("Result: {} = {}", var_key.to_string(), output);

                if var_key.to_string() != output {
                    bindings.insert(
                        var_key.to_string(),
                        Value::try_from(output).expect("Couldn't convert Houtput to Value"),
                    );
                }
            }

            matches.push(QueryResolutionLine::Match(bindings));

            // NOTE: there are outstanding choicepoints, backtrack
            // through them for further solutions. if
            // self.machine_st.b == stub_b we've backtracked to the stub
            // choice point, so we should break.
            self.machine_st.backtrack();

            if self.machine_st.b <= stub_b {
                // NOTE: out of choicepoints to backtrack through, no
                // more solutions to gather.
                break;
            }
        }

        // NOTE: deallocate stub choice point
        if self.machine_st.b == stub_b {
            self.trust_me();
        }

        Ok(QueryResolution::from(matches))
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    use super::*;
    use crate::machine::{QueryMatch, QueryResolution, Value};

    #[test]
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    #[cfg_attr(miri, ignore)]
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
                    "C" => Value::from("c"),
                    "Actions" => Value::from("[{action: \"addLink\", source: \"this\", predicate: \"todo://state\", target: \"todo://ready\"}]"),
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
                    "C" => Value::from("xyz"),
                    "Actions" => Value::from("[{action: \"addLink\", source: \"this\", predicate: \"recipe://title\", target: \"literal://string:Meta%20Muffins\"}]"),
                }
            ),]))
        );

        let result = machine.run_query(String::from("subject_class(Class, _)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "Class" => Value::from("Todo")
                }),
                QueryMatch::from(btreemap! {
                    "Class" => Value::from("Recipe")
                }),
            ]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
                    "X" => Value::List(
                        Vec::from([
                            Value::Float(OrderedFloat::from(1.0)),
                            Value::Float(OrderedFloat::from(2.0)),
                            Value::Float(OrderedFloat::from(3.0))
                        ])
                    )
                }
            ),]))
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
                    println!(
                        "\n\n=====Result No. {}=======\n{}\n===============",
                        i,
                        last_result.to_string().trim()
                    );
                    assert_eq!(last_result.to_string().trim(), result.to_string().trim(),)
                }
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore = "blocked on streams.rs UB")]
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
    fn replicate_failing_assertion_from_integration_test() {
        let mut machine = Machine::new_lib();

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
            :- discontiguous(triple/3).
:- discontiguous(link/5).
:- discontiguous(reachable/2).
reachable(A,B) :- triple(A,_,B).
reachable(A,B) :- triple(A,_,X), reachable(X,B).
:- discontiguous(hiddenExpression/1).
:- discontiguous(languageAddress/2).
:- discontiguous(languageName/2).
:- discontiguous(expressionAddress/2).
:- discontiguous(register_sdna_flow/2).
:- discontiguous(flowable/2).
:- discontiguous(flow_state/3).
:- discontiguous(start_action/2).
:- discontiguous(action/4).
:- discontiguous(subject_class/2).
:- discontiguous(constructor/2).
:- discontiguous(destructor/2).
:- discontiguous(instance/2).
:- discontiguous(property/2).
:- discontiguous(property_getter/4).
:- discontiguous(property_setter/3).
:- discontiguous(property_resolve/2).
:- discontiguous(property_resolve_language/3).
:- discontiguous(property_named_option/4).
:- discontiguous(collection/2).
:- discontiguous(collection_getter/4).
:- discontiguous(collection_setter/3).
:- discontiguous(collection_remover/3).
:- discontiguous(collection_adder/3).
:- discontiguous(p3_class_icon/2).
:- discontiguous(p3_class_color/2).
:- discontiguous(p3_instance_color/3).
"#,
            ),
        );

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                :- discontiguous(triple/3).
:- discontiguous(link/5).
triple("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
link("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", 1706199296474, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
:- discontiguous(reachable/2).
reachable(A,B) :- triple(A,_,B).
reachable(A,B) :- triple(A,_,X), reachable(X,B).
:- discontiguous(hiddenExpression/1).
:- discontiguous(languageAddress/2).
languageAddress("literal://string:Todo", "literal").
languageAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
:- discontiguous(languageName/2).
languageName("literal://string:Todo", "literal").
languageName("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
:- discontiguous(expressionAddress/2).
expressionAddress("literal://string:Todo", "string:Todo").
expressionAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
:- discontiguous(register_sdna_flow/2).
:- discontiguous(flowable/2).
:- discontiguous(flow_state/3).
:- discontiguous(start_action/2).
:- discontiguous(action/4).
:- discontiguous(subject_class/2).
:- discontiguous(constructor/2).
:- discontiguous(destructor/2).
:- discontiguous(instance/2).
:- discontiguous(property/2).
:- discontiguous(property_getter/4).
:- discontiguous(property_setter/3).
:- discontiguous(property_resolve/2).
:- discontiguous(property_resolve_language/3).
:- discontiguous(property_named_option/4).
:- discontiguous(collection/2).
:- discontiguous(collection_getter/4).
:- discontiguous(collection_setter/3).
:- discontiguous(collection_remover/3).
:- discontiguous(collection_adder/3).
:- discontiguous(p3_class_icon/2).
:- discontiguous(p3_class_color/2).
:- discontiguous(p3_instance_color/3).
:- use_module(library(lists)).
subject_class("Todo", c).
constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').
instance(c, Base) :- triple(Base, "todo://state", _).

destructor(c, '[{action: "removeLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').

property(c, "state").
property_getter(c, Base, "state", Value) :- triple(Base, "todo://state", Value).
property_setter(c, "state", '[{action: "setSingleTarget", source: "this", predicate: "todo://state", target: "value"}]').

property(c, "title").
property_resolve(c, "title").
property_resolve_language(c, "title", "literal").
property_getter(c, Base, "title", Value) :- triple(Base, "todo://has_title", Value).
property_setter(c, "title", '[{action: "setSingleTarget", source: "this", predicate: "todo://has_title", target: "value"}]').

property(c, "isLiked").
property_getter(c, Base, "isLiked", Value) :- triple(Base, "flux://has_reaction", "flux://thumbsup"), Value = true.

collection(c, "comments").
collection_getter(c, Base, "comments", List) :- findall(C, triple(Base, "todo://comment", C), List).
collection_adder(c, "commentss", '[{action: "addLink", source: "this", predicate: "todo://comment", target: "value"}]').
collection_remover(c, "commentss", '[{action: "removeLink", source: "this", predicate: "todo://comment", target: "value"}]').
collection_setter(c, "commentss", '[{action: "collectionSetter", source: "this", predicate: "todo://comment", target: "value"}]').

collection(c, "entries").
collection_getter(c, Base, "entries", List) :- findall(C, triple(Base, "flux://entry_type", C), List).
collection_adder(c, "entriess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_remover(c, "entriess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_setter(c, "entriess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').

collection(c, "messages").
collection_getter(c, Base, "messages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), instance(OtherClass, Target), subject_class("Message", OtherClass)), List).
collection_adder(c, "messagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_remover(c, "messagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_setter(c, "messagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').

collection(c, "likedMessages").
collection_getter(c, Base, "likedMessages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), triple(Target, "flux://has_reaction", "flux://thumbsup")), List).
collection_adder(c, "likedMessagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_remover(c, "likedMessagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
collection_setter(c, "likedMessagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
"#,
            ),
        );

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                :- discontiguous(triple/3).
                :- discontiguous(link/5).
                triple("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
                triple("literal://string:construct%20test", "todo://state", "todo://ready").
                link("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", 1706199296474, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
                link("literal://string:construct%20test", "todo://state", "todo://ready", 1706199296530, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
                :- discontiguous(reachable/2).
                reachable(A,B) :- triple(A,_,B).
                reachable(A,B) :- triple(A,_,X), reachable(X,B).
                :- discontiguous(hiddenExpression/1).
                :- discontiguous(languageAddress/2).
                languageAddress("literal://string:Todo", "literal").
                languageAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
                languageAddress("literal://string:construct%20test", "literal").
                :- discontiguous(languageName/2).
                languageName("literal://string:Todo", "literal").
                languageName("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
                languageName("literal://string:construct%20test", "literal").
                :- discontiguous(expressionAddress/2).
                expressionAddress("literal://string:Todo", "string:Todo").
                expressionAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
                expressionAddress("literal://string:construct%20test", "string:construct%20test").
                :- discontiguous(register_sdna_flow/2).
                :- discontiguous(flowable/2).
                :- discontiguous(flow_state/3).
                :- discontiguous(start_action/2).
                :- discontiguous(action/4).
                :- discontiguous(subject_class/2).
                :- discontiguous(constructor/2).
                :- discontiguous(destructor/2).
                :- discontiguous(instance/2).
                :- discontiguous(property/2).
                :- discontiguous(property_getter/4).
                :- discontiguous(property_setter/3).
                :- discontiguous(property_resolve/2).
                :- discontiguous(property_resolve_language/3).
                :- discontiguous(property_named_option/4).
                :- discontiguous(collection/2).
                :- discontiguous(collection_getter/4).
                :- discontiguous(collection_setter/3).
                :- discontiguous(collection_remover/3).
                :- discontiguous(collection_adder/3).
                :- discontiguous(p3_class_icon/2).
                :- discontiguous(p3_class_color/2).
                :- discontiguous(p3_instance_color/3).
                :- use_module(library(lists)).
                subject_class("Todo", c).
                constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').
                instance(c, Base) :- triple(Base, "todo://state", _).
                
                destructor(c, '[{action: "removeLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').
                
                property(c, "state").
                property_getter(c, Base, "state", Value) :- triple(Base, "todo://state", Value).
                property_setter(c, "state", '[{action: "setSingleTarget", source: "this", predicate: "todo://state", target: "value"}]').
                
                property(c, "title").
                property_resolve(c, "title").
                property_resolve_language(c, "title", "literal").
                property_getter(c, Base, "title", Value) :- triple(Base, "todo://has_title", Value).
                property_setter(c, "title", '[{action: "setSingleTarget", source: "this", predicate: "todo://has_title", target: "value"}]').
                
                property(c, "isLiked").
                property_getter(c, Base, "isLiked", Value) :- triple(Base, "flux://has_reaction", "flux://thumbsup"), Value = true.
                
                collection(c, "comments").
                collection_getter(c, Base, "comments", List) :- findall(C, triple(Base, "todo://comment", C), List).
                collection_adder(c, "commentss", '[{action: "addLink", source: "this", predicate: "todo://comment", target: "value"}]').
                collection_remover(c, "commentss", '[{action: "removeLink", source: "this", predicate: "todo://comment", target: "value"}]').
                collection_setter(c, "commentss", '[{action: "collectionSetter", source: "this", predicate: "todo://comment", target: "value"}]').
                
                collection(c, "entries").
                collection_getter(c, Base, "entries", List) :- findall(C, triple(Base, "flux://entry_type", C), List).
                collection_adder(c, "entriess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "entriess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "entriess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
                collection(c, "messages").
                collection_getter(c, Base, "messages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), instance(OtherClass, Target), subject_class("Message", OtherClass)), List).
                collection_adder(c, "messagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "messagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "messagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
                collection(c, "likedMessages").
                collection_getter(c, Base, "likedMessages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), triple(Target, "flux://has_reaction", "flux://thumbsup")), List).
                collection_adder(c, "likedMessagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "likedMessagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "likedMessagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
        "#));

        machine.consult_module_string(
            "facts",
            String::from(
                r#"
                :- discontiguous(triple/3).
                :- discontiguous(link/5).
                triple("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
                triple("literal://string:construct%20test", "todo://state", "todo://ready").
                triple("literal://string:get%20proxy%20test", "todo://state", "todo://ready").
                link("literal://string:Todo", "ad4m://sdna", "literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", 1706199296474, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
                link("literal://string:construct%20test", "todo://state", "todo://ready", 1706199296530, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
                link("literal://string:get%20proxy%20test", "todo://state", "todo://ready", 1706199296724, "did:key:z6Mkoszv7RVeQjbDkHb2R7CYtvdMYc2Po8GqAmR1W6zizp7K").
                :- discontiguous(reachable/2).
                reachable(A,B) :- triple(A,_,B).
                reachable(A,B) :- triple(A,_,X), reachable(X,B).
                :- discontiguous(hiddenExpression/1).
                :- discontiguous(languageAddress/2).
                languageAddress("literal://string:Todo", "literal").
                languageAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
                languageAddress("literal://string:construct%20test", "literal").
                languageAddress("literal://string:get%20proxy%20test", "literal").
                :- discontiguous(languageName/2).
                languageName("literal://string:Todo", "literal").
                languageName("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "literal").
                languageName("literal://string:construct%20test", "literal").
                languageName("literal://string:get%20proxy%20test", "literal").
                :- discontiguous(expressionAddress/2).
                expressionAddress("literal://string:Todo", "string:Todo").
                expressionAddress("literal://string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A", "string:subject_class%28%22Todo%22%2C%20c%29.%0Aconstructor%28c%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0Ainstance%28c%2C%20Base%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20_%29.%0A%0Adestructor%28c%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22todo%3A%2F%2Fready%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22state%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22state%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fstate%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22state%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fstate%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22title%22%29.%0Aproperty_resolve%28c%2C%20%22title%22%29.%0Aproperty_resolve_language%28c%2C%20%22title%22%2C%20%22literal%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22title%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22todo%3A%2F%2Fhas_title%22%2C%20Value%29.%0Aproperty_setter%28c%2C%20%22title%22%2C%20%27%5B%7Baction%3A%20%22setSingleTarget%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fhas_title%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Aproperty%28c%2C%20%22isLiked%22%29.%0Aproperty_getter%28c%2C%20Base%2C%20%22isLiked%22%2C%20Value%29%20%3A-%20triple%28Base%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%2C%20Value%20%3D%20true.%0A%0Acollection%28c%2C%20%22comments%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22comments%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22todo%3A%2F%2Fcomment%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22commentss%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22todo%3A%2F%2Fcomment%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22entries%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22entries%22%2C%20List%29%20%3A-%20findall%28C%2C%20triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20C%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22entriess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22messages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22messages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20instance%28OtherClass%2C%20Target%29%2C%20subject_class%28%22Message%22%2C%20OtherClass%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22messagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A%0Acollection%28c%2C%20%22likedMessages%22%29.%0Acollection_getter%28c%2C%20Base%2C%20%22likedMessages%22%2C%20List%29%20%3A-%20setof%28Target%2C%20%28triple%28Base%2C%20%22flux%3A%2F%2Fentry_type%22%2C%20Target%29%2C%20triple%28Target%2C%20%22flux%3A%2F%2Fhas_reaction%22%2C%20%22flux%3A%2F%2Fthumbsup%22%29%29%2C%20List%29.%0Acollection_adder%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22addLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_remover%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22removeLink%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0Acollection_setter%28c%2C%20%22likedMessagess%22%2C%20%27%5B%7Baction%3A%20%22collectionSetter%22%2C%20source%3A%20%22this%22%2C%20predicate%3A%20%22flux%3A%2F%2Fentry_type%22%2C%20target%3A%20%22value%22%7D%5D%27%29.%0A").
                expressionAddress("literal://string:construct%20test", "string:construct%20test").
                expressionAddress("literal://string:get%20proxy%20test", "string:get%20proxy%20test").
                :- discontiguous(register_sdna_flow/2).
                :- discontiguous(flowable/2).
                :- discontiguous(flow_state/3).
                :- discontiguous(start_action/2).
                :- discontiguous(action/4).
                :- discontiguous(subject_class/2).
                :- discontiguous(constructor/2).
                :- discontiguous(destructor/2).
                :- discontiguous(instance/2).
                :- discontiguous(property/2).
                :- discontiguous(property_getter/4).
                :- discontiguous(property_setter/3).
                :- discontiguous(property_resolve/2).
                :- discontiguous(property_resolve_language/3).
                :- discontiguous(property_named_option/4).
                :- discontiguous(collection/2).
                :- discontiguous(collection_getter/4).
                :- discontiguous(collection_setter/3).
                :- discontiguous(collection_remover/3).
                :- discontiguous(collection_adder/3).
                :- discontiguous(p3_class_icon/2).
                :- discontiguous(p3_class_color/2).
                :- discontiguous(p3_instance_color/3).
                :- use_module(library(lists)).
                subject_class("Todo", c).
                constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').
                instance(c, Base) :- triple(Base, "todo://state", _).
                
                destructor(c, '[{action: "removeLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').
                
                property(c, "state").
                property_getter(c, Base, "state", Value) :- triple(Base, "todo://state", Value).
                property_setter(c, "state", '[{action: "setSingleTarget", source: "this", predicate: "todo://state", target: "value"}]').
                
                property(c, "title").
                property_resolve(c, "title").
                property_resolve_language(c, "title", "literal").
                property_getter(c, Base, "title", Value) :- triple(Base, "todo://has_title", Value).
                property_setter(c, "title", '[{action: "setSingleTarget", source: "this", predicate: "todo://has_title", target: "value"}]').
                
                property(c, "isLiked").
                property_getter(c, Base, "isLiked", Value) :- triple(Base, "flux://has_reaction", "flux://thumbsup"), Value = true.
                
                collection(c, "comments").
                collection_getter(c, Base, "comments", List) :- findall(C, triple(Base, "todo://comment", C), List).
                collection_adder(c, "commentss", '[{action: "addLink", source: "this", predicate: "todo://comment", target: "value"}]').
                collection_remover(c, "commentss", '[{action: "removeLink", source: "this", predicate: "todo://comment", target: "value"}]').
                collection_setter(c, "commentss", '[{action: "collectionSetter", source: "this", predicate: "todo://comment", target: "value"}]').
                
                collection(c, "entries").
                collection_getter(c, Base, "entries", List) :- findall(C, triple(Base, "flux://entry_type", C), List).
                collection_adder(c, "entriess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "entriess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "entriess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
                collection(c, "messages").
                collection_getter(c, Base, "messages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), instance(OtherClass, Target), subject_class("Message", OtherClass)), List).
                collection_adder(c, "messagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "messagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "messagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
                collection(c, "likedMessages").
                collection_getter(c, Base, "likedMessages", List) :- setof(Target, (triple(Base, "flux://entry_type", Target), triple(Target, "flux://has_reaction", "flux://thumbsup")), List).
                collection_adder(c, "likedMessagess", '[{action: "addLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_remover(c, "likedMessagess", '[{action: "removeLink", source: "this", predicate: "flux://entry_type", target: "value"}]').
                collection_setter(c, "likedMessagess", '[{action: "collectionSetter", source: "this", predicate: "flux://entry_type", target: "value"}]').
                
        "#,
            ),
        );

        let query = String::from(
            r#"subject_class("Todo", C), instance(C, "literal://string:construct%20test")."#,
        );
        let _ = machine.run_query(query);

        let query = String::from(
            r#"subject_class("Todo", C), instance(C, "literal://string:construct%20test")."#,
        );
        let _ = machine.run_query(query);

        let query = String::from(r#"subject_class("Todo", C), property(C, Property)."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "C" => Value::from("c"),
                    "Property" => Value::from("state"),
                }),
                QueryMatch::from(btreemap! {
                    "C" => Value::from("c"),
                    "Property" => Value::from("title"),
                }),
                QueryMatch::from(btreemap! {
                    "C" => Value::from("c"),
                    "Property" => Value::from("isLiked"),
                }),
            ]))
        );
    }
}
