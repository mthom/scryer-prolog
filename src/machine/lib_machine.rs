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
        // if an exception is thrown. since the and/or stack is presumed empty,

        let stub_b = self.machine_st.stack.allocate_or_frame(0);
        let or_frame = self.machine_st.stack.index_or_frame_mut(0);

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

        // Write parsed term to heap
        let term_write_result =
            write_term_to_heap(&term, &mut self.machine_st.heap, &self.machine_st.atom_tbl)
                .expect("couldn't write term to heap");

        // Write term to heap
        self.machine_st.registers[1] = self.machine_st.heap[term_write_result.heap_loc];

        self.machine_st.cp = LIB_QUERY_SUCCESS; // BREAK_FROM_DISPATCH_LOOP_LOC;
        self.machine_st.p = self
            .indices
            .code_dir
            .get(&(atom!("call"), 1))
            .expect("couldn't get code index")
            .local()
            .unwrap();
        self.machine_st.b0 = self.machine_st.b;

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

        self.allocate_stub_choice_point();

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

            if term_write_result.var_dict.is_empty() {
                if self.machine_st.p == LIB_QUERY_SUCCESS {
                    matches.push(QueryResolutionLine::True);
                    break;
                } else if self.machine_st.p == BREAK_FROM_DISPATCH_LOOP_LOC {
                    // NOTE: only print results on success
                    // self.machine_st.fail = false;
                    // println!("b == stub_b");
                    matches.push(QueryResolutionLine::False);
                    break;
                }
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

                bindings.insert(var_key.to_string(), Value::try_from(output).expect("asdfs"));
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
    fn stress_integration_test() {
        let mut machine = Machine::new_lib();

        // File with test commands, i.e. program code to consult and queries to run
        let code = include_str!("./lib_integration_test_commands.txt");

        // Split the code into blocks
        let blocks = code.split("=====");

        let mut i = 0;
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
                i += 1;
                println!("query #{}: {}", i, query);
                // Parse and execute the query
                let result = machine.run_query(query.to_string());

                assert!(result.is_ok());

                // Print the result
                println!("{:?}", result);
            } else if let Some(code) = block.strip_prefix("consult") {
                println!("load code: {}", code);

                // Load the code into the machine
                machine.consult_module_string("facts", code.to_string());
            }
        }
    }

    #[test]
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
                    "Predicate" => Value::from("Predicate"),
                    "Result" => Value::List(
                        Vec::from([
                            Value::List([Value::from("p1"), Value::from("b")].into()),
                            Value::List([Value::from("p2"), Value::from("b")].into()),
                        ])
                    ),
                    "Target" => Value::from("Target"),
                }
            ),]))
        );
    }
}
