use std::collections::BTreeMap;
use std::sync::Arc;

use crate::atom_table;
use crate::heap_print::{HCPrinter, HCValueOutputter, PrinterOutputter};
use crate::machine::BREAK_FROM_DISPATCH_LOOP_LOC;
use crate::machine::mock_wam::CompositeOpDir;
use crate::parser::parser::{Parser, Tokens};
use crate::read::write_term_to_heap;
use crate::machine::machine_indices::VarKey;
use crate::parser::ast::{Var, VarPtr};
use indexmap::IndexMap;

use super::{
    Machine, MachineConfig, QueryResult, QueryResolutionLine, 
    Atom, AtomCell, HeapCellValue, HeapCellValueTag, Value, QueryResolution,
    streams::Stream
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
        self.machine_st.registers[2] = atom_as_cell!(&atom_table::AtomTable::build_with(&self.machine_st.atom_tbl, module_name));

        self.run_module_predicate(atom!("loader"), (atom!("consult_stream"), 2));
    }

    pub fn run_query(&mut self, query: String) -> QueryResult {
        println!("Query: {}", query);
        // Parse the query so we can analyze and then call the term
        let mut parser = Parser::new(
            Stream::from_owned_string(query, &mut self.machine_st.arena),
            &mut self.machine_st
        );
        let op_dir = CompositeOpDir::new(&self.indices.op_dir, None);
        let term = parser.read_term(&op_dir, Tokens::Default).expect("Failed to parse query");

        // Write parsed term to heap
        let term_write_result = write_term_to_heap(&term, &mut self.machine_st.heap, &mut self.machine_st.atom_tbl).expect("couldn't write term to heap");

        // Write term to heap
        self.machine_st.registers[1] = self.machine_st.heap[term_write_result.heap_loc];

        self.machine_st.cp = BREAK_FROM_DISPATCH_LOOP_LOC;
        self.machine_st.p = self.indices.code_dir.get(&(atom!("call"), 1)).expect("couldn't get code index").local().unwrap();

        let var_names: IndexMap<_, _> = term_write_result.var_dict.iter()
            .map(|(var_key, cell)| match var_key {
                // NOTE: not the intention behind Var::InSitu here but
                // we can hijack it to store anonymous variables
                // without creating problems.
                VarKey::AnonVar(h) => (*cell, VarPtr::from(Var::InSitu(*h))),
                VarKey::VarPtr(var_ptr) => (*cell, var_ptr.clone()),
            })
            .collect();

        let mut matches: Vec<QueryResolutionLine> = Vec::new();
        // Call the term
        loop {
            self.dispatch_loop();

            if self.machine_st.fail {
                // NOTE: only print results on success
                self.machine_st.fail = false;
                println!("false");
                matches.push(QueryResolutionLine::False);
                break;
            }

            let mut bindings: BTreeMap<String, Value> = BTreeMap::new();
            
            for (var_key, term_to_be_printed) in &term_write_result.var_dict {
                if var_key.to_string().starts_with("_") {
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
                println!("Result: {} = {}", var_key.to_string(), output);
                
                bindings.insert(var_key.to_string(), Value::try_from(output).expect("asdfs"));
            }

            matches.push(QueryResolutionLine::Match(bindings));

            if self.machine_st.b > 0 {
                println!("b: {}", self.machine_st.b);
                // NOTE: there are outstanding choicepoints, backtrack
                // through them for further solutions.
                self.machine_st.backtrack();
            } else {
                println!("breaking");
                // NOTE: out of choicepoints to backtrack through, no
                // more solutions to gather.
                break;
            }
        }

        Ok(QueryResolution::from(matches))
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    use super::*;
    use crate::machine::{QueryMatch, Value, QueryResolution};

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
            Err(String::from("error(existence_error(procedure,triple/3),triple/3)."))
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

        let result = machine.run_query(String::from("subject_class(\"Todo\", C), constructor(C, Actions)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "C" => Value::from("c"),
                    "Actions" => Value::from("[{action: \"addLink\", source: \"this\", predicate: \"todo://state\", target: \"todo://ready\"}]"),
                }),
            ]))
        );

        let result = machine.run_query(String::from("subject_class(\"Recipe\", C), constructor(C, Actions)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "C" => Value::from("xyz"),
                    "Actions" => Value::from("[{action: \"addLink\", source: \"this\", predicate: \"recipe://title\", target: \"literal://string:Meta%20Muffins\"}]"),
                }),
            ]))
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
            "#.to_string());

        let result = machine.run_query(String::from("list(X)."));
        assert_eq!(
            result,
            Ok(QueryResolution::Matches(vec![
                QueryMatch::from(btreemap! {
                    "X" => Value::List(Vec::from([
                        Value::Float(OrderedFloat(1.0)),
                        Value::Float(OrderedFloat(2.0)),
                        Value::Float(OrderedFloat(3.0)),
                        ]))
                }),
            ]))
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

    #[ignore = "fails on windows"]
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
            if block.starts_with("query") {
                // Extract the query from the block
                let query = &block[5..];

                i += 1;
                println!("query #{}: {}", i, query);
                // Parse and execute the query
                let result = machine.run_query(query.to_string());

                assert!(result.is_ok());

                // Print the result
                println!("{:?}", result);
            } else if block.starts_with("consult") {
                // Extract the code from the block
                let code = &block[7..];

                println!("load code: {}", code);

                // Load the code into the machine
                machine.consult_module_string("facts", code.to_string());
            }
        }

    }
}
