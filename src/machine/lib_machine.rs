use std::collections::BTreeSet;
use std::sync::Arc;

use crate::atom_table;
use crate::heap_print::{HCPrinter, HCValueOutputter, PrinterOutputter};
use crate::machine::BREAK_FROM_DISPATCH_LOOP_LOC;
use crate::machine::mock_wam::{CompositeOpDir, Term, Fixnum};
use crate::parser::parser::{Parser, Tokens};
use crate::read::write_term_to_heap;
use crate::machine::machine_indices::VarKey;
use crate::parser::ast::{Var, VarPtr};
use indexmap::IndexMap;

use super::{
    Machine, MachineConfig, QueryResult, QueryResolutionLine, 
    Atom, AtomCell, HeapCellValue, HeapCellValueTag,
    streams::Stream
};
use ref_thread_local::__Deref;
fn print_term(term: &Term) {
    match term {
        Term::Clause(clause, atom, terms) => {
            println!("clause: {:?}", clause);
            println!("atom: {:?}", atom.as_str());
            println!("terms: {:?}", terms);

            for term in terms {
               print_term(term);
            }
        },
        Term::Cons(cons, term1, term2) => {
            println!("constant: {:?}", cons);
            println!("term1: {:?}", term1);
            println!("term2: {:?}", term2);
        },
        Term::Literal(cell, literal) => {
            println!("Cell: {:?}", cell);
            println!("Literal: {:?}", literal);
        },
        Term::Var(var_reg, var_ptr) => {
            println!("Var: {:?}, {:?}", var_reg.get(), var_ptr.deref());
        },
        Term::CompleteString(cell, atom) => {
            println!("Cell: {:?}", cell);
            println!("Atom: {:?}", atom.as_str());
        },
        _ => {
            println!("Parsed query: {:?}", term);
        }
    }
    
}

impl Machine {
    pub fn new_lib() -> Self {
        Machine::new(MachineConfig::in_memory().with_toplevel(include_str!("../lib_toplevel.pl")))
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

        // Call the term
        loop {
            self.dispatch_loop();

            if self.machine_st.fail {
                // NOTE: only print results on success
                self.machine_st.fail = false;
                break;
            }

            for (var_key, term_to_be_printed) in &term_write_result.var_dict {
                let mut printer = HCPrinter::new(
                    &mut self.machine_st.heap,
                    Arc::clone(&self.machine_st.atom_tbl),
                    &mut self.machine_st.stack,
                    &self.indices.op_dir,
                    PrinterOutputter::new(),
                    *term_to_be_printed,
                );

                // NOTE: I've converted the former register settings
                // for '$write_term'/8 to printer settings. Registers
                // are not read by the printer.
                printer.ignore_ops = false;
                printer.numbervars = true;
                printer.quoted = true;
                printer.max_depth = 1000; // NOTE: set this to 0 for unbounded depth
                printer.double_quotes = false;
                printer.var_names = var_names.clone();

                println!("Varnames: {:?}", printer.var_names);

                let output = printer.print();

                println!("Print: {:?}", output);
                println!("Result: {} = {}", var_key.to_string(), output.result());
            }

            if self.machine_st.b > 0 {
                // NOTE: there are outstanding choicepoints, backtrack
                // through them for further solutions.
                self.machine_st.backtrack();
            } else {
                // NOTE: out of choicepoints to backtrack through, no
                // more solutions to gather.
                break;
            }
        }

        Err("not implementend".to_string())
    }

    pub fn parse_output(&self) -> QueryResult {
        let output = self.get_user_output().trim().to_string();
        //println!("Output: {}", output);
        if output.starts_with("error(") {
            Err(output)
        } else {
            // Remove duplicate lines
            Ok(output
                // 1. Split into disjunct matches
                .split(";")
                .map(|s| s.trim())
                // 2. Dedupe through Set
                .collect::<BTreeSet<&str>>()
                .iter()
                .cloned()
                // 3. Back to Vec
                .collect::<Vec<&str>>()
                .iter()
                // 4. Trim and remove empty lines
                .map(|s| s.trim())
                .map(|s| if s.ends_with(".") { s[..s.len()-1].to_string() } else { s.to_string() })
                .filter(|s| !s.is_empty())
                // 5. Parse into QueryResolutionLine
                .map(QueryResolutionLine::try_from)
                // 6. Remove lines that couldn't be parsed, so we still keep the ones they did
                .filter_map(Result::ok)
                .collect::<Vec<QueryResolutionLine>>()
                .into())
        }
    }
}

#[cfg(test)]
mod tests {
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
                    "Class" => Value::from("Recipe")
                }),
                QueryMatch::from(btreemap! {
                    "Class" => Value::from("Todo")
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
                    "X" => Value::List(Vec::from([Value::from("1"), Value::from("2"), Value::from("3")]))
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
