use std::collections::BTreeSet;

use crate::machine::BREAK_FROM_DISPATCH_LOOP_LOC;
use crate::machine::mock_wam::{CompositeOpDir, Term};
use crate::parser::parser::{Parser, Tokens};

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
        self.machine_st.registers[2] = atom_as_cell!(self.machine_st.atom_tbl.build_with(module_name));

        self.run_module_predicate(atom!("loader"), (atom!("consult_stream"), 2));
    }

    pub fn run_query(&mut self, query: String) -> QueryResult {
        //let input = format!("{}", query);
        //println!("Running query: {}", input);

        // Create a new Stream from the user input
        let stream = Stream::from_owned_string(query.clone(), &mut self.machine_st.arena);
        // Read the term from the user input
        let _result = self.machine_st.read_term_from_user_input(stream, &mut self.indices);


        // Parse the query so we can analyze and then call the term
        let mut parser = Parser::new(
            Stream::from_owned_string(query, &mut self.machine_st.arena),
            &mut self.machine_st
        );
        let op_dir = CompositeOpDir::new(&self.indices.op_dir, None);
        let term = parser.read_term(&op_dir, Tokens::Default).expect("Failed to parse query");

        // ... trying to understand what's going on here
        print_term(&term);

        // Extract the atom from the term which we need to find the code index
        let term_atom = if let Term::Clause(_, atom, _) = term {
            atom
        } else {
            panic!("Expected a clause");
        };
        println!("term_atom: {:?}", term_atom.as_str());
        //println!("code_dir: {:?}", self.indices.code_dir);
        let code_index = self.indices.code_dir.get(&(term_atom, term.arity()));
        println!("code_index: {:?}", code_index);

        // Ok, we have a code_index, so we can set the program counter to the code index:

        self.machine_st.cp = BREAK_FROM_DISPATCH_LOOP_LOC;
        self.machine_st.p = code_index.expect("couldn't get code index").local().unwrap();

        println!("running dispatch loop");
        self.dispatch_loop();
        println!("done");

        // If we don't set this register, we get an error in write_term.
        // It seems to be the register that holds max_depth
        self.machine_st.registers[7] = 50.into();

        let op_dir = &self.indices.op_dir;
        let printer = self.machine_st.write_term(op_dir)
            .expect("Couldn't get printer from write_term")
            .expect("Couldn't get printer from write_term");

        println!("Varnames: {:?}", printer.var_names);
        println!("Printer: {:?}", printer);

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

    #[tokio::test]
    async fn programatic_query() {
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

    #[tokio::test]
    async fn failing_query() {
        let mut machine = Machine::new_lib();
        let query = String::from(r#"triple("a",P,"b")."#);
        let output = machine.run_query(query);
        assert_eq!(
            output,
            Err(String::from("error(existence_error(procedure,triple/3),triple/3)."))
        );
    }

    #[tokio::test]
    async fn complex_results() {
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

    #[tokio::test]
    async fn list_results() {
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


    #[tokio::test]
    async fn consult() {
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
    #[tokio::test]
    async fn stress_integration_test() {
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
