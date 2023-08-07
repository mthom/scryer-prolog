use std::collections::BTreeSet;

use super::{
    Machine, MachineConfig, QueryResult, QueryResolutionLine, 
    Atom, AtomCell, HeapCellValue, HeapCellValueTag,
    streams::Stream
};

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
        let input = format!("{}", query);
        //println!("Running query: {}", input);
        self.set_user_input(input);
        self.run_top_level(atom!("$toplevel"), (atom!("run_input_once"), 0));
        self.parse_output()
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
                .map(|s| s.replace(".", ""))
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
