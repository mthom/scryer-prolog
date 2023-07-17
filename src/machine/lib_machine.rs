use super::{Machine, MachineConfig, QueryResult, QueryResultLine, Atom};

impl Machine {
    pub fn new_lib() -> Self {
        Machine::new(MachineConfig::in_memory().with_toplevel(include_str!("../lib_toplevel.pl")))
    }

    pub fn run_query(&mut self, query: String) -> QueryResult {
        self.set_user_input(query);
        self.run_top_level(atom!("$toplevel"), (atom!("run_input_once"), 0));
        self.parse_output()
    }

    pub fn parse_output(&self) -> QueryResult {
        let output = self.get_user_output();
        output
            .split(";")
            .map(|s| s.trim())
            .map(|s| s.replace(".", ""))
            .filter(|s| !s.is_empty())
            .map(QueryResultLine::try_from)
            .filter_map(Result::ok)
            .collect::<Vec<QueryResultLine>>()
            .into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{QueryMatch, Value};

    #[test]
    fn programatic_query() {
        let mut machine = Machine::with_test_streams();

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
            QueryResult::Matches(vec![
                QueryMatch::from(btreemap! {
                    "P" => Value::from("p1"),
                }),
                QueryMatch::from(btreemap! {
                    "P" => Value::from("p2"),
                }),
            ])
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("a","p1","b")."#)),
            QueryResult::True
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("x","y","z")."#)),
            QueryResult::False
        );
    }
}
