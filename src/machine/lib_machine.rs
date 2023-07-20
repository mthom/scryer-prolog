use super::{Machine, MachineConfig, QueryResult, QueryResultLine, Atom};

impl Machine {
    pub fn new_lib() -> Self {
        Machine::new(MachineConfig::in_memory().with_toplevel(include_str!("../lib_toplevel.pl")))
    }

    pub fn run_query(&mut self, query: String) -> Result<QueryResult, String> {
        self.set_user_input(query);
        self.run_top_level(atom!("$toplevel"), (atom!("run_input_once"), 0));
        self.parse_output()
    }

    pub fn parse_output(&self) -> Result<QueryResult, String> {
        let output = self.get_user_output().trim().to_string();
        if output.starts_with("error(") {
            Err(output)
        } else {
            Ok(output
                .split(";")
                .map(|s| s.trim())
                .map(|s| s.replace(".", ""))
                .filter(|s| !s.is_empty())
                .map(QueryResultLine::try_from)
                .filter_map(Result::ok)
                .collect::<Vec<QueryResultLine>>()
                .into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{QueryMatch, Value};

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
            Ok(QueryResult::Matches(vec![
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
            Ok(QueryResult::True)
        );

        assert_eq!(
            machine.run_query(String::from(r#"triple("x","y","z")."#)),
            Ok(QueryResult::False)
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
}
