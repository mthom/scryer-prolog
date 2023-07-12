use ordered_float::OrderedFloat;
use rug::*;
use std::{collections::BTreeMap};
use crate::atom_table::*;

use super::Machine;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResult {
    True,
    False,
    Matches(Vec<QueryResultLine>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResultLine {
    True,
    False,
    Match(BTreeMap<String, Value>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Integer(Integer),
    Rational(Rational),
    Float(OrderedFloat<f64>),
    Atom(Atom),
    String(String),
    List(Vec<Value>),
    Structure(Atom, Vec<Value>),
    Var,
}

impl From<Vec<QueryResultLine>> for QueryResult {
    fn from(query_result_lines: Vec<QueryResultLine>) -> Self {
        // If there is only one line, and it is true or false, return that.
        if query_result_lines.len() == 1 {
            match query_result_lines[0].clone() {
                QueryResultLine::True => return QueryResult::True,
                QueryResultLine::False => return QueryResult::False,
                _ => {}
            }
        }

        // If there is at least one line with true and no matches, return true.
        if query_result_lines.iter().any(|l| l == &QueryResultLine::True)
            && !query_result_lines.iter().any(|l| {
            if let &QueryResultLine::Match(_) = l { true } else { false }
        }) {
            return QueryResult::True;
        }

        // If there is at least one match, return all matches.
        if query_result_lines.iter().any(|l| {
            if let &QueryResultLine::Match(_) = l { true } else { false }
        }) {
            let all_matches = query_result_lines.into_iter()
                .filter(|l| {
                    if let &QueryResultLine::Match(_) = l { true } else { false }
                })
                .collect::<Vec<_>>();
            return QueryResult::Matches(all_matches);
        }

        QueryResult::False
    }
}


impl TryFrom<String> for QueryResultLine {
    type Error = ();
    fn try_from(string: String) -> Result<Self, Self::Error> {
        match string.as_str() {
            "true" => Ok(QueryResultLine::True),
            "false" => Ok(QueryResultLine::False),
            _ => Ok(QueryResultLine::Match(
                string.split(",")
                    .map(|s| s.trim())
                    .filter(|s| !s.is_empty())
                    .map(|s| -> Result<(String, Value), ()>{
                        let mut iter = s.split(" = ");

                        let key = iter.next().unwrap().to_string();
                        let value = iter.next().unwrap().to_string();

                        Ok((key, Value::try_from(value)?))
                    })
                    .filter_map(Result::ok)
                    .collect::<BTreeMap<_, _>>()
                ))
        }
    }
}

impl TryFrom<String> for Value {
    type Error = ();
    fn try_from(string: String) -> Result<Self, Self::Error> {
        let trimmed = string.trim();

        if trimmed.starts_with("'") && trimmed.ends_with("'") {
            Ok(Value::String(trimmed[1..trimmed.len() - 1].into()))
        } else 
        if trimmed.starts_with("\"") && trimmed.ends_with("\"") {
            Ok(Value::String(trimmed[1..trimmed.len() - 1].into()))
        } else if trimmed.starts_with("[") && trimmed.ends_with("]") {
            let mut iter = trimmed[1..trimmed.len() - 1].split(",");

            let mut values = vec![];

            while let Some(s) = iter.next() {
                values.push(Value::try_from(s.to_string())?);
            }

            Ok(Value::List(values))
        } else if trimmed.starts_with("{") && trimmed.ends_with("}") {
            let mut iter = trimmed[1..trimmed.len() - 1].split(",");

            let mut values = vec![];

            while let Some(value) = iter.next() {
                let mut iter = value.split(":");

                let key = iter.next().unwrap().to_string();
                let value = iter.next().unwrap().to_string();

                values.push(Value::try_from(value)?);
            }

            Ok(Value::Structure(atom!("{}"), values))
        } else if trimmed.starts_with("<<") && trimmed.ends_with(">>") {
            let mut iter = trimmed[2..trimmed.len() - 2].split(",");

            let mut values = vec![];

            while let Some(value) = iter.next() {
                let mut iter = value.split(":");

                let key = iter.next().unwrap().to_string();
                let value = iter.next().unwrap().to_string();

                values.push(Value::try_from(value)?);
            }

            Ok(Value::Structure(atom!("<<>>"), values))
        } else {
            Err(())
        }
    }
}