use crate::atom_table::*;
use dashu::*;
use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashMap;

pub type QueryResult = Result<QueryResolution, String>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolution {
    True,
    False,
    Matches(Vec<QueryMatch>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryMatch {
    pub bindings: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolutionLine {
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

impl From<BTreeMap<&str, Value>> for QueryMatch {
    fn from(bindings: BTreeMap<&str, Value>) -> Self {
        QueryMatch {
            bindings: bindings
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect::<BTreeMap<_, _>>(),
        }
    }
}

impl From<BTreeMap<String, Value>> for QueryMatch {
    fn from(bindings: BTreeMap<String, Value>) -> Self {
        QueryMatch { bindings }
    }
}

impl From<Vec<QueryResolutionLine>> for QueryResolution {
    fn from(query_result_lines: Vec<QueryResolutionLine>) -> Self {
        // If there is only one line, and it is true or false, return that.
        if query_result_lines.len() == 1 {
            match query_result_lines[0].clone() {
                QueryResolutionLine::True => return QueryResolution::True,
                QueryResolutionLine::False => return QueryResolution::False,
                _ => {}
            }
        }

        // If there is only one line, and it is an empty match, return true.
        if query_result_lines.len() == 1 {
            if let QueryResolutionLine::Match(m) = query_result_lines[0].clone() {
                if m.is_empty() {
                    return QueryResolution::True;
                }
            }
        }

        // If there is at least one line with true and no matches, return true.
        if query_result_lines
            .iter()
            .any(|l| l == &QueryResolutionLine::True)
            && !query_result_lines
                .iter()
                .any(|l| matches!(l, QueryResolutionLine::Match(_)))
        {
            return QueryResolution::True;
        }

        // If there is at least one match, return all matches.
        let all_matches = query_result_lines
            .into_iter()
            .filter(|l| matches!(l, QueryResolutionLine::Match(_)))
            .map(|l| match l {
                QueryResolutionLine::Match(m) => QueryMatch::from(m),
                _ => unreachable!(),
            })
            .collect::<Vec<_>>();

        if !all_matches.is_empty() {
            return QueryResolution::Matches(all_matches);
        }

        QueryResolution::False
    }
}

fn split_response_string(input: &str) -> Vec<String> {
    let mut level_bracket = 0;
    let mut level_parenthesis = 0;
    let mut in_double_quotes = false;
    let mut in_single_quotes = false;
    let mut start = 0;
    let mut result = Vec::new();

    for (i, c) in input.chars().enumerate() {
        match c {
            '[' => level_bracket += 1,
            ']' => level_bracket -= 1,
            '(' => level_parenthesis += 1,
            ')' => level_parenthesis -= 1,
            '"' => in_double_quotes = !in_double_quotes,
            '\'' => in_single_quotes = !in_single_quotes,
            ',' if level_bracket == 0
                && level_parenthesis == 0
                && !in_double_quotes
                && !in_single_quotes =>
            {
                result.push(input[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }

    result.push(input[start..].trim().to_string());
    result
}

fn split_key_value_pairs(input: &str) -> Vec<(String, String)> {
    let items = split_response_string(input);
    let mut result = Vec::new();

    for item in items {
        let parts: Vec<&str> = item.splitn(2, '=').collect();
        if parts.len() == 2 {
            let key = parts[0].trim().to_string();
            let value = parts[1].trim().to_string();
            result.push((key, value));
        }
    }

    result
}

fn parse_prolog_response(input: &str) -> HashMap<String, String> {
    let mut map: HashMap<String, String> = HashMap::new();
    // Use regex to match strings including commas inside them
    for result in split_key_value_pairs(input) {
        let key = result.0;
        let value = result.1;
        // cut off at given characters/strings:
        let value = value.split('\n').next().unwrap().to_string();
        let value = value.split(' ').next().unwrap().to_string();
        let value = value.split('\t').next().unwrap().to_string();
        let value = value.split("error").next().unwrap().to_string();
        map.insert(key, value);
    }

    map
}

impl TryFrom<String> for QueryResolutionLine {
    type Error = ();
    fn try_from(string: String) -> Result<Self, Self::Error> {
        match string.as_str() {
            "true" => Ok(QueryResolutionLine::True),
            "false" => Ok(QueryResolutionLine::False),
            _ => Ok(QueryResolutionLine::Match(
                parse_prolog_response(&string)
                    .iter()
                    .map(|(k, v)| -> Result<(String, Value), ()> {
                        let key = k.to_string();
                        let value = v.to_string();
                        Ok((key, Value::try_from(value)?))
                    })
                    .filter_map(Result::ok)
                    .collect::<BTreeMap<_, _>>(),
            )),
        }
    }
}

fn split_nested_list(input: &str) -> Vec<String> {
    let mut level = 0;
    let mut start = 0;
    let mut result = Vec::new();

    for (i, c) in input.chars().enumerate() {
        match c {
            '[' => level += 1,
            ']' => level -= 1,
            ',' if level == 0 => {
                result.push(input[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }

    result.push(input[start..].trim().to_string());
    result
}

impl TryFrom<String> for Value {
    type Error = ();
    fn try_from(string: String) -> Result<Self, Self::Error> {
        let trimmed = string.trim();

        if let Ok(float_value) = string.parse::<f64>() {
            Ok(Value::Float(OrderedFloat(float_value)))
        } else if let Ok(int_value) = string.parse::<i128>() {
            Ok(Value::Integer(int_value.into()))
        } else if trimmed.starts_with('\'') && trimmed.ends_with('\'')
            || trimmed.starts_with('"') && trimmed.ends_with('"')
        {
            Ok(Value::String(trimmed[1..trimmed.len() - 1].into()))
        } else if trimmed.starts_with('[') && trimmed.ends_with(']') {
            let split = split_nested_list(&trimmed[1..trimmed.len() - 1]);

            let values = split
                .into_iter()
                .map(Value::try_from)
                .collect::<Result<Vec<_>, _>>()?;

            Ok(Value::List(values))
        } else if trimmed.starts_with('{') && trimmed.ends_with('}') {
            let iter = trimmed[1..trimmed.len() - 1].split(',');
            let mut values = vec![];

            for value in iter {
                let items: Vec<_> = value.split(':').collect();
                if items.len() == 2 {
                    let _key = items[0].to_string();
                    let value = items[1].to_string();
                    values.push(Value::try_from(value)?);
                }
            }

            Ok(Value::Structure(atom!("{}"), values))
        } else if trimmed.starts_with("<<") && trimmed.ends_with(">>") {
            let iter = trimmed[2..trimmed.len() - 2].split(',');
            let mut values = vec![];

            for value in iter {
                let items: Vec<_> = value.split(':').collect();
                if items.len() == 2 {
                    let _key = items[0].to_string();
                    let value = items[1].to_string();
                    values.push(Value::try_from(value)?);
                }
            }

            Ok(Value::Structure(atom!("<<>>"), values))
        } else if !trimmed.contains(',') && !trimmed.contains('\'') && !trimmed.contains('"') {
            Ok(Value::String(trimmed.into()))
        } else {
            Err(())
        }
    }
}

impl From<&str> for Value {
    fn from(str: &str) -> Self {
        Value::String(str.to_string())
    }
}
