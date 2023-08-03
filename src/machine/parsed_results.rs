use crate::atom_table::*;
use ordered_float::OrderedFloat;
use dashu::*;
use std::collections::BTreeMap;
use regex::Regex;
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
            match query_result_lines[0].clone() {
                QueryResolutionLine::Match(m) => {
                    if m.is_empty() {
                        return QueryResolution::True;
                    }
                }
                _ => {}
            }
        }

        // If there is at least one line with true and no matches, return true.
        if query_result_lines
            .iter()
            .any(|l| l == &QueryResolutionLine::True)
            && !query_result_lines.iter().any(|l| {
                if let &QueryResolutionLine::Match(_) = l {
                    true
                } else {
                    false
                }
            })
        {
            return QueryResolution::True;
        }

        // If there is at least one match, return all matches.
        let all_matches = query_result_lines
            .into_iter()
            .filter(|l| {
                if let &QueryResolutionLine::Match(_) = l {
                    true
                } else {
                    false
                }
            })
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

fn parse_prolog_response(input: &str) -> HashMap<String, String> {
    let mut map: HashMap<String, String> = HashMap::new();
    // Use regex to match strings including commas inside them
    let re = Regex::new(r"(\w+)\s=\s([^,]*'[^']*'[^,]*|[^,]*)").unwrap();
    
    for cap in re.captures_iter(input) {
        let key = cap[1].to_string();
        let value = cap[2].trim_end_matches(',').trim().to_string();
        // cut off at given characters/strings:
        let value = value.split("\n").next().unwrap().to_string();
        let value = value.split("  ").next().unwrap().to_string();
        let value = value.split("\t").next().unwrap().to_string();
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
                    .collect::<BTreeMap<_, _>>()
                )
            ),
        }
    }
}

impl TryFrom<String> for Value {
    type Error = ();
    fn try_from(string: String) -> Result<Self, Self::Error> {
        let trimmed = string.trim();

        if trimmed.starts_with("'") && trimmed.ends_with("'") {
            Ok(Value::String(trimmed[1..trimmed.len() - 1].into()))
        } else if trimmed.starts_with("\"") && trimmed.ends_with("\"") {
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
                let items: Vec<_> = value.split(":").collect();
                if items.len() == 2 {
                    let _key = items[0].to_string();
                    let value = items[1].to_string();
                    values.push(Value::try_from(value)?);
                }
            }

            Ok(Value::Structure(atom!("{}"), values))
        } else if trimmed.starts_with("<<") && trimmed.ends_with(">>") {
            let mut iter = trimmed[2..trimmed.len() - 2].split(",");
            let mut values = vec![];

            while let Some(value) = iter.next() {
                let items: Vec<_> = value.split(":").collect();
                if items.len() == 2 {
                    let _key = items[0].to_string();
                    let value = items[1].to_string();
                    values.push(Value::try_from(value)?);
                }
            }

            Ok(Value::Structure(atom!("<<>>"), values))
        } else if !trimmed.contains(",") && !trimmed.contains("'") && !trimmed.contains("\"") {
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
