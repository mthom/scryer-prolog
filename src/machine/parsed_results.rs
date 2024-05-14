use crate::atom_table::*;
use crate::heap_iter::{stackful_post_order_iter, NonListElider};
use crate::machine::{F64Offset, F64Ptr, Fixnum, HeapCellValueTag};
use crate::parser::ast::Var;
use dashu::*;
use indexmap::IndexMap;
use ordered_float::OrderedFloat;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt::Display;
use std::fmt::Write;
use std::iter::FromIterator;

use super::Machine;
use super::{HeapCellValue, Number};

pub type QueryResult = Result<QueryResolution, String>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolution {
    True,
    False,
    Matches(Vec<QueryMatch>),
}

pub fn write_prolog_value_as_json<W: Write>(
    writer: &mut W,
    value: &Value,
) -> Result<(), std::fmt::Error> {
    match value {
        Value::Integer(i) => write!(writer, "{}", i),
        Value::Float(f) => write!(writer, "{}", f),
        Value::Rational(r) => write!(writer, "{}", r),
        Value::Atom(a) => writer.write_str(a.as_str()),
        Value::String(s) => {
            if let Err(_e) = serde_json::from_str::<serde_json::Value>(s.as_str()) {
                //treat as string literal
                //escape double quotes
                write!(
                    writer,
                    "\"{}\"",
                    s.replace('\"', "\\\"")
                        .replace('\n', "\\n")
                        .replace('\t', "\\t")
                        .replace('\r', "\\r")
                )
            } else {
                //return valid json string
                writer.write_str(s)
            }
        }
        Value::List(l) => {
            writer.write_char('[')?;
            if let Some((first, rest)) = l.split_first() {
                write_prolog_value_as_json(writer, first)?;

                for other in rest {
                    writer.write_char(',')?;
                    write_prolog_value_as_json(writer, other)?;
                }
            }
            writer.write_char(']')
        }
        Value::Structure(s, l) => {
            write!(writer, "\"{}\":[", s.as_str())?;

            if let Some((first, rest)) = l.split_first() {
                write_prolog_value_as_json(writer, first)?;
                for other in rest {
                    writer.write_char(',')?;
                    write_prolog_value_as_json(writer, other)?;
                }
            }
            writer.write_char(']')
        }
        _ => writer.write_str("null"),
    }
}

fn write_prolog_match_as_json<W: std::fmt::Write>(
    writer: &mut W,
    query_match: &QueryMatch,
) -> Result<(), std::fmt::Error> {
    writer.write_char('{')?;
    let mut iter = query_match.bindings.iter();

    if let Some((k, v)) = iter.next() {
        write!(writer, "\"{k}\":")?;
        write_prolog_value_as_json(writer, v)?;

        for (k, v) in iter {
            write!(writer, ",\"{k}\":")?;
            write_prolog_value_as_json(writer, v)?;
        }
    }
    writer.write_char('}')
}

impl Display for QueryResolution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryResolution::True => f.write_str("true"),
            QueryResolution::False => f.write_str("false"),
            QueryResolution::Matches(matches) => {
                f.write_char('[')?;
                if let Some((first, rest)) = matches.split_first() {
                    write_prolog_match_as_json(f, first)?;
                    for other in rest {
                        f.write_char(',')?;
                        write_prolog_match_as_json(f, other)?;
                    }
                }
                f.write_char(']')
            }
        }
    }
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
    Atom(String),
    String(String),
    List(Vec<Value>),
    Structure(String, Vec<Value>),
    Var(String),
}

/// This is an auxiliary function to turn a count into names of anonymous variables like _A, _B,
/// _AB, etc...
fn count_to_letter_code(mut count: usize) -> String {
    let mut letters = Vec::new();

    loop {
        let letter_idx = (count % 26) as u32;
        letters.push(char::from_u32('A' as u32 + letter_idx).unwrap());
        count /= 26;

        if count == 0 {
            break;
        }
    }

    letters.into_iter().chain("_".chars()).rev().collect()
}

impl Value {
    pub(crate) fn from_heapcell(
        machine: &mut Machine,
        heap_cell: HeapCellValue,
        var_names: &mut IndexMap<HeapCellValue, Var>,
    ) -> Self {
        // Adapted from MachineState::read_term_from_heap
        let mut term_stack = vec![];

        machine.machine_st.heap[0] = heap_cell;

        let mut iter = stackful_post_order_iter::<NonListElider>(
            &mut machine.machine_st.heap,
            &mut machine.machine_st.stack,
            0,
        );

        let mut anon_count: usize = 0;

        while let Some(addr) = iter.next() {
            let addr = unmark_cell_bits!(addr);

            read_heap_cell!(addr,
                (HeapCellValueTag::Lis) => {
                    let tail = term_stack.pop().unwrap();
                    let head = term_stack.pop().unwrap();

                    let list = match tail {
                        Value::Atom(atom) if atom == "[]" => match head {
                            Value::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                Value::String(a.to_string())
                            }
                            _ => Value::List(vec![head]),
                        },
                        Value::List(elems) if elems.is_empty() => match head {
                            // a.chars().collect::<Vec<_>>().len() == 1
                            Value::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                Value::String(a.to_string())
                            },
                            _ => Value::List(vec![head]),
                        },
                        Value::List(mut elems) => {
                            elems.insert(0, head);
                            Value::List(elems)
                        },
                        Value::String(mut elems) => match head {
                            Value::Atom(ref a) if a.chars().collect::<Vec<_>>().len() == 1 => {
                                // Handle lists of char as strings
                                elems.insert(0, a.chars().next().unwrap());
                                Value::String(elems)
                            },
                            _ => {
                                let mut elems: Vec<Value> = elems
                                    .chars()
                                    .map(|x| Value::Atom(x.into()))
                                    .collect();
                                elems.insert(0, head);
                                Value::List(elems)
                            }
                        },
                        _ => {
                            Value::Structure(".".into(), vec![head, tail])
                        }
                    };
                    term_stack.push(list);
                }
                (HeapCellValueTag::Var | HeapCellValueTag::AttrVar | HeapCellValueTag::StackVar) => {
                    let var = var_names.get(&addr).cloned();
                    match var {
                        Some(name) => term_stack.push(Value::Var(name.to_string())),
                        _ => {
                            let anon_name = loop {
                                // Generate a name for the anonymous variable
                                let anon_name = count_to_letter_code(anon_count);

                                // Find if this name is already being used
                                var_names.sort_by(|_, a, _, b| a.cmp(b));

                                let binary_result = var_names.binary_search_by(|_,a| {
                                    let a: &String = a.borrow();
                                    a.cmp(&anon_name)
                                });

                                match binary_result {
                                    Ok(_) => anon_count += 1, // Name already used
                                    Err(_) => {
                                        // Name not used, assign it to this variable
                                        let var = anon_name.clone();
                                        var_names.insert(addr, Var::from(var));
                                        break anon_name;
                                    },
                                }
                            };
                            term_stack.push(Value::Var(anon_name));
                        },
                    }
                }
                (HeapCellValueTag::F64, f) => {
                    term_stack.push(Value::Float(*f));
                }
                (HeapCellValueTag::Fixnum, n) => {
                    term_stack.push(Value::Integer(n.into()));
                }
                (HeapCellValueTag::Cons) => {
                    match Number::try_from(addr) {
                        Ok(Number::Integer(i)) => term_stack.push(Value::Integer((*i).clone())),
                        Ok(Number::Rational(r)) => term_stack.push(Value::Rational((*r).clone())),
                        _ => {}
                    }
                }
                (HeapCellValueTag::Atom, (name, arity)) => {
                    //let h = iter.focus().value() as usize;
                    //let mut arity = arity;

                    // Not sure why/if this is needed.
                    // Might find out with better testing later.
                    /*
                    if iter.heap.len() > h + arity + 1 {
                        let value = iter.heap[h + arity + 1];

                        if let Some(idx) = get_structure_index(value) {
                            // in the second condition, arity == 0,
                            // meaning idx cannot pertain to this atom
                            // if it is the direct subterm of a larger
                            // structure.
                            if arity > 0 || !iter.direct_subterm_of_str(h) {
                                term_stack.push(
                                    Term::Literal(Cell::default(), Literal::CodeIndex(idx))
                                );

                                arity += 1;
                            }
                        }
                    }
                    */

                    if arity == 0 {
                        let atom_name = name.as_str().to_string();
                        if atom_name == "[]" {
                            term_stack.push(Value::List(vec![]));
                        } else {
                            term_stack.push(Value::Atom(atom_name));
                        }
                    } else {
                        let subterms = term_stack
                            .drain(term_stack.len() - arity ..)
                            .collect();

                        term_stack.push(Value::Structure(name.as_str().to_string(), subterms));
                    }
                }
                (HeapCellValueTag::PStrLoc, pstr_loc) => {
                    let tail = term_stack.pop().unwrap();
                    let char_iter = iter.base_iter.heap.char_iter(pstr_loc);

                    match tail {
                        Value::Atom(atom) => {
                            if atom == "[]" {
                                term_stack.push(Value::String(atom.as_str().to_string()));
                            }
                        },
                        Value::List(l) if l.is_empty() => {
                            term_stack.push(Value::String(char_iter.collect()));
                        }
                        Value::List(l) => {
                            let mut list: Vec<Value> = char_iter
                                .map(|x| Value::Atom(x.to_string()))
                                .collect();
                            list.extend(l.into_iter());
                            term_stack.push(Value::List(list));
                        },
                        _ => {
                            let mut list: Vec<Value> = char_iter
                                .map(|x| Value::Atom(x.to_string()))
                                .collect();

                            let mut partial_list = Value::Structure(
                                ".".into(),
                                vec![
                                    list.pop().unwrap(),
                                    tail,
                                ],
                            );

                            while let Some(last) = list.pop() {
                                partial_list = Value::Structure(
                                    ".".into(),
                                    vec![
                                        last,
                                        partial_list,
                                    ],
                                );
                            }

                            term_stack.push(partial_list);
                        }
                    }
                }
                _ => {
                }
            );
        }

        debug_assert_eq!(term_stack.len(), 1);
        term_stack.pop().unwrap()
    }
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

        // If there is only one line, and it is an empty match, return false.
        if query_result_lines.len() == 1 {
            if let QueryResolutionLine::Match(m) = query_result_lines[0].clone() {
                if m.is_empty() {
                    return QueryResolution::False;
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

impl FromIterator<QueryResolutionLine> for QueryResolution {
    fn from_iter<I: IntoIterator<Item = QueryResolutionLine>>(iter: I) -> Self {
        // TODO: Probably a good idea to implement From<Vec<QueryResolutionLine>> based on this
        // instead.
        iter.into_iter().collect::<Vec<_>>().into()
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

            Ok(Value::Structure("{}".into(), values))
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

            Ok(Value::Structure("<<>>".into(), values))
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
