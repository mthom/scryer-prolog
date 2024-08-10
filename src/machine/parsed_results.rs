use crate::atom_table::*;
use dashu::*;
use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt::Display;
use std::fmt::Write;
use std::str::FromStr;

pub type QueryResult = Result<QueryResolution, String>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolution {
    True,
    False,
    Matches(Vec<QueryMatch>),
}

pub fn write_literal_str_as_json_str<W: Write>(
    writer: &mut W,
    val: &str,
) -> Result<(), std::fmt::Error> {
    writer.write_char('"')?;

    for c in val.chars() {
        write_char_to_json_str(c, writer)?;
    }

    writer.write_char('"')
}

pub fn write_prolog_str_as_rust_str<W: Write>(
    writer: &mut W,
    val: &str,
) -> Result<(), std::fmt::Error> {
    let mut chars = val.chars();
    while let Some(c) = chars.next() {
        match c {
            // re-escape prolog escape sequences to json escape sequences
            '\\' => match chars
                .next()
                .expect("a prolog string shouldn't end with the start of an escape sequence")
            {
                'a' => writer.write_char('\u{0007}')?,
                'b' => writer.write_char('\u{0008}')?,
                'f' => writer.write_char('\u{000C}')?,
                'n' => writer.write_char('\n')?,
                'r' => writer.write_char('\r')?,
                's' => writer.write_char(' ')?,
                't' => writer.write_char('\t')?,
                'v' => writer.write_char('\u{000B}')?,
                'x' => todo!(r"hexadecimal escape of the form \xXX..\ are currently not supported"),
                'u' => todo!(r"unicode escape of the form \uXXXX are currently not supported"),
                'U' => todo!(r"unicode escape of the form \UXXXXXXXX are currently not supported"),
                // \40 octal escape ?
                '\\' => writer.write_char('\\')?,
                '"' => writer.write_char('"')?,
                '\'' => writer.write_char('\'')?,
                '`' => writer.write_char('`')?,
                other => panic!("Unrecognized escape sequence begining with \\{other}"),
            },
            _ => writer.write_char(c)?,
        }
    }
    Ok(())
}

#[inline]
fn write_char_to_json_str<W: std::fmt::Write>(
    c: char,
    writer: &mut W,
) -> Result<(), std::fmt::Error> {
    Ok(match c {
        '"' => writer.write_str(r#"\""#)?,
        '\\' => writer.write_str(r"\\")?,
        '\u{0008}' => writer.write_str(r"\b")?,
        '\u{000C}' => writer.write_str(r"\f")?,
        '\n' => writer.write_str(r"\n")?,
        '\r' => writer.write_str(r"\r")?,
        '\t' => writer.write_str(r"\t")?,
        '\u{0000}'..='\u{001F}' => write!(writer, "\\u{:04X}", c as u32)?,
        ' '..='\u{10FFFF}' => writer.write_char(c)?,
    })
}

pub fn write_prolog_value_as_json<W: Write>(
    writer: &mut W,
    value: &Value,
) -> Result<(), std::fmt::Error> {
    match value {
        Value::Integer(i) => write!(writer, "{i}"),
        Value::Float(f) => write!(writer, "{f}"),
        Value::Rational(r) => {
            if r.is_int() {
                write!(writer, "{r}")
            } else {
                write!(writer, "\"{r}\"")
            }
        }
        Value::Atom(a) => write_literal_str_as_json_str(writer, &a.as_str()),
        Value::String(s) => write_literal_str_as_json_str(writer, s),
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
            writer.write_char('{')?;
            write_literal_str_as_json_str(writer, &s.as_str())?;
            writer.write_str(":[")?;

            if let Some((first, rest)) = l.split_first() {
                write_prolog_value_as_json(writer, first)?;
                for other in rest {
                    writer.write_char(',')?;
                    write_prolog_value_as_json(writer, other)?;
                }
            }
            writer.write_str("]}")
        }
        Value::Var => writer.write_str("null"),
    }
}

fn write_prolog_match_as_json<W: std::fmt::Write>(
    writer: &mut W,
    query_match: &QueryMatch,
) -> Result<(), std::fmt::Error> {
    writer.write_char('{')?;
    let mut iter = query_match.bindings.iter();

    if let Some((k, v)) = iter.next() {
        write_literal_str_as_json_str(writer, k)?;
        writer.write_char(':')?;
        write_prolog_value_as_json(writer, v)?;

        for (k, v) in iter {
            writer.write_char(',')?;
            write_literal_str_as_json_str(writer, k)?;
            writer.write_char(':')?;
            write_prolog_value_as_json(writer, v)?;
        }
    }
    writer.write_char('}')
}

fn write_prolog_query_resolution_as_json<W: std::fmt::Write>(
    resolution: &QueryResolution,
    f: &mut W,
) -> Result<(), std::fmt::Error> {
    match resolution {
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

impl Display for QueryResolution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write_prolog_query_resolution_as_json(self, f)
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
    Atom(Atom),
    String(String),
    List(Vec<Value>),
    Structure(Atom, Vec<Value>),
    Var,
}

impl Value {
    pub fn str_literal<S: Into<String>>(s: S) -> Self {
        Value::String(s.into())
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

fn split_response_string(input: &str) -> Vec<&str> {
    let mut level_bracket = 0;
    let mut level_parenthesis = 0;
    let mut in_double_quotes = false;
    let mut in_single_quotes = false;
    let mut start = 0;
    let mut result = Vec::new();
    let mut escape_next = false;

    for (i, c) in input.char_indices() {
        let in_quotes = in_single_quotes | in_double_quotes;
        let escaped = escape_next;
        escape_next = false;

        match c {
            '[' if !in_quotes => level_bracket += 1,
            ']' if !in_quotes => level_bracket -= 1,
            '(' if !in_quotes => level_parenthesis += 1,
            ')' if !in_quotes => level_parenthesis -= 1,
            // FIXME hex escape sequenches of the form \xXX..\ at the end of a string arn't handled properly
            // the ending \ can cause the closing quote to be ignored
            '\\' if in_quotes && !escaped => escape_next = true,
            '"' if !in_single_quotes && !escaped => in_double_quotes = !in_double_quotes,
            '\'' if !in_double_quotes && !escaped => in_single_quotes = !in_single_quotes,
            ',' if level_bracket == 0 && level_parenthesis == 0 && !in_quotes => {
                result.push(input[start..i].trim());
                start = i + ','.len_utf8();
            }
            _ => {}
        }
    }
    let remainder = input[start..].trim();
    if !remainder.is_empty() {
        result.push(remainder);
    }
    result
}

fn split_key_value_pairs(input: &str) -> Vec<(&str, &str)> {
    let items = split_response_string(input);
    let mut result = Vec::new();

    for item in items {
        if let Some((key, value)) = item.split_once('=') {
            let key = key.trim();
            let value = value.trim();
            result.push((key, value));
        }
    }

    result
}

fn parse_prolog_response(input: &str) -> HashMap<&str, &str> {
    let mut map: HashMap<_, _> = HashMap::new();
    // Use regex to match strings including commas inside them
    for (key, value) in split_key_value_pairs(input) {
        // cut off at given characters/strings:
        let value = value.split_once('\n').map_or(value, |(v, _)| v);
        let value = value.split_once(' ').map_or(value, |(v, _)| v);
        let value = value.split_once('\t').map_or(value, |(v, _)| v);
        let value = value.split_once("error").map_or(value, |(v, _)| v);
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
                    .map(|(key, value)| -> Result<(String, Value), ()> {
                        let key = key.to_string();
                        Ok((key, value.parse()?))
                    })
                    .filter_map(Result::ok)
                    .collect::<BTreeMap<_, _>>(),
            )),
        }
    }
}

pub(crate) fn strip_circumfix(haystack: &str, prefix: char, suffix: char) -> Option<&str> {
    haystack.strip_prefix(prefix)?.strip_suffix(suffix)
}

pub(crate) fn strip_circumfix_str<'hay>(
    haystack: &'hay str,
    prefix: &str,
    suffix: &str,
) -> Option<&'hay str> {
    haystack.strip_prefix(prefix)?.strip_suffix(suffix)
}

impl FromStr for Value {
    type Err = ();
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        let trimmed = string.trim();

        if let Ok(float_value) = string.parse::<f64>() {
            Ok(Value::Float(OrderedFloat(float_value)))
        } else if let Ok(int_value) = string.parse::<i128>() {
            Ok(Value::Integer(int_value.into()))
        } else if let Some(unquoted) =
            strip_circumfix(trimmed, '\'', '\'').or_else(|| strip_circumfix(trimmed, '"', '"'))
        {
            // pre-allocate enough capacity in case nothing needs to be un-escaped
            // this will over allocate in case the string contains escape sequences
            let mut str = String::with_capacity(unquoted.len());
            write_prolog_str_as_rust_str(&mut str, unquoted)
                .expect("writing to a string shouldn't fail");

            Ok(Value::String(str))
        } else if let Some(unbracketed) = strip_circumfix(trimmed, '[', ']') {
            let split = split_response_string(unbracketed);

            let values = split
                .into_iter()
                .map(Value::from_str)
                .collect::<Result<Vec<_>, _>>()?;

            Ok(Value::List(values))
        } else if let Some(unbraced) = strip_circumfix(trimmed, '{', '}') {
            let iter = split_response_string(unbraced);
            let mut values = vec![];

            for value in iter {
                let items: Vec<_> = value.split(':').collect();
                if let [_key, value] = items.as_slice() {
                    values.push(value.parse()?);
                }
            }

            Ok(Value::Structure(atom!("{}"), values))
        } else if let Some(un_double_angle_bracketed) = strip_circumfix_str(trimmed, "<<", ">>") {
            let iter = split_response_string(un_double_angle_bracketed);
            let mut values = vec![];

            for value in iter {
                let items: Vec<_> = value.split(':').collect();
                if let [_key, value] = items.as_slice() {
                    values.push(value.parse()?);
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
