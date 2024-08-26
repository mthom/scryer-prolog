use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::iter::FromIterator;

use super::Machine;
use super::{HeapCellValue, Number};
use crate::atom_table::*;
use crate::heap_iter::{stackful_post_order_iter, NonListElider};
use crate::machine::{F64Offset, F64Ptr, Fixnum, HeapCellValueTag};
use crate::parser::ast::{Var, VarPtr};

use dashu::*;
use indexmap::IndexMap;
use integer::IBig;
use integer::UBig;
use num_traits::cast::ToPrimitive;
use ordered_float::OrderedFloat;
use serde::ser::SerializeMap;
use serde::ser::SerializeSeq;
use serde::Serialize;
use serde::Serializer;

pub type QueryResult = Result<QueryResolution, String>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct QueryMatch {
    pub bindings: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolutionLine {
    True,
    False,
    Match(QueryMatch),
}

impl Serialize for QueryResolutionLine {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            QueryResolutionLine::True => serializer.serialize_bool(true),
            QueryResolutionLine::False => serializer.serialize_bool(false),
            QueryResolutionLine::Match(m) => m.serialize(serializer),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResolution {
    True,
    False,
    Matches(Vec<QueryMatch>),
}

impl Serialize for QueryResolution {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            QueryResolution::True => serializer.serialize_bool(true),
            QueryResolution::False => serializer.serialize_bool(false),
            QueryResolution::Matches(matches) => matches.serialize(serializer),
        }
    }
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

impl Value {
    pub fn conjunction(conj: &[Value]) -> Value {
        if conj.is_empty() {
            panic!("can't create empty conjunction");
        } else if conj.len() == 1 {
            return conj[0].clone();
        }

        let mut conj_rev = conj.iter().rev();

        let last = conj_rev.next().unwrap().clone();
        let beflast = conj_rev.next().unwrap().clone();
        let mut conj_term = Value::Structure(",".into(), vec![beflast, last]);

        for val in conj_rev {
            conj_term = Value::Structure(",".into(), vec![val.clone(), conj_term]);
        }

        conj_term
    }

    pub fn disjunction(disj: &[Value]) -> Value {
        if disj.is_empty() {
            panic!("can't create empty disjunction");
        } else if disj.len() == 1 {
            return disj[0].clone();
        }

        let mut disj_rev = disj.iter().rev();

        let last = disj_rev.next().unwrap().clone();
        let beflast = disj_rev.next().unwrap().clone();
        let mut disj_term = Value::Structure(";".into(), vec![beflast, last]);

        for val in disj_rev {
            disj_term = Value::Structure(";".into(), vec![val.clone(), disj_term]);
        }

        disj_term
    }
}

impl From<&QueryResolutionLine> for Value {
    fn from(qrl: &QueryResolutionLine) -> Self {
        match qrl {
            QueryResolutionLine::True => Value::Atom("true".into()),
            QueryResolutionLine::False => Value::Atom("false".into()),
            QueryResolutionLine::Match(m) => Value::conjunction(
                &m.bindings
                    .iter()
                    .map(|(k, v)| {
                        Value::Structure("=".into(), vec![Value::Var(k.clone()), v.clone()])
                    })
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

impl From<&QueryResolution> for Value {
    fn from(qr: &QueryResolution) -> Self {
        match qr {
            QueryResolution::True => Value::Atom("true".into()),
            QueryResolution::False => Value::Atom("false".into()),
            QueryResolution::Matches(matches) => Value::disjunction(
                &matches
                    .iter()
                    .map(|m| {
                        Value::conjunction(
                            &m.bindings
                                .iter()
                                .map(|(k, v)| {
                                    Value::Structure(
                                        "=".into(),
                                        vec![Value::Var(k.clone()), v.clone()],
                                    )
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

struct ValueRationalInner {
    numerator: IBig,
    denominator: UBig,
}

impl Serialize for ValueRationalInner {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(2))?;
        match self.numerator.to_i64() {
            Some(small) => seq.serialize_element(&small)?,
            None => seq.serialize_element(&self.numerator.to_string())?,
        }
        match self.denominator.to_u64() {
            Some(small) => seq.serialize_element(&small)?,
            None => seq.serialize_element(&self.denominator.to_string())?,
        }
        seq.end()
    }
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Value::Integer(i) => match i.to_i64() {
                Some(small) => serializer.serialize_i64(small),
                None => {
                    let mut map = serializer.serialize_map(Some(1))?;
                    map.serialize_entry("integer", &i.to_string())?;
                    map.end()
                }
            },
            Value::Rational(r) => {
                let (numerator, denominator) = r.clone().into_parts();
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry(
                    "rational",
                    &ValueRationalInner {
                        numerator,
                        denominator,
                    },
                )?;
                map.end()
            }
            Value::Float(f) => serializer.serialize_f64(f.into_inner()),
            Value::Atom(a) => match a.as_str() {
                "true" => serializer.serialize_bool(true),
                "false" => serializer.serialize_bool(false),
                "[]" => {
                    // This should never be reached if this was obtained from run_query_iter(),
                    // but is here for completeness.
                    let seq = serializer.serialize_seq(Some(0))?;
                    seq.end()
                }
                _ => {
                    let mut map = serializer.serialize_map(Some(1))?;
                    map.serialize_entry("atom", a)?;
                    map.end()
                }
            },
            Value::String(s) => serializer.serialize_str(s),
            Value::List(l) => l.serialize(serializer),
            Value::Structure(f, args) => {
                if f == "," && args.len() == 2 {
                    // Conjunction syntax sugar
                    let mut conj = vec![args[0].clone()];
                    let mut curr_val = args[1].clone();
                    loop {
                        if let Value::Structure(f, args) = &curr_val {
                            if f == "," && args.len() == 2 {
                                conj.push(args[0].clone());
                                curr_val = args[1].clone();
                                continue;
                            }
                        }
                        conj.push(curr_val);
                        break;
                    }
                    let mut map = serializer.serialize_map(Some(1))?;
                    map.serialize_entry("conjunction", &conj)?;
                    map.end()
                } else if f == ";" && args.len() == 2 {
                    // Disjunction syntax sugar
                    let mut disj = vec![args[0].clone()];
                    let mut curr_val = args[1].clone();
                    loop {
                        if let Value::Structure(f, args) = &curr_val {
                            if f == ";" && args.len() == 2 {
                                disj.push(args[0].clone());
                                curr_val = args[1].clone();
                                continue;
                            }
                        }
                        disj.push(curr_val);
                        break;
                    }
                    let mut map = serializer.serialize_map(Some(1))?;
                    map.serialize_entry("disjunction", &disj)?;
                    map.end()
                } else {
                    let mut map = serializer.serialize_map(Some(2))?;
                    map.serialize_entry("functor", f)?;
                    map.serialize_entry("args", args)?;
                    map.end()
                }
            }
            Value::Var(v) => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("variable", v)?;
                map.end()
            }
        }
    }
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
        var_names: &mut IndexMap<HeapCellValue, VarPtr>,
    ) -> Self {
        // Adapted from MachineState::read_term_from_heap
        let mut term_stack = vec![];
        let iter = stackful_post_order_iter::<NonListElider>(
            &mut machine.machine_st.heap,
            &mut machine.machine_st.stack,
            heap_cell,
        );

        let mut anon_count: usize = 0;
        let var_ptr_cmp = |a, b| match a {
            Var::Named(name_a) => match b {
                Var::Named(name_b) => name_a.cmp(&name_b),
                _ => Ordering::Less,
            },
            _ => match b {
                Var::Named(_) => Ordering::Greater,
                _ => Ordering::Equal,
            },
        };

        for addr in iter {
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
                    let var = var_names.get(&addr).map(|x| x.borrow().clone());
                    match var {
                        Some(Var::Named(name)) => term_stack.push(Value::Var(name)),
                        _ => {
                            let anon_name = loop {
                                // Generate a name for the anonymous variable
                                let anon_name = count_to_letter_code(anon_count);

                                // Find if this name is already being used
                                var_names.sort_by(|_, a, _, b| {
                                    var_ptr_cmp(a.borrow().clone(), b.borrow().clone())
                                });
                                let binary_result = var_names.binary_search_by(|_,a| {
                                    let var_ptr = Var::Named(anon_name.clone());
                                    var_ptr_cmp(a.borrow().clone(), var_ptr.clone())
                                });

                                match binary_result {
                                    Ok(_) => anon_count += 1, // Name already used
                                    Err(_) => {
                                        // Name not used, assign it to this variable
                                        let var_ptr = VarPtr::from(Var::Named(anon_name.clone()));
                                        var_names.insert(addr, var_ptr);
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
                (HeapCellValueTag::Char, c) => {
                    term_stack.push(Value::Atom(c.into()));
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
                (HeapCellValueTag::CStr, s) => {
                    term_stack.push(Value::String(s.as_str().to_string()));
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
                (HeapCellValueTag::PStr, atom) => {
                    let tail = term_stack.pop().unwrap();

                    match tail {
                        Value::Atom(atom) => {
                            if atom == "[]" {
                                term_stack.push(Value::String(atom.as_str().to_string()));
                            }
                        },
                        Value::List(l) => {
                            let mut list: Vec<Value> = atom
                                .as_str()
                                .to_string()
                                .chars()
                                .map(|x| Value::Atom(x.to_string()))
                                .collect();
                            list.extend(l.into_iter());
                            term_stack.push(Value::List(list));
                        },
                        _ => {
                            let mut list: Vec<Value> = atom
                                .as_str()
                                .to_string()
                                .chars()
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
                // I dont know if this is needed here.
                /*
                (HeapCellValueTag::PStrLoc, h) => {
                    let atom = cell_as_atom_cell!(iter.heap[h]).get_name();
                    let tail = term_stack.pop().unwrap();

                    term_stack.push(Term::PartialString(
                        Cell::default(),
                        atom.as_str().to_owned(),
                        Box::new(tail),
                    ));
                }
                */
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
                if m.bindings.is_empty() {
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
            .filter_map(|l| match l {
                QueryResolutionLine::Match(m) => Some(m),
                _ => None,
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

#[cfg(test)]
mod tests {
    use rational::RBig;
    use serde_json::json;

    use super::*;

    #[test]
    fn value_json_serialize() {
        let ibig = IBig::from(10).pow(100);
        let ubig = UBig::from(7u32).pow(100);
        let prolog_value = Value::Structure(
            "a".into(),
            vec![
                Value::Atom("asdf".into()),
                Value::Atom("true".into()),
                Value::Atom("false".into()),
                Value::String("fdsa".into()),
                Value::List(vec![Value::Integer(1.into()), Value::Float(2.43.into())]),
                Value::Integer(ibig.clone()),
                Value::Rational(RBig::from_parts(1.into(), 7u32.into())),
                Value::Rational(RBig::from_parts(ibig.clone(), 7u32.into())),
                Value::Rational(RBig::from_parts(1.into(), ubig.clone())),
                Value::Rational(RBig::from_parts(ibig.clone(), ubig.clone())),
                Value::Var("X".into()),
            ],
        );

        let json_value = json!({
            "functor": "a",
            "args": [
                { "atom": "asdf" },
                true,
                false,
                "fdsa",
                [1, 2.43],
                { "integer": ibig.to_string() },
                { "rational": [1, 7] },
                { "rational": [ibig.to_string(), 7] },
                { "rational": [1, ubig.to_string()] },
                { "rational": [ibig.to_string(), ubig.to_string()] },
                { "variable": "X" },
            ],
        });

        assert_eq!(json_value, serde_json::to_value(prolog_value).unwrap());
    }

    #[test]
    fn value_json_serialize_conjuntions() {
        let prolog_value = Value::List(vec![
            Value::Structure(
                ",".into(),
                vec![
                    Value::Integer(1.into()),
                    Value::Structure(
                        ",".into(),
                        vec![Value::String("asdf".into()), Value::Atom("fdsa".into())],
                    ),
                ],
            ),
            Value::Structure(
                ",".into(),
                vec![
                    Value::Integer(1.into()),
                    Value::String("asdf".into()),
                    Value::Atom("fdsa".into()),
                ],
            ),
        ]);

        let json_value = json!([
            { "conjunction": [1, "asdf", { "atom": "fdsa" }] },
            { "functor": ",", "args": [1, "asdf", { "atom": "fdsa" }] },
        ]);

        assert_eq!(json_value, serde_json::to_value(prolog_value).unwrap());
    }

    #[test]
    fn value_json_serialize_disjunctions() {
        let prolog_value = Value::List(vec![
            Value::Structure(
                ";".into(),
                vec![
                    Value::Integer(1.into()),
                    Value::Structure(
                        ";".into(),
                        vec![Value::String("asdf".into()), Value::Atom("fdsa".into())],
                    ),
                ],
            ),
            Value::Structure(
                ";".into(),
                vec![
                    Value::Integer(1.into()),
                    Value::String("asdf".into()),
                    Value::Atom("fdsa".into()),
                ],
            ),
        ]);

        let json_value = json!([
            { "disjunction": [1, "asdf", { "atom": "fdsa" }] },
            { "functor": ";", "args": [1, "asdf", { "atom": "fdsa" }] },
        ]);

        assert_eq!(json_value, serde_json::to_value(prolog_value).unwrap());
    }

    #[test]
    fn query_resolution_line_json() {
        let qrl = QueryResolutionLine::True;
        let json_value = json!(true);
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());

        let qrl = QueryResolutionLine::False;
        let json_value = json!(false);
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());

        let qrl = QueryResolutionLine::Match(QueryMatch::from(btreemap! {
            "X" => Value::Atom("asdf".into()),
            "Y" => Value::String("fdsa".into()),
        }));
        let json_value = json!({
            "bindings": {
                "X": { "atom": "asdf" },
                "Y": "fdsa",
            },
        });
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());
    }

    #[test]
    fn query_resolution_json() {
        let qrl = QueryResolution::True;
        let json_value = json!(true);
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());

        let qrl = QueryResolution::False;
        let json_value = json!(false);
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());

        let qrl = QueryResolution::Matches(vec![
            QueryMatch::from(btreemap! {
                "X" => Value::Atom("a".into()),
            }),
            QueryMatch::from(btreemap! {
                "X" => Value::Atom("b".into()),
                "Y" => Value::Atom("c".into()),
            }),
        ]);
        let json_value = json!([
            {
                "bindings": {
                    "X": { "atom": "a" },
                },
            },
            {
                "bindings": {
                    "X": { "atom": "b" },
                    "Y": { "atom": "c" },
                },
            },
        ]);
        assert_eq!(json_value, serde_json::to_value(qrl).unwrap());
    }
}
