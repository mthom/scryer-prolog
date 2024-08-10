use std::{num::NonZeroI128, str::FromStr};

use dashu::Rational;
use prop::test_runner::Reason;
use proptest::prelude::*;

use scryer_prolog::{
    atom_table::{Atom, AtomTable},
    machine::parsed_results::{QueryMatch, QueryResolution, Value},
};

fn generate_query_resolution() -> impl Strategy<Value = QueryResolution> {
    prop_oneof![
        Just(QueryResolution::False),
        Just(QueryResolution::True),
        prop::collection::vec(generate_query_match(), 1..5).prop_map(QueryResolution::Matches)
    ]
}

fn atom() -> impl Strategy<Value = Atom> {
    any::<String>().prop_map(|atom| AtomTable::build_with(&AtomTable::new(), &atom))
}

fn generate_query_match() -> impl Strategy<Value = QueryMatch> {
    prop::collection::btree_map(any::<String>(), generate_value(), 1..5)
        .prop_map(|map| QueryMatch { bindings: map })
}

fn generate_value() -> impl Strategy<Value = Value> {
    let leaf = prop_oneof![
        Just(Value::Var),
        any::<u128>().prop_map(|v| Value::Integer(v.into())),
        any::<(i128, NonZeroI128)>().prop_map(|(n, d)| Value::Rational(
            Rational::from_parts_signed(n.into(), i128::from(d).into())
        )),
        any::<f64>().prop_map(|f| Value::Float(ordered_float::OrderedFloat(f))),
        atom().prop_map(Value::Atom),
        any::<String>().prop_map(Value::String),
    ];

    leaf.prop_recursive(8, 32, 10, |inner| {
        prop_oneof![
            (atom(), prop::collection::vec(inner.clone(), 0..10))
                .prop_map(|(atom, values)| Value::Structure(atom, values)),
            prop::collection::vec(inner.clone(), 0..10).prop_map(Value::List)
        ]
    })
}

#[test]
fn result_is_valid_json() {
    let table = AtomTable::new();

    proptest! {
        |(query_result in generate_query_resolution())|{
            let json_str = format!("{query_result}");
            if let Err(err) = serde_json::Value::from_str(&json_str) {
                println!("{json_str:?}");
                return Err(TestCaseError::Fail(Reason::from(format!("{err}"))))
            }
        }
    };

    drop(table);
}
