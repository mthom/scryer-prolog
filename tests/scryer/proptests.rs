use std::num::NonZeroI128;

use dashu::Rational;
use proptest::prelude::*;

use scryer_prolog::machine::parsed_results::{QueryMatch, QueryResolution, Value};

fn generate_query_resolution() -> impl Strategy<Value = QueryResolution> {
    prop_oneof![
        Just(QueryResolution::False),
        Just(QueryResolution::True),
        prop::collection::vec(generate_query_match(), 1..5).prop_map(QueryResolution::Matches)
    ]
}

fn generate_query_match() -> impl Strategy<Value = QueryMatch> {
    prop::collection::btree_map(any::<String>(), generate_value(), 1..5)
        .prop_map(|map| QueryMatch { bindings: map })
}

fn float_roundtrips(&orig: &'_ f64) -> bool {
    let Ok(json) = serde_json::to_string(&orig) else {
        return false;
    };

    let Ok(round_trip) = serde_json::from_str::<f64>(&json) else {
        return false;
    };

    orig == round_trip
}

fn generate_value() -> impl Strategy<Value = Value> {
    let leaf = prop_oneof![
        any::<u128>().prop_map(|v| Value::Integer(v.into())),
        any::<(i128, NonZeroI128)>().prop_map(|(n, d)| Value::Rational(
            Rational::from_parts_signed(n.into(), i128::from(d).into())
        )),
        any::<f64>()
            .prop_filter("failes serde_json roundtrip", float_roundtrips)
            .prop_map(|f| Value::Float(ordered_float::OrderedFloat(f))),
        any::<String>().prop_map(Value::Atom),
        any::<String>().prop_map(Value::String),
        any::<String>().prop_map(Value::Var),
    ];

    leaf.prop_recursive(8, 32, 10, |inner| {
        prop_oneof![
            (any::<String>(), prop::collection::vec(inner.clone(), 0..10))
                .prop_map(|(functor, values)| Value::Structure(functor, values)),
            prop::collection::vec(inner.clone(), 0..10).prop_map(Value::List)
        ]
    })
}

proptest! {
    #![proptest_config(
        if cfg!(miri) {
            ProptestConfig {
                failure_persistence: None,
                cases: 5,
                ..ProptestConfig::default()
            }
        } else {
            ProptestConfig::default()
        }
    )]


    // test that we can sucessfully serialize and then deserialize a value
    #[test]
    fn value_serde(original_value in generate_value()) {
        let json = serde_json::to_string(&original_value).unwrap();
        println!("{json}");
        let roundtrip_value = serde_json::from_str(&json).unwrap();
        prop_assert_eq!(original_value, roundtrip_value);
    }

    #[test]
    fn query_resolution_serde(original_value in generate_query_resolution()) {
        let json = serde_json::to_string(&original_value).unwrap();
        let roundtrip_value = serde_json::from_str(&json).unwrap();
        prop_assert_eq!(original_value, roundtrip_value);
    }
}
