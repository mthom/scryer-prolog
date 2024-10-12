use super::*;
use crate::machine::{QueryMatch, QueryResolution, Term};

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
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
        Ok(QueryResolution::Matches(vec![
            QueryMatch::from(btreemap! {
                "P" => Term::from("p1"),
            }),
            QueryMatch::from(btreemap! {
                "P" => Term::from("p2"),
            }),
        ]))
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("a","p1","b")."#)),
        Ok(QueryResolution::True)
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("x","y","z")."#)),
        Ok(QueryResolution::False)
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn failing_query() {
    let mut machine = Machine::new_lib();
    let query = String::from(r#"triple("a",P,"b")."#);
    let output = machine.run_query(query);
    assert_eq!(
        output,
        Err(String::from(
            "error existence_error procedure / triple 3 / triple 3"
        ))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn complex_results() {
    let mut machine = Machine::new_lib();
    machine.load_module_string(
        "facts",
        r#"
        :- discontiguous(subject_class/2).
        :- discontiguous(constructor/2).

        subject_class("Todo", c).
        constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').

        subject_class("Recipe", xyz).
        constructor(xyz, '[{action: "addLink", source: "this", predicate: "recipe://title", target: "literal://string:Meta%20Muffins"}]').
        "#.to_string());

    let result = machine.run_query(String::from(
        "subject_class(\"Todo\", C), constructor(C, Actions).",
    ));
    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "C" => Term::Atom("c".into()),
                "Actions" => Term::Atom("[{action: \"addLink\", source: \"this\", predicate: \"todo://state\", target: \"todo://ready\"}]".into()),
            }
        ),]))
    );

    let result = machine.run_query(String::from(
        "subject_class(\"Recipe\", C), constructor(C, Actions).",
    ));
    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "C" => Term::Atom("xyz".into()),
                "Actions" => Term::Atom("[{action: \"addLink\", source: \"this\", predicate: \"recipe://title\", target: \"literal://string:Meta%20Muffins\"}]".into()),
            }
        ),]))
    );

    let result = machine.run_query(String::from("subject_class(Class, _)."));
    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![
            QueryMatch::from(btreemap! {
                "Class" => Term::String("Todo".into())
            }),
            QueryMatch::from(btreemap! {
                "Class" => Term::String("Recipe".into())
            }),
        ]))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn empty_predicate() {
    let mut machine = Machine::new_lib();
    machine.load_module_string(
        "facts",
        r#"
        :- discontiguous(subject_class/2).
        "#
        .to_string(),
    );

    let result = machine.run_query(String::from("subject_class(X, _)."));
    assert_eq!(result, Ok(QueryResolution::False));
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn list_results() {
    let mut machine = Machine::new_lib();
    machine.load_module_string(
        "facts",
        r#"
        list([1,2,3]).
        "#
        .to_string(),
    );

    let result = machine.run_query(String::from("list(X)."));
    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => Term::List(vec![
                    Term::Integer(1.into()),
                    Term::Integer(2.into()),
                    Term::Integer(3.into()),
                ]),
            }
        ),]))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn consult() {
    let mut machine = Machine::new_lib();

    machine.consult_module_string(
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
        Ok(QueryResolution::Matches(vec![
            QueryMatch::from(btreemap! {
                "P" => Term::from("p1"),
            }),
            QueryMatch::from(btreemap! {
                "P" => Term::from("p2"),
            }),
        ]))
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("a","p1","b")."#)),
        Ok(QueryResolution::True)
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("x","y","z")."#)),
        Ok(QueryResolution::False)
    );

    machine.consult_module_string(
        "facts",
        String::from(
            r#"
            triple("a", "new", "b").
            "#,
        ),
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("a","p1","b")."#)),
        Ok(QueryResolution::False)
    );

    assert_eq!(
        machine.run_query(String::from(r#"triple("a","new","b")."#)),
        Ok(QueryResolution::True)
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
#[ignore = "uses old flawed interface"]
fn integration_test() {
    let mut machine = Machine::new_lib();

    // File with test commands, i.e. program code to consult and queries to run
    let code = include_str!("./lib_integration_test_commands.txt");

    // Split the code into blocks
    let blocks = code.split("=====");

    let mut i = 0;
    let mut last_result: Option<_> = None;
    // Iterate over the blocks
    for block in blocks {
        // Trim the block to remove any leading or trailing whitespace
        let block = block.trim();

        // Skip empty blocks
        if block.is_empty() {
            continue;
        }

        // Check if the block is a query
        if let Some(query) = block.strip_prefix("query") {
            // Parse and execute the query
            let result = machine.run_query(query.to_string());
            assert!(result.is_ok());

            last_result = Some(result);
        } else if let Some(code) = block.strip_prefix("consult") {
            // Load the code into the machine
            machine.consult_module_string("facts", code.to_string());
        } else if let Some(result) = block.strip_prefix("result") {
            i += 1;
            if let Some(Ok(ref last_result)) = last_result {
                println!("\n\n=====Result No. {i}=======\n{last_result}\n===============");
                assert_eq!(last_result.to_string(), result.to_string().trim(),)
            }
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn findall() {
    let mut machine = Machine::new_lib();

    machine.consult_module_string(
        "facts",
        String::from(
            r#"
            triple("a", "p1", "b").
            triple("a", "p2", "b").
            "#,
        ),
    );

    let query =
        String::from(r#"findall([Predicate, Target], triple(_,Predicate,Target), Result)."#);
    let output = machine.run_query(query);
    assert_eq!(
        output,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "Result" => Term::List(
                    Vec::from([
                        Term::List([Term::from("p1"), Term::from("b")].into()),
                        Term::List([Term::from("p2"), Term::from("b")].into()),
                    ])
                ),
            }
        ),]))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn dont_return_partial_matches() {
    let mut machine = Machine::new_lib();

    machine.consult_module_string(
        "facts",
        String::from(
            r#"
            :- discontiguous(property_resolve/2).
            subject_class("Todo", c).
            "#,
        ),
    );

    let query = String::from(r#"property_resolve(C, "isLiked"), subject_class("Todo", C)."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::False));

    let query = String::from(r#"subject_class("Todo", C), property_resolve(C, "isLiked")."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::False));
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn dont_return_partial_matches_without_discountiguous() {
    let mut machine = Machine::new_lib();

    machine.consult_module_string(
        "facts",
        String::from(
            r#"
            a("true for a").
            b("true for b").
            "#,
        ),
    );

    let query = String::from(r#"a("true for a")."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::True));

    let query = String::from(r#"a("true for a"), b("true for b")."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::True));

    let query = String::from(r#"a("true for b"), b("true for b")."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::False));

    let query = String::from(r#"a("true for a"), b("true for a")."#);
    let output = machine.run_query(query);
    assert_eq!(output, Ok(QueryResolution::False));
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn non_existent_predicate_should_not_cause_panic_when_other_predicates_are_defined() {
    let mut machine = Machine::new_lib();

    machine.consult_module_string(
        "facts",
        String::from(
            r#"
            triple("a", "p1", "b").
            triple("a", "p2", "b").
            "#,
        ),
    );

    let query = String::from("non_existent_predicate(\"a\",\"p1\",\"b\").");

    let result = machine.run_query(query);

    assert_eq!(
        result,
        Err(String::from("error existence_error procedure / non_existent_predicate 3 / non_existent_predicate 3"))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn atom_quoting() {
    let mut machine = Machine::new_lib();

    let query = "X = '.'.".into();

    let result = machine.run_query(query);

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => Term::Atom(".".into()),
            }
        )]))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn rational_number() {
    use crate::parser::dashu::rational::RBig;
    let mut machine = Machine::new_lib();

    let query = "X is 1 rdiv 2.".into();

    let result = machine.run_query(query);

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => Term::Rational(RBig::from_parts(1.into(), 2u32.into())),
            }
        )]))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn big_integer() {
    use crate::parser::dashu::integer::IBig;
    let mut machine = Machine::new_lib();

    let query = "X is 10^100.".into();

    let result = machine.run_query(query);

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => Term::Integer(IBig::from(10).pow(100)),
            }
        )]))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn complicated_term() {
    let mut machine = Machine::new_lib();

    let query = "X = a(\"asdf\", [42, 2.54, asdf, a, [a,b|_], Z]).".into();

    let result = machine.run_query(query);

    let expected = Term::Structure(
        // Composite term
        "a".into(),
        vec![
            Term::String("asdf".into()), // String
            Term::List(vec![
                Term::Integer(42.into()),  // Fixnum
                Term::Float(2.54.into()),  // Float
                Term::Atom("asdf".into()), // Atom
                Term::Atom("a".into()),    // Char
                Term::Structure(
                    // Partial string
                    ".".into(),
                    vec![
                        Term::Atom("a".into()),
                        Term::Structure(
                            ".".into(),
                            vec![
                                Term::Atom("b".into()),
                                Term::Var("_A".into()), // Anonymous variable
                            ],
                        ),
                    ],
                ),
                Term::Var("Z".into()), // Named variable
            ]),
        ],
    );

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => expected,
            }
        )]))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_2341() {
    let mut machine = Machine::new_lib();

    machine.load_module_string(
        "facts",
        String::from(
            r#"
            male(stephen).
            parent(albert,edward).
            father(F,C):-parent(F,C),male(F).
            "#,
        ),
    );

    let query = String::from(r#"father(F,C)."#);
    let output = machine.run_query(query);

    assert_eq!(output, Ok(QueryResolution::False));
}

#[test]
#[cfg_attr(miri, ignore)]
fn query_iterator_determinism() {
    let mut machine = Machine::new_lib();

    {
        let mut iterator = machine.run_query_iter("X = 1.".into());

        iterator.next();
        assert_eq!(iterator.next(), None);
    }

    {
        let mut iterator = machine.run_query_iter("X = 1 ; false.".into());

        iterator.next();

        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
        assert_eq!(iterator.next(), None);
    }

    {
        let mut iterator = machine.run_query_iter("false.".into());

        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
        assert_eq!(iterator.next(), None);
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn query_iterator_backtracking_when_no_variables() {
    let mut machine = Machine::new_lib();

    let mut iterator = machine.run_query_iter("true;false.".into());

    assert_eq!(iterator.next(), Some(Ok(LeafAnswer::True)));
    assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
    assert_eq!(iterator.next(), None);
}

#[test]
#[cfg_attr(miri, ignore)]
fn differentiate_anonymous_variables() {
    let mut machine = Machine::new_lib();

    let result = machine.run_query("A = [_,_], _B = 1 ; B = [_,_].".into());

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![
            QueryMatch::from(btreemap! {
                "A" => Term::List(vec![Term::Var("_A".into()), Term::Var("_C".into())]),
                "_B" => Term::Integer(1.into()),
            }),
            QueryMatch::from(btreemap! {
                "B" => Term::List(vec![Term::Var("_A".into()), Term::Var("_C".into())]),
            }),
        ]))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn order_of_variables_in_binding() {
    let mut machine = Machine::new_lib();

    let result = machine.run_query("X = Y, Z = W.".into());

    assert_eq!(
        result,
        Ok(QueryResolution::Matches(vec![QueryMatch::from(
            btreemap! {
                "X" => Term::Var("Y".into()),
                "Z" => Term::Var("W".into()),
            }
        ),]))
    );
}

