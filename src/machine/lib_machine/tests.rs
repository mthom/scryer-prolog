use super::*;
use crate::MachineBuilder;

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn programatic_query() {
    let mut machine = MachineBuilder::default().build();

    machine.load_module_string(
        "facts",
        String::from(
            r#"
            triple("a", "p1", "b").
            triple("a", "p2", "b").
            "#,
        ),
    );

    let query = r#"triple("a",P,"b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(
        complete_answer,
        [
            LeafAnswer::from_bindings([("P", Term::string("p1")),]),
            LeafAnswer::from_bindings([("P", Term::string("p2")),]),
        ],
    );

    let query = r#"triple("a","p1","b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(complete_answer, [LeafAnswer::True],);

    let query = r#"triple("x","y","z")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(complete_answer, [LeafAnswer::False],);
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn failing_query() {
    let mut machine = MachineBuilder::default().build();
    let query = r#"triple("a",P,"b")."#;
    let complete_answer: Result<Vec<_>, _> = machine.run_query(query).collect();

    assert_eq!(
        complete_answer,
        Err(Term::compound(
            "error",
            [
                Term::compound(
                    "existence_error",
                    [
                        Term::atom("procedure"),
                        Term::compound("/", [Term::atom("triple"), Term::integer(3)]),
                    ]
                ),
                Term::compound("/", [Term::atom("triple"), Term::integer(3)]),
            ],
        ))
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn complex_results() {
    let mut machine = MachineBuilder::default().build();
    machine.load_module_string(
        "facts",
        r#"
        :- discontiguous(subject_class/2).
        :- discontiguous(constructor/2).

        subject_class("Todo", c).
        constructor(c, '[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]').

        subject_class("Recipe", xyz).
        constructor(xyz, '[{action: "addLink", source: "this", predicate: "recipe://title", target: "literal://string:Meta%20Muffins"}]').
        "#,
    );

    let complete_answer: Vec<_> = machine
        .run_query(r#"subject_class("Todo", C), constructor(C, Actions)."#)
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([
            ("C", Term::atom("c")),
            (
                "Actions",
                Term::atom(
                    r#"[{action: "addLink", source: "this", predicate: "todo://state", target: "todo://ready"}]"#
                )
            ),
        ])],
    );

    let complete_answer: Vec<_> = machine
        .run_query(r#"subject_class("Recipe", C), constructor(C, Actions)."#)
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([
            ("C", Term::atom("xyz")),
            (
                "Actions",
                Term::atom(
                    r#"[{action: "addLink", source: "this", predicate: "recipe://title", target: "literal://string:Meta%20Muffins"}]"#
                )
            ),
        ])],
    );

    let complete_answer: Vec<_> = machine
        .run_query("subject_class(Class, _).")
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(
        complete_answer,
        [
            LeafAnswer::from_bindings([("Class", Term::string("Todo"))]),
            LeafAnswer::from_bindings([("Class", Term::string("Recipe"))]),
        ],
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn empty_predicate() {
    let mut machine = MachineBuilder::default().build();
    machine.load_module_string(
        "facts",
        r#"
        :- discontiguous(subject_class/2).
        "#,
    );

    let complete_answer: Vec<_> = machine
        .run_query("subject_class(X, _).")
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False]);
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn list_results() {
    let mut machine = MachineBuilder::default().build();
    machine.load_module_string(
        "facts",
        r#"
        list([1,2,3]).
        "#,
    );

    let complete_answer: Vec<_> = machine
        .run_query("list(X).")
        .collect::<Result<_, _>>()
        .unwrap();
    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([(
            "X",
            Term::list([Term::integer(1), Term::integer(2), Term::integer(3)]),
        )])],
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn consult() {
    let mut machine = MachineBuilder::default().build();

    machine.consult_module_string(
        "facts",
        r#"
        triple("a", "p1", "b").
        triple("a", "p2", "b").
        "#,
    );

    let query = r#"triple("a",P,"b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(
        complete_answer,
        [
            LeafAnswer::from_bindings([("P", Term::string("p1"))]),
            LeafAnswer::from_bindings([("P", Term::string("p2"))]),
        ],
    );

    let query = r#"triple("a","p1","b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::True],);

    let query = r#"triple("x","y","z")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False],);

    machine.consult_module_string(
        "facts",
        r#"
            triple("a", "new", "b").
            "#,
    );

    let query = r#"triple("a","p1","b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False],);

    let query = r#"triple("a","new","b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::True]);
}

/*
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
#[ignore = "uses old flawed interface"]
fn integration_test() {
    let mut machine = MachineBuilder::default().build();

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
*/

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn findall() {
    let mut machine = MachineBuilder::default().build();

    machine.consult_module_string(
        "facts",
        r#"
        triple("a", "p1", "b").
        triple("a", "p2", "b").
        "#,
    );

    let query = r#"findall([Predicate, Target], triple(_,Predicate,Target), Result)."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([(
            "Result",
            Term::list([
                Term::list([Term::string("p1"), Term::string("b")]),
                Term::list([Term::string("p2"), Term::string("b")]),
            ])
        )])]
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn dont_return_partial_matches() {
    let mut machine = MachineBuilder::default().build();

    machine.consult_module_string(
        "facts",
        r#"
        :- discontiguous(property_resolve/2).
        subject_class("Todo", c).
        "#,
    );

    let query = r#"property_resolve(C, "isLiked"), subject_class("Todo", C)."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False]);

    let query = r#"subject_class("Todo", C), property_resolve(C, "isLiked")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False]);
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn dont_return_partial_matches_without_discountiguous() {
    let mut machine = MachineBuilder::default().build();

    machine.consult_module_string(
        "facts",
        r#"
        a("true for a").
        b("true for b").
        "#,
    );

    let query = r#"a("true for a")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::True]);

    let query = r#"a("true for a"), b("true for b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::True]);

    let query = r#"a("true for b"), b("true for b")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False]);

    let query = r#"a("true for a"), b("true for a")."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();
    assert_eq!(complete_answer, [LeafAnswer::False]);
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn non_existent_predicate_should_not_cause_panic_when_other_predicates_are_defined() {
    let mut machine = MachineBuilder::default().build();

    machine.consult_module_string(
        "facts",
        r#"
        triple("a", "p1", "b").
        triple("a", "p2", "b").
        "#,
    );

    let query = r#"non_existent_predicate("a","p1","b")."#;
    let complete_answer: Result<Vec<_>, _> = machine.run_query(query).collect();

    assert_eq!(
        complete_answer,
        Err(Term::compound(
            "error",
            [
                Term::compound(
                    "existence_error",
                    [
                        Term::atom("procedure"),
                        Term::compound(
                            "/",
                            [Term::atom("non_existent_predicate"), Term::integer(3)],
                        ),
                    ],
                ),
                Term::compound(
                    "/",
                    [Term::atom("non_existent_predicate"), Term::integer(3)]
                ),
            ],
        ))
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn atom_quoting() {
    let mut machine = MachineBuilder::default().build();

    let query = "X = '.'.";
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([("X", Term::atom("."))])]
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn rational_number() {
    use crate::parser::dashu::rational::RBig;
    let mut machine = MachineBuilder::default().build();

    let query = "X is 1 rdiv 2.";
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([(
            "X",
            Term::rational(RBig::from_parts(1.into(), 2u32.into()))
        )])]
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn big_integer() {
    use crate::parser::dashu::integer::IBig;
    let mut machine = MachineBuilder::default().build();

    let query = "X is 10^100.";
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([(
            "X",
            Term::integer(IBig::from(10).pow(100))
        )])],
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn complicated_term() {
    let mut machine = MachineBuilder::default().build();

    let query = r#"X = a("asdf", [42, 2.54, asdf, a, [a,b|_], Z])."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    let expected = Term::Compound(
        // Compound term
        "a".into(),
        vec![
            Term::String("asdf".into()), // String
            Term::List(vec![
                Term::Integer(42.into()),  // Fixnum
                Term::Float(2.54),         // Float
                Term::Atom("asdf".into()), // Atom
                Term::Atom("a".into()),    // Char
                Term::Compound(
                    // Partial string
                    ".".into(),
                    vec![
                        Term::Atom("a".into()),
                        Term::Compound(
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
        complete_answer,
        [LeafAnswer::from_bindings([("X", expected)])]
    );
}

#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_2341() {
    let mut machine = MachineBuilder::default().build();

    machine.load_module_string(
        "facts",
        r#"
        male(stephen).
        parent(albert,edward).
        father(F,C):-parent(F,C),male(F).
        "#,
    );

    let query = r#"father(F,C)."#;
    let complete_answer: Vec<_> = machine.run_query(query).collect::<Result<_, _>>().unwrap();

    assert_eq!(complete_answer, [LeafAnswer::False]);
}

#[test]
#[cfg_attr(miri, ignore)]
fn query_iterator_determinism() {
    let mut machine = MachineBuilder::default().build();

    {
        let mut iterator = machine.run_query("X = 1.");

        iterator.next();
        assert_eq!(iterator.next(), None);
    }

    {
        let mut iterator = machine.run_query("X = 1 ; false.");

        iterator.next();

        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
        assert_eq!(iterator.next(), None);
    }

    {
        let mut iterator = machine.run_query("false.");

        assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
        assert_eq!(iterator.next(), None);
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn query_iterator_backtracking_when_no_variables() {
    let mut machine = MachineBuilder::default().build();

    let mut iterator = machine.run_query("true;false.");

    assert_eq!(iterator.next(), Some(Ok(LeafAnswer::True)));
    assert_eq!(iterator.next(), Some(Ok(LeafAnswer::False)));
    assert_eq!(iterator.next(), None);
}

#[test]
#[cfg_attr(miri, ignore)]
fn differentiate_anonymous_variables() {
    let mut machine = MachineBuilder::default().build();

    let complete_answer: Vec<_> = machine
        .run_query("A = [_,_], _B = 1 ; B = [_,_].")
        .collect::<Result<_, _>>()
        .unwrap();

    assert_eq!(
        complete_answer,
        [
            LeafAnswer::from_bindings([
                (
                    "A",
                    Term::list([Term::variable("_A"), Term::variable("_C")])
                ),
                ("_B", Term::integer(1)),
            ]),
            LeafAnswer::from_bindings([(
                "B",
                Term::list([Term::variable("_A"), Term::variable("_C")])
            ),]),
        ]
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn order_of_variables_in_binding() {
    let mut machine = MachineBuilder::default().build();

    let complete_answer: Vec<_> = machine
        .run_query("X = Y, Z = W.")
        .collect::<Result<_, _>>()
        .unwrap();

    assert_eq!(
        complete_answer,
        [LeafAnswer::from_bindings([
            ("X", Term::variable("Y")),
            ("Z", Term::variable("W")),
        ])]
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn errors_and_exceptions() {
    let mut machine = MachineBuilder::default().build();

    let complete_answer: Vec<_> = machine.run_query("functor(_,_,_).").collect();

    assert_eq!(
        complete_answer,
        [Err(Term::compound(
            "error",
            [
                Term::atom("instantiation_error"),
                Term::compound("/", [Term::atom("functor"), Term::integer(3)]),
            ],
        ))]
    );

    let complete_answer: Vec<_> = machine.run_query("throw(a).").collect();

    assert_eq!(
        complete_answer,
        [Ok(LeafAnswer::Exception(Term::atom("a")))]
    );
}
