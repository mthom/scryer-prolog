use super::*;
use test_utils::*;

#[test]
fn test_queries_on_facts()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p(Z, Z).");
    submit(&mut wam, "clouds(are, nice).");

    assert_prolog_success!(&mut wam, "?- p(Z, Z).", ["Z = _0"]);
    assert_prolog_success!(&mut wam, "?- p(Z, z).", ["Z = z"]);
    assert_prolog_success!(&mut wam, "?- p(Z, w).", ["Z = w"]);

    assert_prolog_failure!(&mut wam, "?- p(z, w).");

    assert_prolog_success!(&mut wam, "?- p(w, w).");

    assert_prolog_failure!(&mut wam, "?- clouds(Z, Z).");

    assert_prolog_success!(&mut wam, "?- clouds(are, Z).", ["Z = nice"]);
    assert_prolog_success!(&mut wam, "?- clouds(Z, nice).", ["Z = are"]);

    submit(&mut wam, "p(Z, h(Z, W), f(W)).");

    assert_prolog_failure!(&mut wam, "?- p(z, h(z, z), f(w)).");
    assert_prolog_success!(&mut wam, "?- p(z, h(z, w), f(w)).");
    assert_prolog_success!(&mut wam, "?- p(z, h(z, W), f(w)).", ["W = w"]);
    assert_prolog_success!(&mut wam, "?- p(Z, h(Z, w), f(Z)).", ["Z = w"]);
    assert_prolog_failure!(&mut wam, "?- p(z, h(Z, w), f(Z)).");

    submit(&mut wam, "p(f(X), h(Y, f(a)), Y).");

    assert_prolog_success!(&mut wam, "?- p(Z, h(Z, W), f(W)).", ["W = f(a)", "Z = f(f(a))"]);
}

#[test]
fn test_queries_on_rules() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(X, Y) :- q(X, Z), r(Z, Y).");
    submit(&mut wam, "q(q, s).");
    submit(&mut wam, "r(s, t).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", ["Y = t", "X = q"]);
    assert_prolog_success!(&mut wam, "?- p(q, t).");
    assert_prolog_failure!(&mut wam, "?- p(t, q).");
    assert_prolog_success!(&mut wam, "?- p(q, T).", ["T = t"]);
    assert_prolog_failure!(&mut wam, "?- p(t, t).");

    submit(&mut wam, "p(X, Y) :- q(f(f(X)), R), r(S, T).");
    submit(&mut wam, "q(f(f(X)), r).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", ["X = _0", "Y = _1"]);

    submit(&mut wam, "q(f(f(x)), r).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", ["X = x", "Y = _1"]);

    submit(&mut wam, "p(X, Y) :- q(X, Y), r(X, Y).");
    submit(&mut wam, "q(s, t).");
    submit(&mut wam, "r(X, Y) :- r(a).");
    submit(&mut wam, "r(a).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", ["X = s", "Y = t"]);
    assert_prolog_failure!(&mut wam, "?- p(t, S).");
    assert_prolog_success!(&mut wam, "?- p(s, T).", ["T = t"]);
    assert_prolog_success!(&mut wam, "?- p(S, t).", ["S = s"]);

    submit(&mut wam, "p(f(f(a), g(b), X), g(b), h) :- q(X, Y).");
    submit(&mut wam, "q(X, Y).");

    assert_prolog_success!(&mut wam,  "?- p(f(X, Y, Z), g(b), h).", ["Z = _3", "Y = g(b)", "X = f(a)"]);
    assert_prolog_failure!(&mut wam, "?- p(f(X, g(Y), Z), g(Z), X).");
    assert_prolog_success!(&mut wam, "?- p(f(X, g(Y), Z), g(Z), h).", ["Z = b", "Y = b", "X = f(a)"]);
    assert_prolog_success!(&mut wam, "?- p(Z, Y, X).", ["X = h", "Y = g(b)", "Z = f(f(a), g(b), _7)"]);
    assert_prolog_success!(&mut wam, "?- p(f(X, Y, Z), Y, h).", ["Y = g(b)", "Z = _3", "X = f(a)"]);

    submit(&mut wam, "p(_, f(_, Y, _)) :- h(Y).");
    submit(&mut wam, "h(y).");

    assert_prolog_success!(&mut wam, "?- p(_, f(_, Y, _)).", ["Y = y"]);
    assert_prolog_success!(&mut wam, "?- p(_, f(_, y, _)).");
    assert_prolog_failure!(&mut wam, "?- p(_, f(_, z, _)).");
}

#[test]
fn test_queries_on_predicates() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(X, a). p(b, X).");

    assert_prolog_success!(&mut wam, "?- p(x, Y).", ["Y = a"]);
    assert_prolog_success!(&mut wam, "?- p(X, a).", ["X = _0",  // 1st case
                                                     "X = b"]); // 2nd case.
    assert_prolog_success!(&mut wam, "?- p(b, X).", ["X = a",  // 1st case
                                                     "X = _0"]); // 2nd case.
    assert_prolog_success!(&mut wam, "?- p(X, X).", ["X = a",
                                                     "X = b"]);
    assert_prolog_success!(&mut wam, "?- p(b, a).");
    assert_prolog_failure!(&mut wam, "?- p(a, b).");

    submit(&mut wam, "p(X, Y, a). p(X, a, Y). p(X, Y, a).");

    assert_prolog_success!(&mut wam, "?- p(c, d, X).", ["X = a",
                                                    "X = a"]);
    assert_prolog_success!(&mut wam, "?- p(a, a, a).");
    assert_prolog_failure!(&mut wam, "?- p(b, c, d).");

    submit(&mut wam, "p(X, a). p(X, Y) :- q(Z), p(X, X).");

    assert_prolog_success!(&mut wam, "?- p(X, Y).", ["X = _0", "Y = a"]);
    assert_prolog_success!(&mut wam, "?- p(x, a).");
    assert_prolog_success!(&mut wam, "?- p(X, a).", ["X = _0"]);
    assert_prolog_failure!(&mut wam, "?- p(X, b).");

    submit(&mut wam, "q(z).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, b).", ["X = a",
                                                                "X = a",
                                                                "X = a"],
                                      3);
    assert_prolog_success!(&mut wam, "?- p(x, a).");
    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", ["X = _0", "Y = a",
                                                                "Y = _1", "X = a",
                                                                "Y = _1", "X = a"],
                                      3);

    submit(&mut wam, "p(X, a). p(X, Y) :- q(Y), p(X, X).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", ["X = _0", "Y = a",
                                                                "Y = z", "X = a"],
                                      2);
    assert_prolog_failure!(&mut wam, "?- p(X, b).");

    submit(&mut wam, "p(a, z). p(X, Y) :- q(Y), p(X, Y).");

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, Y).", ["X = a", "Y = z",
                                                                "X = a", "Y = z"],
                                      2);

    assert_prolog_success_with_limit!(&mut wam, "?- p(X, z).", ["X = a",
                                                                "X = a"],
                                      2);
    assert_prolog_success!(&mut wam, "?- p(a, z).");
    assert_prolog_success_with_limit!(&mut wam, "?- p(a, X).", ["X = z",
                                                                "X = z"],
                                      2);
    assert_prolog_failure!(&mut wam, "?- p(b, a).");

    submit(&mut wam, "p(X, Y, Z) :- q(X), r(Y), s(Z).
                      p(a, b, Z) :- q(Z).");

    submit(&mut wam, "q(x).");
    submit(&mut wam, "r(y).");
    submit(&mut wam, "s(z).");

    assert_prolog_success!(&mut wam, "?- p(X, Y, Z).", ["Y = y", "X = x", "Z = z",
                                                        "Y = b", "X = a", "Z = x"]);
    assert_prolog_failure!(&mut wam, "?- p(a, b, c).");
    assert_prolog_success!(&mut wam, "?- p(a, b, C).", ["C = x"]);

    submit(&mut wam, "p(X) :- q(X). p(X) :- r(X).");
    submit(&mut wam, "q(X) :- a.");
    submit(&mut wam, "r(X) :- s(X, t). r(X) :- t(X, u).");
    
    submit(&mut wam, "s(x, t).");
    submit(&mut wam, "t(y, u).");

    assert_prolog_success!(&mut wam, "?- p(X).", ["X = x",
                                                  "X = y"]);
    assert_prolog_success!(&mut wam, "?- p(x).");
    assert_prolog_success!(&mut wam, "?- p(y).");
    assert_prolog_failure!(&mut wam, "?- p(z).");

    submit(&mut wam, "p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
                      p(X, Y, Z) :- h(Y), g(W), z(Z).");
    submit(&mut wam, "g(f(X)) :- z(X). g(X) :- h(X).");
    submit(&mut wam, "h(w). h(x). h(z).");
    submit(&mut wam, "f(s).");
    submit(&mut wam, "z(Z).");

    assert_prolog_success!(&mut wam, "?- p(X, Y, Z).", ["Y = h(w)", "X = f(f(s))", "Z = _2",
                                                        "Y = h(x)", "X = f(f(s))", "Z = _2",
                                                        "Y = h(z)", "X = f(f(s))", "Z = _2",
                                                        "Y = w", "Z = _2", "X = _0",
                                                        "Y = w", "Z = _2", "X = _0",
                                                        "Y = w", "Z = _2", "X = _0",
                                                        "Y = w", "Z = _2", "X = _0",
                                                        "Y = x", "Z = _2", "X = _0",
                                                        "Y = x", "Z = _2", "X = _0",
                                                        "Y = x", "Z = _2", "X = _0",
                                                        "Y = x", "Z = _2", "X = _0",
                                                        "Y = z", "Z = _2", "X = _0",
                                                        "Y = z", "Z = _2", "X = _0",
                                                        "Y = z", "Z = _2", "X = _0",
                                                        "Y = z", "Z = _2", "X = _0"]);
    assert_prolog_success!(&mut wam, "?- p(X, X, Z).", ["Z = _1", "X = w",
                                                        "Z = _1", "X = w",
                                                        "Z = _1", "X = w",
                                                        "Z = _1", "X = w",
                                                        "Z = _1", "X = x",
                                                        "Z = _1", "X = x",
                                                        "Z = _1", "X = x",
                                                        "Z = _1", "X = x",
                                                        "Z = _1", "X = z",
                                                        "Z = _1", "X = z",
                                                        "Z = _1", "X = z",
                                                        "Z = _1", "X = z"]);
    assert_prolog_success!(&mut wam, "?- p(f(f(Z)), Y, Z).", ["Y = h(w)", "Z = s",
                                                              "Y = h(x)", "Z = s",
                                                              "Y = h(z)", "Z = s",
                                                              "Y = w", "Z = _1",
                                                              "Y = w", "Z = _1",
                                                              "Y = w", "Z = _1",
                                                              "Y = w", "Z = _1",
                                                              "Y = x", "Z = _1",
                                                              "Y = x", "Z = _1",
                                                              "Y = x", "Z = _1",
                                                              "Y = x", "Z = _1",
                                                              "Y = z", "Z = _1",
                                                              "Y = z", "Z = _1",
                                                              "Y = z", "Z = _1",
                                                              "Y = z", "Z = _1"]);
    assert_prolog_success!(&mut wam, "?- p(X, X, X).", ["X = w",
                                                        "X = w",
                                                        "X = w",
                                                        "X = w",
                                                        "X = x",
                                                        "X = x",
                                                        "X = x",
                                                        "X = x",
                                                        "X = z",
                                                        "X = z",
                                                        "X = z",
                                                        "X = z"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y, X).", ["Y = h(w)", "X = f(f(s))",
                                                        "Y = h(x)", "X = f(f(s))",
                                                        "Y = h(z)", "X = f(f(s))",
                                                        "Y = w", "X = _0",
                                                        "Y = w", "X = _0",
                                                        "Y = w", "X = _0",
                                                        "Y = w", "X = _0",
                                                        "Y = x", "X = _0",
                                                        "Y = x", "X = _0",
                                                        "Y = x", "X = _0",
                                                        "Y = x", "X = _0",
                                                        "Y = z", "X = _0",
                                                        "Y = z", "X = _0",
                                                        "Y = z", "X = _0",
                                                        "Y = z", "X = _0"]);
    assert_prolog_failure!(&mut wam, "?- p(f(f(X)), h(f(X)), Y).");

    submit(&mut wam, "p(X) :- f(Y), g(Y), i(X, Y).");
    submit(&mut wam, "g(f(a)). g(f(b)). g(f(c)).");
    submit(&mut wam, "f(f(a)). f(f(b)). f(f(c)).");
    submit(&mut wam, "i(X, X).");

    assert_prolog_success!(&mut wam, "?- p(X).", ["X = f(a)",
                                                  "X = f(b)",
                                                  "X = f(c)"]);
    
    submit(&mut wam, "p(X) :- f(f(Y)), g(Y, f(Y)), i(X, f(Y)).");
    submit(&mut wam, "g(Y, f(Y)) :- g(f(Y)).");

    assert_prolog_success!(&mut wam, "?- p(X).", ["X = f(a)",
                                                  "X = f(b)",
                                                  "X = f(c)"]);    
}

#[test]
fn test_queries_on_cuts() {
    let mut wam = Machine::new();

    // test shallow cuts.
    submit(&mut wam, "memberchk(X, [X|_]) :- !.
                      memberchk(X, [_|Xs]) :- memberchk(X, Xs).");

    assert_prolog_success!(&mut wam, "?- memberchk(X, [a,b,c]).", ["X = a"]);
    assert_prolog_success!(&mut wam, "?- memberchk([X,X], [a,b,c,[d,e],[d,d]]).", ["X = d"]);
    assert_prolog_success!(&mut wam, "?- memberchk([X,X], [a,b,c,[D,d],[e,e]]).", ["X = d", "D = d"]);
    assert_prolog_failure!(&mut wam, "?- memberchk([X,X], [a,b,c,[e,d],[f,e]]).");
    assert_prolog_failure!(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,d],[f,e]]).");
    assert_prolog_success!(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,e,d],[f,e]]).", ["X = e",
                                                                                       "Y = d"]);

    // test deep cuts.
    submit(&mut wam, "commit :- a, !.");

    assert_prolog_failure!(&mut wam, "?- commit.");

    submit(&mut wam, "a.");

    assert_prolog_success!(&mut wam, "?- commit.");

    submit(&mut wam, "commit(X) :- a(X), !.");

    assert_prolog_failure!(&mut wam, "?- commit(X).");

    submit(&mut wam, "a(x).");

    assert_prolog_success!(&mut wam, "?- commit(X).", ["X = x"]);

    submit(&mut wam, "a :- b, !, c. a :- d.");

    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "b.");

    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "d.");

    // we've committed to the first clause since the query on b
    // succeeds, so we expect failure here.
    assert_prolog_failure!(&mut wam, "?- a.");

    submit(&mut wam, "c.");

    assert_prolog_success!(&mut wam, "?- a.");

    submit(&mut wam, "a(X) :- b, !, c(X). a(X) :- d(X).");

    assert_prolog_failure!(&mut wam, "?- a(X).");

    submit(&mut wam, "c(c).");
    submit(&mut wam, "d(d).");

    assert_prolog_success!(&mut wam, "?- a(X).", ["X = c"]);

    submit(&mut wam, "b.");

    assert_prolog_success!(&mut wam, "?- a(X).", ["X = c"]);

    wam.clear();

    assert_prolog_failure!(&mut wam, "?- c(X).");

    submit(&mut wam, "a(X) :- b, c(X), !. a(X) :- d(X).");
    submit(&mut wam, "b.");

    assert_prolog_failure!(&mut wam, "?- a(X).");

    submit(&mut wam, "d(d).");

    assert_prolog_success!(&mut wam, "?- a(X).", ["X = d"]);

    submit(&mut wam, "c(c).");

    assert_prolog_success!(&mut wam, "?- a(X).", ["X = c"]);
}

#[test]
fn test_queries_on_lists()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p([Z, W]).");

    assert_prolog_success!(&mut wam, "?- p([Z, Z]).", ["Z = _0"]);
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", ["Z = _0", "W = [_3]"]);
    assert_prolog_success!(&mut wam, "?- p([Z | [Z]]).", ["Z = _0"]);
    assert_prolog_success!(&mut wam, "?- p([Z | [W]]).", ["Z = _2", "W = _0"]);
    assert_prolog_failure!(&mut wam, "?- p([Z | []]).");

    submit(&mut wam, "p([Z, Z]).");

    assert_prolog_success!(&mut wam, "?- p([Z, Z]).", ["Z = _0"]);
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", ["Z = _0", "W = [_0]"]);
    assert_prolog_success!(&mut wam, "?- p([Z | [Z]]).", ["Z = _0"]);
    assert_prolog_success!(&mut wam, "?- p([Z | [W]]).", ["Z = _2", "W = _2"]);
    assert_prolog_failure!(&mut wam, "?- p([Z | []]).");

    submit(&mut wam, "p([Z]).");

    assert_prolog_failure!(&mut wam, "?- p([Z, Z]).");
    assert_prolog_failure!(&mut wam, "?- p([Z, W, Y]).");
    assert_prolog_success!(&mut wam, "?- p([Z | W]).", ["W = []", "Z = _0"]);
    assert_prolog_failure!(&mut wam, "?- p([Z | [Z]]).");
    assert_prolog_failure!(&mut wam, "?- p([Z | [W]]).");
    assert_prolog_success!(&mut wam, "?- p([Z | []]).", ["Z = _0"]);

    submit(&mut wam, "member(X, [X|_]).
                      member(X, [_|Xs]) :- member(X, Xs).");

    assert_prolog_failure!(&mut wam, "?- member(a, [c, [X, Y]]).");
    assert_prolog_failure!(&mut wam, "?- member(c, [a, [X, Y]]).");
    assert_prolog_success!(&mut wam, "?- member(a, [a, [X, Y]]).", ["X = _2", "Y = _0"]);
    
    assert_prolog_success!(&mut wam, "?- member(a, [X, Y, Z]).", ["Y = _2", "X = a",  "Z = _0",
                                                                  "Y = a",  "X = _4", "Z = _0",
                                                                  "Y = _2",  "X = _4", "Z = a"]);

    assert_prolog_success!(&mut wam, "?- member([X, X], [a, [X, Y]]).", ["X = _0", "Y = _0"]);
    assert_prolog_success!(&mut wam, "?- member([X, X], [a, [b, c], [b, b], [Z, x], [d, f]]).",
                           ["Z = _14", "X = b",
                            "Z = x",   "X = x"]);
    assert_prolog_failure!(&mut wam, "?- member([X, X], [a, [b, c], [b, d], [foo, x], [d, f]]).");
    assert_prolog_success!(&mut wam, "?- member([X, Y], [a, [b, c], [b, b], [Z, x], [d, f]]).",
                           ["X = b", "Y = c", "Z = _14",
                            "X = b", "Y = b", "Z = _14",
                            "X = _14", "Y = x", "Z = _14",
                            "X = d", "Y = f", "Z = _14"]);
    assert_prolog_failure!(&mut wam, "?- member([X, Y, Y], [a, [b, c], [b, b], [Z, x], [d, f]]).");
    assert_prolog_failure!(&mut wam, "?- member([X, Y, Z], [a, [b, c], [b, b], [Z, x], [d, f]]).");
}
