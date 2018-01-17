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

#[test]
fn test_queries_on_indexed_predicates()
{
    let mut wam = Machine::new();

    submit(&mut wam, "p(a) :- a.
                      p(b) :- b, f(X).
                      p(c) :- c, g(X).
                      p(f(a)) :- a.
                      p(g(b, c)) :- b.
                      p(g(b)) :- b.
                      p([a|b]) :- a.
                      p([]).
                      p(X) :- x.
                      p([c, d, e]).");

    assert_prolog_failure!(&mut wam, "?- p(a).");
    assert_prolog_failure!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_failure!(&mut wam, "?- p(f(a)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, c)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", ["X = [e]"]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", ["X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", ["Y = c", "X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", ["Xs = [e]", "Y = c"]);

    submit(&mut wam, "a.");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_failure!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(f(a)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, X)).");
    assert_prolog_failure!(&mut wam, "?- p(g(Y, c)).");
    assert_prolog_failure!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", ["X = [e]"]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", ["X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", ["X = b", "Y = a",
                                                      "Y = c", "X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", ["Xs = [e]", "Y = c"]);

    submit(&mut wam, "b.");
    submit(&mut wam, "f(x).");

    assert_prolog_success!(&mut wam, "?- p(a).");
    assert_prolog_success!(&mut wam, "?- p(b).");
    assert_prolog_failure!(&mut wam, "?- p(c).");
    assert_prolog_success!(&mut wam, "?- p(f(a)).");
    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", ["X = c"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", ["X = c", "Y = b"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", ["Y = b"]);    
    assert_prolog_success!(&mut wam, "?- p(g(b)).");
    assert_prolog_success!(&mut wam, "?- p([]).");
    assert_prolog_success!(&mut wam, "?- p([c, d, e]).");
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", ["X = [e]"]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", ["X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", ["X = b", "Y = a",
                                                      "Y = c", "X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", ["Xs = [e]", "Y = c"]);

    submit(&mut wam, "c.");
    submit(&mut wam, "g(X).");

    assert_eq!(submit(&mut wam, "?- p(a)."), true);
    assert_eq!(submit(&mut wam, "?- p(b)."), true);
    assert_eq!(submit(&mut wam, "?- p(c)."), true);
    assert_eq!(submit(&mut wam, "?- p(f(a))."), true);
    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", ["X = c"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", ["X = c", "Y = b"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", ["Y = b"]);
    assert_eq!(submit(&mut wam, "?- p(g(b))."), true);
    assert_eq!(submit(&mut wam, "?- p([])."), true);
    assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", ["X = [e]"]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", ["X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", ["X = b", "Y = a",
                                                      "Y = c", "X = [d, e]"]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", ["Xs = [e]", "Y = c"]);
    assert_eq!(submit(&mut wam, "?- p(blah)."), false);

    submit(&mut wam, "x.");

    assert_eq!(submit(&mut wam, "?- p(a)."), true);
    assert_eq!(submit(&mut wam, "?- p(b)."), true);
    assert_eq!(submit(&mut wam, "?- p(c)."), true);
    assert_eq!(submit(&mut wam, "?- p(true(a))."), true);
    
    assert_prolog_success!(&mut wam, "?- p(g(b, X)).", ["X = c",
                                                        "X = _2"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, X)).", ["X = c", "Y = b",
                                                        "X = _2", "Y = _1"]);
    assert_prolog_success!(&mut wam, "?- p(g(Y, c)).", ["Y = b",
                                                        "Y = _1"]);
    
    assert_eq!(submit(&mut wam, "?- p(g(b))."), true);
    assert_eq!(submit(&mut wam, "?- p([])."), true);
    assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
    
    assert_prolog_success!(&mut wam, "?- p([c, d | X]).", ["X = _1",
                                                           "X = [e]"]);
    assert_prolog_success!(&mut wam, "?- p([c|X]).", ["X = [d, e]",
                                                      "X = _1"]);
    assert_prolog_success!(&mut wam, "?- p([Y|X]).", ["X = b", "Y = a",
                                                      "Y = c", "X = [d, e]",
                                                      "X = _1", "Y = _0"]);
    assert_prolog_success!(&mut wam, "?- p([Y|[d|Xs]]).", ["Xs = [e]", "Y = c",
                                                           "Xs = _1", "Y = _2"]);
    
    assert_prolog_success!(&mut wam, "?- p(blah).");

    submit(&mut wam, "ind_call(or(X, Y)) :- ind_call(X).
                      ind_call(trace) :- trace.
                      ind_call(or(X, Y)) :- ind_call(Y).
                      ind_call(notrace) :- notrace.
                      ind_call(nl) :- nl.
                      ind_call(X) :- builtin(X).
                      ind_call(X) :- extern(X).
                      ind_call(ind_call(X)) :- ind_call(X).
                      ind_call(repeat).
                      ind_call(repeat) :- ind_call(repeat).
                      ind_call(false).");

    assert_eq!(submit(&mut wam, "?- ind_call(repeat)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(false)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(repeat))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(false))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(notrace)."), false);
    assert_eq!(submit(&mut wam, "?- ind_call(nl)."), false);
    assert_eq!(submit(&mut wam, "?- ind_call(builtin(X))."), false);
    assert_eq!(submit(&mut wam, "?- ind_call(extern(X))."), false);

    submit(&mut wam, "notrace.");
    submit(&mut wam, "nl.");

    assert_eq!(submit(&mut wam, "?- ind_call(repeat)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(false)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(repeat))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(false))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(notrace)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(nl)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(builtin(X))."), false);
    assert_eq!(submit(&mut wam, "?- ind_call(extern(X))."), false);

    submit(&mut wam, "builtin(X).");
    submit(&mut wam, "extern(x).");

    assert_eq!(submit(&mut wam, "?- ind_call(repeat)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(false)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(repeat))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(ind_call(false))."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(notrace)."), true);
    assert_eq!(submit(&mut wam, "?- ind_call(nl)."), true);
    assert_prolog_success!(&mut wam, "?- ind_call(builtin(X)).", ["X = _1"]);
    assert_prolog_success!(&mut wam, "?- ind_call(extern(X)).", ["X = _1"]);
}

#[test]
fn test_queries_on_conjuctive_queries() {
    let mut wam = Machine::new();

    submit(&mut wam, "p(a, b).");
    submit(&mut wam, "q(b, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).", ["X = a", "Z = c", "Y = b"]);
    assert_prolog_failure!(&mut wam, "?- p(X, Y), q(Y, X).");

    submit(&mut wam, "p(a, [f(g(X))]).");
    submit(&mut wam, "q(Y, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).", ["Y = f(g(_9))", "X = a", "Z = c"]);
    assert_prolog_failure!(&mut wam, "?- p(X, Y), q(Y, X).");

    submit(&mut wam, "member(X, [X|_]).
                      member(X, [_|Xs]) :- member(X, Xs).");

    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c]), member(X, [a,b,c]).",
                           ["X = a",
                            "X = b",
                            "X = c"]);
    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c]), member(X, [b,c]).",
                           ["X = b",
                            "X = c"]);
    assert_prolog_success!(&mut wam, "?- member(X, [a,c]), member(X, [b,c]).",
                           ["X = c"]);    
    assert_prolog_success!(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [a,d]).",
                           ["X = a"]);
    assert_prolog_failure!(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [e]).");
    assert_prolog_success!(&mut wam, "?- member([X,X],[a,b,c,[d,d],[e,d]]),
                                         member(X, [a,b,c,d,e,f,g]),
                                         member(Y, [X, a, b, c, d]).",
                           ["X = d", "Y = d",
                            "X = d", "Y = a",
                            "X = d", "Y = b",
                            "X = d", "Y = c",
                            "X = d", "Y = d"]);

    submit(&mut wam, "p(a, [f(g(X))]). p(X, c) :- c.");
    submit(&mut wam, "c.");
    submit(&mut wam, "q(Y, c).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).",
                           ["X = a",  "Z = c", "Y = f(g(_9))",
                            "X = _0", "Z = c", "Y = c"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, Z).",
                           ["Z = c", "Y = f(g(_9))", "X = a"]);

    submit(&mut wam, "q([f(g(x))], Z). q([f(g(y))], Y). q([f(g(z))], a).");

    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, Z).",
                           ["Z = _10", "X = a", "Y = f(g(x))",
                            "Z = _10", "X = a", "Y = f(g(y))",
                            "Z = a", "X = a", "Y = f(g(z))"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, Z).",
                           ["X = a", "Y = f(g(x))", "Z = _10",
                            "X = a", "Y = f(g(y))", "Z = _10",
                            "X = a", "Y = f(g(z))", "Z = a"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), !, q(Y, X).",
                           ["X = a", "Y = f(g(x))",
                            "X = a", "Y = f(g(y))",
                            "X = a", "Y = f(g(z))"]);

    submit(&mut wam, "p(X, [f(g(x))]). p(X, [f(g(y))]). p(X, [f(g(z))]).");

    assert_prolog_failure!(&mut wam, "?- q(f(X), Y), p(X, Y).");
    assert_prolog_success!(&mut wam, "?- q(X, Y), p(X, Y).",
                           ["Y = [f(g(x))]", "X = f(g(x))",
                            "Y = [f(g(y))]", "X = f(g(x))",
                            "Y = [f(g(z))]", "X = f(g(x))",
                            "Y = [f(g(x))]", "X = f(g(y))",
                            "Y = [f(g(y))]", "X = f(g(y))",
                            "Y = [f(g(z))]", "X = f(g(y))"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), q(X, Y).",
                           ["Y = f(g(x))", "X = [f(g(x))]",
                            "Y = f(g(x))", "X = [f(g(y))]",
                            "Y = f(g(y))", "X = [f(g(x))]",
                            "Y = f(g(y))", "X = [f(g(y))]",
                            "Y = f(g(z))", "X = [f(g(x))]",
                            "Y = f(g(z))", "X = [f(g(y))]"]);
    assert_prolog_success!(&mut wam, "?- p(X, Y), q(Y, X).",
                           ["Y = f(g(x))", "X = s_0_2",
                            "Y = f(g(y))", "X = s_0_2",
                            "Y = f(g(z))", "X = a"]);
    assert_prolog_success!(&mut wam, "?- q(X, Y), p(Y, X).",
                           ["Y = s_0_1", "X = f(g(x))",
                            "Y = s_0_1", "X = f(g(y))",
                            "Y = a"    , "X = f(g(z))"]);
}

#[test]
fn test_queries_on_call_n()
{
    let mut wam = Machine::new();

    submit(&mut wam, "maplist(Pred, []).
                      maplist(Pred, [X|Xs]) :- call(Pred, X), maplist(Pred, Xs).");
    submit(&mut wam, "f(a). f(b). f(c).");

    assert_prolog_success!(&mut wam, "?- maplist(f, [X,Y,Z]).",
                           ["X = a", "Y = a", "Z = a",
                            "X = a", "Y = a", "Z = b",
                            "X = a", "Y = a", "Z = c",
                            "X = a", "Y = b", "Z = a",
                            "X = a", "Y = b", "Z = b",
                            "X = a", "Y = b", "Z = c",
                            "X = a", "Y = c", "Z = a",
                            "X = a", "Y = c", "Z = b",
                            "X = a", "Y = c", "Z = c",
                            "X = b", "Y = a", "Z = a",
                            "X = b", "Y = a", "Z = b",
                            "X = b", "Y = a", "Z = c",
                            "X = b", "Y = b", "Z = a",
                            "X = b", "Y = b", "Z = b",
                            "X = b", "Y = b", "Z = c",
                            "X = b", "Y = c", "Z = a",
                            "X = b", "Y = c", "Z = b",
                            "X = b", "Y = c", "Z = c",
                            "X = c", "Y = a", "Z = a",
                            "X = c", "Y = a", "Z = b",
                            "X = c", "Y = a", "Z = c",
                            "X = c", "Y = b", "Z = a",
                            "X = c", "Y = b", "Z = b",
                            "X = c", "Y = b", "Z = c",
                            "X = c", "Y = c", "Z = a",
                            "X = c", "Y = c", "Z = b",
                            "X = c", "Y = c", "Z = c"]);
                            
    assert_prolog_success!(&mut wam, "?- maplist(f, [a,Y,Z]).",
                           ["Z = a", "Y = a",
                            "Z = a", "Y = b",
                            "Z = a", "Y = c",
                            "Z = b", "Y = a",
                            "Z = b", "Y = b",
                            "Z = b", "Y = c",
                            "Z = c", "Y = a",
                            "Z = c", "Y = b",
                            "Z = c", "Y = c"]);
                            
    assert_prolog_success!(&mut wam, "?- maplist(f, [X,a,b]).",
                           ["X = a",
                            "X = b",
                            "X = c"]);
    assert_eq!(submit(&mut wam, "?- maplist(f, [c,a,b])."), true);
    assert_eq!(submit(&mut wam, "?- maplist(f, [d,e,f])."), false);
    assert_eq!(submit(&mut wam, "?- maplist(f, [])."), true);
    assert_eq!(submit(&mut wam, "?- maplist(f(X), [a,b,c])."), false);

    submit(&mut wam, "f(X) :- call(X), call(X).");
    submit(&mut wam, "p(x). p(y).");

    assert_eq!(submit(&mut wam, "?- f(p)."), false);
    assert_prolog_success!(&mut wam, "?- f(p(X)).", ["X = x",
                                                     "X = y"]);
    assert_eq!(submit(&mut wam, "?- f(p(x))."), true);
    assert_eq!(submit(&mut wam, "?- f(p(w))."), false);
    assert_eq!(submit(&mut wam, "?- f(p(X, Y))."), false);

    submit(&mut wam, "f(P) :- call(P, X), call(P, Y).");

    assert_eq!(submit(&mut wam, "?- f(p)."), true);
    assert_eq!(submit(&mut wam, "?- f(non_existent)."), false);

    submit(&mut wam, "f(P, X, Y) :- call(P, X), call(P, Y).");

    assert_prolog_success!(&mut wam, "?- f(p, X, Y).", ["X = x", "Y = x",
                                                        "X = y", "Y = x",
                                                        "X = x", "Y = y",
                                                        "X = y", "Y = y"]);
    assert_prolog_success!(&mut wam, "?- f(p, x, Y).", ["Y = x",
                                                        "Y = y"]);
    assert_prolog_success!(&mut wam, "?- f(p, X, y).", ["X = x",
                                                        "X = y"]);
    assert_eq!(submit(&mut wam, "?- f(p, x, y)."), true);
    assert_eq!(submit(&mut wam, "?- f(p, X, z)."), false);
    assert_eq!(submit(&mut wam, "?- f(p, z, Y)."), false);

    assert_prolog_success!(&mut wam, "?- call(p, X).", ["X = x",
                                                        "X = y"]);
    assert_eq!(submit(&mut wam, "?- call(p, x)."), true);
    assert_eq!(submit(&mut wam, "?- call(p, y)."), true);
    assert_eq!(submit(&mut wam, "?- call(p, z)."), false);

    submit(&mut wam, "r(f(X)) :- p(X). r(g(Y)) :- p(Y).");

    assert_prolog_success!(&mut wam, "?- f(r, X, Y).",
                           ["X = f(x)", "Y = f(x)", 
                            "X = f(x)", "Y = f(y)", 
                            "X = f(x)", "Y = g(x)", 
                            "X = f(x)", "Y = g(y)", 
                            "X = f(y)", "Y = f(x)", 
                            "X = f(y)", "Y = f(y)", 
                            "X = f(y)", "Y = g(x)", 
                            "X = f(y)", "Y = g(y)", 
                            "X = g(x)", "Y = f(x)", 
                            "X = g(x)", "Y = f(y)", 
                            "X = g(x)", "Y = g(x)", 
                            "X = g(x)", "Y = g(y)", 
                            "X = g(y)", "Y = f(x)",                            
                            "X = g(y)", "Y = f(y)",                            
                            "X = g(y)", "Y = g(x)",                             
                            "X = g(y)", "Y = g(y)"]);
    assert_prolog_success!(&mut wam, "?- f(r, X, X).",
                           ["X = f(x)",
                            "X = f(y)",
                            "X = g(x)",
                            "X = g(y)"]);
    assert_prolog_success!(&mut wam, "?- f(r, f(X), g(Y)).",
                           ["X = x", "Y = x",
                            "X = x", "Y = y",
                            "X = y", "Y = x",
                            "X = y", "Y = y"]);
    assert_eq!(submit(&mut wam, "?- f(r, j(X), h(Y))."), false);

    submit(&mut wam, "p(one, one). p(one, two). p(two, two).");

    assert_prolog_success!(&mut wam, "?- f(p(one), X, Y).",
                           ["X = one", "Y = one",
                            "X = one", "Y = two",
                            "X = two", "Y = two",
                            "X = two", "Y = one"]);
    assert_prolog_success!(&mut wam, "?- f(p(one), X, X).",
                           ["X = one",
                            "X = two"]);
    assert_prolog_success!(&mut wam, "?- f(p(one), one, Y).",
                           ["Y = one",
                            "Y = two"]);
    assert_eq!(submit(&mut wam, "?- f(p(one), one, two)."), true);
    assert_eq!(submit(&mut wam, "?- f(p(one), one, three)."), false);

    assert_eq!(submit(&mut wam, "?- f(p(two), one, two)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(two), two, one)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(two), two, two)."), true);
    assert_eq!(submit(&mut wam, "?- f(p(two), two, three)."), false);

    assert_eq!(submit(&mut wam, "?- f(p(three), X, Y)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(three), X, X)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(three), one, Y)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(three), one, two)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(three), one, three)."), false);

    submit(&mut wam, "f(P, X) :- call(P, X).");

    assert_eq!(submit(&mut wam, "?- f(p(one), one)."), true);
    assert_eq!(submit(&mut wam, "?- f(p(two), two)."), true);
    assert_eq!(submit(&mut wam, "?- f(p(two), one)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(three), one)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(one), three)."), false);
    assert_eq!(submit(&mut wam, "?- f(p(two), three)."), false);

    submit(&mut wam, "p(f(g(X)), compound, [lists,are,good]).");

    assert_prolog_success!(&mut wam, "?- call(p(f(g(X))), Y, Z).",
                           ["Y = compound", "Z = [lists, are, good]", "X = _3"]);

    submit(&mut wam, "david_lynch(coffee).
                      david_lynch(pie).
                      david_lynch(kyle(Film)) :- kyle(Film).");

    submit(&mut wam, "kyle(dune).
                      kyle(blue_velvet).
                      kyle(showgirls).
                      kyle(flintstones).");

    assert_prolog_success!(&mut wam, "?- call(david_lynch, X).",
                           ["X = coffee",
                            "X = pie",
                            "X = kyle(dune)",
                            "X = kyle(blue_velvet)",
                            "X = kyle(showgirls)",
                            "X = kyle(flintstones)"]);
    assert_prolog_success!(&mut wam, "?- call(david_lynch, kyle(Film)).",
                           ["Film = dune",
                            "Film = blue_velvet",
                            "Film = showgirls",
                            "Film = flintstones"]);
    assert_eq!(submit(&mut wam, "?- call(david_lynch, kyle(Film), _)."), false);

    submit(&mut wam, "call_mult(P, X) :- call(call(P), X).");

    assert_prolog_success!(&mut wam, "?- call_mult(p(X), Y).",
                           ["Y = one", "X = one",
                            "Y = two", "X = one",
                            "Y = two", "X = two"]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(X), X).",
                           ["X = one",
                            "X = two"]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(one), X).",
                           ["X = one",
                            "X = two"]);
    assert_prolog_success!(&mut wam, "?- call_mult(p(X), one).", ["X = one"]);
    assert_eq!(submit(&mut wam, "?- call_mult(p(two), one)."), false);
    assert_eq!(submit(&mut wam, "?- call_mult(p(two), two)."), true);

    assert_prolog_success!(&mut wam, "?- call(call(p(one)), X), call(call(p(two)), two).",
                           ["X = one",
                            "X = two"]);
    assert_prolog_success!(&mut wam, "?- call(call(p(one, X))), call(call(p(two, two))).",
                           ["X = one",
                            "X = two"]);
    assert_eq!(submit(&mut wam, "?- call(call(p(one)), X), call(call(p(two)), one)."), false);
    assert_prolog_success!(&mut wam, "?- call(call(p(X)), X), call(call(p(Y)), Y).",
                           ["X = one", "Y = one",
                            "X = one", "Y = two",
                            "X = two", "Y = two",
                            "X = two", "Y = one"]);
    assert_prolog_success!(&mut wam, "?- call(call(p(X)), Y), call(call(p(Y)), X).",
                           ["X = one", "Y = one",
                            "X = two", "Y = two"]);
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p)), X, Y).",
                           ["X = one", "Y = one",
                            "Y = two", "X = one",
                            "Y = two", "X = two"]);
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), Y).",
                           ["X = one", "Y = one",
                            "Y = two", "X = one",
                            "Y = two", "X = two"]);
    assert_eq!(submit(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), X, Y)."), false);
    assert_prolog_success!(&mut wam, "?- call(call(p), X, Y), call(call(call(p(X))), X).",
                           ["X = one", "Y = one",
                            "Y = two", "X = one",
                            "Y = two", "X = two"]);

    submit(&mut wam, "f(call(f, undefined)). f(undefined).");
    submit(&mut wam, "call_var(P) :- P.");

    assert_prolog_success!(&mut wam, "?- f(X), call_var(X).",
                           ["X = call(f, undefined)"]);
    assert_prolog_success!(&mut wam, "?- f(call(f, Q)), call_var(call(f, Q)).",
                           ["Q = undefined"]);
    assert_eq!(submit(&mut wam, "?- call_var(call(undefined, Q))."), false);

    assert_eq!(submit(&mut wam, "?- call(call)."), false);
    assert_eq!(submit(&mut wam, "?- call(call(call))."), false);
    assert_eq!(submit(&mut wam, "?- call(call(call(call)))."), false);
    assert_eq!(submit(&mut wam, "?- call(call(call(call(call))))."), false);
    assert_eq!(submit(&mut wam, "?- call(call(call(call(call(call)))))."), false);
    assert_prolog_success!(&mut wam, "?- call(call(call(call(call(call(p(X))))))).",
                           ["X = x",
                            "X = y"]);
}

#[test]
fn test_queries_on_exceptions()
{
    let mut wam = Machine::new();

    submit(&mut wam, "f(a). f(_) :- throw(stuff).");
    submit(&mut wam, "handle(stuff).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(E)).",
                           ["E = _2", "X = a",
                            "E = stuff", "X = _1"]);

    submit(&mut wam, "f(a). f(X) :- g(X).");
    submit(&mut wam, "g(x). g(y). g(z).");
    submit(&mut wam, "handle(x). handle(y).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), X, handle(X)).",
                           ["X = a",
                            "X = x",
                            "X = y",
                            "X = z"]);
    assert_prolog_success!(&mut wam, "?- catch(f(a), _, handle(X)).",
                           ["X = _4"]);
    assert_eq!(submit(&mut wam, "?- catch(f(b), _, handle(X))."), false);

    submit(&mut wam, "g(x). g(X) :- throw(x).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), x, handle(X)).",
                           ["X = a",
                            "X = x",
                            "X = x",
                            "X = y"]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), x, handle(z)).",
                           ["X = a",
                            "X = x"]);
    assert_eq!(submit(&mut wam, "?- catch(f(z), x, handle(x))."), true);
    assert_eq!(submit(&mut wam, "?- catch(f(z), x, handle(y))."), true);
    assert_eq!(submit(&mut wam, "?- catch(f(z), x, handle(z))."), false);

    submit(&mut wam, "f(X) :- throw(stuff).");
    submit(&mut wam, "handle(stuff). handle(other_stuff).");

    // the first 3 cases should deterministically succeed.
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(E)).",
                           ["X = _1", "E = stuff"]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(stuff)).",
                           ["X = _1", "E = stuff"]);
    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle(other_stuff)).",
                           ["X = _1", "E = stuff"]);
    assert_eq!(submit(&mut wam, "?- catch(f(X), E, handle(not_stuff))."), false);

    submit(&mut wam, "f(success). f(X) :- catch(g(X), E, handle(E)).");
    submit(&mut wam, "g(g_success). g(g_success_2). g(X) :- throw(X).");
    submit(&mut wam, "handle(x). handle(y). handle(z).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           ["X = success", "E = _2",
                            "X = g_success", "E = _2",
                            "X = g_success_2", "E = _2",
                            "X = _1", "E = _2",
                            "X = _1", "E = _2",
                            "X = _1", "E = _2"]);
    assert_eq!(submit(&mut wam, "?- catch(f(fail), _, _)."), false);
    assert_eq!(submit(&mut wam, "?- catch(f(x), _, _)."), true);
    assert_eq!(submit(&mut wam, "?- catch(f(y), _, _)."), true);
    assert_eq!(submit(&mut wam, "?- catch(f(z), _, _)."), true);

    submit(&mut wam, "f(success). f(E) :- catch(g(E), E, handle(E)).");
    submit(&mut wam, "g(g_success). g(g_success_2). g(X) :- throw(X).");
    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(X).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           ["X = success", "E = _2",
                            "X = g_success", "E = _2",
                            "X = g_success_2", "E = _2",
                            "X = x", "E = _2",
                            "X = y", "E = _2",
                            "X = z", "E = _2"]);

    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(handle_top(X)).");
    submit(&mut wam, "handle_top(an_error_1). handle_top(an_error_2).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, E).",
                           ["X = success", "E = _2",
                            "X = g_success", "E = _2",
                            "X = g_success_2", "E = _2",
                            "X = x", "E = _2",
                            "X = y", "E = _2",
                            "X = z", "E = _2",
                            "X = _1", "E = handle_top(an_error_1)",
                            "X = _1", "E = handle_top(an_error_2)"]);    

    submit(&mut wam, "handle(x). handle(y). handle(z). handle(v) :- throw(X).");

    assert_prolog_success!(&mut wam, "?- catch(f(X), E, handle_top(E)).",
                           ["X = success", "E = _2",
                            "X = g_success", "E = _2",
                            "X = g_success_2", "E = _2",
                            "X = x", "E = _2",
                            "X = y", "E = _2",
                            "X = z", "E = _2",
                            "E = an_error_1", "X = _1",
                            "E = an_error_2", "X = _1"]);
}

#[test]
fn test_queries_on_arithmetic()
{
    let mut wam = Machine::new();

    assert_prolog_success!(&mut wam, "?- X is 1, X is X.", ["X = 1"]);
    assert_eq!(submit(&mut wam, "?- X is 1, X is X + 1."), false);
    assert_prolog_success!(&mut wam, "?- X is 1, X is X + 0.", ["X = 1"]);
    assert_prolog_success!(&mut wam, "?- X is 1, X is X * 1.", ["X = 1"]);
    assert_eq!(submit(&mut wam, "?- X is 1, X is X * 2."), false);

    assert_eq!(submit(&mut wam, "?- X is 1 + a."), false);
    assert_eq!(submit(&mut wam, "?- X is 1 + Y."), false);
    assert_prolog_success!(&mut wam, "?- Y is 2 + 2 - 2, X is 1 + Y, X = 3.",
                           ["X = 3", "Y = 2"]);
    assert_eq!(submit(&mut wam, "?- Y is 2 + 2 - 2, X is 1 + Y, X = 2."), false);

    assert_eq!(submit(&mut wam, "?- 6 is 6."), true);
    assert_eq!(submit(&mut wam, "?- 6 is 3 + 3."), true);
    assert_eq!(submit(&mut wam, "?- 6 is 3 * 2."), true);
    assert_eq!(submit(&mut wam, "?- 7 is 3 * 2."), false);
    assert_eq!(submit(&mut wam, "?- 7 is 3.5 * 2."), false);
    assert_eq!(submit(&mut wam, "?- 7.0 is 3.5 * 2."), true);
    assert_eq!(submit(&mut wam, "?- 7.0 is 14 / 2."), true);
    assert_eq!(submit(&mut wam, "?- 4.666 is 14.0 / 3."), false);
    assert_eq!(submit(&mut wam, "?- 4.0 is 8.0 / 2."), true);

    submit(&mut wam, "f(X) :- X is 5 // 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           ["E = zero_divisor", "X = _1"]);
    
    submit(&mut wam, "f(X) :- X is (5 rdiv 1) / 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           ["E = zero_divisor", "X = _1"]);
    
    submit(&mut wam, "f(X) :- X is 5.0 / 0.");

    assert_prolog_success!(&mut wam, "?- catch(f(X), evaluation_error(E), true), E = zero_divisor.",
                           ["E = zero_divisor", "X = _1"]);
    
    assert_prolog_success!(&mut wam, "?- X is ((3 + 4) // 2) + 2 - 1 // 1, Y is 2+2, Z is X+Y.",
                           ["Y = 4", "X = 4", "Z = 8"]);

    assert_prolog_success!(&mut wam, "?- X is ((3 + 4) // 2) + 2 - 1 // 1, Y is 2+2, Z = 8, Y is 4.",
                           ["Y = 4", "X = 4", "Z = 8"]);

    assert_prolog_success!(&mut wam, "?- X is (3 rdiv 4) / 2, Y is 3 rdiv 8, X = Y.",
                           ["X = 3/8", "Y = 3/8"]);

    assert_prolog_success!(&mut wam, "?- X is 10 xor -4, X is -10.", ["X = -10"]);
    assert_prolog_success!(&mut wam, "?- X is 4 xor -7, X is -3.", ["X = -3"]);
    assert_prolog_success!(&mut wam, "?- X is 10 xor 5 + 55, X = 70.", ["X = 70"]);
    
    assert_prolog_success!(&mut wam, "?- X is 10 rem -3, X = 1.", ["X = 1"]);
    assert_prolog_success!(&mut wam, "?- X is 10 mod -3, X is -2.", ["X = -2"]);
}
