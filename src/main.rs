extern crate termion;
mod prolog;

use prolog::io::*;
use prolog::machine::*;

#[cfg(test)]
mod tests {
    use super::*;
    use prolog::codegen::*;

    fn submit(wam: &mut Machine, buffer: &str) -> bool {
        wam.reset();

        match parse_code(buffer.trim()) {
            Some(tl) =>
                match eval(wam, &tl) {
                    EvalSession::InitialQuerySuccess(_, _) |
                    EvalSession::EntrySuccess |
                    EvalSession::SubsequentQuerySuccess =>
                        true,
                    _ => false
                },
            None => panic!("Grammatical error of some kind!")
        }
    }

    #[test]
    fn test_queries_on_facts() {
        let mut wam = Machine::new();

        submit(&mut wam, "p(Z, Z).");
        submit(&mut wam, "clouds(are, nice).");

        // submit returns true on failure, false on success.
        assert_eq!(submit(&mut wam, "?- p(Z, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(Z, z)."), true);
        assert_eq!(submit(&mut wam, "?- p(Z, w)."), true);
        assert_eq!(submit(&mut wam, "?- p(z, w)."), false);
        assert_eq!(submit(&mut wam, "?- p(w, w)."), true);
        assert_eq!(submit(&mut wam, "?- clouds(Z, Z)."), false);
        assert_eq!(submit(&mut wam, "?- clouds(are, Z)."), true);
        assert_eq!(submit(&mut wam, "?- clouds(Z, nice)."), true);

        assert_eq!(submit(&mut wam, "?- p(Z, h(Z, W), f(W))."), false);

        submit(&mut wam, "p(Z, h(Z, W), f(W)).");

        assert_eq!(submit(&mut wam, "?- p(z, h(z, z), f(w))."), false);
        assert_eq!(submit(&mut wam, "?- p(z, h(z, w), f(w))."), true);
        assert_eq!(submit(&mut wam, "?- p(z, h(z, W), f(w))."), true);
        assert_eq!(submit(&mut wam, "?- p(Z, h(Z, w), f(Z))."), true);
        assert_eq!(submit(&mut wam, "?- p(z, h(Z, w), f(Z))."), false);

        submit(&mut wam, "p(f(X), h(Y, f(a)), Y).");

        assert_eq!(submit(&mut wam, "?- p(Z, h(Z, W), f(W))."), true);
    }

    #[test]
    fn test_queries_on_rules() {
        let mut wam = Machine::new();

        submit(&mut wam, "p(X, Y) :- q(X, Z), r(Z, Y).");
        submit(&mut wam, "q(q, s).");
        submit(&mut wam, "r(s, t).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(q, t)."), true);
        assert_eq!(submit(&mut wam, "?- p(t, q)."), false);
        assert_eq!(submit(&mut wam, "?- p(q, T)."), true);
        assert_eq!(submit(&mut wam, "?- p(Q, t)."), true);
        assert_eq!(submit(&mut wam, "?- p(t, t)."), false);

        submit(&mut wam, "p(X, Y) :- q(f(f(X)), R), r(S, T).");
        submit(&mut wam, "q(f(f(X)), r).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);

        submit(&mut wam, "q(f(f(x)), r).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);

        submit(&mut wam, "p(X, Y) :- q(X, Y), r(X, Y).");
        submit(&mut wam, "q(s, t).");
        submit(&mut wam, "r(X, Y) :- r(a).");
        submit(&mut wam, "r(a).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(t, S)."), false);
        assert_eq!(submit(&mut wam, "?- p(t, s)."), false);
        assert_eq!(submit(&mut wam, "?- p(s, T)."), true);
        assert_eq!(submit(&mut wam, "?- p(S, t)."), true);

        submit(&mut wam, "p(f(f(a), g(b), X), g(b), h) :- q(X, Y).");
        submit(&mut wam, "q(X, Y).");

        assert_eq!(submit(&mut wam, "?- p(f(X, Y, Z), g(b), h)."), true);
        assert_eq!(submit(&mut wam, "?- p(f(X, g(Y), Z), g(Z), X)."), false);
        assert_eq!(submit(&mut wam, "?- p(f(X, g(Y), Z), g(Z), h)."), true);
        assert_eq!(submit(&mut wam, "?- p(Z, Y, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(f(X, Y, Z), Y, h)."), true);

        submit(&mut wam, "p(_, f(_, Y, _)) :- h(Y).");
        submit(&mut wam, "h(y).");

        assert_eq!(submit(&mut wam, "?- p(_, f(_, Y, _))."), true);
        assert_eq!(submit(&mut wam, "?- p(_, f(_, y, _))."), true);
        assert_eq!(submit(&mut wam, "?- p(_, f(_, z, _))."), false);
    }

    #[test]
    fn test_queries_on_predicates() {
        let mut wam = Machine::new();

        submit(&mut wam, "p(X, a). p(b, X).");

        assert_eq!(submit(&mut wam, "?- p(x, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(b, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(a, b)."), false);

        submit(&mut wam, "p(X, Y, a). p(X, a, Y). p(X, Y, a).");

        assert_eq!(submit(&mut wam, "?- p(c, d, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(a, a, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b, c, d)."), false);

        submit(&mut wam, "p(X, a). p(X, Y) :- q(Z), p(X, X).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(x, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, b)."), false);

        submit(&mut wam, "q(z).");

        assert_eq!(submit(&mut wam, "?- p(X, b)."), true);
        assert_eq!(submit(&mut wam, "?- p(x, a)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);

        submit(&mut wam, "p(X, a). p(X, Y) :- q(Y), p(X, X).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, b)."), false);

        submit(&mut wam, "p(a, z). p(X, Y) :- q(Y), p(X, Y).");

        assert_eq!(submit(&mut wam, "?- p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, z)."), true);
        assert_eq!(submit(&mut wam, "?- p(a, z)."), true);
        assert_eq!(submit(&mut wam, "?- p(a, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(b, a)."), false);

        submit(&mut wam, "p(X, Y, Z) :- q(X), r(Y), s(Z).
                          p(a, b, Z) :- q(Z).");

        submit(&mut wam, "q(x).");
        submit(&mut wam, "r(y).");
        submit(&mut wam, "s(z).");

        assert_eq!(submit(&mut wam, "?- p(X, Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(a, b, c)."), false);
        assert_eq!(submit(&mut wam, "?- p(a, b, C)."), true);

        submit(&mut wam, "p(X) :- q(X). p(X) :- r(X).");
        submit(&mut wam, "q(X) :- a.");
        submit(&mut wam, "r(X) :- s(X, t). r(X) :- t(X, u).");

        submit(&mut wam, "s(x, t).");
        submit(&mut wam, "t(y, u).");

        assert_eq!(submit(&mut wam, "?- p(X)."), true);
        assert_eq!(submit(&mut wam, "?- p(x)."), true);
        assert_eq!(submit(&mut wam, "?- p(y)."), true);
        assert_eq!(submit(&mut wam, "?- p(z)."), false);

        submit(&mut wam, "p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
                          p(X, Y, Z) :- h(Y), g(W), z(Z).");
        submit(&mut wam, "g(f(X)) :- z(X). g(X) :- h(X).");
        submit(&mut wam, "h(w). h(x). h(z).");
        submit(&mut wam, "f(s).");
        submit(&mut wam, "z(Z).");

        assert_eq!(submit(&mut wam, "?- p(X, Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, X, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(f(f(Z)), Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, X, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y, X)."), true);
        assert_eq!(submit(&mut wam, "?- p(f(f(X)), h(f(X)), Y)."), false);

        submit(&mut wam, "p(X) :- f(Y), g(Y), i(X, Y).");
        submit(&mut wam, "g(f(a)). g(f(b)). g(f(c)).");
        submit(&mut wam, "f(f(a)). f(f(b)). f(f(c)).");
        submit(&mut wam, "i(X, X).");

        assert_eq!(submit(&mut wam, "?- p(X)."), true);

        submit(&mut wam, "p(X) :- f(f(Y)), g(Y, f(Y)), i(X, f(Y)).");
        submit(&mut wam, "g(Y, f(Y)) :- g(f(Y)).");

        assert_eq!(submit(&mut wam, "?- p(X)."), true);
    }

    #[test]
    fn test_queries_on_cuts() {
        let mut wam = Machine::new();

        // test shallow cuts.
        submit(&mut wam, "memberchk(X, [X|_]) :- !.
                          memberchk(X, [_|Xs]) :- memberchk(X, Xs).");

        assert_eq!(submit(&mut wam, "?- memberchk(X, [a,b,c])."), true);
        assert_eq!(submit(&mut wam, "?- memberchk([X,X], [a,b,c,[d,e],[d,d]])."), true);
        assert_eq!(submit(&mut wam, "?- memberchk([X,X], [a,b,c,[D,d],[e,e]])."), true);
        assert_eq!(submit(&mut wam, "?- memberchk([X,X], [a,b,c,[e,d],[f,e]])."), false);
        assert_eq!(submit(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,d],[f,e]])."), false);
        assert_eq!(submit(&mut wam, "?- memberchk([X,X,Y], [a,b,c,[e,e,d],[f,e]])."), true);

        // test deep cuts.
        submit(&mut wam, "commit :- a, !.");

        assert_eq!(submit(&mut wam, "?- commit."), false);

        submit(&mut wam, "a.");

        assert_eq!(submit(&mut wam, "?- commit."), true);

        submit(&mut wam, "commit(X) :- a(X), !.");

        assert_eq!(submit(&mut wam, "?- commit(X)."), false);

        submit(&mut wam, "a(x).");

        assert_eq!(submit(&mut wam, "?- commit(X)."), true);

        submit(&mut wam, "a :- b, !, c. a :- d.");

        assert_eq!(submit(&mut wam, "?- a."), false);

        submit(&mut wam, "b.");

        assert_eq!(submit(&mut wam, "?- a."), false);

        submit(&mut wam, "d.");

        // we've committed to the first clause since the query on b
        // succeeds, so we expect failure here.
        assert_eq!(submit(&mut wam, "?- a."), false);

        submit(&mut wam, "c.");

        assert_eq!(submit(&mut wam, "?- a."), true);

        submit(&mut wam, "a(X) :- b, !, c(X). a(X) :- d(X).");

        assert_eq!(submit(&mut wam, "?- a(X)."), false);

        submit(&mut wam, "c(c).");
        submit(&mut wam, "d(d).");

        assert_eq!(submit(&mut wam, "?- a(X)."), true);

        submit(&mut wam, "b.");

        assert_eq!(submit(&mut wam, "?- a(X)."), true);

        wam.clear();

        assert_eq!(submit(&mut wam, "?- c(X)."), false);

        submit(&mut wam, "a(X) :- b, c(X), !. a(X) :- d(X).");
        submit(&mut wam, "b.");

        assert_eq!(submit(&mut wam, "?- a(X)."), false);

        submit(&mut wam, "d(d).");

        assert_eq!(submit(&mut wam, "?- a(X)."), true);

        submit(&mut wam, "c(c).");

        assert_eq!(submit(&mut wam, "?- a(X)."), true);
    }

    #[test]
    fn test_queries_on_lists() {
        let mut wam = Machine::new();

        submit(&mut wam, "p([Z, W]).");

        assert_eq!(submit(&mut wam, "?- p([Z, Z])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z, W, Y])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z | W])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | [Z]])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | [W]])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | []])."), false);

        submit(&mut wam, "p([Z, Z]).");

        assert_eq!(submit(&mut wam, "?- p([Z, Z])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z, W, Y])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z | W])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | [Z]])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | [W]])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | []])."), false);

        submit(&mut wam, "p([Z]).");

        assert_eq!(submit(&mut wam, "?- p([Z, Z])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z, W, Y])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z | W])."), true);
        assert_eq!(submit(&mut wam, "?- p([Z | [Z]])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z | [W]])."), false);
        assert_eq!(submit(&mut wam, "?- p([Z | []])."), true);

        submit(&mut wam, "member(X, [X|Xs]).
                          member(X, [Y|Xs]) :- member(X, Xs).");

        assert_eq!(submit(&mut wam, "?- member(a, [c, [X, Y]])."), false);
        assert_eq!(submit(&mut wam, "?- member(c, [a, [X, Y]])."), false);
        assert_eq!(submit(&mut wam, "?- member(a, [a, [X, Y]])."), true);
        assert_eq!(submit(&mut wam, "?- member(a, [X, Y, Z])."), true);
        assert_eq!(submit(&mut wam, "?- member([X, X], [a, [X, Y]])."), true);
        assert_eq!(submit(&mut wam, "?- member([X, X], [a, [b, c], [b, b], [Z, x], [d, f]])."), true);
        assert_eq!(submit(&mut wam, "?- member([X, X], [a, [b, c], [b, d], [foo, x], [d, f]])."), false);
        assert_eq!(submit(&mut wam, "?- member([X, Y], [a, [b, c], [b, b], [Z, x], [d, f]])."), true);
        assert_eq!(submit(&mut wam, "?- member([X, Y, Y], [a, [b, c], [b, b], [Z, x], [d, f]])."), false);
        assert_eq!(submit(&mut wam, "?- member([X, Y, Z], [a, [b, c], [b, b], [Z, x], [d, f]])."), false);
    }

    #[test]
    fn test_queries_on_indexed_predicates() {
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

        assert_eq!(submit(&mut wam, "?- p(a)."), false);
        assert_eq!(submit(&mut wam, "?- p(b)."), false);
        assert_eq!(submit(&mut wam, "?- p(c)."), false);
        assert_eq!(submit(&mut wam, "?- p(f(a))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(b, X))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(Y, X))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(Y, c))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(b))."), false);
        assert_eq!(submit(&mut wam, "?- p([])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d | X])."), true);
        assert_eq!(submit(&mut wam, "?- p([c|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|[d|Xs]])."), true);

        submit(&mut wam, "a.");

        assert_eq!(submit(&mut wam, "?- p(a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b)."), false);
        assert_eq!(submit(&mut wam, "?- p(c)."), false);
        assert_eq!(submit(&mut wam, "?- p(f(a))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b, X))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(Y, X))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(Y, c))."), false);
        assert_eq!(submit(&mut wam, "?- p(g(b))."), false);
        assert_eq!(submit(&mut wam, "?- p([])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d | X])."), true);
        assert_eq!(submit(&mut wam, "?- p([c|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|[d|Xs]])."), true);

        submit(&mut wam, "b.");
        submit(&mut wam, "f(x).");

        assert_eq!(submit(&mut wam, "?- p(a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b)."), true);
        assert_eq!(submit(&mut wam, "?- p(c)."), false);
        assert_eq!(submit(&mut wam, "?- p(f(a))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, c))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b))."), true);
        assert_eq!(submit(&mut wam, "?- p([])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d | X])."), true);
        assert_eq!(submit(&mut wam, "?- p([c|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|[d|Xs]])."), true);

        submit(&mut wam, "c.");
        submit(&mut wam, "g(X).");

        assert_eq!(submit(&mut wam, "?- p(a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b)."), true);
        assert_eq!(submit(&mut wam, "?- p(c)."), true);
        assert_eq!(submit(&mut wam, "?- p(f(a))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, c))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b))."), true);
        assert_eq!(submit(&mut wam, "?- p([])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d | X])."), true);
        assert_eq!(submit(&mut wam, "?- p([c|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|[d|Xs]])."), true);
        assert_eq!(submit(&mut wam, "?- p(blah)."), false);

        submit(&mut wam, "x.");

        assert_eq!(submit(&mut wam, "?- p(a)."), true);
        assert_eq!(submit(&mut wam, "?- p(b)."), true);
        assert_eq!(submit(&mut wam, "?- p(c)."), true);
        assert_eq!(submit(&mut wam, "?- p(true(a))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, X))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(Y, c))."), true);
        assert_eq!(submit(&mut wam, "?- p(g(b))."), true);
        assert_eq!(submit(&mut wam, "?- p([])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d, e])."), true);
        assert_eq!(submit(&mut wam, "?- p([c, d | X])."), true);
        assert_eq!(submit(&mut wam, "?- p([c|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|X])."), true);
        assert_eq!(submit(&mut wam, "?- p([Y|[d|Xs]])."), true);
        assert_eq!(submit(&mut wam, "?- p(blah)."), true);

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
        assert_eq!(submit(&mut wam, "?- ind_call(builtin(X))."), true);
        assert_eq!(submit(&mut wam, "?- ind_call(extern(X))."), true);
    }

    #[test]
    fn test_queries_on_conjuctive_queries() {
        let mut wam = Machine::new();

        submit(&mut wam, "p(a, b).");
        submit(&mut wam, "q(b, c).");

        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, X)."), false);

        submit(&mut wam, "p(a, [f(g(X))]).");
        submit(&mut wam, "q(Y, c).");

        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, X)."), false);

        submit(&mut wam, "member(X, [X|_]).
                          member(X, [_|Xs]) :- member(X, Xs).");

        assert_eq!(submit(&mut wam, "?- member(X, [a,b,c]), member(X, [a,b,c])."), true);
        assert_eq!(submit(&mut wam, "?- member(X, [a,b,c]), member(X, [b,c])."), true);
        assert_eq!(submit(&mut wam, "?- member(X, [a,c]), member(X, [b,c])."), true);
        assert_eq!(submit(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [a,d])."), true);
        assert_eq!(submit(&mut wam, "?- member(X, [a,b,c,d]), !, member(X, [e])."), false);
        assert_eq!(submit(&mut wam, "?- member([X,X],[a,b,c,[d,d],[e,d]]),
                                        member(X, [a,b,c,d,e,f,g]), 
                                        member(Y, [X, a, b, c, d])."),
                          true);
        assert_eq!(submit(&mut wam, "?- member([X,X],[a,b,c,[d,d],[e,d]]),
                                        member(X, [a,b,c,d,e,f,g]), 
                                        !,
                                        member(Y, [X, a, b, c, d])."),
                          true);
        
        submit(&mut wam, "p(a, [f(g(X))]).");
        submit(&mut wam, "q(Y, c).");

        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, X)."), false);

        submit(&mut wam, "p(a, [f(g(X))]). p(X, c) :- c.");
        submit(&mut wam, "c.");
        submit(&mut wam, "q(Y, c).");

        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), !, q(Y, Z)."), true);

        submit(&mut wam, "q([f(g(x))], Z). q([f(g(y))], Y). q([f(g(z))], a).");

        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), !, q(Y, Z)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), !, q(Y, X)."), true);

        submit(&mut wam, "p(X, [f(g(x))]). p(X, [f(g(y))]). p(X, [f(g(z))]).");

        assert_eq!(submit(&mut wam, "?- q(f(X), Y), p(X, Y)."), false);
        assert_eq!(submit(&mut wam, "?- q(X, Y), p(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), q(X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- p(X, Y), q(Y, X)."), true);
        assert_eq!(submit(&mut wam, "?- q(X, Y), p(Y, X)."), true);
    }

    #[test]
    fn test_queries_on_call_n()
    {
        let mut wam = Machine::new();
        
        submit(&mut wam, "maplist(Pred, []).
                          maplist(Pred, [X|Xs]) :- call(Pred, X), maplist(Pred, Xs).");
        submit(&mut wam, "f(a). f(b). f(c).");

        assert_eq!(submit(&mut wam, "?- maplist(f, [X,Y,Z])."), true);
        assert_eq!(submit(&mut wam, "?- maplist(f, [a,Y,Z])."), true);
        assert_eq!(submit(&mut wam, "?- maplist(f, [X,a,b])."), true);
        assert_eq!(submit(&mut wam, "?- maplist(f, [c,a,b])."), true);
        assert_eq!(submit(&mut wam, "?- maplist(f, [d,e,f])."), false);
        assert_eq!(submit(&mut wam, "?- maplist(f, [])."), true);
        assert_eq!(submit(&mut wam, "?- maplist(f(X), [a,b,c])."), false);

        submit(&mut wam, "f(X) :- call(X), call(X).");
        submit(&mut wam, "p(x). p(y).");

        assert_eq!(submit(&mut wam, "?- f(p)."), false);
        assert_eq!(submit(&mut wam, "?- f(p(X))."), true);
        assert_eq!(submit(&mut wam, "?- f(p(x))."), true);
        assert_eq!(submit(&mut wam, "?- f(p(w))."), false);
        assert_eq!(submit(&mut wam, "?- f(p(X, Y))."), false);

        submit(&mut wam, "f(P) :- call(P, X), call(P, Y).");

        assert_eq!(submit(&mut wam, "?- f(p)."), true);
        assert_eq!(submit(&mut wam, "?- f(non_existent)."), false);

        submit(&mut wam, "f(P, X, Y) :- call(P, X), call(P, Y).");

        assert_eq!(submit(&mut wam, "?- f(p, X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- f(p, x, Y)."), true);
        assert_eq!(submit(&mut wam, "?- f(p, X, y)."), true);
        assert_eq!(submit(&mut wam, "?- f(p, x, y)."), true);
        assert_eq!(submit(&mut wam, "?- f(p, X, z)."), false);
        assert_eq!(submit(&mut wam, "?- f(p, z, Y)."), false);
        
        assert_eq!(submit(&mut wam, "?- call(p, X)."), true);
        assert_eq!(submit(&mut wam, "?- call(p, x)."), true);
        assert_eq!(submit(&mut wam, "?- call(p, y)."), true);
        assert_eq!(submit(&mut wam, "?- call(p, z)."), false);

        submit(&mut wam, "r(f(X)) :- p(X). r(g(Y)) :- p(Y).");

        assert_eq!(submit(&mut wam, "?- f(r, X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- f(r, X, X)."), true);
        assert_eq!(submit(&mut wam, "?- f(r, f(X), g(Y))."), true);
        assert_eq!(submit(&mut wam, "?- f(r, j(X), h(Y))."), false);

        submit(&mut wam, "p(one, one). p(one, two). p(two, two).");

        assert_eq!(submit(&mut wam, "?- f(p(one), X, Y)."), true);
        assert_eq!(submit(&mut wam, "?- f(p(one), X, X)."), true);
        assert_eq!(submit(&mut wam, "?- f(p(one), one, Y)."), true);
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

        assert_eq!(submit(&mut wam, "?- call(p(f(g(X))), Y, Z)."), true);

        submit(&mut wam, "david_lynch(coffee).
                          david_lynch(pie).
                          david_lynch(kyle(Film)) :- kyle(Film).");

        submit(&mut wam, "kyle(dune).
                          kyle(blue_velvet).
                          kyle(showgirls).
                          kyle(flintstones).");

        assert_eq!(submit(&mut wam, "?- call(david_lynch, X)."), true);
        assert_eq!(submit(&mut wam, "?- call(david_lynch, kyle(Film))."), true);
        assert_eq!(submit(&mut wam, "?- call(david_lynch, kyle(Film), _)."), false);

        submit(&mut wam, "call_mult(P, X) :- call(call(P), X).");
        
        assert_eq!(submit(&mut wam, "?- call_mult(p(X), Y)."), true);
        assert_eq!(submit(&mut wam, "?- call_mult(p(X), X)."), true);
        assert_eq!(submit(&mut wam, "?- call_mult(p(one), X)."), true);
        assert_eq!(submit(&mut wam, "?- call_mult(p(X), one)."), true);
        assert_eq!(submit(&mut wam, "?- call_mult(p(two), one)."), false);
        assert_eq!(submit(&mut wam, "?- call_mult(p(two), two)."), true);

        submit(&mut wam, "f(call(f, undefined)). f(undefined).");
        submit(&mut wam, "call_var(P) :- P.");
                
        assert_eq!(submit(&mut wam, "?- f(X), call_var(X)."), true);
        assert_eq!(submit(&mut wam, "?- f(call(f, Q)), call_var(call(f, Q))."), true);
        assert_eq!(submit(&mut wam, "?- call_var(call(undefined, Q))."), false);

        assert_eq!(submit(&mut wam, "?- call(call)."), false);
        assert_eq!(submit(&mut wam, "?- call(call(call))."), false);
        assert_eq!(submit(&mut wam, "?- call(call(call(call)))."), false);
        assert_eq!(submit(&mut wam, "?- call(call(call(call(call))))."), false);
        assert_eq!(submit(&mut wam, "?- call(call(call(call(call(call)))))."), false);
        assert_eq!(submit(&mut wam, "?- call(call(call(call(call(call(p(X)))))))."), true);
    }
}

fn process_buffer(wam: &mut Machine, buffer: &str)
{
    match parse_code(buffer.trim()) {
        Some(tl) => {
            let result = eval(wam, &tl);
            print(wam, result);
        },
        None => println!("Grammatical error!")
    };
}

fn prolog_repl() {
    let mut wam = Machine::new();

    loop {
        print!("prolog> ");

        let buffer = read();

        if buffer == "quit\n" {
            break;
        } else if buffer == "clear\n" {
            wam.clear();
            continue;
        }

        process_buffer(&mut wam, buffer.trim());
        wam.reset();
    }
}

fn main() {
    prolog_repl();
}
