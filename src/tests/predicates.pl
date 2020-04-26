:- module(test_on_predicates, []).

:- dynamic(p/2).
:- dynamic(p/3).

:- dynamic(q/1).

p(_, a).
p(b, _).

test_queries_on_predicates :-
    findall(Y, p(x, Y), [a]),
    findall(X, p(X, a), [_,b]),
    findall(X, p(b, X), [a,_]),
    findall(X, p(X, X), [a,b]),
    p(b, a),
    \+ p(a, b),
    retract(p(_,a)),
    retract(p(b,_)),
    assertz(p(_, _,a)),
    assertz(p(_,a,_)),
    assertz(p(_,_,a)),
    findall(X, p(c,d,X), [a,a]),
    findall(X, p(a,a,a), [a,a,a]),
    \+ p(b,c,d),
    findall(., retract(p(_,_,_)), _),
    assertz(p(_, a)),
    assertz(q(z)),
    findall(Y, p(_,Y), [a]),
    p(x,a),
    p(_,a),
    \+ p(_,b),
    assertz((p(X, Y) :- q(Z), p(X, X))),
    once(p(X,b)),
    retract((p(X, Y) :- q(Z), p(X, X))),
    retract(q(z)).

:- initialization(test_queries_on_predicates).
