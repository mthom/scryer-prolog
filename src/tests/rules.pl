:- module(tests_on_rules, []).

:- dynamic(p/3).
:- dynamic(p/2).
:- dynamic(q/2).
:- dynamic(r/2).
:- dynamic(r/1).
:- dynamic(h/1).

p(X, Y) :- q(X, Z), r(Z, Y).
q(q, s).
r(s, t).

test_queries_on_rules :-
    \+ \+ findall([X,Y], p(X, Y), [[q, t]]),
    p(q, t),
    \+ p(t, q),
    \+ \+ findall(T, p(q, T), [t]),
    \+ p(t, t),
    \+ \+ retract((p(X,Y) :- q(X,Z), r(Z, Y))),
    retract(q(_,_)),
    \+ \+ assertz((p(X,_) :- q(f(f(X)), _), r(_, _))),
    \+ \+ assertz(q(f(f(X)), r)),
    p(_,_),
    retract(q(_,_)),
    assertz(q(f(f(x)), r)),
    \+ \+ findall(X, p(X,_), [x]),
    \+ \+ retract((p(X,_) :- q(f(f(X)), _), r(_, _))),
    retract(q(_,_)),
    \+ \+ assertz((p(X, Y) :- q(X, Y), r(X, Y))),
    assertz(q(s, t)),
    retract(r(_,_)),
    \+ \+ assertz((r(X, Y) :- r(a))),
    assertz(r(a)),
    \+ \+ findall([X,Y], p(X, Y), [[s,t]]),
    \+ p(t, _),
    \+ \+ findall(T, p(s, T), [t]),
    \+ \+ findall(S, p(S, t), [s]),
    \+ \+ assertz((p(f(f(a), g(b), X), g(b), h) :- q(X, _))),
    retract(q(_,_)),
    assertz(q(_,_)),
    \+ \+ findall([X,Y,Z], p(f(X, Y, Z), g(b), h), [[f(a), g(b), _]]),
    \+ p(f(X, g(_), Z), g(Z), X),
    \+ \+ findall([X,Y,Z], p(f(X, g(Y), Z), g(Z), h), [[f(a), b, b]]),
    \+ \+ findall([X,Y,Z], p(Z, Y, X), [[h, g(b), f(f(a),g(b),_)]]),
    \+ \+ findall([X,Y,Z], p(f(X, Y, Z), Y, h), [[f(a), g(b), _]]),
    \+ \+ retract((p(X, Y) :- q(X, Y), r(X, Y))),
    \+ \+ retract((p(f(f(a), g(b), X), g(b), h) :- q(X, _))),
    \+ \+ assertz((p(_, f(_, Y, _)) :- h(Y))),
    assertz(h(y)),
    \+ \+ findall(Y, p(_, f(_, Y, _)), [y]),
    p(_, f(_, y, _)),
    \+ p(_, f(_, z, _)),
    \+ \+ retract((p(_, f(_, Y, _)) :- h(Y))),
    cleanup.

cleanup :- abolish(p/3),
	   abolish(p/2),
	   abolish(q/2),
	   abolish(r/2),
	   abolish(r/1),
	   abolish(h/1).

:- initialization(test_queries_on_rules).
