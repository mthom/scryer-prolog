:- module(tests_on_facts, []).

:- dynamic(p/2).
:- dynamic(p/3).

p(Z, Z).
clouds(are, nice).
p(Z, h(Z, W), f(W)).

test_queries_on_facts :-
    findall(Z, p(Z, Z), [Z]),
    findall(Z, p(Z, z), [z]),
    findall(Z, p(Z, w), [w]),
    \+ p(z, w),
    p(w, w),
    \+ clouds(Z, Z),
    findall(Z, clouds(are, Z), [nice]),
    \+ p(z, h(z, z), f(w)),
    p(z, h(z, w), f(w)),
    findall(W, p(z, h(z, W), f(w)), [w]),
    findall(Z, p(Z, h(Z, w), f(Z)), [w]),
    \+ p(z, h(Z, w), f(Z)),
    retract(p(_,_,_)),
    assertz(p(Z, h(Z, W), f(W))),
    p(f(f(a)), h(f(f(a)), f(a)), f(f(a))),
    retract(p(Z, h(Z, W), f(W))).

:- initialization(test_queries_on_facts).
