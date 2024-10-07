% This file is only for test cases that don't break compilation

:- use_module(library(lists)).
:- use_module(library(warnings)).

% Should warn regarding unsound type tests
t :-
    x; integer(_).

% Should warn about deeply nested negations
n :-
    \+ \+ \+ foo(_).

% Should trigger meta-predicate warning
x(G) :- G.
y(G) :- call(G, 1).
z(G) :- maplist(G, "abc").

% Shouldn't trigger meta-predicate warning
a(L) :- maplist(=(_), L).
