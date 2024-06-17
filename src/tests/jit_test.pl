:- use_module(library(jit)).

a(X) :- b(X).
b(X) :- X is 1 + 1 + 1 + 1.
c(X, Y) :- X is Y + 1.

test :-
    jit_compile(b/1),
    jit_compile(a/1),
    a(X),
    X = 4,
    jit_compile(c/2),
    c(2, 1).
