:- use_module(library(dcgs)).

id(X) --> X.

call_id :-
    id("Hello", X, []),
    X = "Hello".

:- initialization(call_id).
