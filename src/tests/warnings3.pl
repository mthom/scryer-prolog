:- use_module(library(warnings)).

j(X, B) :-
    X is [1] + sqrt(-phi*B + max(3+5)).
