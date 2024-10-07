% This file is only for test cases that don't break compilation

:- use_module(library(warnings)).

t :-
    x; integer(_).

n :-
    \+ \+ \+ foo(_).
