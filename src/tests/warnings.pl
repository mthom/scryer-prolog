:- use_module(library(warnings)).

t :-
    x; integer(_).

n :-
    \+ \+ \+ foo(_).

x :-
    a.
    b,
    c.
