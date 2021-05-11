:- module(test_si, [test_si/0]).

:- use_module(library(si)).

test_string :-
    string_si([a,b]),
    \+ string_si([a|non_string]),
    \+ string_si(abc),
    \+ string_si([0'a]),
    string_si([]),
    \+ string_si(['']),
    L = [a|L], 
    \+ string_si(L).

test_si :-
    test_string.
