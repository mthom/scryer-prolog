:- module(test_si, [test_si/0]).

:- use_module(library(si)).

test_string :-
    maplist_si(char_si, [a,b]),
    \+ maplist_si(char_si, [a|non_string]),
    \+ maplist_si(char_si, abc),
    \+ maplist_si(char_si, [0'a]),
    maplist_si(char_si, []),
    \+ maplist_si(char_si, ['']),
    L = [a|L], 
    \+ maplist_si(char_si, L),
    \+ maplist_si(char_si, [_,non_char]).

test_si :-
    test_string.
