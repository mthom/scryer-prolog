:- module(subterm_expansion, []).

:- use_module(library(macros)).

% Workaround for lacking subterm substitution
user:goal_expansion(foo(M#A), foo(X)) :-
    expand_goal(M#A, _, X).
user:goal_expansion(X = (M#B), X = Y) :-
    expand_goal(M#B, _, Y).
