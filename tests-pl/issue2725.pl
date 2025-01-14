:- module(issue2725, []).
:- use_module(library(dcgs)).

% Tests that the id/3 dcg can be called.
% library(dcgs) currently expands it to id(X, Y, Z) :- phrase(X, Y, Z).
id(X) --> X.
call_id :-
    id("Hello", X, []),
    X = "Hello".
:- initialization(call_id).

test_default_strip_module :-
    strip_module(hello, M, P),
    nonvar(M),
    M = issue2725,
    nonvar(P),
    P = hello,
    strip_module(hello, issue2725, _),
    strip_module(hello, M, P).
:- initialization(test_default_strip_module).

% Tests that strip_module followed by call works with or without the module: prefix.
strip_module_call(Pred) :-
    loader:strip_module(Pred, M, Pred0),
    call(M:Pred0).

my_true.

test_strip_module_call :-
    strip_module_call(my_true),
    strip_module_call(issue2725:my_true).
:- initialization(test_strip_module_call).

% :- initialization(loader:prolog_load_context(module, M), write(M), write('\n')).
% :- initialization(loader:load_context(user)).
