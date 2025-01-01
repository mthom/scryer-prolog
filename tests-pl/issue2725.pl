:- use_module(library(dcgs)).

id(X) --> X.

call_id :-
    id("Hello", X, []),
    X = "Hello".
:- initialization(call_id).

test_default_strip_module :-
    strip_module(hello, M, P),
    nonvar(M),
    M = user,
    nonvar(P),
    P = hello,
    strip_module(hello, user, _),
    strip_module(hello, M, P).
:- initialization(test_default_strip_module).

test_default_module :-
    default_module(M),
    nonvar(M),
    M = user,
    default_module(user),
    default_module(M).
:- initialization(test_default_module).

strip_module_call(Pred) :-
    strip_module(Pred, M, Pred0),
    call(M:Pred0).

my_true.

test_strip_module_call :-
    strip_module_call(my_true),
    strip_module_call(user:my_true).
:- initialization(test_strip_module_call).
