:- module(arithmetic, [msb/2, lsb/2]).

:- use_module(library(error)).

lsb(X, N) :-
    builtins:must_be_number(X, lsb/2),
    (   \+ integer(X) -> type_error(integer, X, lsb/2)
    ;   X < 1 -> domain_error(not_less_than_one, X, lsb/2)
    ;   builtins:can_be_number(N, lsb/2),
        X1 is X /\ (-X),
        msb_(X1, -1, N)
    ).

msb(X, N) :-
    builtins:must_be_number(X, msb/2),
    (   \+ integer(X) -> type_error(integer, X, msb/2)
    ;   X < 1 -> domain_error(not_less_than_one, X, msb/2)
    ;   builtins:can_be_number(N, msb/2),
        X1 is X >> 1,
        msb_(X1, 0, N)
    ).

msb_(0, N, N) :- !.
msb_(X, M, N) :-
    X1 is X >> 1,
    M1 is M + 1,
    msb_(X1, M1, N).
