:- module(arithmetic, [msb/2, lsb/2]).

lsb(X, N) :-
    builtins:must_be_number(X, lsb/2),
    (   \+ integer(X) -> throw(error(type_error(integer, X), lsb/2))
    ;   builtins:can_be_number(N, lsb/2),
        X1 is X /\ (-X),
        msb(X1, N)
    ).

msb(X, N) :-
    builtins:must_be_number(X, msb/2),
    (   \+ integer(X) -> throw(error(type_error(integer, X), msb/2))
    ;   builtins:can_be_number(N, msb/2),
        X1 is abs(X) >> 1,
        msb_(X1, 0, N1),
        S is sign(X),
        (   S = 1 -> N = N1
        ;   N is N1 + 1
        )
    ).

msb_(0, N, N) :- !.
msb_(X, M, N) :-
    X1 is X >> 1,
    M1 is M + 1,
    msb_(X1, M1, N).
