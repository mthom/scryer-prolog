:- module(arithmetic, [lsb/2, msb/2, mediants/2]).

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

mediants_precision(1.0e-15).

mediants(Real, Fraction) :-
    builtins:must_be_number(Real, mediants),
    Fraction = P/Q,
    mediants_precision(Eps),
    R is abs(Real),
    stern_brocot(Eps, R, P1/Q),
    P is sign(Real) * P1.

% If 0 <= Eps <= 1e-16 then the search is for "infinite" precision.
stern_brocot(Eps, Real, Fraction) :-
    Rn is Real - Eps,
    Rp is Real + Eps,
    stern_brocot_(Rn, Rp, 0/1, 1/0, Fraction).

stern_brocot_(Rn, Rp, A/B, C/D, Fraction) :-
    M0 is A + C,
    M1 is B + D,
    M is M0 / M1,
    (   M < Rn -> stern_brocot_(Rn, Rp, M0/M1, C/D, Fraction)
    ;   M > Rp -> stern_brocot_(Rn, Rp, A/B, M0/M1, Fraction)
    ;   Fraction = M0/M1
    ).
