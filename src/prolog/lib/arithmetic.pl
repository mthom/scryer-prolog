:- module(arithmetic, [lsb/2, msb/2, stern_brocot/3]).

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

stern_brocot(E0/E1, Fraction0, Fraction) :-
    P1/Q1 = Fraction0,
    !,
    (   \+ integer(E0) -> type_error(integer, E0, stern_brocot/3)
    ;   \+ integer(E1) -> type_error(integer, E1, stern_brocot/3)
    ;   \+ integer(P1) -> type_error(integer, P1, stern_brocot/3)
    ;   \+ integer(Q1) -> type_error(integer, Q1, stern_brocot/3)
    ;   S is sign(E0) * sign(E1), S < 0 ->
            domain_error(not_less_than_zero, E0/E1, stern_brocot/3)
    ;   P2 is abs(P1),
        Q2 is abs(Q1),
        Qn1n is P2 * E1 - Q2 * E0,
        Qn1d is Q2 * E1,
        simplify_fraction(Qn1n/Qn1d, Qn1),
        Qp1n is P2 * E1 + Q2 * E0,
        Qp1d = Qn1d,
        simplify_fraction(Qp1n/Qp1d, Qp1),
        fraction_stern_brocot_(Qn1, Qp1, 0/1, 1/0, P3/Q3),
        P4 is sign(P1) * sign(Q1) * P3,
        Fraction = P4/Q3
    ).

% If 0 <= Eps0 <= 1e-16 then the search is for "infinite" precision.
stern_brocot(Eps0, Real0, Fraction) :-
    (   Real0 = R1/R2 ->
            builtins:must_be_number(R1, stern_brocot/3),
            builtins:must_be_number(R2, stern_brocot/3),
            Real is R1/R2
    ;   builtins:must_be_number(Real0, stern_brocot/3),
        Real = Real0
    ),
    (   Eps0 = E0/E1 ->
            builtins:must_be_number(E0, stern_brocot/3),
            builtins:must_be_number(E1, stern_brocot/3),
            % Eps is Eps0 % doesn't work
            Eps is E0/E1
    ;   Eps = Eps0
    ),
    S is sign(Eps),
    (   S < 0 -> domain_error(not_less_than_zero, Eps0, stern_brocot/3)
    ;   Rn is abs(Real) - Eps,
        Rp is abs(Real) + Eps,
        stern_brocot_(Rn, Rp, 0/1, 1/0, P1/Q),
        P is sign(Real) * P1,
        Fraction = P/Q
    ).

fraction_stern_brocot_(Qnn/Qnd, Qpn/Qpd, A/B, C/D, Fraction) :-
    Fn1 is A + C,
    Fd1 is B + D,
    simplify_fraction(Fn1/Fd1, Fn/Fd),
    S1 is sign(Fn * Qnd - Fd * Qnn),
    S2 is sign(Fn * Qpd - Fd * Qpn),
    (   S1 < 0 ->
            fraction_stern_brocot_(Qnn/Qnd, Qpn/Qpd, Fn/Fd, C/D, Fraction)
    ;   S2 > 0 ->
            fraction_stern_brocot_(Qnn/Qnd, Qpn/Qpd, A/B, Fn/Fd, Fraction)
    ;   Fraction = Fn/Fd
    ).

stern_brocot_(Rn, Rp, A/B, C/D, Fraction) :-
    M0 is A + C,
    M1 is B + D,
    M is M0 / M1,
    (   M < Rn -> stern_brocot_(Rn, Rp, M0/M1, C/D, Fraction)
    ;   M > Rp -> stern_brocot_(Rn, Rp, A/B, M0/M1, Fraction)
    ;   Fraction = M0/M1
    ).

simplify_fraction(A0/B0, A/B) :-
    G is gcd(A0, B0),
    A is A0 div G,
    B is B0 div G.
