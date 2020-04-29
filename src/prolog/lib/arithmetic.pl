:- module(arithmetic, [lsb/2, msb/2, number_to_rational/2,
                       number_to_rational/3,
                       rational_numerator_denominator/3]).

:- use_module(library(charsio), [write_term_to_chars/3]).
:- use_module(library(error)).
:- use_module(library(lists), [append/3, member/2]).

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

number_to_rational(Real0, Fraction) :-
    (   var(Real) -> instantiation_error(number_to_rational/2)
    ;   Real0 = R1/R2 ->
        (   member(R, [R1, R2]), \+ number(R) ->
                type_error(number, R, number_to_rational/2)
        ;   Real = R1/R2
        )
    ;   number(Real0),
        Real = Real0/1
    ),
    number_to_rational(1.0e-6/1, Real, Fraction).

% If 0 <= Eps0 <= 1e-16 then the search is for "infinite" precision.
number_to_rational(Eps0, Real0, Fraction) :-
    (   var(Eps0) -> instantiation_error(number_to_rational/3)
    ;   Eps0 = E0/E1 ->
        (   member(E, [E0, E1]), \+ number(E) ->
                type_error(number, E, number_to_rational/3)
        ;   Eps = E0/E1
        )
    ;   number(Eps0),
        Eps = Eps0/1
    ),
    (   var(Real0) -> instantiation_error(number_to_rational/3)
    ;   Real0 = R1/R2 ->
        (   member(R, [R1, R2]), \+ number(R) ->
                type_error(number, R, number_to_rational/3)
        ;   Real = R1/R2
        )
    ;   number(Real0),
        Real = Real0/1
    ),
    E0/E1 = Eps,
    P0/Q0 = Real,
    S is sign(E0) * sign(E1),
    (   S < 0 -> domain_error(not_less_than_zero, Eps0, number_to_rational/3)
    ;   P1 is abs(P0),
        Q1 is abs(Q0),
        Qn1n is P1 * E1 - Q1 * E0,
        Qn1d is Q1 * E1,
        Qn1 = Qn1n/Qn1d,
        Qp1n is P1 * E1 + Q1 * E0,
        Qp1d = Qn1d,
        Qp1 = Qp1n/Qp1d,
        stern_brocot_(Qn1, Qp1, 0/1, 1/0, P2/Q2),
        P3 is sign(P0) * sign(Q0) * P2,
        Fraction is P3 rdiv Q2
    ).

number(X) :-
    (   integer(X)
    ;   float(X)
    ;   rational(X)
    ).

stern_brocot_(Qnn/Qnd, Qpn/Qpd, A/B, C/D, Fraction) :-
    Fn1 is A + C,
    Fd1 is B + D,
    simplify_fraction(Fn1/Fd1, Fn/Fd),
    S1 is sign(Fn * Qnd - Fd * Qnn),
    S2 is sign(Fn * Qpd - Fd * Qpn),
    (   S1 < 0 -> stern_brocot_(Qnn/Qnd, Qpn/Qpd, Fn/Fd, C/D, Fraction)
    ;   S2 > 0 -> stern_brocot_(Qnn/Qnd, Qpn/Qpd, A/B, Fn/Fd, Fraction)
    ;   Fraction = Fn/Fd
    ).

simplify_fraction(A0/B0, A/B) :-
    G is gcd(A0, B0),
    A is A0 div G,
    B is B0 div G.

rational_numerator_denominator(R, N, D) :-
    write_term_to_chars(R, [], Cs),
    append(Ns, [' ', r, d, i, v, ' '|Ds], Cs),
    number_chars(N, Ns),
    number_chars(D, Ds).
