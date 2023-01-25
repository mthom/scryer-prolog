/** Arithmetic predicates

These predicates are additions to standard the arithmetic functions provided by `is/2`.
*/

:- module(arithmetic, [expmod/4, lcm/3, lsb/2, msb/2, number_to_rational/2,
                       number_to_rational/3, popcount/2,
                       rational_numerator_denominator/3]).

:- use_module(library(charsio), [write_term_to_chars/3]).
:- use_module(library(error)).
:- use_module(library(lists), [append/3, member/2]).


%% expmod(+Base, +Expo, +Mod, -R).
%
% Modular exponentiation. Base, Expo and Mod must be integers.
expmod(Base, Expo, Mod, R) :-
    (   member(N, [Base, Expo, Mod]), var(N) -> instantiation_error(expmod/4)
    ;   member(N, [Base, Expo, Mod]), \+ integer(N) ->
        type_error(integer, N, expmod/4)
    ;   Expo < 0 -> domain_error(not_less_than_zero, Expo, expmod/4)
    ;   expmod_(Base, Expo, Mod, 1, R)
    ).

expmod_(_, _, 1, _, 0) :- !.
expmod_(_, 0, _, R, R) :- !.
expmod_(Base0, Expo0, Mod, C0, R) :-
    Expo0 /\ 1 =:= 1,
    C is (C0 * Base0) mod Mod,
    !,
    Expo is Expo0 >> 1,
    Base is (Base0 * Base0) mod Mod,
    expmod_(Base, Expo, Mod, C, R).
expmod_(Base0, Expo0, Mod, C, R) :-
    Expo is Expo0 >> 1,
    Base is (Base0 * Base0) mod Mod,
    expmod_(Base, Expo, Mod, C, R).

%% lcm(+A, +B, -Lcm) is det.
%
% Calculates the Least common multiple for A and B: the smallest positive integer
% that is divisible by both A and B.
% 
% A and B need to be integers.
lcm(A, B, X) :-
    builtins:must_be_number(A, lcm/2),
    builtins:must_be_number(B, lcm/2),
    (   \+ integer(A) -> type_error(integer, A, lcm/2)
    ;   \+ integer(B) -> type_error(integer, B, lcm/2)
    ;   (A = 0, B = 0) -> X = 0
    ;   builtins:can_be_number(X, lcm/2),
	X is abs(B) // gcd(A,B) * abs(A)
    ).

%% lsb(+X, -N).
%
% True iff N is the least significat bit of integer X
lsb(X, N) :-
    builtins:must_be_number(X, lsb/2),
    (   \+ integer(X) -> type_error(integer, X, lsb/2)
    ;   X < 1 -> domain_error(not_less_than_one, X, lsb/2)
    ;   builtins:can_be_number(N, lsb/2),
        X1 is X /\ (-X),
        msb_(X1, -1, N)
    ).

%% msb(+X, -N).
%
% True iff N is the most significant bit of integer X
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

%% number_to_rational(+Real, -Fraction).
%
% True iff given a number Real, Fraction is the same number represented as a fraction.
number_to_rational(Real, Fraction) :-
    (   var(Real) -> instantiation_error(number_to_rational/2)
    ;   integer(Real) -> Fraction is Real rdiv 1
    ;   (rational(Real) ; float(Real)) ->
            number_to_rational(1.0e-6, Real, Fraction)
    ;   type_error(number, Real, number_to_rational/2)
    ).

% If 0 <= Eps0 <= 1e-16 then the search is for "infinite" precision.
number_to_rational(Eps0, Real0, Fraction) :-
    (   var(Eps0) -> instantiation_error(number_to_rational/3)
    ;   \+ number(Eps0) -> type_error(number, Eps0, number_to_rational/3)
    ;   Eps0 < 0 -> domain_error(not_less_than_zero, Eps0, number_to_rational/3)
    ;   Eps_ is Eps0 rdiv 1,
        rational_numerator_denominator(Eps_, EpsN, EpsD),
        Eps = EpsN/EpsD
    ),
    (   var(Real0) -> instantiation_error(number_to_rational/3)
    ;   \+ number(Real0) -> type_error(number, Eps0, number_to_rational/3)
    ;   Real_ is Real0 rdiv 1,
        rational_numerator_denominator(Real_, RealN, RealD),
        Real = RealN/RealD
    ),
    E0/E1 = Eps,
    P0/Q0 = Real,
    (   P0 < 0 -> I1 is -1 + P0 // Q0
    ;   I1 is P0 // Q0
    ),
    P1 is P0 mod Q0,
    Q1 = Q0,
    (   P1 =:= 0 -> Fraction is I1 + 0 rdiv 1
    ;   Qn1n is max(P1 * E1 - Q1 * E0, 0),
        Qn1d is Q1 * E1,
        Qn1 = Qn1n/Qn1d,
        Qp1n is P1 * E1 + Q1 * E0,
        Qp1d = Qn1d,
        Qp1 = Qp1n/Qp1d,
        stern_brocot_(Qn1, Qp1, 0/1, 1/0, P2/Q2),
        Fraction is I1 + P2 rdiv Q2
    ),
    !.

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
    A is A0 // G,
    B is B0 // G.

%% rational_numerator_denominator(+Fraction, -Numerator, -Denominator).
%
% True iff given a fraction Fraction, Numerator is the numerator of that fraction
% and Denominator the denominator.
rational_numerator_denominator(R, N, D) :-
    write_term_to_chars(R, [], Cs),
    append(Ns, [' ', r, d, i, v, ' '|Ds], Cs),
    number_chars(N, Ns),
    number_chars(D, Ds).

%% popcount(+Number, -Bits1).
%
% True iff given an integer Number, Bits1 is the amount of 1 bits the binary representation
% of that number has.
popcount(X, N) :-
    must_be(integer, X),
    '$popcount'(X, N).
