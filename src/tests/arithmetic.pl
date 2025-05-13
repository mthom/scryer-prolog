:- module(arithmetic_tests, []).
:- use_module(test_framework).
:- use_module(library(pairs)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(between)).

test_value(X, Y, Expected) :-
    R1 is 7 rdiv 8,
    R2 is -9 rdiv 10,
    pairs_keys_values(Pairs, [1, -2, 3.4, -5.6, R1, R2, 18446744073709551616, -9223372036854775808], Expected),
    member(X-Y, Pairs).

approx_eq(X, Y) :-
    Delta is abs(X - Y),
    Delta < 0.00001.

test_abs(X, Exp) :-
    Y is abs(X),
    Y == Exp,
    call(is, Y, abs(X)).

test_neg(X, Exp) :-
    Y is -X,
    Y == Exp,
    call(is, Y, -X).

test_truncate(X, Exp) :-
    Y is truncate(X),
    Y == Exp,
    call(is, Y, truncate(X)).

test_floor(X, Exp) :-
    Y is floor(X),
    Y == Exp,
    call(is, Y, floor(X)).

test_ceiling(X, Exp) :-
    Y is ceiling(X),
    Y == Exp,
    call(is, Y, ceiling(X)).

test_round(X, Exp) :-
    Y is round(X),
    Y == Exp,
    call(is, Y, round(X)).

test_float(X, Exp) :-
    Y is float(X),
    Y == Exp,
    call(is, Y, float(X)).

test_plus(X) :-
    Y is +X,
    Y == X,
    call(is, Y, +X).

test_cos_sin(X) :-
    Cos is cos(X),
    Sin is sin(X),
    ground(Cos),
    ground(Sin),
    call(is, Cos, cos(X)),
    call(is, Sin, sin(X)),

    One is Cos * Cos + Sin * Sin,
    arithmetic_tests:approx_eq(One, 1.0),

    Sin2 is cos(X - pi/2),
    arithmetic_tests:approx_eq(Sin, Sin2),
    call(is, Sin3, cos(X - pi/2)),
    arithmetic_tests:approx_eq(Sin, Sin3),

    Cos2 is sin(X + pi/2),
    arithmetic_tests:approx_eq(Cos, Cos2),
    call(is, Cos3, sin(X + pi/2)),
    arithmetic_tests:approx_eq(Cos, Cos3).

test_tan(X) :-
    Cos is cos(X),
    Sin is sin(X),
    Tan is tan(X),
    Tan2 is Sin / Cos,
    arithmetic_tests:approx_eq(Tan, Tan2),
    call(is, Tan, tan(X)).

test_float_fractional_part(X, Exp) :-
    Y is float_fractional_part(X),
    arithmetic_tests:approx_eq(Y, Exp),
    call(is, Y, float_fractional_part(X)).

test_float_integer_part(X, Exp) :-
    Y is float_integer_part(X),
    Y == Exp,
    call(is, Y, float_integer_part(X)).

test_sqrt(X) :-
    Abs is abs(X),
    Y is sqrt(Abs),
    Y2 is Y * Y,
    One is Y2 / Abs,
    arithmetic_tests:approx_eq(One, 1.0),
    call(is, Y, sqrt(abs(X))).

test_log(X) :-
    Abs is abs(X),
    Y is log(Abs),
    Y2 is e ^ Y,
    One is Y2 / Abs,
    arithmetic_tests:approx_eq(One, 1.0),
    call(is, Y, log(abs(X))).

test_exp(X) :-
    Y is exp(X),
    Y2 is e ^ X,
    arithmetic_tests:approx_eq(Y2, Y),
    call(is, Y, exp(X)).

test_acos(X) :-
    XMod is abs(X) - (floor(abs(X) / pi) * pi),
    Cos is cos(XMod),
    Y is acos(Cos),
    arithmetic_tests:approx_eq(Y, XMod),
    call(is, Y, acos(Cos)).

test_asin(X) :-
    XMod is abs(X) - (floor(abs(X) / (pi / 2)) * (pi / 2)),
    Sin is sin(XMod),
    Y is asin(Sin),
    arithmetic_tests:approx_eq(Y, XMod),
    call(is, Y, asin(Sin)).

test_atan(X) :-
    XMod is abs(X) - (floor(abs(X) / (pi / 2)) * (pi / 2)),
    Tan is tan(XMod),
    Y is atan(Tan),
    arithmetic_tests:approx_eq(Y, XMod),
    call(is, Y, atan(Tan)).

test_bitwise_complement(X, Exp) :-
    X2 is floor(X),
    Y is \X2,
    Y == Exp,
    call(is, Y, \X2).

test_sign(X, Exp) :-
    Y is sign(X),
    Y == Exp,
    call(is, Y, sign(X)).

test_add(X, Y, Z) :-
    Z2 is X + Y,
    Z == Z2,
    call(is, Z3, X + Y),
    Z == Z3,
    Z is Y + X,
    call(is, Z, Y + X).

test_mul(X, Y, Z) :-
    Z2 is X * Y,
    Z == Z2,
    call(is, Z3, X * Y),
    Z == Z3,
    Z is Y * X,
    call(is, Z, Y * X).

test_sub(X, Y) :-
    Z is X + (-Y),
    Z2 is X - Y,
    Z == Z2,
    call(is, Z3, X - Y),
    Z == Z3.

test_idiv :-
    Z is -2 // 3,
    Z == 0,
    Z2 is -4 // 3,
    Z2 == -1,
    \+ catch(_ is 5.0 // 2, _, false),
    \+ catch(_ is 5 // 2.0, _, false),
    \+ catch(_ is 5 // 0, _, false),
    \+ catch(_ is 36893488147419103232 // 0, _, false),
    Z3 is 36893488147419103232 // 3,
    Z3 == 12297829382473034410.

test_div :-
    Z is -2 div 3,
    Z == -1,
    Z2 is -4 div 3,
    Z2 == -2,
    \+ catch(_ is 5.0 div 2, _, false),
    \+ catch(_ is 5 div 2.0, _, false),
    \+ catch(_ is 5 div 0, _, false),
    \+ catch(_ is 36893488147419103232 div 0, _, false),
    Z3 is 36893488147419103232 div 3,
    Z3 == 12297829382473034410.

test_pow(X, Y, Z) :-
    Z2 is X ** Y,
    Z == Z2,
    call(is, Z3, X ** Y),
    Z == Z3.

test_ipow(X, Y, Z) :-
    Z2 is X ^ Y,
    Z == Z2,
    call(is, Z3, X ^ Y),
    Z == Z3.


test_min_max(X, Y, L) :-
    lists:nth1(X, L, XVal),
    lists:nth1(Y, L, YVal),
    Min is min(XVal, YVal),
    call(is, Min2, min(XVal, YVal)),
    Min == Min2,
    Max is max(XVal, YVal),
    call(is, Max2, max(XVal, YVal)),
    Max == Max2,
    (
        X < Y -> Min == XVal, Max == YVal
        ; Min == YVal, Max == XVal
    ).



test_rdiv(X, Y) :-
    Z is X rdiv Y,
    call(is, Z2, X rdiv Y),
    Z == Z2,
    Z3 is float(Z) / (X / Y),
    arithmetic_tests:approx_eq(Z3, 1.0).


test_shift(X, Y) :-
    (Y >= 0 ->
        ShlExpected is X * (2 ^ Y),
        ShrExpected is X // (2 ^ Y)
    ;
        ShlExpected is X // (2 ^ -Y),
        ShrExpected is X * (2 ^ -Y)
    ),
    Shl is X << Y,
    Shr is X >> Y,
    Shl == ShlExpected,
    Shr == ShrExpected,
    call(is, Shl2, X << Y),
    call(is, Shr2, X >> Y),
    Shl == Shl2,
    Shr == Shr2.

test_and_or_xor(X, Y, AndExpected, OrExpected, XorExpected) :-
    And is X /\ Y,
    And2 is Y /\ X,
    And == AndExpected,
    And == And2,
    Or is X \/ Y,
    Or2 is Y \/ X,
    Or == OrExpected,
    Or == Or2,
    Xor is xor(X, Y),
    Xor2 is xor(Y, X),
    Xor == XorExpected,
    Xor2 == Xor,

    call(is, And3, X /\ Y),
    call(is, Or3, X \/ Y),
    call(is, Xor3, xor(X, Y)),
    And3 == And,
    Or3 == Or,
    Xor3 == Xor.

test_mod_rem(X, Y) :-
    RemExpected is X - (X // Y) * Y,
    ModExpected is X - (X div Y) * Y,
    Mod is X mod Y,
    Rem is X rem Y,
    call(is, Mod2, X mod Y),
    call(is, Rem2, X rem Y),
    Mod2 == Mod,
    Mod == ModExpected,
    X2 is ((X - Mod) // Y) * Y + Mod,
    X2 == X,
    Rem == RemExpected,
    Rem2 == Rem.

test_atan2(Angle) :-
    Cos is cos(Angle),
    Sin is sin(Angle),
    A is atan2(Sin, Cos),
    arithmetic_tests:approx_eq(A, Angle),
    call(is, A2, atan2(Sin, Cos)),
    A == A2,
    A3 is atan2(Sin * 1.5, Cos * 1.5),
    arithmetic_tests:approx_eq(A3, Angle).

test_gcd(X, Y, Expected) :-
    Gcd is gcd(X, Y),
    Gcd2 is gcd(Y, X),
    call(is, Gcd3, gcd(X, Y)),
    Gcd == Expected,
    Gcd2 == Expected,
    Gcd3 == Expected.

test_bad_uninstantiated :- _ is _.
test_bad_uninstantiated2 :- _ is _ + 1.
test_bad_recursive :- X is 1 \/ X.
test_bad_corecursive :- X = Y, Y is 2 \/ X.
test_bad_corecursive2 :- X = 1 /\ Y, Y is 2 + X.

% This is unfortunately a bit too spicy for the compiler as of now:
% insert_infinite(X, Inf, Inf) :- X == recursive.
% insert_infinite(X, _, X) :- nonvar(X) -> X \= recursive; true.

% term_expansion(make_infinite(Name, X is Op), (Name :- X is Infinite)) :-
%     Op =.. [OpName, Lhs, Rhs],
%     insert_infinite(Lhs, Infinite, LhsInf),
%     insert_infinite(Rhs, Infinite, RhsInf),
%     Infinite =.. [OpName, LhsInf, RhsInf].

% :- dynamic(test_bad_recursive2/0).
% make_infinite(test_bad_recursive2, _ is 1 + recursive).

test("test_value", (
    R1 is 7 rdiv 8,
    R2 is -9 rdiv 10,
    findall([X, Y], arithmetic_tests:test_value(
        X, Y,
        [1, -2, 3.4, -5.6, R1, R2, 18446744073709551616, -9223372036854775808]
    ), L),
    length(L, Len),
    Len > 0
)).

test("abs", (
    R1 is 7 rdiv 8,
    R2 is 9 rdiv 10,
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1, 2, 3.4, 5.6, R1, R2, 18446744073709551616, 9223372036854775808]
    ), arithmetic_tests:test_abs(X, Exp))
)).

test("neg", (
    R1 is -7 rdiv 8,
    R2 is 9 rdiv 10,
    forall(arithmetic_tests:test_value(
        X, Exp,
        [-1, 2, -3.4, 5.6, R1, R2, -18446744073709551616, 9223372036854775808]
    ), arithmetic_tests:test_neg(X, Exp))
)).

test("truncate", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1, -2, 3, -5, 0, 0, 18446744073709551616, -9223372036854775808]
    ), arithmetic_tests:test_truncate(X, Exp))
)).

test("floor", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1, -2, 3, -6, 0, -1, 18446744073709551616, -9223372036854775808]
    ), arithmetic_tests:test_floor(X, Exp))
)).

test("ceiling", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1, -2, 4, -5, 1, 0, 18446744073709551616, -9223372036854775808]
    ), arithmetic_tests:test_ceiling(X, Exp))
)).

test("round", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1, -2, 3, -6, 1, -1, 18446744073709551616, -9223372036854775808]
    ), arithmetic_tests:test_round(X, Exp))
)).

test("float", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [1.0, -2.0, 3.4, -5.6, 0.875, -0.9, 18446744073709551616.0, -9223372036854775808.0]
    ), arithmetic_tests:test_float(X, Exp))
)).

test("plus", (
    forall(arithmetic_tests:test_value(X, _, _), arithmetic_tests:test_plus(X))
)).

test("cos_sin", (
    forall((arithmetic_tests:test_value(X, _, _), X < 100.0, X > -100.0), arithmetic_tests:test_cos_sin(X))
)).

test("tan", (
    forall(arithmetic_tests:test_value(X, _, _), arithmetic_tests:test_tan(X))
)).

test("float_fractional_part", (
    forall(
        arithmetic_tests:test_value(X, Exp, [0.0, 0.0, 0.4, -0.6, 0.875, -0.9, 0.0, 0.0]),
        arithmetic_tests:test_float_fractional_part(X, Exp)
    )
)).

test("float_integer_part", (
    forall(
        arithmetic_tests:test_value(X, Exp, [1.0, -2.0, 3.0, -5.0, 0.0, 0.0, 18446744073709551616.0, -9223372036854775808.0]),
        arithmetic_tests:test_float_integer_part(X, Exp)
    )
)).

test("sqrt", (
    forall(arithmetic_tests:test_value(X, _, _), arithmetic_tests:test_sqrt(X)),
    \+ catch(_ is sqrt(-1.0), _, false)
)).

test("log", (
    forall(arithmetic_tests:test_value(X, _, _), arithmetic_tests:test_log(X)),
    \+ catch(_ is log(0.0), _, false),
    \+ catch(_ is log(0), _, false),
    \+ catch(_ is log(-1.0), _, false),
    \+ catch(_ is log(-1), _, false)
)).

test("exp", (
    forall((arithmetic_tests:test_value(X, _, _), X < 1000), arithmetic_tests:test_exp(X)),
    \+ catch(_ is exp(10000), _, false)
)).

test("acos", (
    forall(
        (arithmetic_tests:test_value(X, _, _), X < 1000, X > -1000),
        arithmetic_tests:test_acos(X)
    )
)).

test("asin", (
    forall(
        (arithmetic_tests:test_value(X, _, _), X < 1000, X > -1000),
        arithmetic_tests:test_asin(X)
    )
)).

test("atan", (
    forall(
        (arithmetic_tests:test_value(X, _, _), X < 1000, X > -1000),
        arithmetic_tests:test_atan(X)
    )
)).

test("bitwise_complement", (
    forall(arithmetic_tests:test_value(
        X, Exp,
        [-2, 1, -4, 5, -1, 0, -18446744073709551617, 9223372036854775807]
    ), arithmetic_tests:test_bitwise_complement(X, Exp)),
    \+ catch(_ is \1.0, _, false)
)).

test("sign", (
    forall(
        arithmetic_tests:test_value(X, Exp, [1, -1, 1.0, -1.0, 1, -1, 1, -1]),
        arithmetic_tests:test_sign(X, Exp)
    )
)).

test("add", (
    R is 3 rdiv 7,
    R2 is 17 rdiv 7,
    B is 147573952589676412928,
    BF is -147573952589676412928.0,
    B1 is 147573952589676412929, % B + 1
    B2 is 295147905179352825856,
    BR is 1033017668127734890499 rdiv 7, % B + R
    forall(
        lists:member([X, Y, Z], [
            [0, 0, 0],
            [-100, 120, 20],
            [0.5, -3, -2.5],
            [R, 2, R2],
            [B, 1, B1],
            [B, B, B2],
            [B, BF, 0.0],
            [B, R, BR]
        ]),
        arithmetic_tests:test_add(X, Y, Z)
    )
)).

test("mul", (
    R is 3 rdiv 4,
    R2 is 3 rdiv 2,
    RSquared is 9 rdiv 16,
    forall(
        lists:member([X, Y, Z], [
            [0, 0, 0],
            [2, -3, -6],
            [R, R, RSquared],
            [R, 2, R2],
            [R, 2.0, 1.5],
            [1.5, -4.0, -6.0],
            [4294967296, 4294967296, 18446744073709551616],
            [18446744073709551616, 18446744073709551616, 340282366920938463463374607431768211456],
            [18446744073709551616, R, 13835058055282163712],
            [18446744073709551616, 2.0, 36893488147419103232.0]
        ]),
        arithmetic_tests:test_mul(X, Y, Z)
    )
)).

test("sub", (
    R is 3 rdiv 4,
    forall((
        lists:member(X, [0, 1, -7, 1.5, R, 18446744073709551616]),
        lists:member(Y, [0, 1, -7, 1.5, R, 18446744073709551616])
    ), arithmetic_tests:test_sub(X, Y))
)).

test("idiv", test_idiv).

test("div", test_div).

test("pow", (
    R is 3 rdiv 2,
    forall(
        lists:member([X, Y, Z], [
            [0, 0, 1.0],
            [2, 3, 8.0],
            [-2, 3, -8.0],
            [4294967296, 2, 18446744073709551616.0],
            [4294967296, 2.0, 18446744073709551616.0],
            [R, 2, 2.25],
            [R, 2.0, 2.25]
        ]),
        arithmetic_tests:test_pow(X, Y, Z)
    )
)).

test("ipow", (
    R is 3 rdiv 2,
    forall(
        lists:member([X, Y, Z], [
            [0, 0, 1],
            [2, 3, 8],
            [-2, 3, -8],
            [4294967296, 2, 18446744073709551616],
            [4294967296, 2.0, 18446744073709551616.0],
            [R, 2, 2.25], % Note: Could be implemented to return a rational instead
            [R, 2.0, 2.25],
            [-1, 18446744073709551617, -1],
            [18446744073709551616, 2, 340282366920938463463374607431768211456]
        ]),
        arithmetic_tests:test_ipow(X, Y, Z)
    ),
    \+ catch(X is -3 ^ -2, _, false),
    \+ catch(X is -30000000000000000000000000 ^ -2, _, false),
    \+ catch(X is -3 ^ -20000000000000000000000000, _, false)
)).

test("min_max", (
    R1 is 3 rdiv 2,
    R2 is -4 rdiv 7,
    R3 is 5 rdiv 9,
    L = [-46, R2, 0, R3, 1, R1, 1.6, 9223372036854775807, 9223372036854775808],
    length(L, Len),
    forall((
        between:between(1, Len, X),
        between:between(1, Len, Y)
    ), arithmetic_tests:test_min_max(X, Y, L))
)).

test("rdiv", (
    R is 3 rdiv 7,
    forall((
        lists:member(X, [2, -3, R, 4.5, 9223372036854775807]),
        lists:member(Y, [1, -17, R, 9223372036854775807])
    ), arithmetic_tests:test_rdiv(X, Y)),
    \+ catch(_ is 5 rdiv 0, _, false),
    \+ catch(_ is 36893488147419103232 rdiv 0, _, false)
)).

test("shift", (
    forall((
        % Note: shifting negative integers is implementation-defined.
        lists:member(X, [2, 3, 5, 9223372036854775807, 36893488147419103232]),
        lists:member(Y, [1, 0, -1, 4, -4, 63, 64, -63, -64])
    ), arithmetic_tests:test_shift(X, Y))
)).

test("and_or_xor", (
    forall(lists:member([X, Y, AndExpected, OrExpected, XorExpected], [
        [0, 0, 0, 0, 0],
        [0, 1, 0, 1, 1],
        [1, 1, 1, 1, 0],
        [3, 6, 2, 7, 5],
        [2, -3, 0, -1, -1],
        [-4, -7, -8, -3, 5],
        [
            55340232221128654848,
            110680464442257309696,
            36893488147419103232,
            129127208515966861312,
            92233720368547758080
        ],
        [
            -55340232221128654849,
            -110680464442257309697,
            -129127208515966861313,
            -36893488147419103233,
            92233720368547758080
        ]
    ]), arithmetic_tests:test_and_or_xor(X, Y, AndExpected, OrExpected, XorExpected)),
    \+ catch(_ is 1 /\ 2.0, _, false),
    \+ catch(_ is 1 \/ 2.0, _, false),
    \+ catch(_ is xor(1, 2.0), _, false)
)).

test("mod_rem", (
    forall((
        lists:member(X, [2, -3, 7, 9223372036854775807, 9223372036854775809]),
        lists:member(Y, [1, -17, 7, 9223372036854775807])
    ), arithmetic_tests:test_mod_rem(X, Y)),

    \+ catch(_ is 2 mod 0, _, false),
    \+ catch(_ is 2 rem 0, _, false),

    \+ catch(_ is 2.0 mod 1, _, false),
    \+ catch(_ is 2.0 rem 1, _, false),

    \+ catch(_ is 2 mod 1.0, _, false),
    \+ catch(_ is 2 rem 1.0, _, false)
)).

test("atan2", (
    forall(lists:member(Angle, [0, -1, 1, 3.14, -2.7]), arithmetic_tests:test_atan2(Angle)),
    % ISO states that atan2(0, 0) should throw, but SWI-Prolog chooses to instead return zero.
    \+ catch(X is atan2(0.0, 0.0), _, false),
    \+ catch(X is atan2(0.0, 0), _, false),
    \+ catch(X is atan2(0, 0.0), _, false)
)).

test("gcd", (
    forall(
        lists:member([X, Y, Expected], [
            [0, 0, 0],
            [0, 1, 1],
            [0, 4, 4],
            [1, 4, 1],
            [2, 4, 2],
            [3, 7, 1],
            [9223372036854775807, 343, 49],
            [36893488147419103231, 145295143558111, 145295143558111],
            [258254417031933722617, 36893488147419103231, 36893488147419103231],
            [-9223372036854775808, -9223372036854775808, 9223372036854775808]
        ]),
        arithmetic_tests:test_gcd(X, Y, Expected)
    ),
    \+ catch(X is gcd(1.0, 1), _, false),
    \+ catch(X is gcd(1 rdiv 2, 1), _, false)
)).

test("bad", (
    % Uninstantiated variables:
    \+ catch(test_bad_uninstantiated, _, false),
    \+ catch(call(is, _, X), _, false),
    \+ catch(test_bad_uninstantiated2, _, false),
    \+ catch(call(is, _, X + 1), _, false),

    % Missing function:
    \+ catch(test_bad_missing, _, false),
    \+ catch(call(is, _, float(1, 2, 3)), _, false),

    % Recursive expression:
    \+ catch((X = 1 /\ X, call(is, _, X)), _, false),
    \+ catch(test_bad_recursive, _, false),
    \+ catch(call(is, X, 1 /\ X), _, false),

    % Co-recursive expressions:
    \+ catch(test_bad_corecursive, _, false),
    \+ catch((X = 1 /\ Y, Y = 2 \/ X, _ is Y), _, false),
    \+ catch(test_bad_corecursive2, _, false),
    \+ catch((X = 1 /\ Y, Y is 2 \/ X), _, false)
)).
