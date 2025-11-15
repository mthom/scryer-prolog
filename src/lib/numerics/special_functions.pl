/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2025 by David C. Norris (david@precisionmethods.guru)
   As with all things floating-point, use at your own risk.
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/** Special math functions in the Error, Gamma and Beta families

The underlying Rust implementations come from the
[puruspe](https://docs.rs/puruspe/latest/puruspe/) crate.
*/

:- module(special_functions, [
              erf/2
              ,erfc/2
              ,inverf/2
              ,inverfc/2
              ,gamma/2
              ,gamma/3
              ,gamma_P_Q/4
              ,invgammp/3
              ,log_gamma/2
              ,beta/3
              ,betai/4
              ,invbetai/4
              ,test/2
              ,test_special_functions/0
              ,try_falsify/1
              ,witness/1
          ]).

:- use_module(library(numerics/testutils)).

%% erf(+Xexpr, -Erf)
%
% X is Xexpr ∈ ℝ, Erf is erf(X).
%
% [DLMF §7.2.1](https://dlmf.nist.gov/7.2#E1),
% [`puruspe::error::erf`](https://docs.rs/puruspe/latest/puruspe/error/fn.erf.html)
erf(Xexpr, Erf) :-
    X is Xexpr,
    builtins:must_be_number(X, erf/2),
    '$erf'(X, Erf).

% Demonstrate the roots of x - erf(x))
?- X0 = 0.6174468790806071, erf(X0, X0), _X0 is -X0, erf(_X0, _X0).
   X0 = 0.6174468790806071, _X0 = -0.6174468790806071.

% erf is an odd function:
?- try_falsify(odd_t(erf, real(_))).
   false.

% Another way to say the same thing..
?- witness(odd_t(erf, real(_), false)).
   false.

% ..and yet one more:
?- witness((real(X), erf(X,Erf), erf(-X,_Erf), abs(Erf+_Erf) > 0)).
   false.

%% erfc(+X, -Erfc)
%
% Erfc is erfc(X) for X ∈ ℝ.
%
% [DLMF §7.2.2](https://dlmf.nist.gov/7.2#E2),
% [`puruspe::error::erfc`](https://docs.rs/puruspe/latest/puruspe/error/fn.erfc.html)
erfc(X, Erfc) :-
    builtins:must_be_number(X, erfc/2),
    '$erfc'(X, Erfc).

?- real(X), erf(X, Erf), erfc(X, Erfc), abs(Erf+Erfc-1) > epsilon.
   false.

%% inverf(+ErfX, -X)
%
% X is erf⁻¹(ErfX) for ErfX ∈ (-1,1).
inverf(ErfX, X) :-
    builtins:must_be_number(ErfX, inverf/2),
    '$inverf'(ErfX, X).

?- try_falsify(δ_inverses_t(40*epsilon, erf, inverf, interval(-2,2,_))).
   false.

%% inverfc(+ErfcX, -X)
%
% X is erfc⁻¹(ErfcX) for ErfcX ∈ (0,2).
inverfc(ErfcX, X) :-
    builtins:must_be_number(ErfcX, inverfc/2),
    '$inverfc'(ErfcX, X).

?- try_falsify(δ_inverses_t(40*epsilon, erfc, inverfc, interval(-2,2,_))).
   false.

%% gamma(+X, -Gamma)
%
% Gamma is Γ(X), the [ordinary] gamma function evaluated at X ∈ ℝ.
%
% [DLMF §5.2.1](https://dlmf.nist.gov/5.2#E1)
% [`puruspe::gamma::gamma`](https://docs.rs/puruspe/latest/puruspe/gamma/fn.gamma.html)
gamma(X, Gamma) :-
    builtins:must_be_number(X, gamma/2),
    '$gamma'(X, Gamma).

% Γ(n+1) ≡ n!
?- N = 10, N1 is N+1, gamma(N1, ΓN1), int_realfact(N, Γ11).
   N = 10, N1 = 11, ΓN1 = 3628800.0, Γ11 = 3628800.0.


%% gamma(+A, +X, -Gamma)
%
% Gamma is Γ(A,X), the upper incomplete gamma function, where A > 0
% is the shape parameter and X ≥ 0 is the lower limit of integration.
%
% [DLMF §8.2.2](https://dlmf.nist.gov/8.2#E2),
gamma(A, X, Gamma) :-
    builtins:must_be_number(A, gammq/3),
    builtins:must_be_number(X, gammq/3),
    '$gammq'(A, X, Q),
    gamma(A, GammaA),
    Gamma is Q*GammaA.

%% gamma_P_Q(+A, +X, -P, -Q)
%
% For shape parameter A > 0 and lower limit of integration X ≥ 0,
%
% * P is γ(A,X)/Γ(X), the regularized _lower_ incomplete gamma function, and
% 
% * Q is Γ(A,X)/Γ(X), the regularized _upper_ incomplete gamma function.
%
% [DLMF §8.2.4](https://dlmf.nist.gov/8.2#E4),
% [`puruspe::gammp::gammp`](https://docs.rs/puruspe/latest/puruspe/gamma/fn.gammp.html),
% [`puruspe::gammp::gammq`](https://docs.rs/puruspe/latest/puruspe/gamma/fn.gammq.html)
gamma_P_Q(A, X, P, Q) :-
    builtins:must_be_number(A, gamma_P_Q/4),
    builtins:must_be_number(X, gamma_P_Q/4),
    '$gammp'(A, X, P),
    '$gammq'(A, X, Q).

% P + Q ≈ 1
?- gamma_P_Q(1.2, 2.3, P, Q), abs(P + Q - 1) < epsilon.
   P = 0.8621845438106976, Q = 0.1378154561893024.

%% invgammp(+A, +P, -X)
%
% Given shape parameter A > 0 and probability P ∈ [0,1),
%
% X is the unique solution of P = P(A,X), where P(-,-) is the
% regularized lower incomplete gamma function.
%
% [`puruspe::gamma::invgammp`](https://docs.rs/puruspe/latest/puruspe/gamma/fn.invgammp.html)
invgammp(A, P, X) :-
    builtins:must_be_number(A, invgammp/3),
    builtins:must_be_number(P, invgammp/3),
    '$invgammp'(P, A, X).

?- A = 1.5, P = 0.7, invgammp(A, P, X), gamma_P_Q(A, X, P_, _), abs(P-P_) < epsilon.
   A = 1.5, P = 0.7, X = 1.8324353915624363, P_ = 0.7000000000000001.

%% log_gamma(+X, -LogGamma)
%
% LogGamma is ln(Γ(X)), the natural logarithm of Γ(X).
%
% [`puruspe::gamma::ln_gamma`](https://docs.rs/puruspe/latest/puruspe/gamma/fn.ln_gamma.html)
log_gamma(X, LnGamma) :-
    builtins:must_be_number(X, log_gamma/2),
    '$ln_gamma'(X, LnGamma).

%% beta(+X, +Y, -B)
%
% B is B(X,Y) ≡ Γ(X)*Γ(Y)/Γ(X+Y)
%
% [DLMF  §5.12.1](https://dlmf.nist.gov/5.12#E1)
% [`puruspe::beta::beta`](https://docs.rs/puruspe/latest/puruspe/beta/fn.beta.html)
beta(X, Y, B) :-
    builtins:must_be_number(X, beta/3),
    builtins:must_be_number(Y, beta/3),
    '$beta'(X, Y, B).

%% betai(+A, +B, +X, -Ix)
%
% Given:
%
% * shape parameters A > 0 and B > 0,
% * upper limit of integration X ∈ [0,1],
%
% Ix is Iₓ(A,B) ≡ B(X;A,B)/B(A,B), the regularized incomplete beta function;
%
% [DLMF  §8.17.2](https://dlmf.nist.gov/8.17#E2),
% [`puruspe::beta::betai`](https://docs.rs/puruspe/latest/puruspe/beta/fn.betai.html)
betai(A, B, X, Ix) :-
    builtins:must_be_number(A, betai/4),
    builtins:must_be_number(B, betai/4),
    builtins:must_be_number(X, betai/4),
    '$betai'(A, B, X, Ix).

%% invbetai(+A, +B, +P, -X)
%
% Given:
%
% * shape parameters A > 0 and B > 0,
% * probability P ∈ [0,1],
%
% X ∈ [0,1] is the unique solution of P = Iₓ(A,B) ≡ B(X;A,B)/B(A,B).
%
% [`puruspe::beta::invbetai`](https://docs.rs/puruspe/latest/puruspe/beta/fn.invbetai.html)
invbetai(A, B, P, X) :-
    builtins:must_be_number(A, invbetai/4),
    builtins:must_be_number(B, invbetai/4),
    builtins:must_be_number(P, invbetai/4),
    '$invbetai'(P, A, B, X).


% ============================== TESTS ==============================

%% test_special_functions
%
% Run all tests defined in this module.  (These tests _succeed_ when
% they find counterexamples, so the 'desirable' result is `false`.)
test_special_functions :-
    format("Seeking counterexamples to assertions:~n", []),
    test(T, G), format("% ~s ~n", [T]),
    call(G).

% We default to 1M falsification attempts per assertion, and -- more
% importantly -- use the (unexported) testutils:try_falsify_/2, to
% avoid testutils:reproducibly/0 fixing an RNG seed.  Thus we obtain
% truly pseudorandom tests untainted by seed-hacking impropriety.
:- meta_predicate(try_falsify(1)).
try_falsify(G) :- testutils:try_falsify_(10^6, G).

% A unary witness/1 predicate similarly renders queries more concise.
:- meta_predicate(witness(0)).
witness(G) :- testutils:witness(10^6, G).

:- discontiguous(test/2).

%% test(+Name, ?Goal)
%
% Tests have the signature established by @bakaq's test_framework,
% each with a user-facing string Name, and a Goal which serves as an
% _assertion_ by succeeding iff the Name'd desirable property holds.
test("erf is odd", try_falsify(odd_t(erf, real(_)))).

test("pos root of erf(x)-x", \+ (X0 = 0.6174468790806071, erf(X0, X0))).

test("erfc ≈ 1 - erf", try_falsify(erf_plus_erfc_unity_t(real(_)))).

erf_plus_erfc_unity_t(Any, T) :-
    call_free(Any, X), erf(X, Erf), erfc(X, Erfc),
    (   abs(Erf + Erfc - 1) < epsilon -> T = true
    ;   T = false
    ).

test("inverf ≈ erf⁻¹",
     try_falsify(δ_inverses_t(40*epsilon, erf, inverf, interval(-2,2,_)))).

test("('false' is good)", false).
