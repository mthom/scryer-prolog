/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2025 by David C. Norris (david@precisionmethods.guru)
   As with all things floating-point, use at your own risk.
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/** Utility predicates for testing numerics

*/

:- module(testutils, [
              try_falsify/2
              ,witness/2
              ,real/1
              ,posreal/1
              ,interval/3
              ,call_free/2
              ,odd_t/3
              ,δ_inverses_t/5
              ,int_realfact/2
          ]).

:- use_module(library(lists)).
:- use_module(library(random)).
:- use_module(library(error)).
:- use_module(library(format)).

%% real(-X)
%
% X = tan(U) for uniform U ~ U[-π,π).
real(X) :-
    random(U),
    X is tan(pi*(U - 0.5)).

%% posreal(-X)
%
% X = 1/U for uniform U ~ U[0,1).
posreal(X) :-
    random(U),
    X is 1/U - 1.

%% interval(+A, +B, -X)
%
% X ~ U[A,B).
interval(A, B, X) :-
    random(U),
    X is A + (B-A)*U.

:- meta_predicate(try_falsify(+, 1)).

% NOTE: NON-reproducible tests would in fact be MORE STRINGENT,
%       creating opportunities to detect rare error cases over time.
reproducibly :- set_random(seed(2025)).

%% try_falsify(+IntExpr, ?G_1)
%
% Make (N is IntExpr) attempts to falsify the partial goal G/1,
% reporting the first counterexample found.
try_falsify(N, G_1) :- reproducibly -> try_falsify_(N, G_1).
try_falsify_(IntExpr, G_1) :- N is IntExpr, must_be(integer, N), N > 0,
                      (   call(G_1, false) -> counterexample(G_1)
                      ;   N_ is N - 1,
                          try_falsify_(N_, G_1)
                      ).

%% call_free(?G, -V)
%
% Call goal G, the single free variable of which is bound to V.
call_free(G, V) :- term_variables(G, [V]), call(G).

:- meta_predicate(odd_t(2, 0, ?)).

:- meta_predicate(witness(+, 0)).

%% witness(+N, ?OhNo)
%
% Make N attempts to satisfy the goal OhNo, reporting the first
% counterexample found.
witness(N, OhNo) :- N > 0,
                    (   call(OhNo) -> counterexample(OhNo)
                    ;   N_ is N - 1,
                        witness(N_, OhNo)
                    ).

% The goal below is obviously _designed_ to succeed 10% of the time,
% giving us plenty of chances to see 'counterexamples':
?- witness(10, (random(X), format("% X = ~f~n", [X]), X > 0.9)).
% X = 0.8084510175379878
% X = 0.3173976152322231
% X = 0.6016479707924276
% X = 0.2782828276608216
% X = 0.5737059731916494
% X = 0.4300520177737992
% X = 0.5411038305190763
% X = 0.6901983097300066
% X = 0.05013429563996663
% X = 0.7321078902421636
   false.
% X = 0.6401599325865659
% X = 0.7024957773981413
% X = 0.5798797162672757
% X = 0.3107013295892864
% X = 0.3792925200660049
% X = 0.3424593598278811
% X = 0.0589899862019303
% X = 0.9692529829158145
% COUNTEREXAMPLE: user:random(0.9692529829158145),(current_output(user_output),pio:phrase_to_stream(format:format_([%, ,X, ,=, ,~,f,~,n],[0.9692529829158145]),user_output),flush_output(user_output)),0.9692529829158145>0.9
   X = 0.9692529829158145.

%% odd_t(+F_2, +Any, ?T)
%
% T is the truth-value from testing that function F_2 is
% [odd](https://en.wikipedia.org/wiki/Even_and_odd_functions) at a
% value X obtained via call_free(Any, X).
odd_t(F, Any, T) :-
    (   call_free(Any, X),
        _X is -X,
        call(F, X, Fx),
        call(F, _X, _Fx),
        _Fx is -Fx -> T = true
    ;   T = false
    ).

:- meta_predicate(δ_inverses_t(?, 2, 2, 0, ?)).

%% δ_inverses_t(+Δ, +F_2, +Finv_2, +Any, ?T)
%
% For given functions F_2 and Finv_2, T is the truth-value from
% testing that Finv_2 ∘ F_2 is within Δ of the identity at a value X
% obtained via call_free(Any, X).
δ_inverses_t(Δ, F, Finv, Any, T) :-
    (   call_free(Any, X),
        call(F, X, Fx),
        call(Finv, Fx, X_),
        (   abs(X - X_) < Δ -> T = true
        ;   T = false
        )
    ).

%% int_realfact(+N, -FactN)
%
% FactN is floating-point N!
int_realfact(N, FactN) :-
    N > 0, N_ is N - 1, int_realfact(N_, FactN_), FactN is N*FactN_.
int_realfact(0, 1.0).

counterexample(G) :- format("% COUNTEREXAMPLE: ~w~n", [G]).
