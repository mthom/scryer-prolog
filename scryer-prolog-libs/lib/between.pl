/** Predicates that generate integers

These predicates can be used to reason about integers in a reduced domain that
follow some property. `library(clpz)` provides another way of reasoning about
integers that may also be interesting.
*/

:- module(between, [between/3, gen_int/1, gen_nat/1, numlist/2, numlist/3, repeat/1]).

%% TODO: numlist/5.

:- use_module(library(lists), [length/2]).
:- use_module(library(error)).

%% between(+Lower, +Upper, -X).
%
% Given Lower and Upper are both integer numbers, true iff X is an integer so that _Lower =< X =< Upper_.
% Can be used both to check if X is between Lower and Upper or to generate an integer between
% Lower and Upper.
%
% Examples:
%
% ```
% ?- between(10, 20, 15).
%    true.
% ?- between(10, 20, 25).
%    false.
% ?- between(3, 5, X).
%    X = 3
% ;  X = 4
% ;  X = 5.
% ```
between(Lower, Upper, X) :-
    must_be(integer, Lower),
    must_be(integer, Upper),
    can_be(integer, X),
    (   nonvar(X) ->
        Lower =< X,
        X =< Upper
    ;   Lower =< Upper,
        between_(Lower, Upper, X)
    ).

between_(Lower, Upper, Lower1) :-
   Lower < Upper,
   !,
   (  Lower1 = Lower
   ;  Lower0 is Lower + 1,
      between_(Lower0, Upper, Lower1)
   ).
between_(Lower, Lower, Lower).

enumerate_nats(I, I).
enumerate_nats(I0, N) :-
    I1 is I0 + 1,
    enumerate_nats(I1, N).

%% gen_nat(?N)
%
% True iff N is a natural number.
gen_nat(N) :-
    can_be(integer, N),
    (   var(N) -> enumerate_nats(0, N)
    ;   true
    ).

enumerate_ints(I, I).
enumerate_ints(I0, N) :-
    I0 > 0,
    N is -I0.
enumerate_ints(I0, N) :-
    I1 is I0 + 1,
    enumerate_ints(I1, N).

%% gen_int(?N)
%
% True iff N is an integer.
gen_int(N) :-
    can_be(integer, N),
    (   var(N) -> enumerate_ints(0, N)
    ;   true
    ).

repeat_integer(N) :-
    N > 0.
repeat_integer(N0) :-
    N0 > 0, N1 is N0 - 1, repeat_integer(N1).

%% repeat(+N)
%
% Succeeds N times. This predicate is only included for compatibility and *should not be used*
% because it lacks a declarative interpretation.
repeat(N) :-
    must_be(integer, N), repeat_integer(N).

%% numlist(?Upper, ?List)
%
% True iff List is the list of integers _[1, ..., Upper]_. Example:
%
% ```
% ?- numlist(X, Y).
%    X = 1, Y = [1],
% ;  X = 2, Y = [1,2]
% ;  X = 3, Y = [1,2,3]
% ; ... .
% ```
numlist(Upper, List) :-
    (  integer(Upper) -> findall(X, between(1, Upper, X), List)
    ;  List = [_|_], length(List, Upper), findall(X, between(1, Upper, X), List)
    ).

diag_nats(M, N, M, N).
diag_nats(M, 0, M1, N1) :-
    !,
    M0 is M+1,
    diag_nats(0, M0, M1, N1).
diag_nats(M, N, M1, N1) :-
    M0 is M+1,
    N0 is N-1,
    diag_nats(M0, N0, M1, N1).

diag_nats(0, 0).
diag_nats(M, N) :-
    diag_nats(0, 1, M, N).

diag_nats_signs(0, 0, 0, 0) :- !.
diag_nats_signs(0, M, 0, M0) :- !,
    (  M0 = M ; M0 is -M  ).
diag_nats_signs(M, 0, M0, 0) :- !,
    (  M0 = M ; M0 is -M  ).
diag_nats_signs(M, N, M, N).
diag_nats_signs(M, N, M, N0) :-
    N0 is -N.
diag_nats_signs(M, N, M0, N) :-
    M0 is -M.
diag_nats_signs(M, N, M0, N0) :-
    M0 is -M, N0 is -N.

diag_ints(M, N, M0, N0) :-
    diag_nats(M, N),
    diag_nats_signs(M, N, M0, N0).

diag_ints(M, N) :-
    diag_ints(_, _, M, N).

gen_ints(L, U) :-
    can_be(integer, L), can_be(integer, U),
    (  integer(L), integer(U), !
    ;  integer(L) -> gen_int(U)
    ;  integer(U) -> gen_int(L)
    ;  diag_ints(L, U)
    ),
    L =< U.

%% numlist(?Lower, ?Upper, ?List).
%
% True iff List is a list of the form _[Lower, ..., Upper]_.
% Example:
%
% ```
% ?- numlist(5, 10, X).
%    X = [5,6,7,8,9,10].
% ```
numlist(Lower, Upper, List) :-
    gen_ints(Lower, Upper), findall(X, between(Lower, Upper, X), List).
