% Issue 2632

% Repro for cycle detection crash
:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(error)).
:- use_module(library(lambda)).
:- use_module(library(debug)).

clpz:monotonic.

q_r(T/N, T:U) :- 0 #=< #T, 0 #=< #U, #N #= T + U.

qs_Ts_Us(Qs, ΣTs, ΣUs) :-
    maplist(\Q^T^U^(q_r(Q, T:U)), Qs, Ts, Us),
    intlist_partsums(Ts, ΣTs),
    intlist_partsums(Us, ΣUs).

%% Utility predicates used above:

intlist_partsums([X|Xs], [X|Ss]) :-
    intlist_partsums_acc(Xs, Ss, X).

intlist_partsums_acc([], [], _).
intlist_partsums_acc([X|Xs], [S|Ss], A) :-
    #S #= #X + #A,
    intlist_partsums_acc(Xs, Ss, S).

test_b :-
    once(qs_Ts_Us(_, [1,3], [5,9])).
