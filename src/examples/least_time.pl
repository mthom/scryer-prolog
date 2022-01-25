/*  least_time.pl
 *
 *  By Mark Thom, 2020
 *
 *  find_min_time/2 solves a problem sometimes posed in the first round
 *  of Google interviews: given a time of day in 24 H format, what is the
 *  lexicographically least permutation of the time that is itself a
 *  valid time in 24 H format?
 *
 *  Full generality is achieved using the reif library.
 */

:- module(least_time, [find_min_time/2,
                       write_time_nl/1]).


:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(lists)).
:- use_module(library(reif)).


valid_time([H1,H2,M1,M2], T) :-
    memberd_t(H1, [0,1,2], TH1),
    memberd_t(H2, [0,1,2,3,4,5,6,7,8,9], TH2),
    memberd_t(M1, [0,1,2,3,4,5], TM1),
    memberd_t(M2, [0,1,2,3,4,5,6,7,8,9], TM2),
    (  maplist(=(true), [TH1, TH2, TM1, TM2]) ->
       (  H1 =:= 2 ->
          (  H2 =< 3 ->
             T = true
          ;  T = false
          )
       ;  T = true
       )
    ;  T = false
    ).


permuted_times(Time, PermutedTimes) :-
    setof(P, permutation(Time, P), PermutedTimes0),
    tfilter(valid_time, PermutedTimes0, PermutedTimes).


find_min_time(Time, Min) :-
    valid_time(Time, true),
    permuted_times(Time, [Min|_]).


write_time_nl(Time) :-
    format("\"~w~w:~w~w\"~n", Time).
