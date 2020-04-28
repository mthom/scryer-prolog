/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written April 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   This library provides predicates for reasoning about time.
   Reasoning about time stamps would be a useful addition, for example
   by obtaining the current time, comparing and formatting it.

   '$cpu_now' can be replaced by statistics/2 once that is implemented.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(time, [max_sleep_time/1, sleep/1, time/1]).

:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(error)).

max_sleep_time(0xfffffffffffffbff).

sleep(T) :-
    builtins:must_be_number(T, sleep),
    (   T < 0 ->
        domain_error(not_less_than_zero, T, sleep/1)
    ;   max_sleep_time(N), T > N ->
        throw(error(representation_error(max_sleep_time), sleep/1))
    ;   '$sleep'(T)
    ).

time(Goal) :-
        '$cpu_now'(T0),
        setup_call_cleanup(true,
                           (   Goal,
                               report_time(T0)
                           ),
                           report_time(T0)).

report_time(T0) :-
        '$cpu_now'(T),
        Time is T - T0,
        (   bb_get('$first_answer', true) ->
            format("   % CPU time: ~3f seconds~n", [Time])
        ;   format("% CPU time: ~3f seconds~n   ", [Time])
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- time((true;false)).
   % CPU time: 0.000 seconds
   true
;  % CPU time: 0.001 seconds
   false.

:- time(use_module(library(clpz))).
   % CPU time: 2.762 seconds
   true
;  false.

:- time(use_module(library(lists))).
   % CPU time: 0.000 seconds
   true
;  % CPU time: 0.001 seconds
   false.

?- time(member(X, [a,b,c])).
   % CPU time: 0.000 seconds
   X = a
;  % CPU time: 0.002 seconds
   X = b
;  % CPU time: 0.004 seconds
   X = c
;  % CPU time: 0.007 seconds
   false.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
