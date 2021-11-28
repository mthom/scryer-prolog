/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   This library provides predicates for reasoning about time.

   current_time(T) yields the current system time in an opaque form,
   called a time stamp. Use format_time//2 to describe strings that
   contain attributes of the time stamp.

   The nonterminal format_time//2 describes a list of characters that
   are formatted according to a format string. Usage:

     phrase(format_time(FormatString, TimeStamp), Cs)

   TimeStamp represents a moment in time in an opaque form, as for
   example obtained by current_time/1.

   FormatString is a list of characters that are interpreted literally,
   except for the following specifiers (and possibly more in the future):

     %Y    year of the time stamp. Example: 2020.
     %m    month number (01-12), zero-padded to 2 digits
     %d    day number (01-31), zero-padded to 2 digits
     %H    hour number (00-24), zero-padded to 2 digits
     %M    minute number (00-59), zero-padded to 2 digits
     %S    second number (00-60), zero-padded to 2 digits
     %b    abbreviated month name, always 3 letters
     %a    abbreviated weekday name, always 3 letters
     %A    full weekday name
     %j    day of the year (001-366), zero-padded to 3 digits
     %%    the literal %

   Example:

     ?- current_time(T), phrase(format_time("%d.%m.%Y (%H:%M:%S)", T), Cs).
        T = [...], Cs = "11.06.2020 (00:24:32)".

   sleep(S) sleeps for S seconds (a floating point number).

   time(Goal) reports the execution time of Goal.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(time, [max_sleep_time/1, sleep/1, time/1, current_time/1, format_time//2]).

:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(charsio), [read_term_from_chars/2]).

current_time(T) :-
        '$current_time'(T0),
        read_term_from_chars(T0, T).

format_time([], _) --> [].
format_time(['%','%'|Fs], T) --> !, "%", format_time(Fs, T).
format_time(['%',Spec|Fs], T) --> !,
        (   { member(Spec=Value, T) } ->
            seq(Value)
        ;   { domain_error(time_specifier, Spec, format_time//2) }
        ),
        format_time(Fs, T).
format_time([F|Fs], T) --> [F], format_time(Fs, T).

max_sleep_time(0xfffffffffffffbff).

sleep(T) :-
    builtins:must_be_number(T, sleep),
    (   T < 0 ->
        domain_error(not_less_than_zero, T, sleep/1)
    ;   max_sleep_time(N), T > N ->
        throw(error(representation_error(max_sleep_time), sleep/1))
    ;   '$sleep'(T)
    ).


% '$cpu_now' can be replaced by statistics/2 once that is implemented.

:- meta_predicate time(0).

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
   % CPU time: 0.000 seconds
   % CPU time: 0.001 seconds
   true.

:- time(use_module(library(lists))).
   % CPU time: 0.000 seconds
   % CPU time: 0.001 seconds
   true.

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
