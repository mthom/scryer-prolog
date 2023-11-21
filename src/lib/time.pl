/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2020-2023 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/** This library provides predicates for reasoning about time.
*/

:- module(time, [max_sleep_time/1, sleep/1, time/1, current_time/1, format_time//2]).

:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(charsio), [read_from_chars/2]).


%% current_time(-T)
%
%  Yields the current system time _T_ in an opaque form, called a
%  _time stamp_. Use `format_time//2` to describe strings that contain
%  attributes of the time stamp.

current_time(T) :-
        '$current_time'(T0),
        read_from_chars(T0, T).

%% format_time(FormatString, TimeStamp)//
%
% The nonterminal format_time//2 describes a list of characters that
% are formatted according to a format string. Usage:
%
% ```
%    phrase(format_time(FormatString, TimeStamp), Cs)
% ```
%
% TimeStamp represents a moment in time in an opaque form, as for
% example obtained by `current_time/1`.
%
% FormatString is a list of characters that are interpreted literally,
% except for the following specifiers (and possibly more in the future):
%
% |  `%Y` |  year of the time stamp. Example: 2020.                |
% |  `%m` |  month number (01-12), zero-padded to 2 digits         |
% |  `%d` |  day number (01-31), zero-padded to 2 digits           |
% |  `%H` |  hour number (00-24), zero-padded to 2 digits          |
% |  `%M` |  minute number (00-59), zero-padded to 2 digits        |
% |  `%S` |  second number (00-60), zero-padded to 2 digits        |
% |  `%b` |  abbreviated month name, always 3 letters              |
% |  `%a` |  abbreviated weekday name, always 3 letters            |
% |  `%A` |  full weekday name                                     |
% |  `%j` |  day of the year (001-366), zero-padded to 3 digits    |
% |  `%%` |  the literal `%`                                       |
%
% Example:
%
% ```
%    ?- current_time(T), phrase(format_time("%d.%m.%Y (%H:%M:%S)", T), Cs).
%       T = [...], Cs = "11.06.2020 (00:24:32)".
% ```

format_time([], _) --> [].
format_time(['%','%'|Fs], T) --> !, "%", format_time(Fs, T).
format_time(['%',Spec|Fs], T) --> !,
        (   { member(Spec=Value, T) } ->
            seq(Value)
        ;   { domain_error(time_specifier, Spec, format_time//2) }
        ),
        format_time(Fs, T).
format_time([F|Fs], T) --> [F], format_time(Fs, T).

%% max_sleep_time(T)
%
%  The maximum admissible time span for `sleep/1`.

max_sleep_time(0xfffffffffffffbff).


%% sleep(S)
%
%  Sleeps for S seconds (a floating point number or integer).

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

:- dynamic(time_id/1).
:- dynamic(time_state/3).

time_next_id(N) :-
        (   retract(time_id(N0)) ->
            N is N0 + 1
        ;   N = 0
        ),
        asserta(time_id(N)).


%% time(Goal)
%
%  Reports the execution time of Goal.

time(Goal) :-
        cputime_inferences(T0, I0),
        time_next_id(ID),
        setup_call_cleanup(asserta(time_state(ID, T0, I0)),
                           (   call_cleanup(catch(Goal, E, (report_time(ID),throw(E))),
                                            Det = true),
                               time_true(ID),
                               (   Det == true -> !
                               ;   true
                               )
                           ;   report_time(ID),
                               false
                           ),
                           retract(time_state(ID, _, _))).

cputime_inferences(T, I) :-
        '$cpu_now'(T),
        '$inference_count'(I).

time_true(ID) :-
        report_time(ID).
time_true(ID)  :-
        % on backtracking, update the stored CPU time for this ID
        retract(time_state(ID, _, _)),
        cputime_inferences(T0, I0),
        asserta(time_state(ID, T0, I0)),
        false.

report_time(ID) :-
        time_state(ID, T0, I0),
        cputime_inferences(T, I),
        Time is T - T0,
        Inferences0 is I - I0,
        % we must subtract the number of inferences that time/1 itself takes;
        % this may have to be adapted if the implementation changes,
        % so that (for example) true/1 takes exactly 1 inference.
        (   bb_get('$answer_count', 0) ->
            Inferences is Inferences0 - 60,
            Pre = "   ", Post = ""
        ;   Inferences is Inferences0 - 9,
            Pre = "", Post = "   "
        ),
        phrase((Pre,"% CPU time: ", format_("~3f", [Time]), "s, ",
                format_("~U", [Inferences])," inference",s_if_necessary(Inferences),"\n",
                Post), Cs),
        format("~s", [Cs]).

s_if_necessary(Inferences) -->
        { compare(C, 1, Inferences) },
        s_(C).

s_(=) --> "".
s_(<) --> "s".
s_(>) --> " (exception?)".

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- time((true;false)).
   % CPU time: 0.000s, 1 inference
   true
;  % CPU time: 0.000s, 0 inference (exception?)
   false.

:- time(use_module(library(clpz))).
   % CPU time: 0.343s, 409_874 inferences
   true.

:- time(use_module(library(lists))).
   % CPU time: 0.000s, 19 inferences
   true.

?- time(member(X, "abc")).
   % CPU time: 0.000s, 1 inference
   X = a
;  % CPU time: 0.000s, 3 inferences
   X = b
;  % CPU time: 0.000s, 3 inferences
   X = c.

?- time((repeat,false)).
   % CPU time: 2.726s, 53_330_502 inferences
   error('$interrupt_thrown',repl/0).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
