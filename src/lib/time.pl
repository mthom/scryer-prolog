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
:- dynamic(time_state/2).

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
        '$cpu_now'(T0),
        time_next_id(ID),
        setup_call_cleanup(asserta(time_state(ID, T0)),
                           (   call_cleanup(catch(call_with_unlimited_inference_limit(Goal, Inf, Result),
                                                  E,
                                                  (report_time(ID, Inf),throw(E))),
                                            Det = true),
                               time_true(ID, Inf),
                               (   Det == true -> !
                               ;   true
                               )
                           ;   report_time(ID, Inf),
                               false
                           ),
                           retract(time_state(ID, _))
                          ),
        call(Result).

time_true(ID, Inf) :-
        report_time(ID, Inf).
time_true(ID, _)  :-
        % on backtracking, update the stored CPU time for this ID
        retract(time_state(ID, _)),
        '$cpu_now'(T0),
        asserta(time_state(ID, T0)),
        false.

report_time(ID, Inf) :-
        time_state(ID, T0),
        '$cpu_now'(T),
        Time is T - T0,
        (   var(Inf) ->
            Infs = ""
        ;   (   Inf =:= 1 -> Infs = ", 1 inference"
            ;   phrase(format_(", ~U inferences", [Inf]), Infs)
            )
        ),
        (   bb_get('$answer_count', 0) ->
            Pre = "   ", Post = ""
        ;   Pre = "", Post = "   "
        ),
        format("~s% ~3fs CPU~s~n~s", [Pre,Time,Infs,Post]).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   The following is from library(iso_ext), slightly adapted so that we
   can report the number of inferences. A better abstraction may be
   able to share more inferences-related logic between time/1 and
   call_with_inference_limit/3.

   call_with_unlimited_inference_limit/3 is introduced with new system
   predicates '$install_unlimited_inference_counter'/1 and '$inference_count'/1.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- meta_predicate(call_with_unlimited_inference_limit(0,?,?)).

:- non_counted_backtracking call_with_unlimited_inference_limit/3.

call_with_unlimited_inference_limit(G, Inf, Result) :-
    '$install_unlimited_inference_counter'(Count),
    '$get_current_block'(Bb),
    '$get_b_value'(B),
    call_with_unlimited_inference_limit(G, Bb, B, Count, Inf, Result),
    '$remove_call_policy_check'(B).

:- non_counted_backtracking call_with_unlimited_inference_limit/6.

call_with_unlimited_inference_limit(G, Bb, _B, Count0, Inf, true) :-
    '$install_new_block'(NBb),
    '$call_with_inference_counting'(call(G)),
    '$remove_inference_counter'(NBb, Count1),
    Inf is Count1 - Count0,
    (  '$clean_up_block'(NBb),
       '$reset_block'(Bb)
    ;  '$install_unlimited_inference_counter'(_),
       '$reset_block'(NBb),
       '$fail'
    ).
call_with_unlimited_inference_limit(_, Bb, B, Count0, Inf, false) :-
    '$get_current_block'(NBb),
    '$remove_inference_counter'(NBb, Count1),
    '$reset_block'(Bb),
    '$remove_call_policy_check'(B),
    (  '$get_ball'(_),
       '$push_ball_stack',
       '$get_cp'(Cp),
       '$set_cp_by_default'(Cp),
       '$pop_from_ball_stack',
       '$unwind_stack'
    ;  Inf is Count1 - Count0
    ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- time((true;false)).
%@    % 0.000s CPU, 2 inferences
%@    true
%@ ;  % 0.000s CPU
%@    false.

:- time(use_module(library(clpz))).
%@    % 0.322s CPU, 406_433 inferences
%@    true.

:- time(use_module(library(lists))).
%@    % 0.000s CPU, 20 inferences
%@    true.

?- time(member(X, "abc")).
%@    % 0.000s CPU, 2 inferences
%@    X = a
%@ ;  % 0.000s CPU, 4 inferences
%@    X = b
%@ ;  % 0.000s CPU, 6 inferences
%@    X = c.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
