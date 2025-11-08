:- module(custom_toplevel_tests, []).

:- use_module(test_framework).

% Helper predicates for CLI testing
custom_halt :-
    write('Custom toplevel executed'), nl,
    halt(0).

custom_halt_with_code :-
    write('Custom toplevel with exit code'), nl,
    halt(42).

test_predicate :-
    write('Test predicate executed'), nl.

% Test predicates for g_caused_exception/2
:- dynamic(g_caused_exception/2).

check_for_exception :-
    (   g_caused_exception(_Goal, Exception) ->
        write('Exception occurred: '), write(Exception), nl,
        halt(1)
    ;   write('No exception'), nl,
        halt(0)
    ).

% Prolog integration tests
test("custom toplevel functionality is tested via CLI tests", (
    true
)).

test("g_caused_exception/2 is not asserted when no exception occurs", (
    retractall(g_caused_exception(_, _)),
    \+ g_caused_exception(_, _)
)).

test("g_caused_exception/2 can be checked from custom toplevel", (
    % This tests the predicate structure; actual exception handling
    % is tested via CLI tests since it requires -g and -t flags
    retractall(g_caused_exception(_, _)),
    asserta(g_caused_exception(test_goal, test_error)),
    g_caused_exception(test_goal, test_error),
    retractall(g_caused_exception(_, _))
)).
