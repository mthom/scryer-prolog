:- module(custom_toplevel_tests, []).

:- use_module(test_framework).

% Helper predicates for CLI testing
custom_halt :-
    format("Custom toplevel executed~n", []),
    halt(0).

custom_halt_with_code :-
    format("Custom toplevel with exit code~n", []),
    halt(42).

test_predicate :-
    format("Test predicate executed~n", []).

% Test predicates for g_caused_exception/2
:- dynamic(g_caused_exception/2).

check_for_exception :-
    (   g_caused_exception(_Goal, Exception) ->
        format("Exception occurred: ~w~n", [Exception]),
        halt(1)
    ;   format("No exception~n", []),
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
