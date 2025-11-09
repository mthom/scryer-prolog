% Helper predicates for testing custom toplevel functionality

success_toplevel :-
    format("SUCCESS_TOPLEVEL_EXECUTED~n", []),
    halt(0).

failure_toplevel :-
    format("FAILURE_TOPLEVEL_EXECUTED~n", []),
    halt(1).

exit_code_42 :-
    format("EXIT_CODE_42~n", []),
    halt(42).

write_and_exit :-
    format("Output from custom toplevel~n", []),
    halt(0).

% This one doesn't halt - to test what happens if toplevel doesn't halt
non_halting_toplevel :-
    format("NON_HALTING_TOPLEVEL~n", []).

% Test that toplevel can access loaded predicates
test_file_loaded :-
    format("LOADED_PREDICATE_CALLED~n", []),
    halt(0).

helper_predicate :-
    format("Helper predicate works~n", []).

% g_caused_exception/2 testing predicates
:- dynamic(g_caused_exception/2).

check_exception_halt_1 :-
    (   g_caused_exception(Goal, Exception) ->
        format("EXCEPTION_CAUGHT~n", []),
        format("Goal: ~w~n", [Goal]),
        format("Exception: ~w~n", [Exception]),
        halt(1)
    ;   format("NO_EXCEPTION~n", []),
        halt(0)
    ).

check_exception_halt_0 :-
    (   g_caused_exception(_, _) ->
        format("UNEXPECTED_EXCEPTION~n", []),
        halt(1)
    ;   format("SUCCESS_NO_EXCEPTION~n", []),
        halt(0)
    ).
