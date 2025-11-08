% Helper predicates for testing custom toplevel functionality

success_toplevel :-
    write('SUCCESS_TOPLEVEL_EXECUTED'), nl,
    halt(0).

failure_toplevel :-
    write('FAILURE_TOPLEVEL_EXECUTED'), nl,
    halt(1).

exit_code_42 :-
    write('EXIT_CODE_42'), nl,
    halt(42).

write_and_exit :-
    write('Output from custom toplevel'), nl,
    halt(0).

% This one doesn't halt - to test what happens if toplevel doesn't halt
non_halting_toplevel :-
    write('NON_HALTING_TOPLEVEL'), nl.

% Test that toplevel can access loaded predicates
test_file_loaded :-
    write('LOADED_PREDICATE_CALLED'), nl,
    halt(0).

helper_predicate :-
    write('Helper predicate works'), nl.

% g_caused_exception/2 testing predicates
:- dynamic(g_caused_exception/2).

check_exception_halt_1 :-
    (   g_caused_exception(Goal, Exception) ->
        write('EXCEPTION_CAUGHT'), nl,
        write('Goal: '), write(Goal), nl,
        write('Exception: '), write(Exception), nl,
        halt(1)
    ;   write('NO_EXCEPTION'), nl,
        halt(0)
    ).

check_exception_halt_0 :-
    (   g_caused_exception(_, _) ->
        write('UNEXPECTED_EXCEPTION'), nl,
        halt(1)
    ;   write('SUCCESS_NO_EXCEPTION'), nl,
        halt(0)
    ).
