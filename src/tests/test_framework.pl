:- module(test_framework, [main/1, main_quiet/1]).

:- use_module(library(dcgs)).
:- use_module(library(format)).

main(TestModule) :-
    findall(test(Name, TestModule:Goal), TestModule:test(Name, Goal), Tests),
    run_tests(Tests, Failed),
    show_failed(Failed),
    halt.

main_quiet(TestModule) :-
    findall(test(Name, TestModule:Goal), TestModule:test(Name, Goal), Tests),
    run_tests_quiet(Tests, Failed),
    (   Failed = [] ->
        format("All tests passed", [])
    ;   format("Some tests failed", [])
    ),
    halt.

portray_failed_([]) --> [].
portray_failed_([F|Fs]) -->
    "\"", F, "\"",  "\n", portray_failed_(Fs).

portray_failed([]) --> [].
portray_failed([F|Fs]) -->
    "\n", "Failed tests:", "\n", portray_failed_([F|Fs]).

show_failed(Failed) :-
    phrase(portray_failed(Failed), F),
    format("~s", [F]).

run_tests([], []).
run_tests([test(Name, Goal)|Tests], Failed) :-
    format("Running test \"~s\"~n", [Name]),
    (   call(Goal) ->
        Failed = Failed1
    ;   format("Failed test \"~s\"~n", [Name]),
        Failed = [Name|Failed1]
    ),
    run_tests(Tests, Failed1).

run_tests_quiet([], []).
run_tests_quiet([test(Name, Goal)|Tests], Failed) :-
    (   call(Goal) ->
        Failed = Failed1
    ;   Failed = [Name|Failed1]
    ),
    run_tests_quiet(Tests, Failed1).
