/**/

:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).
:- use_module(library(atts)).

:- use_module(library(when)).

test("condition true before ground/1",(
    A = 1,
    when(ground(A), Run = true),
    Run == true
)).

test("condition true before nonvar/1",(
    A = a(_),
    when(nonvar(A), Run = true),
    Run == true
)).

test("condition true before ','/2",(
    A = 1,
    B = a(_),
    when((ground(A), nonvar(B)), Run = true),
    Run == true
)).

test("condition true before (;)/2",(
    A = 1,
    when((ground(A) ; nonvar(_)), Run1 = true),
    Run1 == true,

    B = a(_),
    when((ground(_) ; nonvar(B)), Run2 = true),
    Run2 == true
)).

test("condition true after ground/1",(
    when(ground(A), Run = true),
    var(Run),
    A = 1,
    Run == true
)).

test("condition true after nonvar/1",(
    when(nonvar(A), Run = true),
    var(Run),
    A = a(_),
    Run == true
)).

test("condition true after ','/2",(
    when((ground(A), nonvar(B)), Run = true),
    var(Run),
    A = 1,
    var(Run),
    B = a(_),
    Run == true
)).

test("condition true after (;)/2",(
    when((ground(A) ; nonvar(_)), Run1 = true),
    var(Run1),
    A = 1,
    Run1 == true,

    when((ground(_) ; nonvar(B)), Run2 = true),
    var(Run2),
    B = a(_),
    Run2 == true
)).

test("multiple when/2 on same variable",(
    when(nonvar(A), Run1 = true),
    when(ground(A), Run2 = true),
    var(Run1), var(Run2),
    A = a(B),
    Run1 == true, var(Run2),
    B = 1,
    Run2 == true
)).

main :-
    findall(test(Name, Goal), test(Name, Goal), Tests),
    run_tests(Tests, Failed),
    show_failed(Failed),
    halt.

main_quiet :-
    findall(test(Name, Goal), test(Name, Goal), Tests),
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

assert_p(A, B) :-
    phrase(portray_clause_(A), Portrayed),
    phrase((B, ".\n"), Portrayed).

call_residual_goals(Goal, ResidualGoals) :-
    call_residue_vars(Goal, Vars),
    variables_residual_goals(Vars, ResidualGoals).

variables_residual_goals(Vars, Goals) :-
    phrase(variables_residual_goals(Vars), Goals).

variables_residual_goals([]) --> [].
variables_residual_goals([Var|Vars]) -->
    dif_:attribute_goals(Var),
    variables_residual_goals(Vars).

