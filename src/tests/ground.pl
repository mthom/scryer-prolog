/**/

:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).
:- use_module(library(atts)).

:- attribute a/1.

a(Var) :- put_atts(Var, +a(hello)).

test("ground#239", (
    % double negate to avoid residual goal being printed
    \+ \+ (a(X), var(X), \+ ground(X))
)).

test("ground#1411",(
    G_0 = ( A=s(A) ), G_0,
    ground(A), ground(G_0)
)).

test("ground#2065",(
    A = [B|_C], B = [A], \+ ground(B), \+ground([B])
)).

test("ground#2073",(
    \+ ground(_-1+_-1),
    \+ ground(1-1-_)
)).

test("ground#2075",(
    G_0 = (_,_,ground(_)),
    G_0 = (D=[D|_],_=D*[],ground(D)),
    \+ G_0,
    _=_B*_,_D=_B*_A,_B=_B*_D,\+ ground(_B),
    A=[A|B],B=A*B,ground(A)
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

portray_failed_([]) --> [].
portray_failed_([F|Fs]) -->
    "\"", F, "\"",  "\n", portray_failed_(Fs).

portray_failed([]) --> [].
portray_failed([F|Fs]) -->
    "\n", "Failed tests:", "\n", portray_failed_([F|Fs]).

show_failed(Failed) :-
    phrase(portray_failed(Failed), F),
    format("~s", [F]).
