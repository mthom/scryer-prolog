/**/

:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).

test("term_variables#1400", (
    term_variables(A+B*C/B-D, Vars),
    term_variables(t(A,B,C,D), Vars),
    Vars = [A,B,C,D]
)).

test("term_variables#1405", (
    \+ (B=[C|D],C=[_|D],C=[B|B], term_variables(B,_), false)
)).

test("term_variables#1409", (
    G_0 = (A=[B|B],A=[C|C]), G_0, term_variables(G_0, Vars), Vars = [B]
)).

test("term_variables#1410", (
    \+ \+ (G_0 = ( A=s(A) ), G_0, term_variables(G_0, Vars), Vars = []),
    E_0 = (_=[B|B]), G_0 = (E_0,\_=B), G_0, term_variables(G_0, Vars)
)).

test("term_variables#1412", (
    G_0 = =([A|B],[A|B]), G_0, term_variables(G_0, Vars),
    Vars = [A,B]
)).

test("term_variables#1414", (
    \+ (\B=A,C=[A|D],B=[a,b|E],C=[D|E], term_variables(\E,_), false)
)).

test("term_variables#2063", (
    A=[B|C], B=[A], term_variables([B], Vars),
    Vars = [C]
)).

test("term_variables#2097", (
    termt(T), term_variables(T,Vs),
    T = [[[A|B]|A]|A], Vs == [A,B]
)).

test("term_variables#2100", (
    termt2(T), term_variables(T,Vs),
    T = [[T|A]|B], Vs == [A,B]
)).

test("term_variables#2101", (
    termt3(T), term_variables(T,Vs),
    T = [[[[A|B]|A]|A]|A], Vs == [A, B]
)).

termt(T) :-
   T = [T1|T2],
   T1 = [T3|A],
   T3 = [A|_],
   T2 = A.

termt2(T) :-
   T = [T1|_B],
   T1 = [T|_A].

termt3(T) :-
   T = [T1|T0],
   T1 = [T2|T3],
   T2 = [T4|A],
   T4 = [A|_],
   T3 = A,
   T0 = A.

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
