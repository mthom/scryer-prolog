/**/

:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).
:- use_module(library(atts)).
:- use_module(library(dif)).

% Tests from https://www.complang.tuwien.ac.at/ulrich/iso-prolog/dif

test("dif#1",(
    call_residual_goals(dif(1,2), Res),
    Res = []
)).

test("dif#2",(
    \+ (dif(1,Y), Y = 1)
)).

test("dif#3",(
    call_residual_goals((dif(1,Y), Y=2), Res),
    Y == 2,
    Res = []
)).

test("dif#4",(
    \+ (dif(X,-Y), X= -Y)
)).

test("dif#5",(
    \+ (dif(X,Y), X=Y)
)).

test("dif#6",(
    \+ (dif(X,Y), X=Y, X=1)
)).

test("dif#7",(
    \+ (dif(-X,-Y), X=Y)
)).

test("dif#8",(
    \+ (dif(-X,-Y), X=Y, X=1)
)).

% I don't understand exactly what is expected for dif#9 and dif#10

test("dif#11",(
    call_residual_goals((X=Y, dif(X-Y,1-2)), Res),
    X == Y,
    Res = []
)).

test("dif#12",(
    call_residual_goals((dif(X-Y,1-2), X=Y), Res),
    X == Y,
    Res = []
)).

test("dif#13",(
    call_residual_goals((X=Y, Y=1, dif(X-Y,1-2)), Res),
    X == 1,
    Y == 1,
    Res = []
)).

test("dif#14",(
    call_residual_goals((dif(X-Y,1-2), X=Y, Y=1), Res),
    X == 1,
    Y == 1,
    Res = []
)).

test("dif#15",(
    call_residual_goals((dif(X-Y,1-2), X=Y, X=2), Res),
    X == 2,
    Y == 2,
    Res = []
)).

test("dif#16",(
    call_residual_goals((dif(A-C,B-D), C-D=z-z, A-B=1-2), Res),
    A == 1,
    B == 2,
    C == z,
    D == z,
    Res = []
)).

test("dif#17",(
    call_residual_goals((A-B=1-2, C-D=z-z, dif(A-C,B-D)), Res),
    A == 1,
    B == 2,
    C == z,
    D == z,
    Res = []
)).

test("dif#18",(
    call_residual_goals((dif(A,[C|B]), A=[[]|_], A=[B]), Res),
    A == [[]],
    B == [],
    Res = [dif:dif([[]], [C])]
)).

test("dif#19",(
    call_residual_goals((dif([E],[/]), E=1), Res),
    E == 1,
    Res = []
)).

test("dif#20",(
    call_residual_goals((dif([a],B), B=[_|_], B=[b]), Res),
    B == [b],
    Res = []
)).

test("dif#21",(
    call_residual_goals((dif([],A), A = [_]), Res),
    A = [_],
    Res = []
)).

test("dif#22",(
    call_residual_goals((A = [_], dif([],A)), Res),
    A = [_],
    Res = []
)).

test("dif#t1",(
    set_prolog_flag(occurs_check, false),
    \+ \+ -X=X
)).

test("dif#t2",(
    set_prolog_flag(occurs_check, false),
    \+ (-X=X, -Y=Y, X\=Y)
)).

test("dif#t3",(
    set_prolog_flag(occurs_check, false),
    call_residual_goals((-X=X, dif(X,1)), Res),
    X == -X,
    Res = []
)).

test("dif#t4",(
    set_prolog_flag(occurs_check, false),
    \+ (-X=X, -Y=Y, dif(X,Y))
)).

test("dif#t5",(
    set_prolog_flag(occurs_check, false),
    \+ (dif(X,Y), -X=X, -Y=Y)
)).

test("dif#t6",(
    set_prolog_flag(occurs_check, false),
    \+ (A=[[]|A],dif(A,B),B=[[]|A])
)).

test("dif#t7",(
    set_prolog_flag(occurs_check, false),
    \+ (dif(-X,X),-Y=Y,X=Y)
)).

test("dif#o1",(
    set_prolog_flag(occurs_check, true),
    \+ (-X = X)
)).

test("dif#o2",(
    set_prolog_flag(occurs_check, true),
    call_residual_goals((dif(-X,X)), Res),
    Res = []
)).

test("dif#o3",(
    set_prolog_flag(occurs_check, true),
    call_residual_goals((dif(-X,Y), X=Y), Res),
    X == Y,
    Res = []
)).

test("dif#12 but with multiple variables in the residuals",(
    call_residual_goals((dif(X-Y-_, 1-2-3), X = Y), Res),
    X == Y,
    Res = []
)).

main :-
    findall(test(Name, Goal), test(Name, Goal), Tests),
    run_tests(Tests, Failed),
    show_failed(Failed),
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
    dif:attribute_goals(Var),
    variables_residual_goals(Vars).

