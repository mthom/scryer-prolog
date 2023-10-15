:- use_module(library(format)).

term1(A) :-
   B=[C|D],
   A=[D|C],
   B=[C|B].

term2(A) :-
   A=[B|C],
   D=[C|C],
   D=[B|D].

term3(A) :-
   A=[_B|C],
   D=[C|_E],
   A=[C|D].

term4(A) :-
   A=[B|C],
   C=[C|B].

term5(A) :-
   A=[_B|C],
   D=[_E|C],
   A=[C|D].

test("acyclic_term_1", (
    L = [_Y,[M,B],B|M], acyclic_term(L)
)).

test("acyclic_term_2", (
    L = [_Y,[M,_B,L]|M], \+ acyclic_term(L)
)).

test("acyclic_term_3", (
    L = [_Y,[M,B,L,B]|M], \+ acyclic_term(L)
)).

test("acyclic_term_4", (
    L = [_Y,[L,_A,_B]|_M], \+ acyclic_term(L)
)).

test("acyclic_term_5", (
    L = [_Y,[M,_A,_B]|M], acyclic_term(L)
)).

test("acyclic_term_6", (
    L = [_Y,[L,_A,_B]|_M], \+ acyclic_term(L)
)).

test("acyclic_term_7", (
    L = [A], A = [T], T = [_|X], X = Y, Y = L, \+ acyclic_term(T)
)).

test("acyclic_term_8", (
    L = [A], A = [T], T = [_|X], X = Y, Y = L, \+ acyclic_term(L)
)).

test("acyclic_term_9", (
    L = [A], A = [T], T = [_|X], X = Y, Y = L, \+ acyclic_term(A)
)).

test("acyclic_term_10", (
    L = [A], A = [T], T = [_|X], X = Y, Y = L, \+ acyclic_term(Y)
)).

test("acyclic_term_11", (
    L = [A], A = [T], T = [_|X], X = Y, Y = L, \+ acyclic_term(X)
)).

test("acyclic_term_12", (
    A = [1|2], X = A, T=a(X, A), acyclic_term(T)
)).

test("acyclic_term_13", (
    A = [A|2], X = A, T=a(X, A), \+ acyclic_term(T)
)).

test("acyclic_term_13", (
    A = [T|2], X = A, T=a(X, A), \+ acyclic_term(T)
)).

test("acyclic_term_14", (
    T = [_A|T], \+ acyclic_term(T)
)).

test("acyclic_term_15", (
    T = [T|_L], \+ acyclic_term(T)
)).

test("acyclic_term_16", (
    A = [1|A], X = A, T=a(X, A), \+ acyclic_term(T)
)).

test("acyclic_term_17", (
    T = [_A| [[[[L|T]|[]]]]], acyclic_term(L)
)).

test("acyclic_term_18", (
    T = [A| [[[[_L|T]|[]]]]], acyclic_term(A)
)).

test("acyclic_term_19", (
    T = [_A| [[[[_L|T]|[]]]]], \+ acyclic_term(T)
)).

test("acyclic_term_20", (
    A = [_C|_B], X = A, T=a(t(X,A), A), acyclic_term(T)
)).

test("acyclic_term_21", (
    X = [a | Rest], Rest = [_Y | Rest], \+ acyclic_term(X)
)).

test("acyclic_term_22", (
    _X = [a | Rest], Rest = [_Y | Rest], \+ acyclic_term(Rest)
)).

test("acyclic_term_23", (
    T = [[_A, T]], G = [1|T], \+ acyclic_term(G)
)).

test("acyclic_term_24", (
    T = [[_A, T]], \+ acyclic_term(T)
)).

test("acyclic_term_25", (
    T = [[_, _], T], \+ acyclic_term(T)
)).

test("acyclic_term_26", (
    T = [[T, _], 1], \+ acyclic_term(T)
)).

test("acyclic_term_27", (
    T = str(A,A), acyclic_term(T)
)).

test("acyclic_term_28", (
    T = str(A,A,A), acyclic_term(T)
)).

test("acyclic_term_29", (
    A = s(B, d(Y)), Y = B, acyclic_term(A),
    acyclic_term(B), acyclic_term(Y)
)).

test("acyclic_term#2111_1", (
    term1(A), \+ acyclic_term(A)
)).

test("acyclic_term#2111_2", (
    term2(A), \+ acyclic_term(A)
)).

test("acyclic_term#2111_3", (
    term3(A), \+ acyclic_term(A)
)).

test("acyclic_term#2111_4", (
    term4(A), \+ acyclic_term(A)
)).

test("acyclic_term#2111_5", (
    term5(A), \+ acyclic_term(A)
)).

test("acyclic_term#2113", (
    A=[]*B,B=[]*B, \+ acyclic_term(A)
)).

test("acyclic_term#2114", (
    A=B*B, acyclic_term(A)
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
