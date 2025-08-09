:- module(reif_tests, []).

:- use_module(library(reif)).
:- use_module(library(lists)).
:- use_module(library(dif)).
:- use_module(library(lambda)).
:- use_module(library(random)).
:- use_module(test_framework).

/*
Those tests are just sanity checks – examples from the paper, to make sure I
haven't messed up.
*/
test("indexing dif/2 p6#1", (
    findall(X-Fs, tfilter(=(X),[1,2,3,2,3,3],Fs), [1-[1], 2-[2,2], 3-[3,3,3], Y-[]]),
    maplist(dif(Y), [1,2,3])
)).
test("indexing dif/2 p6#2", findall(X, duplicate(X,[1,2,3,2,3,3]), [2,3])).
test("indexing dif/2 p7#1", firstduplicate(1, [1,2,3,1])).
test("indexing dif/2 p7#2",(
    firstduplicate(X, [1,2,3,1]),
    X == 1
)).
test("indexing dif/2 p7#3", (
    findall(Y-A-B-C, firstduplicate(Y,[A,B,C]), [X-X-X-_, X-X-B1-X, X-A2-X-X]),
    dif(B1,X),
    dif(A2,X)
)).

test("doesnt modify free variables", (reif:goal_expanded(A,B), A == B, var(A))).
test("expands call/1", reif:goal_expanded(call(a), a)).
test("expands call/1 for modules", reif:goal_expanded(call(a:b(1)), a:b(1))).
test("expands call/2 for modules", reif:goal_expanded(call(a:b,c), a:b(c))).
test("doesn't expand call/2", reif:goal_expanded(call(b,c), call(b,c))).
test("doesn't expand cyclic terms", (
    X=a(X),
    reif:goal_expanded(call(X), Y),
    call(X) == Y
)).
test("doesn't expand cyclic call/1", (
    X=call(X),
    reif:goal_expanded(X, Y),
    X == Y
)).
test("doesn't expand higher order predicates", (
    X = maplist(=(1), _),
    reif:goal_expanded(X, Y),
    X == Y
)).

/*
Following tests capture current results of goal expansion
TODO: Investigate if if_/3 can be further expanded, and if it will be beneficial
*/
test("goal_expansion (=)", (
    subsumes_full_expansion(if_(1=2,a,b), (
        1 \= 2 -> b
    ;   1 == 2 -> a
    ;   1 = 2, a
    ;   dif(1,2), b)))).

test("goal_expansion (;)", (
    subsumes_full_expansion(if_((1=2;3=3),a,b), (
        1 \= 2 -> if_(3=3,a,b)
    ;   1 == 2 -> a
    ;   1 = 2, a
    ;   dif(1,2), if_(3=3,a,b))))).

test("goal_expansion (,)", (
    subsumes_full_expansion(if_((1=2,3=3),a,b), (
        1 \= 2 -> b
    ;   1 == 2 -> if_(3=3,a,b)
    ;   1 = 2, if_(3=3,a,b)
    ;   dif(1,2), b)))).

test("goal_expansion memberd_t", (
    subsumes_full_expansion(if_(memberd_t(f,"abcdefgh"),t,f), (
        call(memberd_t(f,"abcdefgh"),A),
        (   A == true  -> t
        ;   A == false -> f
        ;   nonvar(A)  -> throw(error(type_error(boolean,A),_))
        ;   throw(error(instantiation_error,_))))))).

test("goal_expansion cond_t", (
    subsumes_full_expansion(if_(cond_t(a,b),t,f), (
        call(cond_t(a,b),A),
        (   A == true  -> t
        ;   A == false -> f
        ;   nonvar(A)  -> throw(error(type_error(boolean,A),_))
        ;   throw(error(instantiation_error,_))))))).

test("set of solutions found by tpartition/4 and tfilter/3 is the same and correct", (
    random_test_vector(TestVector),
    findall((N,Ts), tpartition(=(N),TestVector,Ts,_), S),
    findall((N,Ts), tfilter(=(N),TestVector,Ts), S),
    maplist(_+\(N,Ts)^maplist(=(N),Ts), S)
)).

test("cut in one of the branches does not influence condition", (
    findall(X-Y, if_(X=1,!,Y=a), Solutions),
    Expected = [1-Y1,X2-a],
    subsumes_term(Expected, Solutions),
    Solutions = Expected,
    var(Y1),
    var(X2), dif(X2, 1)
)).

test("non-callable branch throws meaningful error", (
    findall(R, result_or_exception(if_(_=1, _=a, 2), R), Solutions),
    Solutions == [if_(1=1,a=a,2), error(type_error(callable,2),call/1)]
)).

test(W, loader:call(T)) :-
    member(T, [
        cuts_outside(!),
        cuts_outside(foo:!),
        cuts_outside((a,!)),
        cuts_outside((!;b(_))),
        cuts_outside(((a;b(_,_);c),!,d)),
        \+ cuts_outside(call((a,!))),
        \+ cuts_outside(((a;b;c),\+ !,d)),
        \+ cuts_outside((! -> a; b)),
        \+ cuts_outside(((x,!;y) -> a; b)),
        catch((cuts_outside(_),false),   E0, E0  = stop(type_error(callable,_))),
        catch((cuts_outside(2),false),   E1, E1 == stop(type_error(callable,2))),
        catch((cuts_outside(1:!),false), E2, E2 == stop(type_error(atom,1))),
        catch((cuts_outside(_:!),false), E3, E3  = stop(type_error(atom,_))),
        (G0 = a(G0), catch((cuts_outside(G0),false), E4, E4 = stop(type_error(acyclic_term,_)))),
        (G1 = m:G1,  catch((cuts_outside(G1),false), E5, E5 = stop(type_error(acyclic_term,_)))),
        catch((cuts_outside((6->a)),false),   E6, E6 == stop(type_error(callable,6))),
        (goal_sanitized(a, X0), X0 == a),
        (goal_sanitized(!, X1), X1 == call(!)),
        (goal_sanitized((a,b;c,d), X2), X2 == (a,b;c,d)),
        (goal_sanitized((\+ \+ a), X3), X3 == (\+ \+ a)),
        % Questionable test case, see #2739
        (goal_sanitized((!,a->c;d), X4), X4 == (!,a->c;d)),
        (goal_sanitized((x,a->!;d), X5), X5 == call((x,a->!;d))),
        (goal_sanitized((a,b,c,!), X6), X6 == call((a,b,c,!))),
        \+ goal_sanitized(0, _),
        \+ goal_sanitized(_, _),
        \+ goal_sanitized((a,_), _),
        \+ goal_sanitized((a,b;1), _)
    ]),
    phrase(format_("callable cut: ~q", [T]), W).

result_or_exception(Goal, Result) :-
    catch((Goal,Result=Goal), Result, true).

random_test_vector(TestVector) :-
    random_integer(0, 1000, Length),
    length(TestVector, Length),
    maplist(random_integer(1,5), TestVector).

% Expand goal until fix point is found
full_expansion(G, X) :-
    user:goal_expansion(G, Gx) -> full_expansion(Gx, X); G = X.

% X is more general than fully expanded goal G
subsumes_full_expansion(G, X) :-
    full_expansion(G, Y),
    subsumes_term(X, Y).

/*
Extra predicates from the paper
*/
duplicate(X, Xs) :-
    tfilter(=(X), Xs, [_,_|_]).

firstduplicate(X, [E|Es]) :-
    if_(memberd_t(E,Es), X=E, firstduplicate(X, Es)).

treememberd_t(_, nil, false).
treememberd_t(E, t(F,L,R), T) :-
    call((E=F; treememberd_t(E,L); treememberd_t(E,R)), T).

tree_non_member(_, nill).
tree_non_member(E, t(F,L,R)) :-
    dif(E,F),
    tree_non_member(E, L),
    tree_non_member(E, R).
