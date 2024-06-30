/** Predicates from [*Indexing dif/2*](https://arxiv.org/abs/1607.01590).

Example:

```
?- tfilter(=(a), [X,Y], Es).
   X = a, Y = a, Es = "aa"
;  X = a, Es = "a", dif:dif(a,Y)
;  Y = a, Es = "a", dif:dif(a,X)
;  Es = [], dif:dif(a,X), dif:dif(a,Y).
```
*/

:- module(reif, [if_/3, (=)/3, (',')/3, (;)/3, cond_t/3, dif/3,
		         memberd_t/3, tfilter/3, tmember/2, tmember_t/3,
		         tpartition/4]).

:- use_module(library(dif)).

% TODO: Remove when fully debugged
:- use_module(library(debug)).
:- use_module(library(format)).
:- op(750, xfy, =>).
:- op(950, fy, +).
+(A) :- call(A).
%+(_).

goal_expanded(MG_0, MGx_0) :-
   var(MG_0),
   !,
   MG_0 = MGx_0.
goal_expanded(call(MG_1, X), MGx_0) :-
   MG_1 = M:G_1, atom(M), callable(G_1), G_1 \= (_:_),
   functor_(G_1, G_0, X),
   \+ predicate_property(M:G_0, (meta_predicate _)),
   !,
   MGx_0 = M:G_0.
goal_expanded(call(G_0), Gx_0) :-
   acyclic_term(G_0),
   nonvar(G_0),
   % more conditions
   !,
   G_0 = Gx_0.
goal_expanded(MG_0, MG_0).


%% functor_(+T, ?TA, ?A).
%
% `TA` is `T` extended with additional parameter `A`
%
% ```
% ?- functor_(a(b), X, c).
%    X = a(b,c).
% ```
functor_(T, TA, A) :-
   functor(T, F, N0),
   N1 is N0+1,
   functor(TA, F, N1),
   arg(N1, TA, A),
   sameargs(N0, T, TA).

sameargs(N0, S, T) :-
   N0 > 0,
   N1 is N0-1,
   arg(N0, S, A),
   arg(N0, T, A),
   sameargs(N1, S, T).
sameargs(0, _, _).


/* FIXME: What does this ↓ comment from the source mean? Is it a list of features, "to do" items or guidelines? */
/*
  no !s that cut outside.
  no variables in place of goals
  no malformed goals like integers
*/


/* FIXME: How can I reproduce this? ↓ */
/* 2do: unqualified If_1: error
*/


user:goal_expansion(if_(If_1, Then_0, Else_0), G_0) :-
    ugoal_expansion(if_(If_1, Then_0, Else_0), G_0),
    % Dump expanded goals to the console for inspection.
    % TODO: Remove when fully debugged
  + portray_clause((if_(If_1,Then_0,Else_0) => G_0)).


%% ugoal_expansion(if_(+If_1, ?Then_0, ?Else_0), -Goal_0).
%
% Performance of if_/3 heavily relies on call/N, this predicates tries to unwrap
% some terms for improved speed.
%
% Expansion rules:
%
% if_(A=B,Then_0,Else_0)
% => if equality of A and B is satisfiable then expanded `Then_0`, otherwise
%    expanded `Else_0`.
%
% if_((A_1;B_1), Then_0, Else_0)
% => if_(A_1, Then_0, if_(B_1, Then_0, Else_0))
%
% if_((A_1,B_1), Then_0, Else_0)
% => if_(A_1, if_(B_1, Then_0, Else_0), Else_0).
%
% Otherwise it simply expands If_1, Then_0 and Else_0 using goal_expanded/2.
% Read it's documentation to find out how it operates.
%
% TODO: Remove code duplication
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
    nonvar(If_1), If_1 = (X = Y),
    goal_expanded(call(Then_0), Thenx_0),
    goal_expanded(call(Else_0), Elsex_0),
    !,
  + write('% =\n'),
    Goal_0 =
        ( X \= Y -> Elsex_0
        ; X == Y -> Thenx_0
        ; X = Y,    Thenx_0
        ; dif(X,Y), Ellsex_0
        ).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal) :-
   nonvar(If_1), If_1 = dif(X, Y),
   goal_expanded(call(Then_0), Thenx_0),
   goal_expanded(call(Else_0), Elsex_0),
   !,
 + write('% ≠\n'),
   Goal =
      ( X \= Y -> Thenx_0
      ; X == Y -> Elsex_0
      ; X = Y,    Elsex_0
      ; dif(X,Y), Thenx_0
      ).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal) :-
    subsumes_term((A_1;B_1), If_1),
    (A_1;B_1) = If_1,
    !,
  + write('% ;\n'),
    Goal = if_(A_1, Then_0, if_(B_1, Then_0, Else_0)).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
    subsumes_term((A_1,B_1), If_1),
    (A_1,B_1) = If_1,
    !,
  + write('% ,\n'),
    Goal_0 = if_(A_1, if_(B_1, Then_0, Else_0), Else_0).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
  + write('% _\n'),
    goal_expanded(call(If_1, T), Ifx_0),
    goal_expanded(call(Then_0), Thenx_0),
    goal_expanded(call(Else_0), Elsex_0),
    Goal_0 =
        (   Ifx_0,
            (  T == true -> Thenx_0
            ;  T == false -> Elsex_0
            ;  nonvar(T) -> throw(error(type_error(boolean,T),_))
            ;  throw(error(instantiation_error,_))
            )
        ).

:- meta_predicate(if_(1, 0, 0)).

if_(If_1, Then_0, Else_0) :-
    call(If_1, T),
    (  T == true  -> call(Then_0)
    ;  T == false -> call(Else_0)
    ;  nonvar(T) -> throw(error(type_error(boolean, T), _))
    ;  throw(error(instantiation_error, _))
    ).

=(X, Y, T) :-
    (  X == Y -> T = true
    ;  X \= Y -> T = false
    ;  T = true, X = Y
    ;  T = false, dif(X, Y)
    ).

dif(X, Y, T) :-
  =(X, Y, NT),
  non(NT, T).

non(true, false).
non(false, true).

:- meta_predicate(tfilter(2, ?, ?)).

tfilter(_, [], []).
tfilter(C_2, [E|Es], Fs0) :-
   if_(call(C_2, E), Fs0 = [E|Fs], Fs0 = Fs),
   tfilter(C_2, Es, Fs).

:- meta_predicate(tpartition(2, ?, ?, ?)).

tpartition(P_2, Xs, Ts, Fs) :-
   i_tpartition(Xs, P_2, Ts, Fs).

i_tpartition([], _P_2, [], []).
i_tpartition([X|Xs], P_2, Ts0, Fs0) :-
   if_( call(P_2, X)
      , ( Ts0 = [X|Ts], Fs0 = Fs )
      , ( Fs0 = [X|Fs], Ts0 = Ts ) ),
   i_tpartition(Xs, P_2, Ts, Fs).

:- meta_predicate(','(1, 1, ?)).

','(A_1, B_1, T) :-
    if_(A_1, call(B_1, T), T = false).

:- meta_predicate(';'(1, 1, ?)).

';'(A_1, B_1, T) :-
    if_(A_1, T = true, call(B_1, T)).

:- meta_predicate(cond_t(1, 0, ?)).

cond_t(If_1, Then_0, T) :-
   if_(If_1, ( Then_0, T = true ), T = false ).

memberd_t(E, Xs, T) :-
   i_memberd_t(Xs, E, T).

i_memberd_t([], _, false).
i_memberd_t([X|Xs], E, T) :-
   if_( X = E, T = true, i_memberd_t(Xs, E, T) ).

:- meta_predicate(tmember(2, ?)).

tmember(P_2, [X|Xs]) :-
   if_( call(P_2, X), true, tmember(P_2, Xs) ).

:- meta_predicate(tmember_t(2, ?, ?)).

tmember_t(_P_2, [], false).
tmember_t(P_2, [X|Xs], T) :-
   if_( call(P_2, X), T = true, tmember_t(P_2, Xs, T) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Unit tests

% indexing_dif_* tests are just sanity checks – examples from the paper, to
% make sure I haven't messed up.
t(true, (
    indexing_dif_p6_e1 :-
        findall(X-Fs, tfilter(=(X),[1,2,3,2,3,3],Fs), [1-[1], 2-[2,2], 3-[3,3,3], Y-[]]),
        maplist(dif(Y), [1,2,3])
)).
t(true, (indexing_dif_p6_e2 :- findall(X, duplicate(X,[1,2,3,2,3,3]), [2,3]))).
t(true, (indexing_dif_p7_e1 :- firstduplicate(1, [1,2,3,1]))).
t(true, (indexing_dif_p7_e2 :- firstduplicate(X, [1,2,3,1]), X == 1)).
t(true, (indexing_dif_p7_e3 :-
    findall(Y-A-B-C, firstduplicate(Y,[A,B,C]), [X-X-X-_, X-X-B1-X, X-A2-X-X]),
    dif(B1,X),
    dif(A2,X)
)).

t(true, (functor_handles_unary_term :- functor_(a(b),G,c), G == a(b,c))).
t(true, (functor_handles_atoms :- functor_(a,G,b), G == a(b))).
t(true, (functor_handles_cyclic_terms :- X = a(b,X), functor_(X,G,c), G == a(b,X,c))).
t(error(instantiation_error), (functor_refuses_free_variable :- functor_(_,a(b),b))).
t(false, (functor_checks_for_correctness :- functor_(a,a,c))).

t(true, (doesnt_modify_free_variables :- goal_expanded(A,B), A == B, var(A))).
t(true, (expands_call1 :- goal_expanded(call(a), a))).
t(true, (expands_call1_for_modules :- goal_expanded(call(a:b(1)), a:b(1)))).
t(true, (expands_call2_for_modules :- goal_expanded(call(a:b,c), a:b(c)))).
t(true, (doesnt_expand_call2 :- goal_expanded(call(b,c), call(b,c)))).
t(true, (doesnt_expand_cyclic_terms :- X=a(X), goal_expanded(call(X), Y), call(X) == Y)).
t(true, (doesnt_expand_cyclic_call1 :- X=call(X), goal_expanded(X, Y), X == Y)).
t(true, (doesnt_expand_higher_order_predicates :- X = maplist(=(1), _), goal_expanded(X, Y), X == Y)).

% This test fails, and I don't know if goal_expanded/2 should be recursive or not,
% and what properties it shall maintain (is idempotence even desirable?).
t(skip, (second_expansion_doesnt_modify_goal :-
    findall(G==Gxx, test_expand_goal_twice(G,Gxx), Goals), maplist(call, Goals)
)).

test_expand_goal_twice(G, Gxx) :-
    test_goal(G), goal_expanded(G,Gx), goal_expanded(Gx, Gxx).
test_goal(_).
test_goal(call(a)).
test_goal(call(a:b(1))).
test_goal(call(a:b,c)).
test_goal(call(call(a))).
test_goal(call(call(a:b))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extras from the paper

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Unit test support (probably should be moved to another module)

:- use_module(library(iso_ext)).
:- use_module(library(lists)).

:- dynamic([t/2]).

%% testall.
%
% Fails if at least one test doesn't pass, but still executes all of them no
% matter what while printing report line for each unit test.
%
% Report looks like the following:
%
% ```
% true:[test_name,...]
% false:test_name
% skip:test_name
% error(ErrorTerm):test_name
% ```
%
% Test succeeds if it perfroms according to its expected outcome. Test may
% succeed multiple times.
%
% Test definition looks like this:
%
% ```
% t(ExpectedOutcome, (TestName :- TestBody)).
% ```
%
% Where:
%   `ExpectedOutcome` is either `true`, `false` or `error(ErrorTerm)` when an exception is expected.
%   `TestName` is a term describing the test (usually an atom)
%   `TestBody` is an actual test case
%
% TODO: Write tips for writting tests
% FIXME: There some quirks when using inside modules, because of (:)/2.
testall :- findall(C, testsingle(C), Cs), maplist(pass, Cs).

pass(true).
pass(skip).

%% testsingle(-TestResult).
%
% Retrieves unit tests and executes it. Always succeeds.
testsingle(C) :-
    gettest(D, G),
    asserta(D),
    call_cleanup(runtest(G,C), retract(D)).

%% gettest(-TestPredicate, -TestQuery).
%
% Retrieves unit test from the datebase, fails if no tests were found or test
% definition is incorrect.
%
% TODO: Throw exception, don't fail.
% FIXME: Handle modules correctly
gettest((H:-B), G) :- t(E, (H:-B)), expectation_goal(E, H, G).
expectation_goal(true, H, H).
expectation_goal(false, H, \+reif:H).
expectation_goal(error(E), H, catch(reif:H, error(E, _), true)).
expectation_goal(skip, H, true(H)).
true(_).

%% runtest(+Goal, -ResultCode).
%
% Try to collect all solutions and print predicate outcome no matter what.
% Always succeeds.
runtest(G, C) :- catch(findall(G,G,S), E, S = x(E)), what_to_print(S, G, C:R), write(C:R), nl.
what_to_print([],          G, false:G).
what_to_print([true(H)|_], _,  skip:H).
what_to_print([H|T],       _,  true:[H|T]) :- H \= true(_).
what_to_print(x(E),        G,     E:G).
