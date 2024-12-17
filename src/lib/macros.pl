:- module(macros, [
    op(199, xfy, (#)),
    op(1200, xfy, (==>)),
    macro/3
]).

:- use_module(library(si), [atomic_si/1,when_si/2]).
:- use_module(library(error), [instantiation_error/1]).
:- use_module(library(loader), [prolog_load_context/2]).
:- use_module(library(goals), [call_unifiers/2,expand_subgoals/3]).
:- use_module(library(warnings), [warn/2]).

:- discontiguous(macro/3).
:- multifile(macro/3).

user:term_expansion((M#A ==> B), X) :-
    nonvar(B),
    B = (H :- G) ->
        X = (macros:macro(M, A, H) :- G)
    ;   X =  macros:macro(M, A, B).


% Basic
M#(A,B)  ==> M#A, M#B.
M#(A;B)  ==> M#A; M#B.
M#(A->B) ==> M#A -> M#B.
M#(\+ A) ==> \+ M#A.
M#{A}    ==> {M#A}.
_#!      ==> !.


% Compile time computation: Inline last argument
inline_last#G ==> [X] :-
    load_module_context(M),
    M:call(G, X).


% Evaluates G and if it succeeds replaces it with solutions.
compile#G ==> Us :-
    load_module_context(M),
    call_unifiers(M:G, Us).


% Sub-goal expansion
expand#A ==> X :-
    expand_subgoals(_, A, X).


load_module_context(Module) :- prolog_load_context(module, Module), !.
load_module_context(user).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

macro_wrapper(quote, _, _) :- !, false.
macro_wrapper(M, A, X) :- macro(M, A, X).
macro_wrapper(M, A, _) :-
    warn("Unknown macro ~a # ~q", [M,A]),
    throw(error(existence_error(macro/3, goal_expansion/2), [culprit-(M#A)])).

user:goal_expansion(M#A, X) :-
    atomic_si(M),
    when_si(nonvar(A),
        macro_wrapper(M, A, X)
    ).
