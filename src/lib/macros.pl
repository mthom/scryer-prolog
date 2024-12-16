:- module(macros, [
    op(199, xfy, (#)),
    op(1200, xfy, (==>)),
    macro/3
]).

:- use_module(library(si), [atomic_si/1]).
:- use_module(library(error), [instantiation_error/1]).
:- use_module(library(loader), [prolog_load_context/2]).
:- use_module(library(goals), [call_unifiers/2,expand_subgoals/3]).

:- discontiguous(macro/3).
:- multifile(macro/3).

user:term_expansion((M#A ==> B), (macros:macro(M, A, H) :- G)) :- nonvar(B), B = (H :- G).
user:term_expansion((M#A ==> B),  macros:macro(M, A, B)      ).


% Capturing erroneous expansions.
% It slows down expansion, but it will produce (more) meaningful error if some
% user macro happens to be poorly written.
% IMPORTANT: Must be the first macro definition seen by compiler
M#A ==> _  :-
    (var(M); var(A)), instantiation_error(M#A).

% Basic
M#(A,B)  ==> M#A, M#B.
M#(A;B)  ==> M#A; M#B.
M#(A->B) ==> M#A -> M#B.
M#(\+ A) ==> \+ M#A.
M#{A}    ==> {M#A}.
_#!      ==> !.


% Controlling macro expansion.
% Any unrecognized macro will be left as it were, but by using quote you can
% be sure that no other macro definition will be invoked
quote#_   ==> _ :- !, false.


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

user:goal_expansion(M#A, X) :-
    atomic_si(M),
    nonvar(A),
    macro(M, A, X).
