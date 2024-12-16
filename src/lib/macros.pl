:- module(macros, [
    op(199, xfy, (#)),
    op(1200, xfy, (==>)),
    macro/3
]).

:- use_module(library(si), [atomic_si/1]).
:- use_module(library(lists), [maplist/3]).
:- use_module(library(error), [instantiation_error/1]).

:- discontiguous(macro/3).
:- multifile(macro/3).

user:term_expansion((M#A ==> B), (macros:macro(M, A, H) :- G)) :- nonvar(B), B = (H :- G).
user:term_expansion((M#A ==> B),  macros:macro(M, A, B)      ).


% Capturing erroneous expansions.
% It slows down expansion, but it will produce (more) meaningful error if some
% user macro happens to be poorly written.
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
    loader:load_context(M),
    M:call(G, X).


% Sub-goal expansion
expand#A ==> X :-
    expand_subgoals(_, A, X).


%% expand_sub_goals(?M, ?A, -X).
%
% Similar to expand_goal/3, but recursively tries to expand every sub-term.
expand_subgoals(M, A, X) :-
    nonvar(A) ->
        (   functor(A, (#), 2) ->
            expand_goal(A, M, X)
        ;   A =.. [F|Args],
            maplist(expand_subgoals(M), Args, XArgs),
            X =.. [F|XArgs]
        )
    ;   A = X.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

user:goal_expansion(M#A, X) :-
    atomic_si(M),
    nonvar(A),
    macro(M, A, X).
