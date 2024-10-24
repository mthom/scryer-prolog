:- module(macros, [
    op(199, xfx, (#)),
    op(1200, xfy, (==>)),
    macro/3
]).

:- use_module(library(si), [atomic_si/1]).

:- discontiguous(macro/3).
:- multifile(macro/3).

user:term_expansion((M#A ==> H :- G), (macros:macro(M, A, H) :- G)).
user:term_expansion((M#A ==> B     ),  macros:macro(M, A, B)      ).

% Basic
M#(A,B)  ==> M#A, M#B.
M#(A;B)  ==> M#A; M#B.
M#(A->B) ==> M#A -> M#B.
M#(\+ A) ==> \+ M#A.
M#{A}    ==> {M#A}.
_#!      ==> !.

% Compile time computation: Inline last argument
inline_last#G ==> [X] :-
    loader:load_context(M),
    M:call(G, X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

user:goal_expansion(M#A, X) :-
    atomic_si(M),
    nonvar(A),
    macro(M, A, X).

:- use_module(library(subterm_expansion)).
