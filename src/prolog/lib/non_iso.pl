%% for builtins that are not part of the ISO standard.
%% must be loaded at the REPL with

%% ?- use_module(library(non_iso)).

:- module(non_iso, [forall/2]).

forall(Generate, Test) :-
    \+ (Generate, \+ Test).

