:- module(m, [gs/1]).

:- use_module(library(lists)).

gs([]).
gs([G|Gs]) :-
        G,
        gs(Gs).
