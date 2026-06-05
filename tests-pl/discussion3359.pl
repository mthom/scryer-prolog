:- use_module(library(dcgs)).
:- use_module(library(tabling)).

:- table expr//0.

expr --> "1".
expr --> expr, "+", expr.

run :- phrase(expr, "1+1+1+1+1").

:- initialization(run).
