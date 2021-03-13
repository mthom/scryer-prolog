:- use_module(library(debug)).
:- use_module(library(format)).

missing_dot :- write('No "." at the end of the line'), nl

:- initialization(missing_dot).
