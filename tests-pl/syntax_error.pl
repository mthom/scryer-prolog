:- use_module(library(debug)).
:- use_module(library(format)).

missing_dot :- write('Not "." at the end of the line'), nl

:- initialize(missing_dot).