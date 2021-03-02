:- use_module(library(debug)).
:- use_module(library(format)).

hello_world :- write('Hello World!'), nl.

:- initialization(hello_world).