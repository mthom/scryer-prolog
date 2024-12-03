:- module(a, [
    hello/2
]).

:- use_module(library(interfaces)).

:- multifile(hello/2).

hello(a, _) :- 0.
