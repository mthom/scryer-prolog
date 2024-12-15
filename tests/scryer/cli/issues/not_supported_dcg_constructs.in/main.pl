:- use_module(library(dcgs)).
:- initialization(abolish(null/0)).
:- dynamic(null/0).

d -->
        (   { true } -> []
        ;   { true } -> []
        ).
