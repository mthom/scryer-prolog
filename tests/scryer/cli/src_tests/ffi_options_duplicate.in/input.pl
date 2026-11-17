:- use_module(library(ffi)).

test :- use_foreign_module("nonexistent.so", [], [scope(local), scope(global)]).
