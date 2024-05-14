:- use_module(library(sgml)).

test :- load_html("<html><head><title>Hello!</title></head></html>", Es, []), write(Es).

:- initialization(test).
