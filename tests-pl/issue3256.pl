:- use_module(library(sgml)).

test :- load_xml("<foo><bar>hello</bar></foo>", Es, []), write(Es).

:- initialization(test).
