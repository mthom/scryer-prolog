:- use_module(library(sgml)).

test :- load_html("<html><head><template>Hello!</template></head></html>", Es, []), write(Es).

:- initialization(test).
