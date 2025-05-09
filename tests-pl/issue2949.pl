:- use_module(library(sgml)).

test :- 
    load_html("<!DOCTYPE html><html><head><title>Hello!</title></head></html>", Es, []), 
    write(Es),
    load_html("<!DOCTYPE html><html><head><title>Hello!</title><!-- comment --></head></html>", Es2, []), 
    write(Es2),
    load_html("<!", Es3, []), 
    write(Es3).

:- initialization(test).
