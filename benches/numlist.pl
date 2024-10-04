:- use_module(library(between)).
run_numlist(Upper, Head) :- numlist(1, Upper, L), L = [Head|_].
