:- use_module(library(format)).


test :- compare(_, ("0"-'2'), ("1"-'1')).

?- test.
   false, unexpected.
   true.
