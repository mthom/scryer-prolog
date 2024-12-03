:- use_module(a).

:- multifile(a:hello/2).

a:hello(a, X) :- X = 1.
a:hello(a, X) :- X = 2.
a:hello(b, X) :- X = 3.
a:hello(a, X) :- X = 4.
a:hella(a, X) :- X = 4.
