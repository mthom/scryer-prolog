:- module(module_resolution, [get_module/2]).

get_module(P, M) :- strip_module(P, M, _).

:- initialization((strip_module(hello, M, _), write(M), write('\n'))).
:- initialization((loader:strip_module(hello, M, _), write(M), write('\n'))).
:- initialization((get_module(hello, M), write(M), write('\n'))).
:- initialization((module_resolution:get_module(hello, M), write(M), write('\n'))).
