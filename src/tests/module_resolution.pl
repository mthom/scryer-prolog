:- module(module_resolution, [get_module/2, some_predicate/2, get_private_module/1]).

:- meta_predicate(get_module(:, ?)).

get_module(Pred, M) :- strip_module(Pred, M, _).

get_private_module(M) :- get_module(private_predicate, M).

some_predicate(X, Y) :- X is Y + 1.
private_predicate(X, Y) :- X is Y - 1.
