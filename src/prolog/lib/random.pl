:- module(random, [maybe/0, set_random/1]).

% succeeds with probability 0.5.
maybe :- '$maybe'.

set_random(Seed) :-
    (   nonvar(Seed) ->
        (  Seed = seed(S) ->
        (  var(S) -> throw(error(instantiation_error, set_random/1))
        ;  integer(S) -> '$set_seed'(S)
        ;  throw(error(type_error(integer(S), set_random/1)))
        )
        )
    ;   throw(error(instantiation_error, set_random/1))
    ).

