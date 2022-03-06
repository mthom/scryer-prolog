:- module(random, [maybe/0, random/1, random_integer/3, set_random/1]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   To retain desirable declarative properties, predicates that internally
   use random numbers should be equipped with an argument that specifies
   the random seed. This makes everything completely reproducible.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- use_module(library(error)).

% succeeds with probability 0.5.
maybe :- '$maybe'.

% The higher the precision, the slower it gets.
random_number_precision(64).

random(R) :-
    var(R),
    random_number_precision(N),
    rnd(N, R).

random_integer(Lower, Upper, R) :-
    var(R),
    (   (var(Lower) ; var(Upper)) ->
        instantiation_error(random_integer/3)
    ;   \+ integer(Lower) ->
        type_error(integer, Lower, random_integer/3)
    ;   \+ integer(Upper) ->
        type_error(integer, Upper, random_integer/3)
    ;   Upper > Lower,
        random(R0),
        R is floor((Upper - Lower) * R0 + Lower)
    ).

rnd(N, R) :-
    rnd_(N, 0, R).

rnd_(0, R, R) :- !.
rnd_(N, R0, R) :-
    maybe,
    !,
    N1 is N - 1,
    rnd_(N1, R0, R).
rnd_(N, R0, R) :-
    N1 is N - 1,
    R1 is R0 + 1.0 / 2.0 ^ N,
    rnd_(N1, R1, R).

set_random(Seed) :-
    (   nonvar(Seed) ->
        (  Seed = seed(S) ->
        (  var(S) -> instantiation_error(set_random/1)
        ;  integer(S) -> '$set_seed'(S)
        ;  type_error(integer, S, set_random/1)
        )
        )
    ;   instantiation_error(set_random/1)
    ).

