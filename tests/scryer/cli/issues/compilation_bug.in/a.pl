% Issue 2706
:- use_module(library(atts)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).

:- attribute a/1.

verify_attributes(_,_, []).

asdf([_|Xs], N) :-
    true,
    N1 is N - 1,
    asdf(Xs, N1).

test_a :-
    put_atts(A, a(1)),
    call_with_inference_limit(asdf(A, 1), 1000, _).
