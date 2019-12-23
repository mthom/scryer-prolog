
:- module(cont, [reset/3, shift/1]).

reset(Goal, Ball, Cont) :-
    call(Goal),
    '$reset_cont_marker',
    '$bind_from_register'(Cont, 3),
    '$bind_from_register'(Ball, 4).

shift(Term) :-
    '$nextEP'(first, E, P),
    get_chunks(E, P, L),
    (  L == [] ->
       Cont = none
    ;  Cont = cont(call_continuation(L))
    ),
    '$write_cont_and_term'(_, _, Cont, Term),
    '$unwind_environments'.

get_chunks(E, P, L) :-
    (  '$points_to_cont_reset_marker'(P) ->
       L = []
    ;  '$get_cont_chunk'(E,P,TB),
       L = [TB|Rest],
       '$nextEP'(E, NextE, NextP),
       get_chunks(NextE, NextP, Rest)
    ).

call_continuation(L) :- '$call_continuation'(L).

'$write_cont_and_term'(_, _, _, _).
