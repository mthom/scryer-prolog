:- module(numbervars, [numbervars/2, numbervars/3]).

numbervars(Term, NewTerm) :- duplicate_term(Term, NewTerm), numbervars(Term, NewTerm, 0, _).

numbervars(Term, NewTerm, N) :-
    ( integer(N), N >= 0 -> duplicate_term(Term, NewTerm), numbervars(Term, NewTerm, N, _)
    ; integer(N) -> throw(error(domain_error(not_less_than_zero, N), numbervars/3))
    ; throw(error(type_error(integer, N), numbervars/3))
    ).

numbervars(Term, NewTerm, N1, N2) :-
    var(Term), !, NewTerm = '$VAR'(N1), N2 is N1 + 1.
numbervars(Term, NewTerm, N1, N2) :- compound(Term), !,
    Term =.. [Name | Args],
    NewTerm =.. [Name | NewArgs],
    fold_numbervars(Args, NewArgs, N1, N2).
numbervars(_, _, _, _).

marked_already(Term, NewTerm) :-
    var(Term), nonvar(NewTerm), NewTerm = '$VAR'(_).
marked_already(Term, NewTerm) :-
    atomic(Term).

fold_numbervars([HeadTerm | Terms], [NewHeadTerm | NewTerms], N1, Nn) :-
    ( marked_already(HeadTerm, NewHeadTerm) -> N1 = N2
    ; numbervars(HeadTerm, NewHeadTerm, N1, N2),
      ( var(N2) -> N1 = N2
      ; true )
    ),
    fold_numbervars(Terms, NewTerms, N2, Nn).
fold_numbervars([], [], _, _).
