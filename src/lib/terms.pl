:- module(terms, [numbervars/3]).

:- use_module(library(error)).

numbervars(Term, N0, N) :-
   catch(internal_numbervars(Term, N0, N),
	     error(E,Ctx),
	     ( ( var(Ctx) -> Ctx = numbervars/3 ; true ), throw(error(E,Ctx) ) ) ).

internal_numbervars(Term, N0, N) :-
   must_be(integer, N0),
   can_be(integer, N),
   term_variables(Term, Vars),
   numberlist(Vars, N0, N).

numberlist([], N, N).
numberlist(['$VAR'(N0)|Vars], N0, N) :-
   N1 is N0+1,
   numberlist(Vars, N1, N).
