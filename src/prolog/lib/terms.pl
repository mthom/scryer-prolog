:- module(terms, [numbervars/2]).

numbervars(Term, N) :-
    integer(N),
    term_variables(Term, Vars),
    numberlist(Vars, N, N1).

numberlist([], N,N).
numberlist(['$VAR'(N0)|Vars], N0,N) :-
   N1 is N0+1,
   numberlist(Vars, N1,N).
