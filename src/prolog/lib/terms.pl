:- module(terms, [term_variables/2, numbervars/2, numbervars/3]).

term_variables(Term, Vars) :- '$term_variables'(Term, Vars).

numbervars(Term, N) :-
    integer(N),
    term_variables(Term, Vars),
    numberlist(Vars, N, N1).
    
numbervars(Term, N0, N) :-
    integer(N0),
    integer(N),
    term_variables(Term, Vars),
    numberlist(Vars, N0, N).

numberlist([], N,N).
numberlist(['$VAR'(N0)|Vars], N0,N) :-
   N1 is N0+1,
   numberlist(Vars, N1,N).
