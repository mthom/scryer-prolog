:- module(statistics, [
    statistics/2
]).

statistics(cputime, T) :-
    '$cpu_now'(T).

statistics(inferences, I) :-
    '$inferences'(I).