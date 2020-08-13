:- module(combination, [combination/2, combinationr/2]).

combination([], []).
combination([L|Ls], [L|Ms]) :-
    combination(Ls, Ms).
combination([_|Ls], Ms) :-
    combination(Ls, Ms).

combinationr([], []).
combinationr([L|Ls], Ms) :-
    combinationr_(Ms, [L|Ls]).

combinationr_([], _).
combinationr_([M|Ms], [M|Ls]) :-
    combinationr_(Ms, [M|Ls]).
combinationr_([M|Ms], [_|Ls]) :-
    combinationr_([M|Ms], Ls).
