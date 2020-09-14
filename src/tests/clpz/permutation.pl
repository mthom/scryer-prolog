:- module(permutation, [arrangement/2, arrangementr/2, permutation/2]).
:- use_module(library(lists), [member/2, same_length/2, select/3]).

permutation(As, Bs) :-
    same_length(As, Bs),
    permutation_(Bs, As).

permutation_([B|Bs], As) :- select(B, As, Cs), permutation_(Bs, Cs).
permutation_([], []).

arrangement([], []).
arrangement([A|As], [B|Bs]) :-
    arrangement_([B|Bs], [A|As]).

arrangement_([], _).
arrangement_([B|Bs], As) :-
    select(B, As, Cs),
    arrangement_(Bs, Cs).

arrangementr([], []).
arrangementr([A|As], Bs) :-
    arrangementr_(Bs, [A|As]).

arrangementr_([], _).
arrangementr_([B|Bs], As) :-
    member(B, As),
    arrangementr_(Bs, As).
