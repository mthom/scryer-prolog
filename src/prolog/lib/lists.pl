:- module(lists, [member/2, select/3, append/3, is_list/1, memberchk/2, reverse/2, maplist/2,
		  maplist/3, maplist/4, maplist/5, maplist/6, maplist/7, maplist/8, maplist/9]).

member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).

select(X, [X|Xs], Xs).
select(X, [Y|Xs], [Y|Ys]) :- select(X, Xs, Ys).

append([], R, R).
append([X|L], R, [X|S]) :- append(L, R, S).

is_list(X) :- var(X), !, false.
is_list([]).
is_list([_|T]) :- is_list(T).

memberchk(X, Xs) :- member(X, Xs), !.

reverse(Xs, Ys) :- reverse(Xs, [], Ys).

reverse([], Ys, Ys).
reverse([H|T], Ps, Rs) :-
    reverse(T, [H|Ps], Rs).

maplist(_, []).
maplist(Cont1, [E1|E1s]) :-
    call(Cont1, E1),
    maplist(Cont1, E1s).

maplist(_, [], []).
maplist(Cont2, [E1|E1s], [E2|E2s]) :-
    call(Cont2, E1, E2),
    maplist(Cont2, E1s, E2s).

maplist(_, [], [], []).
maplist(Cont3, [E1|E1s], [E2|E2s], [E3|E3s]) :-
    call(Cont3, E1, E2, E3),
    maplist(Cont3, E1s, E2s, E3s).

maplist(_, [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s]) :-
    call(Cont, E1, E2, E3, E4),
    maplist(Cont, E1s, E2s, E3s, E4s).

maplist(_, [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s]) :-
    call(Cont, E1, E2, E3, E4, E5),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s).

maplist(_, [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s).

maplist(_, [], [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s], [E7|E7s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6, E7),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s, E7s).

maplist(_, [], [], [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s], [E7|E7s], [E8|E8s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6, E7),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s, E7s, E8s).
