:- module(lists, [member/2, select/3, append/3, memberchk/2,
		  reverse/2, length/2, maplist/2, maplist/3,
		  maplist/4, maplist/5, maplist/6, maplist/7,
		  maplist/8, maplist/9]).

length(Xs, N) :-
    var(N), !,
    '$skip_max_list'(M, -1, Xs, Xs0),
    (  Xs0 == [] -> N = M
    ;  var(Xs0)  -> length_addendum(Xs0, N, M)).
length(Xs, N) :-
    integer(N),
    N >= 0, !,
    '$skip_max_list'(M, N, Xs, Xs0),
    (  Xs0 == [] -> N = M
    ;  var(Xs0)  -> R is N-M, nl, length_rundown(Xs0, R)).
length(_, N) :-
    integer(N), !,
    throw(error(domain_error(not_less_than_zero, N), length/2)).
length(_, N) :-
    throw(error(type_error(integer, N), length/2)).

length_addendum([], N, N).
length_addendum([_|Xs], N, M) :-
    M1 is M + 1,
    length_addendum(Xs, N, M1).

length_rundown(Xs, 0) :- !, Xs = [].
length_rundown([_|Xs], N) :-
    N1 is N-1,
    length_rundown(Xs, N1).

member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).

select(X, [X|Xs], Xs).
select(X, [Y|Xs], [Y|Ys]) :- select(X, Xs, Ys).

append([], R, R).
append([X|L], R, [X|S]) :- append(L, R, S).

memberchk(X, Xs) :- member(X, Xs), !.

reverse(Xs, Ys) :-
    (  nonvar(Xs) -> reverse(Xs, Ys, [], Xs)
    ;  reverse(Ys, Xs, [], Ys)
    ).

reverse([], [], YsRev, YsRev).
reverse([X1|Xs], [Y1|Ys], YsPreludeRev, Xss) :-
    reverse(Xs, Ys, [Y1|YsPreludeRev], Xss).

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
