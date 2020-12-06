:- module(lists, [member/2, select/3, append/2, append/3, foldl/4, foldl/5,
		  memberchk/2, reverse/2, length/2, maplist/2,
		  maplist/3, maplist/4, maplist/5, maplist/6,
		  maplist/7, maplist/8, maplist/9, same_length/2, nth0/3,
		  sum_list/2, transpose/2, list_to_set/2, max_list/2, min_list/2]).


:- use_module(library(error)).


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
    ;  var(Xs0)  -> R is N-M, length_rundown(Xs0, R)).
length(_, N) :-
    integer(N), !,
    domain_error(not_less_than_zero, N, length/2).
length(_, N) :-
    type_error(integer, N, length/2).

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


append([], []).
append([L0|Ls0], Ls) :-
    append(L0, Rest, Ls),
    append(Ls0, Rest).


append([], R, R).
append([X|L], R, [X|S]) :- append(L, R, S).


memberchk(X, Xs) :- member(X, Xs), !.


reverse(Xs, Ys) :-
    (  nonvar(Xs) -> reverse(Xs, Ys, [], Xs)
    ;  reverse(Ys, Xs, [], Ys)
    ).

reverse([], [], YsRev, YsRev).
reverse([_|Xs], [Y1|Ys], YsPreludeRev, Xss) :-
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
    call(Cont, E1, E2, E3, E4, E5, E6, E7, E8),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s, E7s, E8s).


sum_list(Ls, S) :-
        foldl(sum_, Ls, 0, S).

sum_(L, S0, S) :- S is S0 + L.



same_length([], []).
same_length([_|As], [_|Bs]) :-
        same_length(As, Bs).


foldl(Goal_3, Ls, A0, A) :-
        foldl_(Ls, Goal_3, A0, A).

foldl_([], _, A, A).
foldl_([L|Ls], G_3, A0, A) :-
        call(G_3, L, A0, A1),
        foldl_(Ls, G_3, A1, A).


foldl(Goal_4, Xs, Ys, A0, A) :-
        foldl_(Xs, Ys, Goal_4, A0, A).

foldl_([], [], _, A, A).
foldl_([X|Xs], [Y|Ys], G_4, A0, A) :-
        call(G_4, X, Y, A0, A1),
        foldl_(Xs, Ys, G_4, A1, A).

transpose(Ls, Ts) :-
        lists_transpose(Ls, Ts).

lists_transpose([], []).
lists_transpose([L|Ls], Ts) :-
        maplist(same_length(L), Ls),
        foldl(transpose_, L, Ts, [L|Ls], _).

transpose_(_, Fs, Lists0, Lists) :-
        maplist(list_first_rest, Lists0, Fs, Lists).

list_first_rest([L|Ls], L, Ls).


list_to_set(Ls0, Ls) :-
        maplist(with_var, Ls0, LVs0),
        keysort(LVs0, LVs),
        same_elements(LVs),
        pick_firsts(LVs0, Ls).

pick_firsts([], []).
pick_firsts([E-V|EVs], Fs0) :-
        (   V == visited ->
            Fs0 = Fs
        ;   V = visited,
            Fs0 = [E|Fs]
        ),
        pick_firsts(EVs, Fs).

with_var(E, E-_).

same_elements([]).
same_elements([EV|EVs]) :-
        foldl(unify_same, EVs, EV, _).

unify_same(E-V, Prev-Var, E-V) :-
        (   Prev == E ->
            Var = V
        ;   true
        ).


nth0(N, Es, E) :-
        can_be(integer, N),
        can_be(list, Es),
        (   integer(N) ->
            nth0_index(N, Es, E)
        ;   nth0_search(N, Es, E)
        ).

nth0_index(0, [E|_], E) :- !.
nth0_index(N, [_|Es], E) :-
        N > 0,
        N1 is N - 1,
        nth0_index(N1, Es, E).

nth0_search(N, Es, E) :-
        nth0_search(0, N, Es, E).

nth0_search(N, N, [E|_], E).
nth0_search(N0, N, [_|Es], E) :-
        N1 is N0 + 1,
        nth0_search(N1, N, Es, E).


max_list([N|Ns], Max) :-
    foldl(max_list_, Ns, N, Max).

max_list_(N, Max0, Max) :-
    Max is max(N, Max0).

min_list([N|Ns], Min) :-
    foldl(min_list_, Ns, N, Min).

min_list_(N, Min0, Min) :-
    Min is min(N, Min0).

