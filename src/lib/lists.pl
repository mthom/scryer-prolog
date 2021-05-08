:- module(lists, [member/2, select/3, append/2, append/3, foldl/4, foldl/5,
		          memberchk/2, reverse/2, length/2, maplist/2,
		          maplist/3, maplist/4, maplist/5, maplist/6,
		          maplist/7, maplist/8, maplist/9, same_length/2, nth0/3,
		          sum_list/2, transpose/2, list_to_set/2, list_max/2,
                          list_min/2, permutation/2]).

/*  Author:        Mark Thom, Jan Wielemaker, and Richard O'Keefe
    Copyright (c)  2018-2021, Mark Thom
    Copyright (c)  2002-2020, University of Amsterdam
                              VU University Amsterdam
                              SWI-Prolog Solutions b.v.
    All rights reserved.
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.
    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/


:- use_module(library(error)).


:- meta_predicate maplist(1, ?).
:- meta_predicate maplist(2, ?, ?).
:- meta_predicate maplist(3, ?, ?, ?).
:- meta_predicate maplist(4, ?, ?, ?, ?).
:- meta_predicate maplist(5, ?, ?, ?, ?, ?).
:- meta_predicate maplist(6, ?, ?, ?, ?, ?, ?).
:- meta_predicate maplist(7, ?, ?, ?, ?, ?, ?, ?).
:- meta_predicate maplist(8, ?, ?, ?, ?, ?, ?, ?, ?).

:- meta_predicate foldl(3, ?, ?, ?).
:- meta_predicate foldl(4, ?, ?, ?, ?).


length(Xs, N) :-
    var(N),
    !,
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
        foldl(lists:sum_, Ls, 0, S).

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
        maplist(lists:same_length(L), Ls),
        foldl(lists:transpose_, L, Ts, [L|Ls], _).

transpose_(_, Fs, Lists0, Lists) :-
        maplist(lists:list_first_rest, Lists0, Fs, Lists).

list_first_rest([L|Ls], L, Ls).


list_to_set(Ls0, Ls) :-
        maplist(lists:with_var, Ls0, LVs0),
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
        foldl(lists:unify_same, EVs, EV, _).

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


list_max([N|Ns], Max) :-
    foldl(lists:list_max_, Ns, N, Max).

list_max_(N, Max0, Max) :-
    Max is max(N, Max0).

list_min([N|Ns], Min) :-
    foldl(lists:list_min_, Ns, N, Min).

list_min_(N, Min0, Min) :-
    Min is min(N, Min0).

%!  permutation(?Xs, ?Ys) is nondet.
%
%   True when Xs is a permutation of Ys. This can solve for Ys given
%   Xs or Xs given Ys, or  even   enumerate  Xs and Ys together. The
%   predicate  permutation/2  is  primarily   intended  to  generate
%   permutations. Note that a list of  length N has N! permutations,
%   and  unbounded  permutation  generation   becomes  prohibitively
%   expensive, even for rather short lists (10! = 3,628,800).
%
%   The example below illustrates that Xs   and Ys being proper lists
%   is not a sufficient condition to use the above replacement.
%
%     ==
%     ?- permutation([1,2], [X,Y]).
%     X = 1, Y = 2 ;
%     X = 2, Y = 1 ;
%     false.
%     ==
%
%   @error  type_error(list, Arg) if either argument is not a proper
%           or partial list.

permutation(Xs, Ys) :-
    '$skip_max_list'(Xlen, -1, Xs, XTail),
    '$skip_max_list'(Ylen, -1, Ys, YTail),
    (   XTail == [], YTail == []            % both proper lists
    ->  Xlen == Ylen
    ;   var(XTail), YTail == []             % partial, proper
    ->  length(Xs, Ylen)
    ;   XTail == [], var(YTail)             % proper, partial
    ->  length(Ys, Xlen)
    ;   var(XTail), var(YTail)              % partial, partial
    ->  length(Xs, Len),
        length(Ys, Len)
    ;   must_be(list, Xs),                  % either is not a list
        must_be(list, Ys)
    ),
    perm(Xs, Ys).

perm([], []).
perm(List, [First|Perm]) :-
    select(First, List, Rest),
    perm(Rest, Perm).
