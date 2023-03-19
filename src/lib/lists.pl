/**
List manipulation predicates
*/

:- module(lists, [member/2, select/3, append/2, append/3, foldl/4, foldl/5,
		          memberchk/2, reverse/2, length/2, maplist/2,
		          maplist/3, maplist/4, maplist/5, maplist/6,
		          maplist/7, maplist/8, maplist/9, same_length/2, nth0/3, nth0/4, nth1/3, nth1/4,
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

:- use_module(library(error)).

:- meta_predicate(resource_error(+,:)).

resource_error(Resource, Context) :-
   throw(error(resource_error(Resource), Context)).

%% length(?Xs, ?N).
%
% Relates a list to its length (number of elements). It can be used to count the elements of a current list or
% to create a list full of free variables with N length.
%
% ```
% ?- length("abc", 3).
%    true.
% ?- length("abc", N).
%    N = 3.
% ?- length(Xs, 3).
%    Xs = [_A,_B,_C].
% ```

length(Xs0, N) :-
   '$skip_max_list'(M, N, Xs0,Xs),
   !,
   (  Xs == [] -> N = M
   ;  nonvar(Xs) -> var(N), Xs = [_|_], resource_error(finite_memory,length/2)
   ;  nonvar(N) -> R is N-M, length_rundown(Xs, R)
   ;  N == Xs -> failingvarskip(Xs), resource_error(finite_memory,length/2)
   ;  length_addendum(Xs, N, M)
   ).
length(_, N) :-
   integer(N), !,
   domain_error(not_less_than_zero, N, length/2).
length(_, N) :-
   type_error(integer, N, length/2).

length_rundown(Xs, 0) :- !, Xs = [].
length_rundown(Vs, N) :-
    '$unattributed_var'(Vs), % unconstrained
    !,
    '$det_length_rundown'(Vs, N).
length_rundown([_|Xs], N) :- % force unification
    N1 is N-1,
    length(Xs, N1). % maybe some new info on Xs

failingvarskip(Xs) :-
    '$unattributed_var'(Xs), % unconstrained
    !.
failingvarskip([_|Xs0]) :- % force unification
    '$skip_max_list'(_, _, Xs0,Xs),
    (  nonvar(Xs) -> Xs = [_|_]
	 ;  failingvarskip(Xs)
    ).

length_addendum([], N, N).
length_addendum([_|Xs], N, M) :-
    M1 is M + 1,
    length_addendum(Xs, N, M1).

%% member(?X, ?Xs).
%
% Succeeds when X unifies with an item of the list Xs, which can be at any position.
%
% ```
% ?- member(X, "hello world").
%    X = h
% ;  ... .
% ```
member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).

%% select(X, Xs0, Xs1).
%
% Succeeds when the list Xs1 is the list Xs0 without the item X
%
% ```
% ?- select(c, "abcd", X).
%    X = "abd"
% ;  false.
% ```
select(X, [X|Xs], Xs).
select(X, [Y|Xs], [Y|Ys]) :- select(X, Xs, Ys).

%% append(+XsXs, ?Xs).
%
% Concatenates a list of lists
%
% ```
% ?- append([[1, 2], [3]], Xs).
%    Xs = [1,2,3].
% ```
append([], []).
append([L0|Ls0], Ls) :-
    append(L0, Rest, Ls),
    append(Ls0, Rest).

%% append(Xs0, Xs1, Xs).
%
% List Xs is the concatenation of Xs0 and Xs1
%
% ```
% ?- append([1,2,3], [4,5,6], Xs).
%    Xs = [1,2,3,4,5,6].
% ```
append([], R, R).
append([X|L], R, [X|S]) :- append(L, R, S).

%% memberchk(?X, +Xs).
%
% This predicate is similar to `member/2`, but it only provides a single answer
memberchk(X, Xs) :- member(X, Xs), !.

%% reverse(?Xs, ?Ys).
%
% Xs is the Ys list in reverse order
%
%     ?- reverse([1,2,3], [3,2,1]).
%        true.
%
reverse(Xs, Ys) :-
    (  nonvar(Xs) -> reverse(Xs, Ys, [], Xs)
    ;  reverse(Ys, Xs, [], Ys)
    ).

reverse([], [], YsRev, YsRev).
reverse([_|Xs], [Y1|Ys], YsPreludeRev, Xss) :-
    reverse(Xs, Ys, [Y1|YsPreludeRev], Xss).

%% maplist(+Predicate, ?Xs0).
%
% This is a metapredicate that applies predicate to each element of the list Xs0
%
% ```
% ?- maplist(write, [1,2,3]).
% 123   true.
% ```
maplist(_, []).
maplist(Cont1, [E1|E1s]) :-
    call(Cont1, E1),
    maplist(Cont1, E1s).

%% maplist(+Predicate, ?Xs0, ?Xs1).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0 and Xs1.
%
% ```
% ?- maplist(length, ["hello", "prolog", "marseille"], Xs1).
%    Xs1 = [5,6,9].
% ```
maplist(_, [], []).
maplist(Cont2, [E1|E1s], [E2|E2s]) :-
    call(Cont2, E1, E2),
    maplist(Cont2, E1s, E2s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1 and Xs2.
maplist(_, [], [], []).
maplist(Cont3, [E1|E1s], [E2|E2s], [E3|E3s]) :-
    call(Cont3, E1, E2, E3),
    maplist(Cont3, E1s, E2s, E3s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2, ?Xs3).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1, Xs2 and Xs3.
maplist(_, [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s]) :-
    call(Cont, E1, E2, E3, E4),
    maplist(Cont, E1s, E2s, E3s, E4s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2, ?Xs3, ?Xs4).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1, Xs2, Xs3 and Xs4.
maplist(_, [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s]) :-
    call(Cont, E1, E2, E3, E4, E5),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2, ?Xs3, ?Xs4, ?Xs5).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1, Xs2, Xs3, Xs4 and Xs5.
maplist(_, [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2, ?Xs3, ?Xs4, ?Xs5, ?Xs6).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1, Xs2, Xs3, Xs4, Xs5 and Xs6.
maplist(_, [], [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s], [E7|E7s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6, E7),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s, E7s).

%% maplist(+Predicate, ?Xs0, ?Xs1, ?Xs2, ?Xs3, ?Xs4, ?Xs5, ?Xs6, ?Xs7).
%
% This is a metapredicate that applies predicate to each element of the lists Xs0, Xs1, Xs2, Xs3, Xs4, Xs5, Xs6 and Xs7.
maplist(_, [], [], [], [], [], [], [], []).
maplist(Cont, [E1|E1s], [E2|E2s], [E3|E3s], [E4|E4s], [E5|E5s], [E6|E6s], [E7|E7s], [E8|E8s]) :-
    call(Cont, E1, E2, E3, E4, E5, E6, E7, E8),
    maplist(Cont, E1s, E2s, E3s, E4s, E5s, E6s, E7s, E8s).

%% sum_list(+Xs, -Sum).
%
% Takes a lists of numbers and unifies Sum with the result of summing all the elements of the list.
%
% ```
% ?- sum_list([2,2,2], 6).
%    true.
% ```
sum_list(Ls, S) :-
        foldl(lists:sum_, Ls, 0, S).

sum_(L, S0, S) :- S is S0 + L.


%% same_length(?Xs, ?Ys).
%
% Succeeds if Xs and Ys are lists of the same length
same_length([], []).
same_length([_|As], [_|Bs]) :-
        same_length(As, Bs).

%% foldl(+Predicate, ?Ls, +A0, ?A).
%
% foldl, sometimes called reduce, is a metapredicate that takes a predicate, a list of items
% and a starting value, and outputs a single value. The predicate _Predicate_ must be able to take the current
% element of the list, the previous value of the computation and the next value of the computation.
%
% For example, if we define sum_ as:
%
% ```
% sum_(L, S0, S) :- S is S0 + L.
% ```
%
% Then we can define `sum_list/2` as the following:
%
% ```
% sum_list(Ls, S) :- foldl(sum_, Ls, 0, S).
% ```

foldl(Goal_3, Ls, A0, A) :-
        foldl_(Ls, Goal_3, A0, A).

foldl_([], _, A, A).
foldl_([L|Ls], G_3, A0, A) :-
        call(G_3, L, A0, A1),
        foldl_(Ls, G_3, A1, A).

%% foldl(+Predicate, ?Ls0, ?Ls1, +A0, ?A).
%
% Same as `foldl/4` but with an extra list
foldl(Goal_4, Xs, Ys, A0, A) :-
        foldl_(Xs, Ys, Goal_4, A0, A).


foldl_([], [], _, A, A).
foldl_([X|Xs], [Y|Ys], G_4, A0, A) :-
        call(G_4, X, Y, A0, A1),
        foldl_(Xs, Ys, G_4, A1, A).

%% transpose(?Ls, ?Ts).
%
% If Ls is a list of lists, Ts contains the transposition
%
% ```
% ?- transpose([[1,1],[2,2]], Ts).
%    Ts = [[1,2],[1,2]].
% ```
transpose(Ls, Ts) :-
        lists_transpose(Ls, Ts).

lists_transpose([], []).
lists_transpose([L|Ls], Ts) :-
        maplist(lists:same_length(L), Ls),
        foldl(lists:transpose_, L, Ts, [L|Ls], _).

transpose_(_, Fs, Lists0, Lists) :-
        maplist(lists:list_first_rest, Lists0, Fs, Lists).

list_first_rest([L|Ls], L, Ls).

%% list_to_set(+Ls0, -Set).
%
% Takes a list Ls0 and returns a list Set that doesn't contain any repeated element
%
% ```
% ?- list_to_set([2,3,4,4,1,2], Set).
%    Set = [2,3,4,1].
% ```
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

%% nth0(?N, ?Ls, ?E).
%
% Succeeds if in the N position of the list Ls, we found the element E. The elements start counting from zero.
%
% ```
% ?- nth0(2, [1,2,3,4], 3).
%    true.
% ```
nth0(N, Es0, E) :-
   nonvar(N),
   '$skip_max_list'(Skip, N, Es0,Es1),
   !,
   (  Skip == N
   -> Es1 = [E|_]
   ;  ( var(Es1) ; Es1 = [_|_] ) % a partial or infinite list
   -> R is N-Skip,
      skipn(R,Es1,Es2),
      Es2 = [E|_]
   ).
nth0(N, Es0, E) :-
   can_be(not_less_than_zero, N),
   Es0 = [E0|Es1],
   nth0_el(0,N, E0,E, Es1).

skipn(N0, Es0,Es) :-
   N0>0,
   !, % should not be necessary #1028
   N1 is N0-1,
   Es0 = [_|Es1],
   skipn(N1, Es1,Es).
skipn(0, Es,Es).

nth0_el(N0,N, E0,E, Es0) :-
   Es0 == [],
   !, % indexing
   N0 = N,
   E0 = E.
nth0_el(N,N, E,E, _).
nth0_el(N0,N, _,E, [E0|Es0]) :-
   N1 is N0+1,
   nth0_el(N1,N, E0,E, Es0).

%% nth1(?N, ?Ls, ?E).
%
% Succeeds if in the N position of the list Ls, we found the element E. The elements start counting from one.
%
% ```
% ?- nth1(2, [1,2,3,4], 2).
%    true.
% ```
nth1(N, Es0, E) :-
   N \== 0,
   nth0(N, [_|Es0], E),
   N \== 0.

skipn(N0, Es0,Es, Xs0,Xs) :-
   N0>0,
   !, % should not be necessary #1028
   N1 is N0-1,
   Es0 = [E|Es1],
   Xs0 = [E|Xs1],
   skipn(N1, Es1,Es, Xs1,Xs).
skipn(0, Es,Es, Xs,Xs).

%% nth0(?N, ?Ls, ?E, ?Rs).
%
% Succeeds if in the N position of the list Ls, we found the element E and the rest of the list is Rs. The elements start counting from zero.
%
% ```
% ?- nth0(2, [1,2,3,4], 3, [1,2,4]).
%    true.
% ```
nth0(N, Es0, E, Es) :-
   integer(N),
   N >= 0,
   !,
   skipn(N, Es0,Es1, Es,Es2),
   Es1 = [E|Es2].
nth0(N, Es0, E, Es) :-
   can_be(not_less_than_zero, N),
   Es0 = [E0|Es1],
   nth0_elx(0,N, E0,E, Es1, Es).

nth0_elx(N0,N, E0,E, Es0, Es) :-
   Es0 == [],
   !,
   N0 = N,
   E0 = E,
   Es0 = Es.
nth0_elx(N,N, E,E, Es, Es).
nth0_elx(N0,N, E0,E, [E1|Es0], [E0|Es]) :-
   N1 is N0+1,
   nth0_elx(N1,N, E1,E, Es0, Es).

% p.p.8.5

%% nth1(?N, ?Ls, ?E, ?Rs).
%
% Succeeds if in the N position of the list Ls, we found the element E and the rest of the list is Rs. The elements start counting from one.
%
% ```
% ?- nth1(2, [1,2,3,4], 2, [1,3,4]).
%    true.
% ```
nth1(N, Es0, E, Es) :-
   N \== 0,
   nth0(N, [_|Es0], E, [_|Es]),
   N \== 0.

%% list_max(+Xs, -Max).
%
% Takes a list Xs and unifies with the maximum value of the list
list_max([N|Ns], Max) :-
    foldl(lists:list_max_, Ns, N, Max).

list_max_(N, Max0, Max) :-
    Max is max(N, Max0).

%% list_min(+Xs, -Min).
%
% Takes a list Xs and unifies with the minimum value of the list
list_min([N|Ns], Min) :-
    foldl(lists:list_min_, Ns, N, Min).

list_min_(N, Min0, Min) :-
    Min is min(N, Min0).

%% permutation(?Xs, ?Ys) is nondet.
%
% True when Xs is a permutation of Ys. This can solve for Ys given
% Xs or Xs given Ys, or  even   enumerate  Xs and Ys together. The
% predicate  `permutation/2`  is  primarily   intended  to  generate
% permutations. Note that a list of  length N has N! permutations,
% and  unbounded  permutation  generation   becomes  prohibitively
% expensive, even for rather short lists (10! = 3,628,800).
%
% The example below illustrates that Xs   and Ys being proper lists
% is not a sufficient condition to use the above replacement.
%
% ```
% ?- permutation([1,2], [X,Y]).
%    X = 1, Y = 2
% ;  X = 2, Y = 1
% ;  false.
% ```
%
%   Throws `type_error(list, Arg)` if either argument is not a proper
%   or partial list.

permutation(Xs, Ys) :-
    '$skip_max_list'(Xlen, _, Xs, XTail),
    '$skip_max_list'(Ylen, _, Ys, YTail),
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
