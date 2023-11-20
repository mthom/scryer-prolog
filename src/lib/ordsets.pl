/*  Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2001-2014, University of Amsterdam
                              VU University Amsterdam
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

:- module(ordsets,
          [ is_ordset/1,                % @Term
            list_to_ord_set/2,          % +List, -OrdSet
            ord_add_element/3,          % +Set, +Element, -NewSet
            ord_del_element/3,          % +Set, +Element, -NewSet
            ord_selectchk/3,            % +Item, ?Set1, ?Set2
            ord_intersect/2,            % +Set1, +Set2 (test non-empty)
            ord_intersect/3,            % +Set1, +Set2, -Intersection
            ord_intersection/3,         % +Set1, +Set2, -Intersection
            ord_intersection/4,         % +Set1, +Set2, -Intersection, -Diff
            ord_disjoint/2,             % +Set1, +Set2
            ord_subtract/3,             % +Set, +Delete, -Remaining
            ord_union/2,                % +SetOfOrdSets, -Set
            ord_union/3,                % +Set1, +Set2, -Union
            ord_union/4,                % +Set1, +Set2, -Union, -New
            ord_subset/2,               % +Sub, +Super (test Sub is in Super)
                                        % Non-Quintus extensions
            ord_empty/1,                % ?Set
            ord_memberchk/2,            % +Element, +Set,
            ord_symdiff/3,              % +Set1, +Set2, ?Diff
                                        % SICSTus extensions
            ord_seteq/2,                % +Set1, +Set2
            ord_intersection/2          % +PowerSet, -Intersection
          ]).

:- use_module(library(lists)).

/** Ordered set manipulation

Ordered sets are lists with unique elements sorted to the standard order
of terms (see `sort/2`). Exploiting ordering,   many of the set operations
can be expressed in order N rather  than N^2 when dealing with unordered
sets that may contain duplicates. The library(ordsets) is available in a
number of Prolog implementations. Our  predicates   are  designed  to be
compatible  with  common  practice   in    the   Prolog  community.
Some  of  these  predicates  match    directly   to  corresponding  list
operations. It is advised to use the  versions from this library to make
clear you are operating on ordered sets.   An exception is `member/2`. See
`ord_memberchk/2`.

The ordsets library is based  on  the   standard  order  of  terms. This
implies it can handle  all  Prolog   terms,  including  variables.  Note
however, that the ordering is not stable  if   a  term inside the set is
further instantiated. Also  note  that   variable  ordering  changes  if
variables in the set are unified with each   other  or a variable in the
set is unified with a variable that  is _older_ than the newest variable
in the set. In  practice,  this  implies   that  it  is  allowed  to use
member(X, OrdSet) on an ordered set that holds  variables only if X is a
fresh variable. In other cases one should   cease  using it as an ordset
because the order it relies on may have been changed.
*/

%% is_ordset(@Term) is semidet.
%
% True if Term is an ordered set.   All predicates in this library
% expect ordered sets as input arguments.  Failing to fullfil this
% assumption results in undefined   behaviour.  Typically, ordered
% sets are created by predicates  from   this  library,  `sort/2` or
% `setof/3`.

is_ordset(Term) :-
    '$skip_max_list'(_, _, Term, Tail), Tail == [], %% is_list(Term),
    is_ordset2(Term).

is_ordset2([]).
is_ordset2([H|T]) :-
    is_ordset3(T, H).

is_ordset3([], _).
is_ordset3([H2|T], H) :-
    H2 @> H,
    is_ordset3(T, H2).


%% ord_empty(?List) is semidet.
%
% True when List is the  empty   ordered  set. Simply unifies list
% with the empty list. Not part of Quintus.

ord_empty([]).


%% ord_seteq(+Set1, +Set2) is semidet.
%
% True if Set1 and Set2  have  the   same  elements.  As  both are
% canonical sorted lists, this is the same as `==/2`.

ord_seteq(Set1, Set2) :-
    Set1 == Set2.


%% list_to_ord_set(+List, -OrdSet) is det.
%
% Transform a list into an ordered set.  This is the same as
% sorting the list.

list_to_ord_set(List, Set) :-
    sort(List, Set).


%% ord_intersect(+Set1, +Set2) is semidet.
%
% True if both ordered sets have a non-empty intersection.

ord_intersect([H1|T1], L2) :-
    ord_intersect_(L2, H1, T1).

ord_intersect_([H2|T2], H1, T1) :-
    compare(Order, H1, H2),
    ord_intersect__(Order, H1, T1, H2, T2).

ord_intersect__(<, _H1, T1,  H2, T2) :-
    ord_intersect_(T1, H2, T2).
ord_intersect__(=, _H1, _T1, _H2, _T2).
ord_intersect__(>, H1, T1,  _H2, T2) :-
    ord_intersect_(T2, H1, T1).


%% ord_disjoint(+Set1, +Set2) is semidet.
%
% True if Set1 and Set2  have  no   common  elements.  This is the
% negation of `ord_intersect/2`.

ord_disjoint(Set1, Set2) :-
    \+ ord_intersect(Set1, Set2).


%% ord_intersect(+Set1, +Set2, -Intersection)
%
% Intersection  holds  the  common  elements  of  Set1  and  Set2.
%
% This predicate is *deprecated*. Use `ord_intersection/3`

ord_intersect(Set1, Set2, Intersection) :-
    oset_int(Set1, Set2, Intersection).


%% ord_intersection(+PowerSet, -Intersection)
%
% Intersection of a powerset. True when Intersection is an ordered
% set holding all elements common to all sets in PowerSet.

ord_intersection(PowerSet, Intersection) :-
    key_by_length(PowerSet, Pairs),
    keysort(Pairs, [_-S|Sorted]),
    l_int(Sorted, S, Intersection).

key_by_length([], []).
key_by_length([H|T0], [L-H|T]) :-
    length(H, L),
    key_by_length(T0, T).

l_int([], S, S).
l_int([_-H|T], S0, S) :-
    ord_intersection(S0, H, S1),
    l_int(T, S1, S).


%% ord_intersection(+Set1, +Set2, -Intersection) is det.
%
% Intersection holds the common elements of Set1 and Set2.  Uses
% `ord_disjoint/2` if Intersection is bound to `[]` on entry.

ord_intersection(Set1, Set2, Intersection) :-
    (   Intersection == []
    ->  ord_disjoint(Set1, Set2)
    ;   oset_int(Set1, Set2, Intersection)
    ).


%% ord_intersection(+Set1, +Set2, ?Intersection, ?Difference) is det.
%
% Intersection  and  difference   between    two   ordered   sets.
% Intersection is the intersection between   Set1  and Set2, while
% Difference is defined by `ord_subtract(Set2, Set1, Difference)`.

ord_intersection([], L, [], L) :- !.
ord_intersection([_|_], [], [], []) :- !.
ord_intersection([H1|T1], [H2|T2], Intersection, Difference) :-
    compare(Diff, H1, H2),
    ord_intersection2(Diff, H1, T1, H2, T2, Intersection, Difference).

ord_intersection2(=, H1, T1, _H2, T2, [H1|T], Difference) :-
    ord_intersection(T1, T2, T, Difference).
ord_intersection2(<, _, T1, H2, T2, Intersection, Difference) :-
    ord_intersection(T1, [H2|T2], Intersection, Difference).
ord_intersection2(>, H1, T1, H2, T2, Intersection, [H2|HDiff]) :-
    ord_intersection([H1|T1], T2, Intersection, HDiff).


%% ord_add_element(+Set1, +Element, ?Set2) is det.
%
% Insert  an  element  into  the  set.    This   is  the  same  as
% `ord_union(Set1, [Element], Set2)`.

ord_add_element(Set1, Element, Set2) :-
    oset_addel(Set1, Element, Set2).


%% ord_del_element(+Set, +Element, -NewSet) is det.
%
% Delete an element from an  ordered  set.   This  is  the same as
% `ord_subtract(Set, [Element], NewSet)`.

ord_del_element(Set, Element, NewSet) :-
    oset_delel(Set, Element, NewSet).


%% ord_selectchk(+Item, ?Set1, ?Set2) is semidet.
%
% `selectchk/3`,  specialised  for  ordered  sets.    Is  true  when
% select(Item, Set1, Set2) and Set1, Set2   are  both sorted lists
% without duplicates. This implementation is only expected to work
% for Item ground and either Set1 or Set2 ground. The "chk" suffix
% is meant to remind you of   `memberchk/2`,  which also expects its
% first  argument  to  be  ground.    `ord_selectchk(X,  S,  T)  =>
% ord_memberchk(X, S) & \+ ord_memberchk(X, T).`
%
% Author: Richard O'Keefe

ord_selectchk(Item, [X|Set1], [X|Set2]) :-
    X @< Item,
    !,
    ord_selectchk(Item, Set1, Set2).
ord_selectchk(Item, [Item|Set1], Set1) :-
    (   Set1 == []
    ->  true
    ;   Set1 = [Y|_]
    ->  Item @< Y
    ).


%% ord_memberchk(+Element, +OrdSet) is semidet.
%
% True if Element is a member of   OrdSet, compared using ==. Note
% that _enumerating_ elements of an ordered  set can be done using
% `member/2`.
%
% Some Prolog implementations also provide  `ord_member/2`, with the
% same semantics as `ord_memberchk/2`.  We   believe  that  having a
% semidet `ord_member/2` is unacceptably inconsistent with the \*\_chk
% convention.  Portable  code  should    use   `ord_memberchk/2`  or
% `member/2`.
%
% Author: Richard O'Keefe

ord_memberchk(Item, [X1,X2,X3,X4|Xs]) :-
    !,
    compare(R4, Item, X4),
    (   R4 = (>) -> ord_memberchk(Item, Xs)
    ;   R4 = (<) ->
        compare(R2, Item, X2),
        (   R2 = (>) -> Item == X3
        ;   R2 = (<) -> Item == X1
        ;/* R2 = (=),   Item == X2 */ true
        )
    ;/* R4 = (=) */ true
    ).
ord_memberchk(Item, [X1,X2|Xs]) :-
    !,
    compare(R2, Item, X2),
    (   R2 = (>) -> ord_memberchk(Item, Xs)
    ;   R2 = (<) -> Item == X1
    ;/* R2 = (=) */ true
    ).
ord_memberchk(Item, [X1]) :-
    Item == X1.


%% ord_subset(+Sub, +Super) is semidet.
%
% Is true if all elements of Sub are in Super

ord_subset([], _).
ord_subset([H1|T1], [H2|T2]) :-
    compare(Order, H1, H2),
    ord_subset_(Order, H1, T1, T2).

ord_subset_(>, H1, T1, [H2|T2]) :-
    compare(Order, H1, H2),
    ord_subset_(Order, H1, T1, T2).
ord_subset_(=, _, T1, T2) :-
    ord_subset(T1, T2).


%% ord_subtract(+InOSet, +NotInOSet, -Diff) is det.
%
% Diff is the set holding all elements of InOSet that are not in
% NotInOSet.

ord_subtract(InOSet, NotInOSet, Diff) :-
    oset_diff(InOSet, NotInOSet, Diff).


%% ord_union(+SetOfSets, -Union) is det.
%
% True if Union is the  union  of   all  elements  in the superset
% SetOfSets. Each member of SetOfSets must  be an ordered set, the
% sets need not be ordered in any way.

ord_union([], []).
ord_union([Set|Sets], Union) :-
    length([Set|Sets], NumberOfSets),
    ord_union_all(NumberOfSets, [Set|Sets], Union, []).

ord_union_all(N, Sets0, Union, Sets) :-
    (   N =:= 1
    ->  Sets0 = [Union|Sets]
    ;   N =:= 2
    ->  Sets0 = [Set1,Set2|Sets],
        ord_union(Set1,Set2,Union)
    ;   A is N>>1,
        Z is N-A,
        ord_union_all(A, Sets0, X, Sets1),
        ord_union_all(Z, Sets1, Y, Sets),
        ord_union(X, Y, Union)
    ).


%% ord_union(+Set1, +Set2, ?Union) is det.
%
% Union is the union of Set1 and Set2

ord_union(Set1, Set2, Union) :-
    oset_union(Set1, Set2, Union).


%% ord_union(+Set1, +Set2, -Union, -New) is det.
%
% True iff `ord_union(Set1, Set2, Union)` and
% `ord_subtract(Set2, Set1, New)`.

ord_union([], Set2, Set2, Set2).
ord_union([H|T], Set2, Union, New) :-
    ord_union_1(Set2, H, T, Union, New).

ord_union_1([], H, T, [H|T], []).
ord_union_1([H2|T2], H, T, Union, New) :-
    compare(Order, H, H2),
    ord_union(Order, H, T, H2, T2, Union, New).

ord_union(<, H, T, H2, T2, [H|Union], New) :-
    ord_union_2(T, H2, T2, Union, New).
ord_union(>, H, T, H2, T2, [H2|Union], [H2|New]) :-
    ord_union_1(T2, H, T, Union, New).
ord_union(=, H, T, _, T2, [H|Union], New) :-
    ord_union(T, T2, Union, New).

ord_union_2([], H2, T2, [H2|T2], [H2|T2]).
ord_union_2([H|T], H2, T2, Union, New) :-
    compare(Order, H, H2),
    ord_union(Order, H, T, H2, T2, Union, New).


%% ord_symdiff(+Set1, +Set2, ?Difference) is det.
%
% Is true when Difference is the  symmetric difference of Set1 and
% Set2. I.e., Difference contains all elements that are not in the
% intersection of Set1 and Set2. The semantics  is the same as the
% sequence below (but the actual   implementation  requires only a
% single scan).
%
% ```
% ord_union(Set1, Set2, Union),
% ord_intersection(Set1, Set2, Intersection),
% ord_subtract(Union, Intersection, Difference).
% ```
%
% For example:
%
% ```
% ?- ord_symdiff([1,2], [2,3], X).
% X = [1,3].
% ```

ord_symdiff([], Set2, Set2).
ord_symdiff([H1|T1], Set2, Difference) :-
    ord_symdiff(Set2, H1, T1, Difference).

ord_symdiff([], H1, T1, [H1|T1]).
ord_symdiff([H2|T2], H1, T1, Difference) :-
    compare(Order, H1, H2),
    ord_symdiff(Order, H1, T1, H2, T2, Difference).

ord_symdiff(<, H1, Set1, H2, T2, [H1|Difference]) :-
    ord_symdiff(Set1, H2, T2, Difference).
ord_symdiff(=, _, T1, _, T2, Difference) :-
    ord_symdiff(T1, T2, Difference).
ord_symdiff(>, H1, T1, H2, Set2, [H2|Difference]) :-
    ord_symdiff(Set2, H1, T1, Difference).

/* The osets library on which ordsets depends.

 Author:        Jon Jagger
    E-mail:        J.R.Jagger@shu.ac.uk
    Copyright (c)  1993-2011, Jon Jagger
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


/* Ordered set manipulation

This library defines set operations on sets represented as ordered
lists.

@author Jon Jagger
@deprecated Use the de-facto library ordsets.pl
*/


%% oset_is(+OSet)
%   check that OSet in correct format (standard order)

oset_is(-) :- !, fail.    % var filter
oset_is([]).
oset_is([H|T]) :-
    oset_is(T, H).

oset_is(-, _) :- !, fail.  % var filter
oset_is([], _H).
oset_is([H|T], H0) :-
    H0 @< H,               % use standard order
    oset_is(T, H).



%% oset_union(+OSet1, +OSet2, -Union).

oset_union([], Union, Union).
oset_union([H1|T1], L2, Union) :-
    union2(L2, H1, T1, Union).

union2([], H1, T1, [H1|T1]).
union2([H2|T2], H1, T1, Union) :-
    compare(Order, H1, H2),
    union3(Order, H1, T1, H2, T2, Union).

union3(<, H1, T1,  H2, T2, [H1|Union]) :-
    union2(T1, H2, T2, Union).
union3(=, H1, T1, _H2, T2, [H1|Union]) :-
    oset_union(T1, T2, Union).
union3(>, H1, T1,  H2, T2, [H2|Union]) :-
    union2(T2, H1, T1, Union).


%% oset_int(+OSet1, +OSet2, -Int)
%   ordered set intersection

oset_int([], _Int, []).
oset_int([H1|T1], L2, Int) :-
    isect2(L2, H1, T1, Int).

isect2([], _H1, _T1, []).
isect2([H2|T2], H1, T1, Int) :-
    compare(Order, H1, H2),
    isect3(Order, H1, T1, H2, T2, Int).

isect3(<, _H1, T1,  H2, T2, Int) :-
    isect2(T1, H2, T2, Int).
isect3(=, H1, T1, _H2, T2, [H1|Int]) :-
    oset_int(T1, T2, Int).
isect3(>, H1, T1,  _H2, T2, Int) :-
    isect2(T2, H1, T1, Int).


%% oset_diff(+InOSet, +NotInOSet, -Diff)
%   ordered set difference

oset_diff([], _Not, []).
oset_diff([H1|T1], L2, Diff) :-
    diff21(L2, H1, T1, Diff).

diff21([], H1, T1, [H1|T1]).
diff21([H2|T2], H1, T1, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1, T1, H2, T2, Diff).

diff12([], _H2, _T2, []).
diff12([H1|T1], H2, T2, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1, T1, H2, T2, Diff).

diff3(<,  H1, T1,  H2, T2, [H1|Diff]) :-
    diff12(T1, H2, T2, Diff).
diff3(=, _H1, T1, _H2, T2, Diff) :-
    oset_diff(T1, T2, Diff).
diff3(>,  H1, T1, _H2, T2, Diff) :-
    diff21(T2, H1, T1, Diff).


%% oset_dunion(+SetofSets, -DUnion)
%   distributed union

oset_dunion([], []).
oset_dunion([H|T], DUnion) :-
    oset_dunion(T, H, DUnion).

oset_dunion([], DUnion, DUnion).
oset_dunion([H|T], DUnion0, DUnion) :-
    oset_union(H, DUnion0, DUnion1),
    oset_dunion(T, DUnion1, DUnion).


%% oset_dint(+SetofSets, -DInt)
%   distributed intersection

oset_dint([], []).
oset_dint([H|T], DInt) :-
    dint(T, H, DInt).

dint([], DInt, DInt).
dint([H|T], DInt0, DInt) :-
    oset_int(H, DInt0, DInt1),
    dint(T, DInt1, DInt).


%!  oset_power(+Set, -PSet)
%
%   True when PSet is the powerset of Set. That is, Pset is a set of
%   all subsets of Set, where each subset is a proper ordered set.

oset_power(S, PSet) :-
    reverse(S, R),
    pset(R, [[]], PSet0),
    sort(PSet0, PSet).


% The powerset of a set  is  the  powerset   of  a  set  of one smaller,
% together with the set of one  smaller   where  each subset is extended
% with the new element.  Note that this produces the elements of the set
% in reverse order.  Hence the reverse in oset_power/2.

pset([], PSet, PSet).
pset([H|T], PSet0, PSet) :-
    happ(PSet0, H, PSet1),
    pset(T, PSet1, PSet).

happ([], _, []).
happ([S|Ss], H, [[H|S],S|Rest]) :-
    happ(Ss, H, Rest).

%% oset_addel(+Set, +El, -Add)
%   ordered set element addition

oset_addel([], El, [El]).
oset_addel([H|T], El, Add) :-
    compare(Order, H, El),
    addel(Order, H, T, El, Add).

addel(<, H, T,  El, [H|Add]) :-
    oset_addel(T, El, Add).
addel(=, H, T, _El, [H|T]).
addel(>, H, T,  El, [El,H|T]).

%% oset_delel(+Set, +El, -Del)
%   ordered set element deletion

oset_delel([], _El, []).
oset_delel([H|T], El, Del) :-
    compare(Order, H, El),
    delel(Order, H, T, El, Del).

delel(<,  H, T,  El, [H|Del]) :-
    oset_delel(T, El, Del).
delel(=, _H, T, _El, T).
delel(>,  H, T, _El, [H|T]).
