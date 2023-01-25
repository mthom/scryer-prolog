/** Reasoning about pairs.

    Pairs are Prolog terms with principal functor `(-)/2`. A pair
    often has the form `Key-Value`. The predicates of this library
    relate pairs to keys and values.
*/

:- module(pairs, [pairs_keys_values/3,
		  pairs_keys/2,
		  pairs_values/2,
		  group_pairs_by_key/2,
		  map_list_to_pairs/3]).


:- meta_predicate map_list_to_pairs(2, ?, ?).

%% pairs_keys_values(?Pairs, ?Keys, ?Values)
%
%  The first argument is a list of Pairs, the second the corresponding
%  Keys, and the third argument the corresponding values.

pairs_keys_values([], [], []).
pairs_keys_values([A-B|ABs], [A|As], [B|Bs]) :-
        pairs_keys_values(ABs, As, Bs).

%% pairs_keys(?Pairs, ?Keys)
%
%  Same as `pairs_keys_values(Pairs, Keys, _)`.

pairs_keys(Ps, Ks) :- pairs_keys_values(Ps, Ks, _).

%% pairs_values(?Pairs, ?Values)
%
%  Same as `pairs_keys_values(Pairs, _, Values)`.

pairs_values(Ps, Vs) :- pairs_keys_values(Ps, _, Vs).

map_list_to_pairs(Pred, Ls, Ps) :-
        map_list_to_pairs2(Ls, Pred, Ps).

map_list_to_pairs2([], _, []).
map_list_to_pairs2([H|T0], Pred, [K-H|T]) :-
        call(Pred, H, K),
        map_list_to_pairs2(T0, Pred, T).


group_pairs_by_key([], []).
group_pairs_by_key([K-V|KVs0], [K-[V|Vs]|KVs]) :-
        same_key(K, KVs0, Vs, KVs1),
        group_pairs_by_key(KVs1, KVs).

same_key(K0, [K1-V|KVs0], [V|Vs], KVs) :-
        K0 == K1, !,
        same_key(K0, KVs0, Vs, KVs).
same_key(_, KVs, [], KVs).
