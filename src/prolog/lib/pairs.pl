:- module(pairs, [pairs_keys_values/3,
		  pairs_keys/2,
		  pairs_values/2,
		  map_list_to_pairs/3]).


pairs_keys_values([], [], []).
pairs_keys_values([A-B|ABs], [A|As], [B|Bs]) :-
        pairs_keys_values(ABs, As, Bs).

pairs_keys(Ps, Ks) :- pairs_keys_values(Ps, Ks, _).

pairs_values(Ps, Vs) :- pairs_keys_values(Ps, _, Vs).

map_list_to_pairs(Pred, Ls, Ps) :-
        map_list_to_pairs2(Ls, Pred, Ps).

map_list_to_pairs2([], _, []).
map_list_to_pairs2([H|T0], Pred, [K-H|T]) :-
        call(Pred, H, K),
        map_list_to_pairs2(T0, Pred, T).
