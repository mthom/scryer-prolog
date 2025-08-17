get_assoc(Key, t(K,V,_,L,R), Val) :-
    compare(Rel, Key, K),
    get_assoc(Rel, Key, V, L, R, Val).

get_assoc(=, _, Val, _, _, Val).
get_assoc(>, Key, _, _, Tree, Val) :- get_assoc(Key, Tree, Val).

test :- get_assoc("1"-'0', t("0"-'2',_, _, t(_,_,_,t,t), t("1"-'0',_,_,t,t)), _).

?- test.
   false, unexpected.
   true.
