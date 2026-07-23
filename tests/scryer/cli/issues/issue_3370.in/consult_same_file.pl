a :- b.
a1 :- b(1).

test :-
   current_predicate(a/0),
   current_predicate(a1/0),
   \+ current_predicate(b/0),
   \+ current_predicate(b/1).

?- test.
   false, unexpected.
   true.