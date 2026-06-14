:- dynamic(foo/1).

test :-
   current_predicate(foo/1).

?- test.
   false, unexpected.
   true.