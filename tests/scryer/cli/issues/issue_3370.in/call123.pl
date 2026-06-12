test :- call(a), current_predicate(a/0).

?- test.
   true, unexpected.
   false.
