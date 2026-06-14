a.
a(1).
a(1,2).
a(1,2,3,4).


test :-
   current_predicate(a/N),
   write(N),nl,
   false;
   true.