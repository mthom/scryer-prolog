:- use_module(library(assoc)).

test :-
  empty_assoc(A1),
  put_assoc(([a]-1), A1, 1, A2),
  put_assoc(([a]-2), A2, 1, A3),
  put_assoc(([b]-1), A3, 1, _).
  

?- test.
   false, unexpected.
   true.
