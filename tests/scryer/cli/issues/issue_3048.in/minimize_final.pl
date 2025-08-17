a(t(K),K) :- ground(K).

test :- a(t(3), M), M=M.

?- test.
   true.
