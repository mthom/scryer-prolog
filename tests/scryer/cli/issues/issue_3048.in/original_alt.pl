:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(between)).

p(Idx, Idx-1).

test(N) :- 
  numlist(N, As),
  maplist(p, As, Bs),
  list_to_assoc(Bs, Assoc),
  is_assoc(Assoc).

run(Max, Bad) :-
  numlist(Max, Num),
  findall(N, (member(N, [0|Num]), \+ test(N)), Bad).

?- N = 20, run(N, Bad).
   Bad = [3,4,6,7,8,9,10,12,13,14,15,16,17,18,19,20], unexpected.
   N = 20, Bad = [].

test :- run(20, []).
