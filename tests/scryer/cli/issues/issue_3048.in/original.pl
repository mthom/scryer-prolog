:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).

put([_], _).
put([Old, New | Tail], Idx) :-
  put_assoc(Idx, Old, 1, New),
  IdxP is Idx +1,
  put([New |Tail], IdxP).

run(Max, Bad) :- 
  empty_assoc(A),
  length(As, Max),
  put([A|As], 1),
  findall(Idx, (nth0(Idx, [A|As], Assoc), \+ is_assoc(Assoc)), Bad).


?- N = 20, run(N, Bad).
   N = 20, Bad = [3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20], unexpected
   ; false.
   N = 20, Bad = []
   ; false.

test :- run(20, []).
