/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

   Safe type tests
   ===============

   "si" stands for "sufficiently instantiated".

   These predicates:

    - throw instantiation errors if the argument is
      not sufficiently instantiated to make a sound decision
    - succeed if the argument is of the specified type
    - fail otherwise.

   For instance, atom_si(A) yields an *instantiation error* if A is a
   variable. This is logically sound, since in that case the argument
   is not sufficiently instantiated to make any decision.

   The definitions are taken from:

       https://stackoverflow.com/questions/27306453/safer-type-tests-in-prolog

   "si" can also be read as "safe inference", so possibly also other
   predicates are candidates for this library.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(si, [atom_si/1,
               integer_si/1,
               atomic_si/1,
               list_si/1]).

:- use_module(library(lists)).

atom_si(A) :-
   functor(A, _, 0),    % for the instantiation error
   atom(A).

integer_si(I) :-
   functor(I, _, 0),
   integer(I).

atomic_si(AC) :-
   functor(AC,_,0).

list_si(L) :-
   \+ \+ length(L, _),
   sort(L, _).
