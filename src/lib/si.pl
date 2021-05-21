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

   "si" can also be read as "sound inference" or "safe inference", so possibly
   also other predicates are candidates for this library.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(si, [atom_si/1,
               integer_si/1,
               atomic_si/1,
               char_si/1,
               list_si/1,
               maplist_si/2]).

:- use_module(library(lists)).

atom_si(A) :-
   functor(A, _, 0),    % for the instantiation error
   atom(A).

integer_si(I) :-
   functor(I, _, 0),
   integer(I).

atomic_si(AC) :-
   functor(AC,_,0).

char_si(Char) :-
   atom_si(Char),
   atom_length(Char, 1).

list_si(L) :-
   \+ \+ length(L, _),
   sort(L, _).

maplist_si(Cont1, List) :-
    list_si(List),
    maplist_success_inst0_inst1(Cont1, List, true, true, Instantiated),
    (   Instantiated ->
        true
    ;   throw(error(instantiation_error, maplist_si/2))
    ).

maplist_success_inst0_inst1(_, [], true, Instantiated, Instantiated).
maplist_success_inst0_inst1(Cont1, [E1|E1s], Success, Instantiated0, Instantiated) :-
    (   catch(
            (call(Cont1, E1), Instantiated1 = Instantiated0),
            error(instantiation_error, _),
            Instantiated1 = false
        ) ->
        maplist_success_inst0_inst1(Cont1, E1s, Success, Instantiated1, Instantiated)
    ;   Instantiated = Instantiated1,
        Success = false
    ).
