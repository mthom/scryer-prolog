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
               list_si/1,
               char_si/1,
               string_si/1]).

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

char_si(Char) :-
   atom_si(Char),
   atom_length(Char, 1).

char_info_accumulator(Char, Uninstantiated0-NonChar0, Uninstantiated1-NonChar1) :-
    (   catch(
            (char_si(Char), Uninstantiated1 = Uninstantiated0),
            error(instantiation_error, _),
            Uninstantiated1 = true
        ) ->
        NonChar1 = NonChar0
    ;   NonChar1 = true
    ).

string_si(String) :-
    list_si(String),
    foldl(char_info_accumulator, String, false-false, Uninstantiated-false),
    (   Uninstantiated ->
        throw(error(instantiation_error, string_si/1))
    ;   true
    ).
