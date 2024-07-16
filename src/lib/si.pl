
/** Safe type tests.

   "si" stands for "sufficiently instantiated". It can also be read as
   "safe inference", so possibly also other predicates are candidates
   for this library.

   A safe type test:

    - throws an *instantiation error* if the argument is
      not sufficiently instantiated to make a sound decision
    - *succeeds* if the argument is of the specified type
    - *fails* otherwise.

   For instance, `atom_si(A)` yields an *instantiation error* if `A` is a
   variable. This is logically sound, since in that case the argument
   is not sufficiently instantiated to make any decision.

   The definitions are taken from [Safer type tests in Prolog](https://stackoverflow.com/questions/27306453/safer-type-tests-in-prolog).

   Examples:

```
?- chars_si(Cs).
   error(instantiation_error,list_si/1).
?- chars_si([h|Cs]).
   error(instantiation_error,list_si/1).
?- chars_si("hello").
   true.
?- chars_si(hello).
   false.
```
*/

:- module(si, [atom_si/1,
               integer_si/1,
               atomic_si/1,
               list_si/1,
               character_si/1,
               term_si/1,
               chars_si/1,
               dif_si/2,
               when_si/2]).

:- use_module(library(lists)).

atom_si(A) :-
   functor(A, _, 0),    % for the instantiation error
   atom(A).

integer_si(I) :-
   functor(I, _, 0),
   integer(I).

atomic_si(AC) :-
   functor(AC,_,0).

% list_si(L) :-
%    \+ \+ length(L, _),
%    sort(L, _).

list_si(L0) :-
   '$skip_max_list'(_,_, L0,L),
   (  nonvar(L) -> L = []
   ;  throw(error(instantiation_error, list_si/1))
   ).

character_si(Ch) :-
   functor(Ch,Ch,0),
   atom(Ch),
   atom_length(Ch,1).

term_si(Term) :-
   (   ground(Term) -> acyclic_term(Term)
   ;   throw(error(instantiation_error, term_si/1))
   ).

chars_si(Chs0) :-
   '$skip_max_list'(_,_, Chs0,Chs),
   ( nonvar(Chs) -> Chs == [] ; true ), % fails for infinite lists too
   failnochars(Chs0, Uninstantiated),
   (  nonvar(Uninstantiated)
   -> throw(error(instantiation_error, chars_si/1))
   ;  true
   ).

failnochars(Chs0, U) :-
   (  var(Chs0) -> U = true
   ;  Chs0 == [] -> true
   ;  Chs0 = [Ch|Chs1],
      (  nonvar(Ch) -> atom(Ch), atom_length(Ch,1)
      ;  U = true
      ),
      failnochars(Chs1, U)
   ).

dif_si(X, Y) :-
   X \== Y,
   ( X \= Y -> true
   ; throw(error(instantiation_error,dif_si/2))
   ).

:- meta_predicate(when_si(+, 0)).

%% when_si(Condition, Goal).
%
% Executes Goal when Condition becomes true. Throws an instantiation error if
% it can't decide.
when_si(Condition, Goal) :-
    % Taken from https://stackoverflow.com/a/40449516
    (   when_condition_si(Condition) ->
        (   Condition ->
            Goal
        ;   throw(error(instantiation_error,when_si/2))
        )
    ;   throw(error(domain_error(when_condition_si, Condition),_))
    ).

when_condition_si(Cond) :-
    var(Cond), !, throw(error(instantiation_error,when_condition_si/2)).
when_condition_si(ground(_)).
when_condition_si(nonvar(_)).
when_condition_si((A, B)) :-
    when_condition_si(A),
    when_condition_si(B).
when_condition_si((A ; B)) :-
    when_condition_si(A),
    when_condition_si(B).
