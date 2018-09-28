:- module(error, [must_be/2, can_be/2]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written September 2018 by Markus Triska (triska@metalevel.at)
   I place this code in the public domain. Use it in any way you want.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   must_be(Type, Term)

   This predicate is intended for type-checks of built-in predicates.

   It asserts that Term is:

       1) instantiated *and*
       2) instantiated to an instance of the given Type.

   It corresponds to usage mode +Term.

   Currently, the following types are supported:

       - integer
       - atom
       - list.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

must_be(Type, Term) :-
        must_be_(Type, Term).


must_be_(Type, _) :-
        var(Type),
        instantiation_error(Type).
must_be_(integer, Term) :- check_(integer, integer, Term).
must_be_(atom, Term)    :- check_(atom, atom, Term).
must_be_(list, Term)    :- check_(ilist, list, Term).

check_(Pred, Type, Term) :-
        (   var(Term) -> instantiation_error(Term)
        ;   call(Pred, Term) -> true
        ;   type_error(Type, Term)
        ).

ilist(V) :- var(V), instantiation_error(V).
ilist([]).
ilist([_|Ls]) :- ilist(Ls).



/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   can_be(Type, Term)

   This predicate is intended for type-checks of built-in predicates.

   It asserts that:

       1) Term is either a variable or instantiated *and*
       2) _if_ it is instantiated, then it is an instance of Type.

   It corresponds to usage mode ?Term.

   It supports the same types as must_be/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


can_be(Type, Term) :-
        (   var(Term) -> true
        ;   must_be(Type, Term)
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Shorthands for throwing ISO errors.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

instantiation_error(_Term) :-
    throw(error(instantiation_error, _)).

domain_error(Type, Term) :-
    throw(error(domain_error(Type, Term), _)).

type_error(Type, Term) :-
    throw(error(type_error(Type, Term), _)).
