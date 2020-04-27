:- module(error, [must_be/2,
                  can_be/2,
                  instantiation_error/1,
                  domain_error/3,
                  type_error/3
                  ]).

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
        must_be_(type, Type),
        must_be_(Type, Term).

must_be_(Type, _) :-
        var(Type),
        instantiation_error(must_be/2).
must_be_(var, Term) :-
        (   var(Term) -> true
        ;   throw(error(uninstantiation_error, must_be/2))
        ).
must_be_(integer, Term) :- check_(integer, integer, Term).
must_be_(atom, Term)    :- check_(atom, atom, Term).
must_be_(list, Term)    :- check_(ilist, list, Term).
must_be_(type, Term)    :- check_(type, type, Term).

check_(Pred, Type, Term) :-
        (   var(Term) -> instantiation_error(must_be/2)
        ;   call(Pred, Term) -> true
        ;   type_error(Type, Term, must_be/2)
        ).

ilist(V) :- var(V), instantiation_error(must_be/2).
ilist([]).
ilist([_|Ls]) :- ilist(Ls).

type(type).
type(integer).
type(atom).
type(list).
type(var).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   can_be(Type, Term)

   This predicate is intended for type-checks of built-in predicates.

   It asserts that there is a substitution which, if applied to Term,
   makes it an instance of Type.

   It corresponds to usage mode ?Term.

   It supports the same types as must_be/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


can_be(Type, Term) :-
        must_be(type, Type),
        (   var(Term) -> true
        ;   can_(Type, Term) -> true
        ;   type_error(Type, Term, can_be/2)
        ).

can_(integer, Term) :- integer(Term).
can_(atom, Term)    :- atom(Term).
can_(list, Term)    :- list_or_partial_list(Term).

list_or_partial_list(Var) :- var(Var).
list_or_partial_list([]).
list_or_partial_list([_|Ls]) :-
        list_or_partial_list(Ls).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Shorthands for throwing ISO errors.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

instantiation_error(Context) :-
    throw(error(instantiation_error, Context)).

domain_error(Type, Term, Context) :-
    throw(error(domain_error(Type, Term), Context)).

type_error(Type, Term, Context) :-
    throw(error(type_error(Type, Term), Context)).
