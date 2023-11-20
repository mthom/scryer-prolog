/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2018-2023 by Markus Triska (triska@metalevel.at)
   I place this code in the public domain. Use it in any way you want.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(error, [must_be/2,
                  can_be/2,
                  instantiation_error/1,
                  domain_error/3,
                  type_error/3
                  ]).


:- meta_predicate check_(1, ?, ?).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   must_be(Type, Term)

   This predicate is intended for type-checks of built-in predicates.

   It asserts that Term is:

       1) instantiated *and*
       2) instantiated to an instance of the given Type.

   It corresponds to usage mode +Term.

   Currently, the following types are supported:

       - atom
       - boolean
       - character
       - chars
       - in_character
       - integer
       - list
       - octet_character
       - octet_chars
       - term
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

must_be(Type, Term) :-
        must_be_(type, Type),
        must_be_(Type, Term).

must_be_(Type, _) :-
        var(Type),
        instantiation_error(must_be/2).
must_be_(var, Term) :-
        (   var(Term) -> true
        ;   throw(error(uninstantiation_error(Term), must_be/2))
        ).
must_be_(integer, Term) :- check_(integer, integer, Term).
must_be_(not_less_than_zero, N) :-
        must_be(integer, N),
        (   N >= 0 -> true
        ;   domain_error(not_less_than_zero, N, must_be/2)
        ).
must_be_(atom, Term)    :- check_(atom, atom, Term).
must_be_(character, T)  :- check_(error:character, character, T).
must_be_(in_character, T) :- check_(error:in_character, in_character, T).
must_be_(chars, Ls) :-
        can_be(chars, Ls), % prioritize type errors over instantiation errors
        must_be(list, Ls),
        (   '$is_partial_string'(Ls) ->
            % The expected case (success) uses a very fast test.
            % We cannot use partial_string/1 from library(iso_ext),
            % because that library itself imports library(error).
            true
        ;   all_characters(Ls)
        ).
must_be_(octet_character, C) :-
        must_be(character, C),
        (   octet_character(C) -> true
        ;   domain_error(octet_character, C, must_be/2)
        ).
must_be_(octet_chars, Cs) :-
        must_be(chars, Cs),
        (   '$first_non_octet'(Cs, C) ->
            domain_error(octet_character, C, must_be/2)
        ;   true
        ).
must_be_(list, Term)    :- check_(error:ilist, list, Term).
must_be_(type, Term)    :- check_(error:type, type, Term).
must_be_(boolean, Term) :- check_(error:boolean, boolean, Term).
must_be_(term, Term)    :-
        (   acyclic_term(Term) ->
            (   ground(Term) ->  true
            ;   instantiation_error(must_be/2)
            )
        ;   type_error(term, Term, must_be/2)
        ).

% We cannot use maplist(must_be(character), Cs), because library(lists)
% uses library(error), so importing it would create a cyclic dependency.

all_characters([]).
all_characters([C|Cs]) :-
        must_be(character, C),
        all_characters(Cs).

check_(Pred, Type, Term) :-
        (   var(Term) -> instantiation_error(must_be/2)
        ;   call(Pred, Term) -> true
        ;   type_error(Type, Term, must_be/2)
        ).

boolean(B) :- ( B == true ; B == false ).

character(C) :-
        atom(C),
        atom_length(C, 1).

octet_character(C) :-
        char_code(C, Code),
        0 =< Code, Code =< 0xff.

in_character(C) :-
        (   character(C)
        ;   C == end_of_file
        ).

ilist(Ls) :-
        '$skip_max_list'(_, _, Ls, Rs),
        (   var(Rs) ->
            instantiation_error(must_be/2)
        ;   Rs == []
        ).

type(type).
type(integer).
type(atom).
type(character).
type(in_character).
type(octet_character).
type(octet_chars).
type(chars).
type(list).
type(var).
type(boolean).
type(term).
type(not_less_than_zero).

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
can_(not_less_than_zero, N) :-
        (   integer(N) ->
            (   N >= 0 -> true
            ;   domain_error(not_less_than_zero, N, can_be/2)
            )
        ;   type_error(integer, N, can_be/2)
        ).
can_(atom, Term)    :- atom(Term).
can_(character, T)  :- character(T).
can_(in_character, T) :- in_character(T).
can_(chars, Ls)     :-
        (   '$is_partial_string'(Ls) -> true
        ;   can_be(list, Ls),
            can_be_chars(Ls)
        ).
can_(octet_character, C) :-
        (   octet_character(C) -> true
        ;   domain_error(octet_character, C, can_be/2)
        ).
can_(octet_chars, Cs) :-
        can_be(chars, Cs),
        (   '$skip_max_list'(_, _, Cs, []), % temporarily turn Cs into a list
            '$first_non_octet'(Cs, C) ->
            domain_error(octet_character, C, can_be/2)
        ;   true
        ).
can_(list, Term)    :- list_or_partial_list(Term).
can_(boolean, Term) :- boolean(Term).
can_(term, Term)    :-
        (   acyclic_term(Term) ->
            true
        ;   type_error(term, Term, can_be/2)
        ).

can_be_chars(Var) :- var(Var), !.
can_be_chars([]).
can_be_chars([X|Xs]) :-
        can_be(character, X),
        can_be_chars(Xs).

list_or_partial_list(Ls) :-
        '$skip_max_list'(_, _, Ls, Rs),
        (   var(Rs) -> true
        ;   Rs == []
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Shorthands for throwing ISO errors.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

instantiation_error(Context) :-
    throw(error(instantiation_error, Context)).

domain_error(Type, Term, Context) :-
    throw(error(domain_error(Type, Term), Context)).

type_error(Type, Term, Context) :-
    throw(error(type_error(Type, Term), Context)).
