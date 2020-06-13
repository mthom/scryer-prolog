/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   SICStus implementation of the Minato task.
   Written Sept. 2017 by Markus Triska (triska@metalevel.at)
   Public domain code.

   For more information, please see:

   https://www.metalevel.at/prolog/attributedvariables
   ===================================================

   A ZDD node is either:

       -) a *leaf* of the form b(true) or b(false)
       -) an *inner node* of the form ( Var -> Then ; Else ).

   In ZDDs, variables that are *not* encountered on a path to TRUE
   must be 0.

   This module exports a single predicate:

   * variables_set_zdd(Vs, ZDD)

   It associates each variable in Vs with the given ZDD. For each
   variable, the ZDD is stored as an attribute zdd_vs(ZDD, Vs).  This
   lets us reason about all variables that originally occurred.

   The internal unification hooks must be implemented so that only
   admissible assignments of truth variables to variables succeed.

   In particular, the Minato task:

   ?- ZDD = ( X -> b(true) ; ( Y -> b(true) ; b(false) ) ),
      Vs = [X,Y],
      variables_set_zdd(Vs, ZDD),
      Vs = [1,1].

           no

   Other examples:

   ?- ZDD = ( X -> b(true) ; ( Y -> b(true) ; b(false) ) ),
      Vs = [X,Y],
      variables_set_zdd(Vs, ZDD),
      X = 1.

           X = 1,
           Y = 0,
           Vs = [1,0] ? ;


   ?- ZDD = ( X -> b(true) ; ( Y -> b(true) ; b(false) ) ),
      Vs = [X,Y],
      variables_set_zdd(Vs, ZDD),
      X = 0.

           X = 0,
           Vs = [0,Y] ? ;

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(zdd, [variables_set_zdd/2]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).

:- attribute zdd_vs/2.

variables_set_zdd(Vs, ZDD) :-
        maplist(set_zdd(ZDD, Vs), Vs).

set_zdd(ZDD, Vs, V) :-
        put_atts(V, +zdd_vs(ZDD, Vs)).


verify_attributes(Var, Value, Goals) :-
        (   get_atts(Var, +zdd_vs(ZDD0,Vs)) ->
            (   integer(Value) ->
                zdd_restriction(ZDD0, Var, Value, ZDD)
            ;   throw(aliasing_not_implemented)
            ),
            phrase(remaining_vars_0(ZDD, Var, Vs), Goals)
        ;   Goals = []
        ).

remaining_vars_0(b(true), Var, Vs) --> all_others_0(Vs, Var).
remaining_vars_0((_;_), _, _) --> [].

all_others_0([], _) --> [].
all_others_0([V|Vs], Var) -->
        (   { var(V), V \== Var } -> [V=0]
        ;   []
        ),
        all_others_0(Vs, Var).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Compute the *restriction* of the ZDD.
   This means that Var has been instantiated to Value.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

zdd_restriction(b(T), _, _, b(T)).
zdd_restriction(( Var0 -> Then0 ; Else0), Var, Value, ZDD) :-
        (   Var0 == Var ->
            (   Value =:= 0 -> ZDD = Else0
            ;   Value =:= 1 -> ZDD = Then0
            ;   throw(no_boolean)
            )
        ;   zdd_restriction(Then0, Var, Value, Then),
            zdd_restriction(Else0, Var, Value, Else),
            ZDD = ( Var0 -> Then ; Else )
        ).
