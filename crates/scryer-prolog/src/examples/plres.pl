/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written by Markus Triska, triska@metalevel.at, Sept. 5th 2006
   Public domain code.
   ----------------------------------------------------------------------

   Resolution calculus for propositional logic.

   For more information about theorem proving with Prolog, see:

   https://www.metalevel.at/prolog/theoremproving
   ==============================================

   Input is a formula in conjunctive normal form, represented as a
   list of clauses; clauses are lists of atoms and terms not/1.

   Example:

   ?- Clauses = [[p,not(q)], [not(p),not(s)], [s,not(q)], [q]],
      pl_resolution(Clauses, Rs),
      maplist(portray_clause, Rs).
   %@ [p, not(q)]-[not(p), not(s)] -->
   %@   [not(q), not(s)].
   %@ [s, not(q)]-[not(q), not(s)] -->
   %@   [not(q)].
   %@ [q]-[not(q)] -->
   %@   [].

   Iterative deepening is used to find a shortest refutation.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(format)).
:- use_module(library(lists)).

pl_resolution(Clauses0, Chain) :-
        maplist(sort, Clauses0, Clauses), % remove duplicates
        length(Chain, _),
        pl_derive_empty_clause(Chain, Clauses).

pl_derive_empty_clause([], Clauses) :-
        member([], Clauses).
pl_derive_empty_clause([C|Cs], Clauses) :-
        pl_resolvent(C, Clauses, Rs),
        pl_derive_empty_clause(Cs, [Rs|Clauses]).

pl_resolvent(((As0-Bs0) --> Rs), Clauses, Rs) :-
        member(As0, Clauses),
        member(Bs0, Clauses),
        select(Q, As0, As),
        select(not(Q), Bs0, Bs),
        append(As, Bs, Rs0),
        sort(Rs0, Rs), % remove duplicates
        maplist(dif(Rs), Clauses).
