/*  CLP(B): Constraint Logic Programming over Boolean Variables

    Author:        Markus Triska
    E-mail:        triska@metalevel.at
    WWW:           https://www.metalevel.at
    Copyright (C): 2019-2023 Markus Triska

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use, copy,
    modify, merge, publish, distribute, sublicense, and/or sell copies
    of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
    HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
    DEALINGS IN THE SOFTWARE.

*/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   CLP(B): Constraint Logic Programming over Boolean Variables.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Public operators.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(clpb, [op(300, fy, ~),
                 op(500, yfx, #),
                 sat/1,
                 taut/2,
                 labeling/1,
                 sat_count/2,
                 weighted_maximum/3,
                 random_labeling/2
                ]).

:- use_module(library(assoc)).
:- use_module(library(between)).
:- use_module(library(atts)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(random)).
:- use_module(library(pairs)).
:- use_module(library(dcgs)).
:- use_module(library(error), [domain_error/3, type_error/3]).

:- attribute
        clpb/1,
        clpb_bdd/1,
        clpb_atom/1,
        clpb_hash/1,
        clpb_max/1,
        clpb_omit_boolean/1,
        clpb_visited/1.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Compatibility predicates.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

must_be(What, Term) :- must_be(What, unknown(Term)-1, Term).

must_be(acyclic, Where, Term) :- !,
        (   acyclic_term(Term) ->
            true
        ;   domain_error(acyclic_term, Term, Where)
        ).
must_be(list, Where, Term) :- !,
        (   acyclic_term(Term), clpz_list(Term, Where) -> true
        ;   type_error(list, Term, Where)
        ).
must_be(list(What), Where, Term) :- !,
        must_be(list, Where, Term),
        maplist(must_be(What, Where), Term).
must_be(ground, _, Term) :- !,
        functor(Term, _, _).

must_be(Type, _, Term) :-
        error:must_be(Type, Term).

clpz_list(Nil, _) :- Nil == [].
clpz_list(Ls, Where) :-
    (   var(Ls) ->
        instantiation_error(Ls, Where)
    ;   Ls = [_|Rest],
        clpz_list(Rest, Where)
    ).


instantiation_error(Term) :- instantiation_error(Term, unknown(Term)-1).

instantiation_error(_, Goal-Arg) :-
	throw(error(instantiation_error, instantiation_error(Goal, Arg))).


domain_error(Expectation, Term) :-
        domain_error(Expectation, Term, unknown(Term)-1).


type_error(Expectation, Term) :-
        type_error(Expectation, Term, unknown(Term)-1).

partition(Pred, Ls0, As, Bs) :-
        include(Pred, Ls0, As),
        exclude(Pred, Ls0, Bs).

goal_expansion(get_attr(Var, Module, Value), (var(Var),get_atts(Var, Access))) :-
        Access =.. [Module,Value].

goal_expansion(put_attr(Var, Module, Value), put_atts(Var, Access)) :-
        Access =.. [Module,Value].

goal_expansion(del_attr(Var, Module), (var(Var) -> put_atts(Var, -Access);true)) :-
        Access =.. [Module,_].


/** Constraint Logic Programming over Boolean variables

## Introduction

This library provides CLP(B), Constraint Logic Programming over
Boolean variables. It can be used to model and solve combinatorial
problems such as verification, allocation and covering tasks.

CLP(B) is an instance of the general CLP(_X_) scheme,
extending logic programming with reasoning over specialised domains.

The implementation is based on reduced and ordered Binary Decision
Diagrams (BDDs).

Benchmarks and usage examples of this library are available from:
[*https://www.metalevel.at/clpb/*](https://www.metalevel.at/clpb/)

## Boolean expressions

A _Boolean expression_ is one of:

| `0`                | false                                |
| `1`                | true                                 |
| _variable_         | unknown truth value                  |
| _atom_             | universally quantified variable      |
| ~ _Expr_           | logical NOT                          |
| _Expr_ + _Expr_    | logical OR                           |
| _Expr_ * _Expr_    | logical AND                          |
| _Expr_ # _Expr_    | exclusive OR                         |
| _Var_ ^ _Expr_     | existential quantification           |
| _Expr_ =:= _Expr_  | equality                             |
| _Expr_ =\= _Expr_  | disequality (same as #)              |
| _Expr_ =< _Expr_   | less or equal (implication)          |
| _Expr_ >= _Expr_   | greater or equal                     |
| _Expr_ < _Expr_    | less than                            |
| _Expr_ > _Expr_    | greater than                         |
| card(Is,Exprs)     | cardinality constraint (_see below_) |
| `+(Exprs)`         | n-fold disjunction (_see below_)     |
| `*(Exprs)`         | n-fold conjunction (_see below_)     |

where _Expr_ again denotes a Boolean expression.

The Boolean expression `card(Is,Exprs)` is true iff the number of true
expressions in the list `Exprs` is a member of the list `Is` of
integers and integer ranges of the form `From-To`. For example, to
state that precisely two of the three variables `X`, `Y` and `Z` are
`true`, you can use `sat(card([2],[X,Y,Z]))`.

`+(Exprs)` and `*(Exprs)` denote, respectively, the disjunction and
conjunction of all elements in the list `Exprs` of Boolean
expressions.

Atoms denote parametric values that are universally quantified. All
universal quantifiers appear implicitly in front of the entire
expression. In residual goals, universally quantified variables always
appear on the right-hand side of equations. Therefore, they can be
used to express functional dependencies on input variables.

## Interface predicates

The most frequently used CLP(B) predicates are:

    * `sat(+Expr)`
      True iff the Boolean expression Expr is satisfiable.

    * `taut(+Expr, -T)`
      If Expr is a tautology with respect to the posted constraints, succeeds
      with *T = 1*. If Expr cannot be satisfied, succeeds with *T = 0*.
      Otherwise, it fails.

    * `labeling(+Vs)`
      Assigns truth values to the variables Vs such that all constraints
      are satisfied.

The unification of a CLP(B) variable _X_ with a term _T_ is equivalent
to posting the constraint sat(X=:=T).

## Examples

Here is an example session with a few queries and their answers:

```
?- use_module(library(clpb)).
   true.

?- sat(X*Y).
   X = 1, Y = 1.

?- sat(X * ~X).
   false.

?- taut(X * ~X, T).
   T = 0, clpb:sat(X=:=X).

?- sat(X^Y^(X+Y)).
   clpb:sat(X=:=X), clpb:sat(Y=:=Y).

?- sat(X*Y + X*Z), labeling([X,Y,Z]).
   X = 1, Y = 0, Z = 1
;  X = 1, Y = 1, Z = 0
;  X = 1, Y = 1, Z = 1.

?- sat(X =< Y), sat(Y =< Z), taut(X =< Z, T).
   T = 1, clpb:sat(X=:=X*Y), clpb:sat(Y=:=Y*Z).

?- sat(1#X#a#b).
   clpb:sat(X=:=a#b).
```

The pending residual goals constrain remaining variables to Boolean
expressions and are declaratively equivalent to the original query.
The last example illustrates that when applicable, remaining variables
are expressed as functions of universally quantified variables.

## Obtaining BDDs

By default, CLP(B) residual goals appear in (approximately) algebraic
normal form (ANF). This projection is often computationally expensive.
We can assert `clpb:clpb_residuals(bdd)` to see the BDD representation
of all constraints. This results in faster projection to residual
goals, and is also useful for learning more about BDDs. For example:

```
?- asserta(clpb:clpb_residuals(bdd)).
   true.

?- sat(X#Y).
node(3)- (v(X, 0)->node(2);node(1)),
node(1)- (v(Y, 1)->true;false),
node(2)- (v(Y, 1)->false;true).
```

Note that this representation cannot be pasted back on the toplevel,
and its details are subject to change. Use copy_term/3 to obtain
such answers as Prolog terms.

The variable order of the BDD is determined by the order in which the
variables first appear in constraints. To obtain different orders,
we can for example use:

```
?- sat(+[1,Y,X]), sat(X#Y).
node(3)- (v(Y, 0)->node(2);node(1)),
node(1)- (v(X, 1)->true;false),
node(2)- (v(X, 1)->false;true).
```

## Enabling monotonic CLP(B)

In the default execution mode, CLP(B) constraints are _not_ monotonic.
This means that _adding_ constraints can yield new solutions. For
example:

```
?-          sat(X=:=1), X = 1+0.
   false.

?- X = 1+0, sat(X=:=1), X = 1+0.
   X = 1+0.
```

This behaviour is highly problematic from a logical point of view, and
it may render [*declarative
debugging*](https://www.metalevel.at/prolog/debugging)
techniques inapplicable.

Assert `clpb:monotonic` to make CLP(B) *monotonic*. If this mode is
enabled, then you must wrap CLP(B) variables with the functor
`v/1`. For example:

```
?- asserta(clpb:monotonic).
   true.

?- sat(v(X)=:=1#1).
   X = 0.
```

## Example: Pigeons

In this example, we are attempting to place _I_ pigeons into _J_ holes
in such a way that each hole contains at most one pigeon. One
interesting property of this task is that it can be formulated using
only _cardinality constraints_ (`card/2`). Another interesting aspect
is that this task has no short resolution refutations in general.

In the following, we use [*Prolog DCG
notation*](https://www.metalevel.at/prolog/dcg) to describe a
list `Cs` of CLP(B) constraints that must all be satisfied.

```
:- use_module(library(clpb)).
:- use_module(library(clpz)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).

pigeon(I, J, Rows, Cs) :-
        length(Rows, I), length(Row, J),
        maplist(same_length(Row), Rows),
        transpose(Rows, TRows),
        phrase((all_cards(Rows,[1]),all_cards(TRows,[0,1])), Cs).

all_cards([], _) --> [].
all_cards([Ls|Lss], Cs) --> [card(Cs,Ls)], all_cards(Lss, Cs).
```

Example queries:

```
?- pigeon(9, 8, Rows, Cs), sat(*(Cs)).
   false.

?- pigeon(2, 3, Rows, Cs), sat(*(Cs)),
   append(Rows, Vs), labeling(Vs),
   maplist(portray_clause, Rows).
[0,0,1].
[0,1,0].
etc.
```

## Example: Boolean circuit

Consider a Boolean circuit that express the Boolean function =|XOR|=
with 4 =|NAND|= gates. We can model such a circuit with CLP(B)
constraints as follows:

```
:- use_module(library(clpb)).

nand_gate(X, Y, Z) :- sat(Z =:= ~(X*Y)).

xor(X, Y, Z) :-
        nand_gate(X, Y, T1),
        nand_gate(X, T1, T2),
        nand_gate(Y, T1, T3),
        nand_gate(T2, T3, Z).
```

Using universally quantified variables, we can show that the circuit
does compute =|XOR|= as intended:

```
?- xor(x, y, Z).
   clpb:sat(Z=:=x#y).
```

## Acknowledgments

The interface predicates of this library follow the example of
[*SICStus Prolog*](https://sicstus.sics.se).

Use SICStus Prolog for higher performance in many cases.

*/


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Each CLP(B) variable belongs to exactly one BDD. Each CLP(B)
   variable gets an attribute (in module "clpb") of the form:

        index_root(Index,Root)

   where Index is the variable's unique integer index, and Root is the
   root of the BDD that the variable belongs to.

   Each CLP(B) variable also gets an attribute in module clpb_hash: an
   association table node(LID,HID) -> Node, to keep the BDD reduced.
   The association table of each variable must be rebuilt on occasion
   to remove nodes that are no longer reachable. We rebuild the
   association tables of involved variables after BDDs are merged to
   build a new root. This only serves to reclaim memory: Keeping a
   node in a local table even when it no longer occurs in any BDD does
   not affect the solver's correctness. However, apply_shortcut/4
   relies on the invariant that every node that occurs in the relevant
   BDDs is also registered in the table of its branching variable.

   A root is a logical variable with a single attribute ("clpb_bdd")
   of the form:

        Sat-BDD

   where Sat is the SAT formula (in original form) that corresponds to
   BDD. Sat is necessary to rebuild the BDD after variable aliasing,
   and to project all remaining constraints to a list of sat/1 goals.

   Finally, a BDD is either:

      *)  The integers 0 or 1, denoting false and true, respectively, or
      *)  A node of the form

           node(ID, Var, Low, High, Aux)
               Where ID is the node's unique integer ID, Var is the
               node's branching variable, and Low and High are the
               node's low (Var = 0) and high (Var = 1) children. Aux
               is a free variable, one for each node, that can be used
               to attach attributes and store intermediate results.

   Variable aliasing is treated as a conjunction of corresponding SAT
   formulae.

   You should think of CLP(B) as a potentially vast collection of BDDs
   that can range from small to gigantic in size, and which can merge.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Type checking.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

is_sat(V)     :- var(V), !, non_monotonic(V).
is_sat(v(V))  :- var(V), !.
is_sat(v(I))  :- integer(I), between(0, 1, I).
is_sat(I)     :- integer(I), between(0, 1, I).
is_sat(A)     :- atom(A).
is_sat(~A)    :- is_sat(A).
is_sat(A*B)   :- is_sat(A), is_sat(B).
is_sat(A+B)   :- is_sat(A), is_sat(B).
is_sat(A#B)   :- is_sat(A), is_sat(B).
is_sat(A=:=B) :- is_sat(A), is_sat(B).
is_sat(A=\=B) :- is_sat(A), is_sat(B).
is_sat(A=<B)  :- is_sat(A), is_sat(B).
is_sat(A>=B)  :- is_sat(A), is_sat(B).
is_sat(A<B)   :- is_sat(A), is_sat(B).
is_sat(A>B)   :- is_sat(A), is_sat(B).
is_sat(+(Ls)) :- must_be(list, Ls), maplist(is_sat, Ls).
is_sat(*(Ls)) :- must_be(list, Ls), maplist(is_sat, Ls).
is_sat(X^F)   :- var(X), is_sat(F).
is_sat(card(Is,Fs)) :-
        must_be(list(ground), Is),
        must_be(list, Fs),
        maplist(is_sat, Fs).

:- dynamic(monotonic/0).

non_monotonic(X) :-
        (   var_index(X, _) ->
            % OK: already constrained to a CLP(B) variable
            true
        ;   monotonic ->
            instantiation_error(X)
        ;   true
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Rewriting to canonical expressions.
   Atoms are converted to variables with a special attribute.
   A global lookup table maintains the correspondence between atoms and
   their variables throughout different sat/1 goals.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

% elementary
sat_rewrite(V, V)       :- var(V), !.
sat_rewrite(I, I)       :- integer(I), !.
sat_rewrite(A, V)       :- atom(A), !, clpb_atom_var(A, V).
sat_rewrite(v(V), V).
sat_rewrite(P0*Q0, P*Q) :- sat_rewrite(P0, P), sat_rewrite(Q0, Q).
sat_rewrite(P0+Q0, P+Q) :- sat_rewrite(P0, P), sat_rewrite(Q0, Q).
sat_rewrite(P0#Q0, P#Q) :- sat_rewrite(P0, P), sat_rewrite(Q0, Q).
sat_rewrite(X^F0, X^F)  :- sat_rewrite(F0, F).
sat_rewrite(card(Is,Fs0), card(Is,Fs)) :-
        maplist(sat_rewrite, Fs0, Fs).
% synonyms
sat_rewrite(~P, R)      :- sat_rewrite(1 # P, R).
sat_rewrite(P =:= Q, R) :- sat_rewrite(~P # Q, R).
sat_rewrite(P =\= Q, R) :- sat_rewrite(P # Q, R).
sat_rewrite(P =< Q, R)  :- sat_rewrite(~P + Q, R).
sat_rewrite(P >= Q, R)  :- sat_rewrite(Q =< P, R).
sat_rewrite(P < Q, R)   :- sat_rewrite(~P * Q, R).
sat_rewrite(P > Q, R)   :- sat_rewrite(Q < P, R).
sat_rewrite(+(Ls), R)   :- foldl(or, Ls, 0, F), sat_rewrite(F, R).
sat_rewrite(*(Ls), R)   :- foldl(and, Ls, 1, F), sat_rewrite(F, R).

or(A, B, B + A).

and(A, B, B * A).

must_be_sat(Sat) :-
        must_be(acyclic, Sat),
        (   is_sat(Sat) -> true
        ;   no_truth_value(Sat)
        ).

no_truth_value(Term) :- domain_error(clpb_expr, Term).

parse_sat(Sat0, Sat) :-
        must_be_sat(Sat0),
        sat_rewrite(Sat0, Sat),
        term_variables(Sat, Vs),
        maplist(enumerate_variable, Vs).

enumerate_variable(V) :-
        (   var_index_root(V, _, _) -> true
        ;   clpb_next_id('$clpb_next_var', Index),
            put_attr(V, clpb, index_root(Index,_)),
            put_empty_hash(V)
        ).

var_index(V, I) :- var_index_root(V, I, _).

var_index_root(V, I, Root) :- get_attr(V, clpb, index_root(I,Root)).

put_empty_hash(V) :-
        empty_assoc(H0),
        put_attr(V, clpb_hash, H0).

sat_roots(Sat, Roots) :-
        term_variables(Sat, Vs),
        maplist(var_index_root, Vs, _, Roots0),
        term_variables(Roots0, Roots).

%% sat(+Expr) is semidet.
%
% True iff Expr is a satisfiable Boolean expression.

sat(Sat0) :-
        (   phrase(sat_ands(Sat0), Ands), Ands = [_,_|_] ->
            maplist(sat, Ands)
        ;   parse_sat(Sat0, Sat),
            sat_bdd(Sat, BDD),
            sat_roots(Sat, Roots),
            roots_and(Roots, Sat0-BDD, And-BDD1),
            maplist(del_bdd, Roots),
            maplist(=(Root), Roots),
            root_put_formula_bdd(Root, And, BDD1),
            is_bdd(BDD1),
            satisfiable_bdd(BDD1)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Posting many small sat/1 constraints is better than posting a huge
   conjunction (or negated disjunction), because unneeded nodes are
   removed from node tables after BDDs are merged. This is not
   possible in sat_bdd/2 because the nodes may occur in other BDDs. A
   better version of sat_bdd/2 or a proper implementation of a unique
   table including garbage collection would make this obsolete and
   also improve taut/2 and sat_count/2 in such cases.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

sat_ands(X) -->
        (   { var(X) } -> [X]
        ;   { X = (A*B) } -> sat_ands(A), sat_ands(B)
        ;   { X = *(Ls) } -> sat_ands_(Ls)
        ;   { X = ~Y } -> not_ors(Y)
        ;   [X]
        ).

sat_ands_([]) --> [].
sat_ands_([L|Ls]) --> [L], sat_ands_(Ls).

not_ors(X) -->
        (   { var(X) } -> [~X]
        ;   { X = (A+B) } -> not_ors(A), not_ors(B)
        ;   { X = +(Ls) } -> not_ors_(Ls)
        ;   [~X]
        ).

not_ors_([]) --> [].
not_ors_([L|Ls]) --> [~L], not_ors_(Ls).

del_bdd(Root) :- del_attr(Root, clpb_bdd).

root_get_formula_bdd(Root, F, BDD) :- get_attr(Root, clpb_bdd, F-BDD).

root_put_formula_bdd(Root, F, BDD) :- put_attr(Root, clpb_bdd, F-BDD).

roots_and(Roots, Sat0-BDD0, Sat-BDD) :-
        foldl(root_and, Roots, Sat0-BDD0, Sat-BDD),
        rebuild_hashes(BDD).

root_and(Root, Sat0-BDD0, Sat-BDD) :-
        (   root_get_formula_bdd(Root, F, B) ->
            Sat = F*Sat0,
            bdd_and(B, BDD0, BDD)
        ;   Sat = Sat0,
            BDD = BDD0
        ).

bdd_and(NA, NB, And) :-
        apply(*, NA, NB, And),
        is_bdd(And).

%% taut(+Expr, -T) is semidet
%
% Tautology check. Succeeds with T = 0 if the Boolean expression Expr
% cannot be satisfied, and with T = 1 if Expr is always true with
% respect to the current constraints. Fails otherwise.

taut(Sat0, T) :-
        parse_sat(Sat0, Sat),
        (   T = 0, \+ sat(Sat) -> true
        ;   T = 1, tautology(Sat) -> true
        ;   false
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   The algebraic equivalence: tautology(F) <=> \+ sat(~F) does NOT
   hold in CLP(B) because the quantifiers of universally quantified
   variables always implicitly appear in front of the *entire*
   expression. Thus we have for example: X+a is not a tautology, but
   ~(X+a), meaning forall(a, ~(X+a)), is unsatisfiable:

      sat(~(X+a)) = sat(~X * ~a) = sat(~X), sat(~a) = X=0, false

   The actual negation of X+a, namely ~forall(A,X+A), in terms of
   CLP(B): ~ ~exists(A, ~(X+A)), is of course satisfiable:

      ?- sat(~ ~A^ ~(X+A)).
      %@ X = 0,
      %@ sat(A=:=A).

   Instead, of such rewriting, we test whether the BDD of the negated
   formula is 0. Critically, this avoids constraint propagation.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

tautology(Sat) :-
        (   phrase(sat_ands(Sat), Ands), Ands = [_,_|_] ->
            maplist(tautology, Ands)
        ;   catch((sat_roots(Sat, Roots),
                   roots_and(Roots, _-1, _-Ands),
                   sat_bdd(1#Sat, BDD),
                   bdd_and(BDD, Ands, B),
                   B == 0,
                   % reset all attributes
                   throw(tautology)),
                  tautology,
                  true)
        ).

satisfiable_bdd(BDD) :-
        (   BDD == 0 -> false
        ;   BDD == 1 -> true
        ;   (   bdd_nodes(var_unbound, BDD, Nodes) ->
                bdd_variables_classification(BDD, Nodes, Classes),
                partition(var_class, Classes, Eqs, Bs, Ds),
                domain_consistency(Eqs, Goal),
                aliasing_consistency(Bs, Ds, Goals),
                maplist(unification, [Goal|Goals])
            ;   % if any variable is instantiated, we do not perform
                % any propagation for now
                true
            )
        ).

var_class(_=_, <).
var_class(further_branching(_,_), =).
var_class(negative_decisive(_), >).

unification(true).
unification(A=B) :- A = B.      % safe_goal/1 detects safety of this call

var_unbound(Node) :-
        node_var_low_high(Node, Var, _, _),
        var(Var).

universal_var(Var) :- get_attr(Var, clpb_atom, _).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   By aliasing consistency, we mean that all unifications X=Y, where
   taut(X=:=Y, 1) holds, are posted.

   To detect this, we distinguish two kinds of variables among those
   variables that are not skipped in any branch: further-branching and
   negative-decisive. X is negative-decisive iff every node where X
   appears as a branching variable has 0 as one of its children. X is
   further-branching iff 1 is not a direct child of any node where X
   appears as a branching variable.

   Any potential aliasing must involve one further-branching, and one
   negative-decisive variable. X=Y must hold if, for each low branch
   of nodes with X as branching variable, Y has high branch 0, and for
   each high branch of nodes involving X, Y has low branch 0.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

aliasing_consistency(Bs, Ds, Goals) :-
        phrase(aliasings(Bs, Ds), Goals).

aliasings([], _) --> [].
aliasings([further_branching(B,Nodes)|Bs], Ds) -->
        { var_index(B, BI) },
        aliasings_(Ds, B, BI, Nodes),
        aliasings(Bs, Ds).

aliasings_([], _, _, _) --> [].
aliasings_([negative_decisive(D)|Ds], B, BI, Nodes) -->
        { var_index(D, DI) },
        (   { DI > BI,
              always_false(high, DI, Nodes),
              always_false(low, DI, Nodes),
              var_or_atom(D, DA), var_or_atom(B, BA) } ->
            [DA=BA]
        ;   []
        ),
        aliasings_(Ds, B, BI, Nodes).

var_or_atom(Var, VA) :-
        (   get_attr(Var, clpb_atom, VA) -> true
        ;   VA = Var
        ).

always_false(Which, DI, Nodes) :-
        phrase(nodes_always_false(Nodes, Which, DI), Opposites),
        maplist(with_aux(unvisit), Opposites).

nodes_always_false([], _, _) --> [].
nodes_always_false([Node|Nodes], Which, DI) -->
        { which_node_child(Which, Node, Child),
          opposite(Which, Opposite) },
        opposite_always_false(Opposite, DI, Child),
        nodes_always_false(Nodes, Which, DI).

which_node_child(low, Node, Child) :-
        node_var_low_high(Node, _, Child, _).
which_node_child(high, Node, Child) :-
        node_var_low_high(Node, _, _, Child).

opposite(low, high).
opposite(high, low).

opposite_always_false(Opposite, DI, Node) -->
        (   { node_visited(Node) } -> []
        ;   { node_var_low_high(Node, Var, Low, High),
              with_aux(put_visited, Node),
              var_index(Var, VI) },
            [Node],
            (   { VI =:= DI } ->
                { which_node_child(Opposite, Node, Child),
                  Child == 0 }
            ;   opposite_always_false(Opposite, DI, Low),
                opposite_always_false(Opposite, DI, High)
            )
        ).

further_branching(Node) :-
        node_var_low_high(Node, _, Low, High),
        Low \== 1,
        High \== 1.

negative_decisive(Node) :-
        node_var_low_high(Node, _, Low, High),
        (   Low == 0 -> true
        ;   High == 0 -> true
        ;   false
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Instantiate all variables that only admit a single Boolean value.

   This is the case if: The variable is not skipped in any branch
   leading to 1 (its being skipped means that it may be assigned
   either 0 or 1 and can thus not be fixed yet), and all nodes where
   it occurs as a branching variable have either lower or upper child
   fixed to 0 consistently.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_consistency(Eqs, Goal) :-
        maplist(eq_a_b, Eqs, Vs, Values),
        Goal = (Vs = Values). % propagate all assignments at once

eq_a_b(A=B, A, B).

consistently_false_(Which, Node) :-
        which_node_child(Which, Node, Child),
        Child == 0.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   In essentially one sweep of the BDD, all variables can be classified:
   Unification with 0 or 1, further branching and/or negative decisive.

   Strategy: Breadth-first traversal of the BDD, failing (and thus
   clearing all attributes) if the variable is skipped in some branch,
   and moving the frontier along each time.

   A formula is only satisfiable if it is a tautology after all (also
   implicitly) existentially quantified variables are projected away.
   However, we only need to check this explicitly if at least one
   universally quantified variable appears. Otherwise, we know that
   the formula is satisfiable at this point, because its BDD is not 0.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

bdd_variables_classification(BDD, Nodes, Classes) :-
        nodes_variables(Nodes, Vs0),
        variables_in_index_order(Vs0, Vs),
        (   partition(universal_var, Vs, [_|_], Es) ->
            foldl(existential, Es, BDD, 1)
        ;   true
        ),
        phrase(variables_classification(Vs, [BDD]), Classes),
        maplist(with_aux(unvisit), Nodes).

variables_classification([], _) --> [].
variables_classification([V|Vs], Nodes0) -->
        { var_index(V, Index) },
        (   { phrase(nodes_with_variable(Nodes0, Index), Nodes) } ->
            (   { maplist(consistently_false_(low), Nodes) } -> [V=1]
            ;   { maplist(consistently_false_(high), Nodes) } -> [V=0]
            ;   []
            ),
            (   { maplist(further_branching, Nodes) } ->
                [further_branching(V, Nodes)]
            ;   []
            ),
            (   { maplist(negative_decisive, Nodes) } ->
                [negative_decisive(V)]
            ;   []
            ),
            { maplist(with_aux(unvisit), Nodes) },
            variables_classification(Vs, Nodes)
        ;   variables_classification(Vs, Nodes0)
        ).

nodes_with_variable([], _) --> [].
nodes_with_variable([Node|Nodes], VI) -->
        { Node \== 1 },
        (   { node_visited(Node) } -> nodes_with_variable(Nodes, VI)
        ;   { with_aux(put_visited, Node),
              node_var_low_high(Node, OVar, Low, High),
              var_index(OVar, OVI) },
            { OVI =< VI },
            (   { OVI =:= VI } -> [Node]
            ;   nodes_with_variable([Low,High], VI)
            ),
            nodes_with_variable(Nodes, VI)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Node management. Always use an existing node, if there is one.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

make_node(Var, Low, High, Node) :-
        (   Low == High -> Node = Low
        ;   low_high_key(Low, High, Key),
            (   lookup_node(Var, Key, Node) -> true
            ;   clpb_next_id('$clpb_next_node', ID),
                Node = node(ID,Var,Low,High,_Aux),
                register_node(Var, Key, Node)
            )
        ).

make_node(Var, Low, High, Node) -->
        % make it conveniently usable within DCGs
        { make_node(Var, Low, High, Node) }.


% The key of a node for hashing is determined by the IDs of its
% children.

low_high_key(Low, High, node(LID,HID)) :-
        node_id(Low, LID),
        node_id(High, HID).


rebuild_hashes(BDD) :-
        bdd_nodes(nodevar_put_empty_hash, BDD, Nodes),
        maplist(re_register_node, Nodes).

nodevar_put_empty_hash(Node) :-
        node_var_low_high(Node, Var, _, _),
        empty_assoc(H0),
        put_attr(Var, clpb_hash, H0).

re_register_node(Node) :-
        node_var_low_high(Node, Var, Low, High),
        low_high_key(Low, High, Key),
        register_node(Var, Key, Node).

register_node(Var, Key, Node) :-
        get_attr(Var, clpb_hash, H0),
        put_assoc(Key, H0, Node, H),
        put_attr(Var, clpb_hash, H).

lookup_node(Var, Key, Node) :-
        get_attr(Var, clpb_hash, H0),
        get_assoc(Key, H0, Node).


node_id(0, false).
node_id(1, true).
node_id(node(ID,_,_,_,_), ID).

node_aux(Node, Aux) :- arg(5, Node, Aux).

node_var_low_high(Node, Var, Low, High) :-
        Node = node(_,Var,Low,High,_).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   sat_bdd/2 converts a SAT formula in canonical form to an ordered
   and reduced BDD.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

sat_bdd(V, Node)           :- var(V), !, make_node(V, 0, 1, Node).
sat_bdd(I, I)              :- integer(I), !.
sat_bdd(V^Sat, Node)       :- !, sat_bdd(Sat, BDD), existential(V, BDD, Node).
sat_bdd(card(Is,Fs), Node) :- !, counter_network(Is, Fs, Node).
sat_bdd(Sat, Node)         :- !,
        Sat =.. [F,A,B],
        sat_bdd(A, NA),
        sat_bdd(B, NB),
        apply(F, NA, NB, Node).

existential(V, BDD, Node) :-
        var_index(V, Index),
        bdd_restriction(BDD, Index, 0, NA),
        bdd_restriction(BDD, Index, 1, NB),
        apply(+, NA, NB, Node).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Counter network for card(Is,Fs).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

counter_network(Cs, Fs, Node) :-
        same_length([_|Fs], Indicators),
        fill_indicators(Indicators, 0, Cs),
        phrase(formulas_variables(Fs, Vars0), ExBDDs),
        maplist(unvisit, Vars0),
        % The counter network is built bottom-up, so variables with
        % highest index must be processed first.
        variables_in_index_order(Vars0, Vars1),
        reverse(Vars1, Vars),
        counter_network_(Vars, Indicators, Node0),
        foldl(existential_and, ExBDDs, Node0, Node).

% Introduce fresh variables for expressions that are not variables.
% These variables are later existentially quantified to remove them.
% Also, new variables are introduced for variables that are used more
% than once, as in card([0,1],[X,X,Y]), to keep the BDD ordered.

formulas_variables([], []) --> [].
formulas_variables([F|Fs], [V|Vs]) -->
        (   { var(F), \+ is_visited(F) } ->
            { V = F,
              put_visited(F) }
        ;   { enumerate_variable(V),
              sat_rewrite(V =:= F, Sat),
              sat_bdd(Sat, BDD) },
            [V-BDD]
        ),
        formulas_variables(Fs, Vs).

counter_network_([], [Node], Node).
counter_network_([Var|Vars], [I|Is0], Node) :-
        foldl(indicators_pairing(Var), Is0, Is, I, _),
        counter_network_(Vars, Is, Node).

indicators_pairing(Var, I, Node, Prev, I) :- make_node(Var, Prev, I, Node).

fill_indicators([], _, _).
fill_indicators([I|Is], Index0, Cs) :-
        (   memberchk(Index0, Cs) -> I = 1
        ;   member(A-B, Cs), between(A, B, Index0) -> I = 1
        ;   I = 0
        ),
        Index1 is Index0 + 1,
        fill_indicators(Is, Index1, Cs).

existential_and(Ex-BDD, Node0, Node) :-
        bdd_and(BDD, Node0, Node1),
        existential(Ex, Node1, Node),
        % remove attributes to avoid residual goals for variables that
        % are only used as substitutes for formulas
        del_attrs(Ex).


del_attrs(Var) :-
        (    var(Var) ->
             put_atts(Var, [
                            -clpb(_),
                            -clpb_bdd(_),
                            -clpb_atom(_),
                            -clpb_hash(_),
                            -clpb_max(_),
                            -clpb_omit_boolean(_),
                            -clpb_visited(_)
                           ])
        ;   true
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Compute F(NA, NB).

   We use a DCG to thread through an implicit argument G0, an
   association table F(IDA,IDB) -> Node, used for memoization.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

apply(F, NA, NB, Node) :-
        empty_assoc(G0),
        phrase(apply(F, NA, NB, Node), [G0], _).

apply(F, NA, NB, Node) -->
        (   { integer(NA), integer(NB) } -> { once(bool_op(F, NA, NB, Node)) }
        ;   { apply_shortcut(F, NA, NB, Node) } -> []
        ;   { node_id(NA, IDA), node_id(NB, IDB), Key =.. [F,IDA,IDB] },
            (   state(G0), { get_assoc(Key, G0, Node) } -> []
            ;   apply_(F, NA, NB, Node),
                state(G0, G),
                { put_assoc(Key, G0, Node, G) }
            )
        ).

apply_shortcut(+, NA, NB, Node) :-
        (   NA == 0 -> Node = NB
        ;   NA == 1 -> Node = 1
        ;   NB == 0 -> Node = NA
        ;   NB == 1 -> Node = 1
        ;   false
        ).

apply_shortcut(*, NA, NB, Node) :-
        (   NA == 0 -> Node = 0
        ;   NA == 1 -> Node = NB
        ;   NB == 0 -> Node = 0
        ;   NB == 1 -> Node = NA
        ;   false
        ).


apply_(F, NA, NB, Node) -->
        { var_less_than(NA, NB),
          !,
          node_var_low_high(NA, VA, LA, HA) },
        apply(F, LA, NB, Low),
        apply(F, HA, NB, High),
        make_node(VA, Low, High, Node).
apply_(F, NA, NB, Node) -->
        { node_var_low_high(NA, VA, LA, HA),
          node_var_low_high(NB, VB, LB, HB),
          VA == VB },
        !,
        apply(F, LA, LB, Low),
        apply(F, HA, HB, High),
        make_node(VA, Low, High, Node).
apply_(F, NA, NB, Node) --> % NB < NA
        { node_var_low_high(NB, VB, LB, HB) },
        apply(F, NA, LB, Low),
        apply(F, NA, HB, High),
        make_node(VB, Low, High, Node).


node_varindex(Node, VI) :-
        node_var_low_high(Node, V, _, _),
        var_index(V, VI).

var_less_than(NA, NB) :-
        (   integer(NB) -> true
        ;   node_varindex(NA, VAI),
            node_varindex(NB, VBI),
            VAI < VBI
        ).

bool_op(+, 0, 0, 0).
bool_op(+, 0, 1, 1).
bool_op(+, 1, 0, 1).
bool_op(+, 1, 1, 1).

bool_op(*, 0, 0, 0).
bool_op(*, 0, 1, 0).
bool_op(*, 1, 0, 0).
bool_op(*, 1, 1, 1).

bool_op(#, 0, 0, 0).
bool_op(#, 0, 1, 1).
bool_op(#, 1, 0, 1).
bool_op(#, 1, 1, 0).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Access implicit state in DCGs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

state(S) --> state(S, S).

state(S0, S), [S] --> [S0].

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Unification. X = Expr is equivalent to sat(X =:= Expr).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

verify_attributes(Var, Other, Gs) :-
        % format("~w = ~w\n", [Var,Other]),
        (   get_attr(Var, clpb, index_root(I,Root)) ->
            (   integer(Other) ->
                (   between(0, 1, Other) ->
                    root_get_formula_bdd(Root, Sat, BDD0),
                    root_put_formula_bdd(Root, Sat, BDD),
                    Gs = [bdd_restriction(BDD0,I,Other,BDD),satisfiable_bdd(BDD)]
                ;   no_truth_value(Other)
                )
            ;   atom(Other) ->
                root_get_formula_bdd(Root, Sat0, _),
                Gs = [root_rebuild_bdd(Root, Sat0)]
            ;   % due to variable aliasing, any BDDs may become unordered,
                % so we need to rebuild the new BDD from the conjunction
                % after the unification is in place
                root_get_formula_bdd(Root, Sat0, _),
                Sat = Sat0*OtherSat,
                parse_sat(Other, OtherSat),
                sat_roots(Sat, Roots),
                phrase(formulas_(Roots), [F|Fs]),
                foldl(and, Fs, F, And),
                maplist(del_bdd, Roots),
                maplist(=(NewRoot), Roots),
                Gs = [root_rebuild_bdd(NewRoot, And)]
            )
        ;   Gs = []
        ).


formulas_([]) --> [].
formulas_([Root|Roots]) -->
        (   { root_get_formula_bdd(Root, F, _) } ->
            [F]
        ;   []
        ),
        formulas_(Roots).

root_rebuild_bdd(Root, Formula) :-
        parse_sat(Formula, Sat),
        sat_bdd(Sat, BDD),
        is_bdd(BDD),
        root_put_formula_bdd(Root, Formula, BDD),
        satisfiable_bdd(BDD).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Support for project_attributes/2.

   This is called by the toplevel as

      project_attributes(+QueryVars, +AttrVars)

   in order to project all remaining constraints onto QueryVars.

   All CLP(B) variables that do not occur in QueryVars
   need to be existentially quantified, so that they do not occur in
   residual goals. This is very easy to do in the case of CLP(B).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

project_attributes(QueryVars0, _) :-
        include(clpb_variable, QueryVars0, QueryVars),
        maplist(var_index_root, QueryVars, _, Roots0),
        sort(Roots0, Roots),
        maplist(remove_hidden_variables(QueryVars), Roots).

clpb_variable(Var) :- var_index(Var, _).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   All CLP(B) variables occurring in BDDs but not in query variables
   become existentially quantified. This must also be reflected in the
   formula. In addition, an attribute is attached to these variables
   to suppress superfluous sat(V=:=V) goals.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

remove_hidden_variables(QueryVars, Root) :-
        root_get_formula_bdd(Root, Formula, BDD0),
        maplist(put_visited, QueryVars),
        bdd_variables(BDD0, HiddenVars0),
        exclude(universal_var, HiddenVars0, HiddenVars),
        maplist(unvisit, QueryVars),
        foldl(existential, HiddenVars, BDD0, BDD),
        foldl(quantify_existantially, HiddenVars, Formula, ExFormula),
        root_put_formula_bdd(Root, ExFormula, BDD).

quantify_existantially(E, E0, E^E0) :- put_attr(E, clpb_omit_boolean, true).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   BDD restriction.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

bdd_restriction(Node, VI, Value, Res) :-
        empty_assoc(G0),
        phrase(bdd_restriction_(Node, VI, Value, Res), [G0], _),
        is_bdd(Res).

bdd_restriction_(Node, VI, Value, Res) -->
        (   { integer(Node) } -> { Res = Node }
        ;   { node_var_low_high(Node, Var, Low, High) } ->
            (   { integer(Var) } ->
                (   { Var =:= 0 } -> bdd_restriction_(Low, VI, Value, Res)
                ;   { Var =:= 1 } -> bdd_restriction_(High, VI, Value, Res)
                ;   { no_truth_value(Var) }
                )
            ;   { var_index(Var, I0),
                  node_id(Node, ID) },
                (   { I0 =:= VI } ->
                    (   { Value =:= 0 } -> { Res = Low }
                    ;   { Value =:= 1 } -> { Res = High }
                    )
                ;   { I0 > VI } -> { Res = Node }
                ;   state(G0), { get_assoc(ID, G0, Res) } -> []
                ;   bdd_restriction_(Low, VI, Value, LRes),
                    bdd_restriction_(High, VI, Value, HRes),
                    make_node(Var, LRes, HRes, Res),
                    state(G0, G),
                    { put_assoc(ID, G0, Res, G) }
                )
            )
        ;   { domain_error(node, Node) }
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Relating a BDD to its elements (nodes and variables).

   Note that BDDs can become quite big (easily millions of nodes), and
   memory space is a major bottleneck for many problems. If possible,
   we therefore do not duplicate the entire BDD in memory (as in
   bdd_ites/2), but only extract its features as needed.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

bdd_nodes(BDD, Ns) :- bdd_nodes(ignore_node, BDD, Ns).

ignore_node(_).

% VPred is a unary predicate that is called for each node that has a
% branching variable (= each inner node).

bdd_nodes(VPred, BDD, Ns) :-
        phrase(bdd_nodes_(VPred, BDD), Ns),
        maplist(with_aux(unvisit), Ns).

bdd_nodes_(VPred, Node) -->
        (   { node_visited(Node) } -> []
        ;   { call(VPred, Node),
              with_aux(put_visited, Node),
              node_var_low_high(Node, _, Low, High) },
            [Node],
            bdd_nodes_(VPred, Low),
            bdd_nodes_(VPred, High)
        ).

node_visited(Node) :- integer(Node).
node_visited(Node) :- with_aux(is_visited, Node).

bdd_variables(BDD, Vs) :-
        bdd_nodes(BDD, Nodes),
        nodes_variables(Nodes, Vs).

nodes_variables(Nodes, Vs) :-
        phrase(nodes_variables_(Nodes), Vs),
        maplist(unvisit, Vs).

nodes_variables_([]) --> [].
nodes_variables_([Node|Nodes]) -->
        { node_var_low_high(Node, Var, _, _) },
        (   { integer(Var) } -> []
        ;   { is_visited(Var) } -> []
        ;   { put_visited(Var) },
            [Var]
        ),
        nodes_variables_(Nodes).

unvisit(V) :- del_attr(V, clpb_visited).

is_visited(V) :- get_attr(V, clpb_visited, true).

put_visited(V) :- put_attr(V, clpb_visited, true).

with_aux(Pred, Node) :-
        node_aux(Node, Aux),
        call(Pred, Aux).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Internal consistency checks.

   To enable these checks, assert clpb:validation/0.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- dynamic(validation/0).

is_bdd(BDD) :-
        (   validation ->
            bdd_ites(BDD, ITEs),
            pairs_values(ITEs, Ls0),
            sort(Ls0, Ls1),
            (   same_length(Ls0, Ls1) -> true
            ;   domain_error(reduced_ites, (ITEs,Ls0,Ls1))
            ),
            (   member(ITE, ITEs), \+ registered_node(ITE) ->
                domain_error(registered_node, ITE)
            ;   true
            ),
            (   member(I, ITEs), \+ clpb_ordered(I) ->
                domain_error(ordered_node, I)
            ;   true
            )
        ;   true
        ).

clpb_ordered(_-ite(Var,High,Low)) :-
        (   var_index(Var, VI) ->
            greater_varindex_than(High, VI),
            greater_varindex_than(Low, VI)
        ;   true
        ).

greater_varindex_than(Node, VI) :-
        (   integer(Node) -> true
        ;   node_var_low_high(Node, Var, _, _),
            (   var_index(Var, OI) ->
                OI > VI
            ;   true
            )
        ).

registered_node(Node-ite(Var,High,Low)) :-
        (   var(Var) ->
            low_high_key(Low, High, Key),
            lookup_node(Var, Key, Node0),
            Node == Node0
        ;   true
        ).

bdd_ites(BDD, ITEs) :-
        bdd_nodes(BDD, Nodes),
        maplist(node_ite, Nodes, ITEs).

node_ite(Node, Node-ite(Var,High,Low)) :-
        node_var_low_high(Node, Var, Low, High).

%% labeling(+Vs) is multi.
%
% Enumerate concrete solutions. Assigns truth values to the Boolean
% variables Vs such that all stated constraints are satisfied.

labeling(Vs0) :-
        must_be(list, Vs0),
        maplist(labeling_var, Vs0),
        variables_in_index_order(Vs0, Vs),
        maplist(indomain, Vs).

labeling_var(V) :- var(V), !.
labeling_var(V) :- V == 0, !.
labeling_var(V) :- V == 1, !.
labeling_var(V) :- domain_error(clpb_variable, V).

variables_in_index_order(Vs0, Vs) :-
        maplist(var_with_index, Vs0, IVs0),
        keysort(IVs0, IVs),
        pairs_values(IVs, Vs).

var_with_index(V, I-V) :-
        (   var_index_root(V, I, _) -> true
        ;   I = 0
        ).

indomain(0).
indomain(1).


%% sat_count(+Expr, -Count) is det.
%
% Count the number of admissible assignments. Count is the number of
% different assignments of truth values to the variables in the
% Boolean expression Expr, such that Expr is true and all posted
% constraints are satisfiable.
%
% A common form of invocation is `sat_count(+[1|Vs], Count)`: This
% counts the number of admissible assignments to `Vs` without imposing
% any further constraints.
%
% Examples:
%
% ```
% ?- sat(A =< B), Vs = [A,B], sat_count(+[1|Vs], Count).
%    Vs = [A,B], Count = 3, clpb:sat(A=:=A*B).
%
% ?- length(Vs, 120),
%    sat_count(+Vs, CountOr),
%    sat_count(*(Vs), CountAnd).
%    Vs = [...],
%    CountOr = 1329227995784915872903807060280344575,
%    CountAnd = 1.
% ```



sat_count(Sat0, N) :-
        catch((parse_sat(Sat0, Sat),
               sat_bdd(Sat, BDD),
               sat_roots(Sat, Roots),
               roots_and(Roots, _-BDD, _-BDD1),
               % we mark variables that occur in Sat0 as visited ...
               term_variables(Sat0, Vs),
               maplist(put_visited, Vs),
               % ... so that they do not appear in Vs1 ...
               bdd_variables(BDD1, Vs1),
               partition(universal_var, Vs1, Univs, Exis),
               % ... and then remove remaining variables:
               foldl(universal, Univs, BDD1, BDD2),
               foldl(existential, Exis, BDD2, BDD3),
               variables_in_index_order(Vs, IVs),
               foldl(renumber_variable, IVs, 1, VNum),
               bdd_count(BDD3, VNum, Count0),
               var_u(BDD3, VNum, P),
               % Do not unify N directly, because we are not prepared
               % for propagation here in case N is a CLP(B) variable.
               N0 is 2^(P - 1)*Count0,
               % reset all attributes and Aux variables
               throw(count(N0))),
              count(N0),
              N = N0).

universal(V, BDD, Node) :-
        var_index(V, Index),
        bdd_restriction(BDD, Index, 0, NA),
        bdd_restriction(BDD, Index, 1, NB),
        apply(*, NA, NB, Node).

renumber_variable(V, I0, I) :-
        put_attr(V, clpb, index_root(I0,_)),
        I is I0 + 1.

bdd_count(Node, VNum, Count) :-
        (   integer(Node) -> Count = Node
        ;   node_aux(Node, Count),
            (   integer(Count) -> true
            ;   node_var_low_high(Node, V, Low, High),
                bdd_count(Low, VNum, LCount),
                bdd_count(High, VNum, HCount),
                bdd_pow(Low, V, VNum, LPow),
                bdd_pow(High, V, VNum, HPow),
                Count is LPow*LCount + HPow*HCount
            )
        ).


bdd_pow(Node, V, VNum, Pow) :-
        var_index(V, Index),
        var_u(Node, VNum, P),
        Pow is 2^(P - Index - 1).

var_u(Node, VNum, Index) :-
        (   integer(Node) -> Index = VNum
        ;   node_varindex(Node, Index)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Pick a solution in such a way that each solution is equally likely.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% random_labeling(+Seed, +Vs) is det.
%
% Select a single random solution. An admissible assignment of truth
% values to the Boolean variables in Vs is chosen in such a way that
% each admissible assignment is equally likely. Seed is an integer,
% used as the initial seed for the random number generator.

single_bdd(Vars0) :-
        maplist(monotonic_variable, Vars0, Vars),
        % capture all variables with a single BDD
        sat(+[1|Vars]).

random_labeling(Seed, Vars) :-
        must_be(list, Vars),
        set_random(seed(Seed)),
        (   ground(Vars) -> true
        ;   catch((single_bdd(Vars),
                   once((member(Var, Vars),var(Var))),
                   var_index_root(Var, _, Root),
                   root_get_formula_bdd(Root, _, BDD),
                   bdd_variables(BDD, Vs),
                   variables_in_index_order(Vs, IVs),
                   foldl(renumber_variable, IVs, 1, VNum),
                   phrase(random_bindings(VNum, BDD), Bs),
                   maplist(del_attrs, Vs),
                   % reset all attribute modifications
                   throw(randsol(Vars, Bs))),
                  randsol(Vars, Bs),
                  true),
            maplist(call, Bs),
            % set remaining variables to 0 or 1 with equal probability
            include(var, Vars, Remaining),
            maplist(maybe_zero, Remaining)
        ).

maybe_zero(Var) :-
        (   maybe -> Var = 0
        ;   Var = 1
        ).

random_bindings(_, Node) --> { Node == 1 }, !.
random_bindings(VNum, Node) -->
        { node_var_low_high(Node, Var, Low, High),
          bdd_count(Node, VNum, Total),
          bdd_count(Low, VNum, LCount) },
        (   { maybe(LCount, Total) } ->
            [Var=0], random_bindings(VNum, Low)
        ;   [Var=1], random_bindings(VNum, High)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Find solutions with maximum weight.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% weighted_maximum(+Weights, +Vs, -Maximum) is multi.
%
% Enumerate weighted optima over admissible assignments. Maximize a
% linear objective function over Boolean variables Vs with integer
% coefficients Weights. This predicate assigns 0 and 1 to the
% variables in Vs such that all stated constraints are satisfied, and
% Maximum is the maximum of `sum(Weight_i*V_i)` over all admissible
% assignments.  On backtracking, all admissible assignments that
% attain the optimum are generated.
%
% This predicate can also be used to _minimize_ a linear Boolean
% program, since negative integers can appear in Weights.
%
% Example:
%
% ```
% ?- sat(A#B), weighted_maximum([1,2,1], [A,B,C], Maximum).
%    A = 0, B = 1, C = 1, Maximum = 3.
% ```

weighted_maximum(Ws, Vars, Max) :-
        must_be(list(integer), Ws),
        must_be(list(var), Vars),
        single_bdd(Vars),
        Vars = [Var|_],
        var_index_root(Var, _,  Root),
        root_get_formula_bdd(Root, _, BDD0),
        bdd_variables(BDD0, Vs),
        % existentially quantify variables that are not considered
        maplist(put_visited, Vars),
        exclude(is_visited, Vs, Unvisited),
        maplist(unvisit, Vars),
        foldl(existential, Unvisited, BDD0, BDD),
        maplist(var_with_index, Vars, IVs),
        pairs_keys_values(Pairs0, IVs, Ws),
        keysort(Pairs0, Pairs1),
        % sum linear combinations of repeated variables
        group_pairs_by_key(Pairs1, Groups),
        maplist(group_sumweights_pair, Groups, Pairs2),
        pairs_keys_values(Pairs2, IVs1, WeightsIndexOrder),
        pairs_values(IVs1, VarsIndexOrder),
        % Pairs is a list of Var-Weight terms, in index order of Vars
        pairs_keys_values(Pairs, VarsIndexOrder, WeightsIndexOrder),
        bdd_maximum(BDD, Pairs, Max),
        max_labeling(BDD, Pairs).

group_sumweights_pair((I-V)-Ws, (I-V)-W) :- sum_list(Ws, W).

max_labeling(1, Pairs) :- max_upto(Pairs, _, _).
max_labeling(node(_,Var,Low,High,Aux), Pairs0) :-
        max_upto(Pairs0, Var, Pairs),
        get_attr(Aux, clpb_max, max(_,Dir)),
        direction_labeling(Dir, Var, Low, High, Pairs).

max_upto([], _, _).
max_upto([Var0-Weight|VWs0], Var, VWs) :-
        (   Var == Var0 -> VWs = VWs0
        ;   Weight =:= 0 ->
            (   Var0 = 0 ; Var0 = 1 ),
            max_upto(VWs0, Var, VWs)
        ;   Weight < 0 -> Var0 = 0, max_upto(VWs0, Var, VWs)
        ;   Var0 = 1, max_upto(VWs0, Var, VWs)
        ).

direction_labeling(low, 0, Low, _, Pairs)   :- max_labeling(Low, Pairs).
direction_labeling(high, 1, _, High, Pairs) :- max_labeling(High, Pairs).

bdd_maximum(1, Pairs, Max) :-
        pairs_values(Pairs, Weights0),
        include(<(0), Weights0, Weights),
        sum_list(Weights, Max).
bdd_maximum(node(_,Var,Low,High,Aux), Pairs0, Max) :-
        (   get_attr(Aux, clpb_max, max(Max,_)) -> true
        ;   (   skip_to_var(Var, Weight, Pairs0, Pairs),
                (   Low == 0 ->
                    bdd_maximum_(High, Pairs, MaxHigh, MaxToHigh),
                    Max is MaxToHigh + MaxHigh + Weight,
                    Dir = high
                ;   High == 0 ->
                    bdd_maximum_(Low, Pairs, MaxLow, MaxToLow),
                    Max is MaxToLow + MaxLow,
                    Dir = low
                ;   bdd_maximum_(Low, Pairs, MaxLow, MaxToLow),
                    bdd_maximum_(High, Pairs, MaxHigh, MaxToHigh),
                    Max0 is MaxToLow + MaxLow,
                    Max1 is MaxToHigh + MaxHigh + Weight,
                    Max is max(Max0,Max1),
                    (   Max0 =:= Max1 -> Dir = _Any
                    ;   Max0 < Max1 -> Dir = high
                    ;   Dir = low
                    )
                ),
                store_maximum(Aux, Max, Dir)
            )
        ).

bdd_maximum_(Node, Pairs, Max, MaxTo) :-
	bdd_maximum(Node, Pairs, Max),
	between_weights(Node, Pairs, MaxTo).

store_maximum(Aux, Max, Dir) :- put_attr(Aux, clpb_max, max(Max,Dir)).

between_weights(Node, Pairs0, MaxTo) :-
        (   Node == 1 -> MaxTo = 0
        ;   node_var_low_high(Node, Var, _, _),
            phrase(skip_to_var_(Var, _, Pairs0, _), Weights0),
            include(<(0), Weights0, Weights),
            sum_list(Weights, MaxTo)
        ).

skip_to_var(Var, Weight, Pairs0, Pairs) :-
        phrase(skip_to_var_(Var, Weight, Pairs0, Pairs), _).

skip_to_var_(Var, Weight, [Var0-Weight0|VWs0], VWs) -->
        (   { Var == Var0 } ->
            { Weight = Weight0, VWs0 = VWs }
        ;   (   { Weight0 =< 0 } -> []
            ;   [Weight0]
            ),
            skip_to_var_(Var, Weight, VWs0, VWs)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Projection to residual goals.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


:- dynamic(clpb_residuals/1).

attribute_goals(Var) -->
        { var_index_root(Var, _, Root) },
        !,
        (   { root_get_formula_bdd(Root, Formula, BDD) } ->
            { del_bdd(Root) },
            (   { clpb_residuals(bdd) } ->
                { bdd_nodes(BDD, Nodes),
                  phrase(nodes(Nodes), Ns) },
                [clpb:'$clpb_bdd'(Ns)]
            ;   { prepare_global_variables(BDD),
                  phrase(sat_ands(Formula), Ands0),
                  ands_fusion(Ands0, Ands),
                  maplist(formula_anf, Ands, ANFs0),
                  sort(ANFs0, ANFs1),
                  exclude(eq_1, ANFs1, ANFs2),
                  variables_separation(ANFs2, ANFs) },
                sats(ANFs)
            ),
            (   { get_attr(Var, clpb_atom, Atom) } ->
                [clpb:sat(Var=:=Atom)]
            ;   []
            ),
            % formula variables not occurring in the BDD should be booleans
            { bdd_variables(BDD, Vs),
              maplist(del_clpb, Vs),
              term_variables(Formula, RestVs0),
              include(clpb_variable, RestVs0, RestVs) },
            booleans(RestVs)
        ;   boolean(Var)  % the variable may have occurred only in taut/2
        ).
attribute_goals(Var) -->
        { get_atts(Var, clpb_max(_)),
          !,
          put_atts(Var, -clpb_max(_)) }.
attribute_goals(Var) -->
        { get_atts(Var, clpb_bdd(BDD)),
          ground(BDD),
          put_atts(Var, -clpb_bdd(_)) }.

del_clpb(Var) :-
        del_attr(Var, clpb),
        del_attr(Var, clpb_hash).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   To make residual projection work with recorded constraints, the
   global counters must be adjusted so that new variables and nodes
   also get new IDs. Also, clpb_next_id/2 is used to actually create
   these counters, because creating them with b_setval/2 would make
   them [] on backtracking, which is quite unfortunate in itself.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

b_setval(K, T) :- bb_b_put(K, T).
nb_setval(K, T) :- bb_put(K, T).
b_getval(K, T) :- bb_get(K, T).

prepare_global_variables(BDD) :-
        clpb_next_id('$clpb_next_var', V0),
        clpb_next_id('$clpb_next_node', N0),
        bdd_nodes(BDD, Nodes),
        foldl(max_variable_node, Nodes, V0-N0, MaxV0-MaxN0),
        MaxV is MaxV0 + 1,
        MaxN is MaxN0 + 1,
        b_setval('$clpb_next_var', MaxV),
        b_setval('$clpb_next_node', MaxN).

max_variable_node(Node, V0-N0, V-N) :-
        node_id(Node, N1),
        node_varindex(Node, V1),
        N is max(N0,N1),
        V is max(V0,V1).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Fuse formulas that share the same variables into single conjunctions.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

ands_fusion(Ands0, Ands) :-
        maplist(with_variables, Ands0, Pairs0),
        keysort(Pairs0, Pairs),
        group_pairs_by_key(Pairs, Groups),
        pairs_values(Groups, Andss),
        maplist(list_to_conjunction, Andss, Ands).

with_variables(F, Vs-F) :-
        term_variables(F, Vs0),
        variables_in_index_order(Vs0, Vs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   If possible, separate variables into different sat/1 goals.
   A formula F can be split in two if for two of its variables A and B,
   taut((A^F)*(B^F) =:= F, 1) holds. In the first conjunct, A does not
   occur, and in the second, B does not occur. We separate variables
   until that is no longer possible. There may be a better way to do this.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

variables_separation(Fs0, Fs) :- separation_fixpoint(Fs0, [], Fs).

separation_fixpoint(Fs0, Ds0, Fs) :-
        phrase(variables_separation_(Fs0, Ds0, Rest), Fs1),
        partition(anf_done, Fs1, Ds1, Fs2),
        maplist(arg(1), Ds1, Ds2),
        maplist(arg(1), Fs2, Fs3),
        append(Ds0, Ds2, Ds3),
        append(Rest, Fs3, Fs4),
        sort(Fs4, Fs5),
        sort(Ds3, Ds4),
        (   Fs5 == [] -> Fs = Ds4
        ;   separation_fixpoint(Fs5, Ds4, Fs)
        ).

anf_done(done(_)).

variables_separation_([], _, []) --> [].
variables_separation_([F0|Fs0], Ds, Rest) -->
        (   { member(Done, Ds), F0 == Done } ->
            variables_separation_(Fs0, Ds, Rest)
        ;   { sat_rewrite(F0, F),
              sat_bdd(F, BDD),
              bdd_variables(BDD, Vs0),
              exclude(universal_var, Vs0, Vs),
              maplist(existential_(BDD), Vs, Nodes),
              phrase(pairs(Nodes), Pairs),
              group_pairs_by_key(Pairs, Groups),
              phrase(groups_separation(Groups, BDD), ANFs) },
            (   { ANFs = [_|_] } ->
                list(ANFs),
                { Rest = Fs0 }
            ;   [done(F0)],
                variables_separation_(Fs0, Ds, Rest)
            )
        ).


existential_(BDD, V, Node) :- existential(V, BDD, Node).

groups_separation([], _) --> [].
groups_separation([BDD1-BDDs|Groups], OrigBDD) -->
        { phrase(separate_pairs(BDDs, BDD1, OrigBDD), Nodes) },
        (   { Nodes = [_|_] } ->
            nodes_anfs([BDD1|Nodes])
        ;   []
        ),
        groups_separation(Groups, OrigBDD).

separate_pairs([], _, _) --> [].
separate_pairs([BDD2|Ps], BDD1, OrigBDD) -->
        (   { apply(*, BDD1, BDD2, And),
              And == OrigBDD } ->
            [BDD2]
        ;   []
        ),
        separate_pairs(Ps, BDD1, OrigBDD).

nodes_anfs([]) --> [].
nodes_anfs([N|Ns]) --> { node_anf(N, ANF) }, [anf(ANF)], nodes_anfs(Ns).

pairs([]) --> [].
pairs([V|Vs]) --> pairs_(Vs, V), pairs(Vs).

pairs_([], _) --> [].
pairs_([B|Bs], A) --> [A-B], pairs_(Bs, A).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Assert clpb:clpb_residuals(bdd) to obtain the BDD nodes as
   residuals. Note that they cannot be used as regular goals.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

nodes([]) --> [].
nodes([Node|Nodes]) -->
        { node_var_low_high(Node, Var0, Low, High),
          var_or_atom(Var0, Var),
          maplist(node_projection, [Node,High,Low], [ID,HID,LID]),
          var_index(Var0, VI) },
        [ID-(v(Var,VI) -> HID ; LID)],
        nodes(Nodes).


node_projection(Node, Projection) :-
        node_id(Node, ID),
        (   integer(ID) -> Projection = node(ID)
        ;   Projection = ID
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   By default, residual goals are sat/1 calls of the remaining formulas,
   using (mostly) algebraic normal form.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

sats([]) --> [].
sats([A|As]) --> [clpb:sat(A)], sats(As).

booleans([]) --> [].
booleans([B|Bs]) --> boolean(B), booleans(Bs).

boolean(Var) -->
        { del_clpb(Var) },
        (   { get_attr(Var, clpb_omit_boolean, true) } -> []
        ;   [clpb:sat(Var =:= Var)]
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Relate a formula to its algebraic normal form (ANF).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

formula_anf(Formula0, ANF) :-
        parse_sat(Formula0, Formula),
        sat_bdd(Formula, Node),
        node_anf(Node, ANF).

node_anf(Node, ANF) :-
        node_xors(Node, Xors0),
        maplist(maplist(monotonic_variable), Xors0, Xors),
        maplist(list_to_conjunction, Xors, Conjs),
        (   Conjs = [Var,C|Rest], clpb_var(Var) ->
            foldl(xor, Rest, C, RANF),
            ANF = (Var =\= RANF)
        ;   Conjs = [One,Var,C|Rest], One == 1, clpb_var(Var) ->
            foldl(xor, Rest, C, RANF),
            ANF = (Var =:= RANF)
        ;   Conjs = [C|Cs],
            foldl(xor, Cs, C, ANF)
        ).

monotonic_variable(Var0, Var) :-
        (   var(Var0), monotonic ->
            Var = v(Var0)
        ;   Var = Var0
        ).

clpb_var(Var) :- var(Var), !.
clpb_var(v(_)).

list_to_conjunction([], 1).
list_to_conjunction([L|Ls], Conj) :- foldl(and, Ls, L, Conj).

xor(A, B, B # A).

eq_1(V) :- V == 1.

node_xors(Node, Xors) :-
        phrase(xors(Node), Xors0),
        % we remove elements that occur an even number of times (A#A --> 0)
        maplist(sort, Xors0, Xors1),
        pairs_keys_values(Pairs0, Xors1, _),
        keysort(Pairs0, Pairs),
        group_pairs_by_key(Pairs, Groups),
        exclude(even_occurrences, Groups, Odds),
        pairs_keys(Odds, Xors2),
        maplist(exclude(eq_1), Xors2, Xors).

even_occurrences(_-Ls) :- length(Ls, L), L mod 2 =:= 0.

xors(Node) -->
        (   { Node == 0 } -> []
        ;   { Node == 1 } -> [[1]]
        ;   { node_var_low_high(Node, Var0, Low, High),
              var_or_atom(Var0, Var),
              node_xors(Low, Ls0),
              node_xors(High, Hs0),
              maplist(with_var(Var), Ls0, Ls),
              maplist(with_var(Var), Hs0, Hs) },
            list(Ls0),
            list(Ls),
            list(Hs)
        ).

list([]) --> [].
list([L|Ls]) --> [L], list(Ls).

with_var(Var, Ls, [Var|Ls]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Global variables for unique node and variable IDs and atoms.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

make_clpb_var('$clpb_next_var') :- nb_setval('$clpb_next_var', 0).

make_clpb_var('$clpb_next_node') :- nb_setval('$clpb_next_node', 0).

make_clpb_var('$clpb_atoms') :-
        empty_assoc(E),
        nb_setval('$clpb_atoms', E).

:- initialization((make_clpb_var(_),false;true)).

clpb_next_id(Var, ID) :-
        b_getval(Var, ID),
        Next is ID + 1,
        b_setval(Var, Next).

clpb_atom_var(Atom, Var) :-
        b_getval('$clpb_atoms', A0),
        (   get_assoc(Atom, A0, Var) -> true
        ;   put_attr(Var, clpb_atom, Atom),
            put_attr(Var, clpb_omit_boolean, true),
            put_assoc(Atom, A0, Var, A),
            b_setval('$clpb_atoms', A)
        ).



/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Compatibility predicates.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


:- meta_predicate(include(1, ?, ?)).

include(_, [], []).
include(Goal, [L|Ls0], Ls) :-
        (   call(Goal, L) ->
            Ls = [L|Rest]
        ;   Ls = Rest
        ),
        include(Goal, Ls0, Rest).

:- meta_predicate(exclude(1, ?, ?)).

exclude(_, [], []).
exclude(Goal, [L|Ls0], Ls) :-
        (   call(Goal, L) ->
            Ls = Rest
        ;   Ls = [L|Rest]
        ),
        exclude(Goal, Ls0, Rest).

partition(Pred, List, Less, Equal, Greater) :-
    partition_(List, Pred, Less, Equal, Greater).

partition_([], _, [], [], []).
partition_([H|T], Pred, L, E, G) :-
    call(Pred, H, Diff),
    partition_(Diff, H, Pred, T, L, E, G).

partition_(<, H, Pred, T, [H|Rest], E, G) :-
    partition_(T, Pred, Rest, E, G).
partition_(=, H, Pred, T, L, [H|Rest], G) :-
    partition_(T, Pred, L, Rest, G).
partition_(>, H, Pred, T, L, E, [H|Rest]) :-
    partition_(T, Pred, L, E, Rest).
