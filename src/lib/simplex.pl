/*
    Author:        Markus Triska
    E-mail:        triska@metalevel.at
    WWW:           http://www.metalevel.at
    Copyright (C): 2005-2022, Markus Triska

    Part of Scryer Prolog. All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/


:- module(simplex,
        [
                assignment/2,
                constraint/3,
                constraint/4,
                constraint_add/4,
                gen_state/1,
                maximize/3,
                minimize/3,
                objective/2,
                shadow_price/3,
                transportation/4,
                variable_value/3
        ]).

:- use_module(library(assoc)).
:- use_module(library(pio)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(charsio)).
:- use_module(library(format)).
:- use_module(library(between)).
:- use_module(library(atts)).
:- use_module(library(arithmetic)).

/** library(simplex): Solve linear programming problems

This library provides several predicates for solving linear
programming problems with the simplex algorithm, and also includes
efficient algorithms for transportation and assignment problems.

Efficiency could be improved significantly by changing the
implementation to the revised simplex method, benefiting from sparse
matrices.

If you are interested in cooperating on such improvements, please
contact me! Enhancing the performance of this library would be a great
thesis project, for example.

## Introduction			{#simplex-intro}

A *linear programming problem* or simply *linear program* (LP)
consists of:

  - a set of _linear_ *constraints*
  - a set of *variables*
  - a _linear_ *objective function*.

The goal is to assign values to the variables so as to _maximize_ (or
minimize) the value of the objective function while satisfying all
constraints.

Many optimization problems can be modeled in this way. As one basic
example, consider a knapsack with fixed capacity C, and a number of
items with sizes `s(i)` and values `v(i)`. The goal is to put as many
items as possible in the knapsack (not exceeding its capacity) while
maximizing the sum of their values.

As another example, suppose you are given a set of _coins_ with
certain values, and you are to find the minimum number of coins such
that their values sum up to a fixed amount. Instances of these
problems are solved below.

Rational arithmetic is used throughout solving linear programs. In
the current implementation, all variables are implicitly constrained
to be _non-negative_. This may change in future versions, and
non-negativity constraints should therefore be stated explicitly.


## Example 1     {#simplex-ex-1}

This is the "radiation therapy" example, taken from _Introduction to
Operations Research_ by Hillier and Lieberman.

[*Prolog DCG notation*](https://www.metalevel.at/prolog/dcg) is
used to _implicitly_ thread the state through posting the constraints:

```
:- use_module(library(simplex)).
:- use_module(library(dcgs)).

radiation(S) :-
	gen_state(S0),
	post_constraints(S0, S1),
	minimize([0.4*x1, 0.5*x2], S1, S).

post_constraints -->
	constraint([0.3*x1, 0.1*x2] =< 2.7),
	constraint([0.5*x1, 0.5*x2] = 6),
	constraint([0.6*x1, 0.4*x2] >= 6),
	constraint([x1] >= 0),
	constraint([x2] >= 0).
```

An example query:

```
?- radiation(S), variable_value(S, x1, Val1),
		 variable_value(S, x2, Val2).
   S = solved(...), Val1 = 15 rdiv 2, Val2 = 9 rdiv 2.
```

## Example 2     {#simplex-ex-2}

Here is an instance of the knapsack problem described above, where `C
= 8`, and we have two types of items: One item with value 7 and size
6, and 2 items each having size 4 and value 4. We introduce two
variables, `x(1)` and `x(2)` that denote how many items to take of
each type.

```
:- use_module(library(simplex)).

knapsack(S) :-
	knapsack_constraints(S0),
	maximize([7*x(1), 4*x(2)], S0, S).

knapsack_constraints(S) :-
	gen_state(S0),
	constraint([6*x(1), 4*x(2)] =< 8, S0, S1),
	constraint([x(1)] =< 1, S1, S2),
	constraint([x(2)] =< 2, S2, S).
```

An example query yields:

```
?- knapsack(S), variable_value(S, x(1), X1),
	        variable_value(S, x(2), X2).
   S = solved(...), X1 = 1 rdiv 1, X2 = 1 rdiv 2.
```

That is, we are to take the one item of the first type, and half of one of
the items of the other type to maximize the total value of items in the
knapsack.

If items can not be split, integrality constraints have to be imposed:

```
knapsack_integral(S) :-
	knapsack_constraints(S0),
	constraint(integral(x(1)), S0, S1),
	constraint(integral(x(2)), S1, S2),
	maximize([7*x(1), 4*x(2)], S2, S).
```

Now the result is different:

```
?- knapsack_integral(S), variable_value(S, x(1), X1),
			 variable_value(S, x(2), X2).

X1 = 0
X2 = 2
```

That is, we are to take only the _two_ items of the second type.
Notice in particular that always choosing the remaining item with best
performance (ratio of value to size) that still fits in the knapsack
does not necessarily yield an optimal solution in the presence of
integrality constraints.

## Example 3      {#simplex-ex-3}

We are given:

  - 3 coins each worth 1 unit
  - 20 coins each worth 5 units and
  - 10 coins each worth 20 units.

The task is to find a _minimal_ number of these coins that amount to
111 units in total. We introduce variables `c(1)`, `c(5)` and `c(20)`
denoting how many coins to take of the respective type:

```
:- use_module(library(simplex)).

coins(S) :-
	gen_state(S0),
	coins(S0, S).

coins -->
	constraint([c(1), 5*c(5), 20*c(20)] = 111),
	constraint([c(1)] =< 3),
	constraint([c(5)] =< 20),
	constraint([c(20)] =< 10),
	constraint([c(1)] >= 0),
	constraint([c(5)] >= 0),
	constraint([c(20)] >= 0),
	constraint(integral(c(1))),
	constraint(integral(c(5))),
	constraint(integral(c(20))),
	minimize([c(1), c(5), c(20)]).
```

An example query:

```
?- coins(S), variable_value(S, c(1), C1),
	     variable_value(S, c(5), C5),
	     variable_value(S, c(20), C20).
   S = solved(...), C1 = 1 rdiv 1, C5 = 2 rdiv 1, C20 = 5 rdiv 1.
```

@author [Markus Triska](https://www.metalevel.at)
*/


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   General Simplex Algorithm
   Structures used:

   tableau(Objective, Variables, Indicators, Constraints)
     *) objective function, represented as row
     *) list of variables corresponding to columns
     *) indicators denoting which variables are still active
     *) constraints as rows

   row(Var, Left, Right)
     *) the basic variable corresponding to this row
     *) coefficients of the left-hand side of the constraint
     *) right-hand side of the constraint
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


find_row(Variable, [Row|Rows], R) :-
        Row = row(V, _, _),
        (   V == Variable -> R = Row
        ;   find_row(Variable, Rows, R)
        ).

%% variable_value(+State, +Variable, -Value)
%
% Value is unified with the value obtained for Variable. State must
% correspond to a solved instance.

variable_value(State, Variable, Value) :-
        functor(State, F, _),
        (   F == solved ->
            solved_tableau(State, Tableau),
            tableau_rows(Tableau, Rows),
            (   find_row(Variable, Rows, Row) -> Row = row(_, _, Value)
            ;   Value = 0
            )
        ;   F == clpr_solved -> no_clpr
        ).

no_clpr :- throw(clpr_not_supported).

var_zero(State, _Coeff*Var) :- variable_value(State, Var, 0).

list_first(Ls, F, Index) :- once(nth0(Index, Ls, F)).

%% shadow_price(+State, +Name, -Value)
%
% Unifies Value with the shadow price corresponding to the linear
% constraint whose name is Name. State must correspond to a solved
% instance.

shadow_price(State, Name, Value) :-
        functor(State, F, _),
        (   F == solved ->
            solved_tableau(State, Tableau),
            tableau_objective(Tableau, row(_,Left,_)),
            tableau_variables(Tableau, Variables),
            solved_names(State, Names),
            memberchk(user(Name)-Var, Names),
            list_first(Variables, Var, Nth0),
            nth0(Nth0, Left, Value)
        ;   F == clpr_solved -> no_clpr
        ).

%% objective(+State, -Objective)
%
% Unifies Objective with the result of the objective function at the
% obtained extremum. State must correspond to a solved instance.

objective(State, Obj) :-
        functor(State, F, _),
        (   F == solved ->
            solved_tableau(State, Tableau),
            tableau_objective(Tableau, Objective),
            Objective = row(_, _, Obj)
        ;   no_clpr
        ).

   % interface functions that access tableau components

tableau_objective(tableau(Obj, _, _, _), Obj).
tableau_rows(tableau(_, _, _, Rows), Rows).
tableau_indicators(tableau(_, _, Inds, _), Inds).
tableau_variables(tableau(_, Vars, _, _), Vars).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   interface functions that access and modify state components

   state is a structure of the form
       state(Num, Names, Cs, Is)
   Num: used to obtain new unique names for slack variables in a side-effect
        free way (increased by one and threaded through)
   Names: list of Name-Var, correspondence between constraint-names and
        names of slack/artificial variables to obtain shadow prices later
   Cs: list of constraints
   Is: list of integer variables

   constraints are initially represented as c(Name, Left, Op, Right),
   and after normalizing as c(Var, Left, Right). Name of unnamed constraints
   is 0. The distinction is important for merging constraints (mainly in
   branch and bound) with existing ones.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


constraint_name(c(Name, _, _, _), Name).
constraint_op(c(_, _, Op, _), Op).
constraint_left(c(_, Left, _, _), Left).
constraint_right(c(_, _, _, Right), Right).

%% gen_state(-State)
%
% Generates an initial state corresponding to an empty linear program.

gen_state(state(0,[],[],[])).

state_add_constraint(C, S0, S) :-
        (   constraint_name(C, 0), constraint_left(C, [_Coeff*_Var]) ->
            state_merge_constraint(C, S0, S)
        ;   state_add_constraint_(C, S0, S)
        ).

state_add_constraint_(C, state(VID,Ns,Cs,Is), state(VID,Ns,[C|Cs],Is)).

state_merge_constraint(C, S0, S) :-
        constraint_left(C, [Coeff0*Var0]),
        constraint_right(C, Right0),
        constraint_op(C, Op),
        (   Coeff0 =:= 0 ->
            (   Op == (=) -> Right0 =:= 0, S0 = S
            ;   Op == (=<) -> S0 = S
            ;   Op == (>=) -> Right0 =:= 0, S0 = S
            )
        ;   Coeff0 < 0 -> state_add_constraint_(C, S0, S)
        ;   Right is Right0 rdiv Coeff0,
            state_constraints(S0, Cs),
            (   select(c(0, [1*Var0], Op, CRight), Cs, RestCs) ->
                (   Op == (=) -> CRight =:= Right, S0 = S
                ;   Op == (=<) ->
                    NewRight is min(Right, CRight),
                    NewCs = [c(0, [1*Var0], Op, NewRight)|RestCs],
                    state_set_constraints(NewCs, S0, S)
                ;   Op == (>=) ->
                    NewRight is max(Right, CRight),
                    NewCs = [c(0, [1*Var0], Op, NewRight)|RestCs],
                    state_set_constraints(NewCs, S0, S)
                )
            ;   state_add_constraint_(c(0, [1*Var0], Op, Right), S0, S)
            )
        ).


state_add_name(Name, Var), [state(VID,[Name-Var|Ns],Cs,Is)] -->
        [state(VID,Ns,Cs,Is)].

state_add_integral(Var, state(VID,Ns,Cs,Is), state(VID,Ns,Cs,[Var|Is])).

state_constraints(state(_, _, Cs, _), Cs).
state_names(state(_,Names,_,_), Names).
state_integrals(state(_,_,_,Is), Is).
state_set_constraints(Cs, state(VID,Ns,_,Is), state(VID,Ns,Cs,Is)).
state_set_integrals(Is, state(VID,Ns,Cs,_), state(VID,Ns,Cs,Is)).


state_next_var(VarID0), [state(VarID1,Names,Cs,Is)] -->
        [state(VarID0,Names,Cs,Is)],
        { VarID1 is VarID0 + 1 }.

solved_tableau(solved(Tableau, _, _), Tableau).
solved_names(solved(_, Names,_), Names).
solved_integrals(solved(_,_,Is), Is).

% User-named constraints are wrapped with user/1 to also allow "0" in
% constraint names.

%% constraint(+Constraint, +S0, -S)
%
% Adds a linear or integrality constraint to the linear program
% corresponding to state S0. A linear constraint is of the form =|Left
% Op C|=, where `Left` is a list of `Coefficient*Variable` terms
% (variables in the context of linear programs can be atoms or
% compound terms) and `C` is a non-negative numeric constant. The list
% represents the sum of its elements. `Op` can be `=`, `=<` or `>=`.
% The coefficient `1` can be omitted. An integrality constraint is of
% the form integral(Variable) and constrains Variable to an integral
% value.


constraint(C, S0, S) :-
        functor(S0, F, _),
        (   F == state ->
            (   C = integral(Var) -> state_add_integral(Var, S0, S)
            ;   constraint_(0, C, S0, S)
            )
        ;   F == clpr_state -> no_clpr
        ).

%% constraint(+Name, +Constraint, +S0, -S)
%
% Like constraint/3, and attaches the name Name (an atom or compound
% term) to the new constraint.

constraint(Name, C, S0, S) :- constraint_(user(Name), C, S0, S).

constraint_(Name, C, S0, S) :-
        functor(S0, F, _),
        (   F == state ->
            (   C = integral(Var) -> state_add_integral(Var, S0, S)
            ;   C =.. [Op, Left0, Right0],
                coeff_one(Left0, Left),
                Right0 >= 0,
                number_to_rational(Right0, Right),
                state_add_constraint(c(Name, Left, Op, Right), S0, S)
            )
        ;   F == clpr_state -> no_clpr
        ).

%% constraint_add(+Name, +Left, +S0, -S)
%
% Left is a list of `Coefficient*Variable` terms. The terms are added
% to the left-hand side of the constraint named Name. S is unified
% with the resulting state.

constraint_add(Name, A, S0, S) :-
        functor(S0, F, _),
        (   F == state ->
            state_constraints(S0, Cs),
            add_left(Cs, user(Name), A, Cs1),
            state_set_constraints(Cs1, S0, S)
        ;   F == clpr_state -> no_clpr
        ).


add_left([c(Name,Left0,Op,Right)|Cs], V, A, [c(Name,Left,Op,Right)|Rest]) :-
        (   Name == V -> append(A, Left0, Left), Rest = Cs
        ;   Left0 = Left, add_left(Cs, V, A, Rest)
        ).

branching_variable(State, Variable) :-
        solved_integrals(State, Integrals),
        member(Variable, Integrals),
        variable_value(State, Variable, Value),
        \+ integer(Value).


worth_investigating(ZStar0, _, _) :- var(ZStar0).
worth_investigating(ZStar0, AllInt, Z) :-
        nonvar(ZStar0),
        (   AllInt =:= 1 -> Z1 is floor(Z)
        ;   Z1 = Z
        ),
        Z1 > ZStar0.


branch_and_bound(Objective, Solved, AllInt, ZStar0, ZStar, S0, S, Found) :-
        objective(Solved, Z),
        (   worth_investigating(ZStar0, AllInt, Z) ->
            (   branching_variable(Solved, BrVar) ->
                variable_value(Solved, BrVar, Value),
                Value1 is floor(Value),
                Value2 is Value1 + 1,
                constraint([BrVar] =< Value1, S0, SubProb1),
                (   maximize_(Objective, SubProb1, SubSolved1) ->
                    Sub1Feasible = 1,
                    objective(SubSolved1, Obj1)
                ;   Sub1Feasible = 0
                ),
                constraint([BrVar] >= Value2, S0, SubProb2),
                (   maximize_(Objective, SubProb2, SubSolved2) ->
                    Sub2Feasible = 1,
                    objective(SubSolved2, Obj2)
                ;   Sub2Feasible = 0
                ),
                (   Sub1Feasible =:= 1, Sub2Feasible =:= 1 ->
                    (   Obj1 >= Obj2 ->
                        First = SubProb1,
                        Second = SubProb2,
                        FirstSolved = SubSolved1,
                        SecondSolved = SubSolved2
                    ;   First = SubProb2,
                        Second = SubProb1,
                        FirstSolved = SubSolved2,
                        SecondSolved = SubSolved1
                    ),
                    branch_and_bound(Objective, FirstSolved, AllInt, ZStar0, ZStar1, First, Solved1, Found1),
                    branch_and_bound(Objective, SecondSolved, AllInt, ZStar1, ZStar2, Second, Solved2, Found2)
                ;   Sub1Feasible =:= 1 ->
                    branch_and_bound(Objective, SubSolved1, AllInt, ZStar0, ZStar1, SubProb1, Solved1, Found1),
                    Found2 = 0
                ;   Sub2Feasible =:= 1 ->
                    Found1 = 0,
                    branch_and_bound(Objective, SubSolved2, AllInt, ZStar0, ZStar2, SubProb2, Solved2, Found2)
                ;   Found1 = 0, Found2 = 0
                ),
                (   Found1 =:= 1, Found2 =:= 1 -> S = Solved2, ZStar = ZStar2
                ;   Found1 =:= 1 -> S = Solved1, ZStar = ZStar1
                ;   Found2 =:= 1 -> S = Solved2, ZStar = ZStar2
                ;   S = S0, ZStar = ZStar0
                ),
                Found is max(Found1, Found2)
            ;   S = Solved, ZStar = Z, Found = 1
            )
        ;   ZStar = ZStar0, S = S0, Found = 0
        ).

%% maximize(+Objective, +S0, -S)
%
% Maximizes the objective function, stated as a list of
% `Coefficient*Variable` terms that represents the sum of its
% elements, with respect to the linear program corresponding to state
% S0. \arg{S} is unified with an internal representation of the solved
% instance.

maximize(Z0, S0, S) :-
        coeff_one(Z0, Z1),
        functor(S0, F, _),
        (   F == state -> maximize_mip(Z1, S0, S)
        ;   F == clpr_state -> no_clpr
        ).

maximize_mip(Z, S0, S) :-
        maximize_(Z, S0, Solved),
        state_integrals(S0, Is),
        (   Is == [] -> S = Solved
        ;   % arrange it so that branch and bound branches on variables
            % in the same order the integrality constraints were stated in
            reverse(Is, Is1),
            state_set_integrals(Is1, S0, S1),
            (   all_integers(Z, Is1) -> AllInt = 1
            ;   AllInt = 0
            ),
            branch_and_bound(Z, Solved, AllInt, _, _, S1, S, 1)
        ).

all_integers([], _).
all_integers([Coeff*V|Rest], Is) :-
        integer(Coeff),
        memberchk(V, Is),
        all_integers(Rest, Is).

%% minimize(+Objective, +S0, -S)
%
% Analogous to maximize/3.

minimize(Z0, S0, S) :-
        coeff_one(Z0, Z1),
        functor(S0, F, _),
        (   F == state ->
            maplist(linsum_negate, Z1, Z2),
            maximize_mip(Z2, S0, S1),
            solved_tableau(S1, tableau(Obj, Vars, Inds, Rows)),
            solved_names(S1, Names),
            Obj = row(z, Left0, Right0),
            all_times(Left0, -1, Left),
            Right is -Right0,
            Obj1 = row(z, Left, Right),
            state_integrals(S0, Is),
            S = solved(tableau(Obj1, Vars, Inds, Rows), Names, Is)
        ;   F == clpr_state -> no_clpr
        ).

op_pendant(>=, =<).
op_pendant(=<, >=).

constraints_collapse([]) --> [].
constraints_collapse([C|Cs]) -->
        { C = c(Name, Left, Op, Right) },
        (   { Name == 0, Left = [1*Var], op_pendant(Op, P) } ->
            { Pendant = c(0, [1*Var], P, Right) },
            (   { select(Pendant, Cs, Rest) } ->
                [c(0, Left, (=), Right)],
                { CsLeft = Rest }
            ;   [C],
                { CsLeft = Cs }
            )
        ;   [C],
            { CsLeft = Cs }
        ),
        constraints_collapse(CsLeft).

% solve a (relaxed) LP in standard form

maximize_(Z, S0, S) :-
        state_constraints(S0, Cs0),
        phrase(constraints_collapse(Cs0), Cs1),
        phrase(constraints_normalize(Cs1, Cs, As0), [S0], [S1]),
        flatten(As0, As1),
        (   As1 == [] ->
            make_tableau(Z, Cs, Tableau0),
            simplex(Tableau0, Tableau),
            state_names(S1, Names),
            state_integrals(S1, Is),
            S = solved(Tableau, Names, Is)
        ;   state_names(S1, Names),
            state_integrals(S1, Is),
            two_phase_simplex(Z, Cs, As1, Names, Is, S)
        ).

flatten(Lss, Ls) :-
        phrase(seqq(Lss), Ls).

make_tableau(Z, Cs, Tableau) :-
        ZC = c(_, Z, _),
        phrase(constraints_variables([ZC|Cs]), Variables0),
        sort(Variables0, Variables),
        constraints_rows(Cs, Variables, Rows),
        linsum_row(Variables, Z, Objective1),
        all_times(Objective1, -1, Obj),
        length(Variables, LVs),
        length(Ones, LVs),
        all_one(Ones),
        Tableau = tableau(row(z, Obj, 0), Variables, Ones, Rows).

all_one(Ones) :- maplist(=(1), Ones).

proper_form(Variables, Rows, _Coeff*A, Obj0, Obj) :-
        (   find_row(A, Rows, PivotRow) ->
            list_first(Variables, A, Col),
            row_eliminate(Obj0, PivotRow, Col, Obj)
        ;   Obj = Obj0
        ).


two_phase_simplex(Z, Cs, As, Names, Is, S) :-
        % phase 1: minimize sum of articifial variables
        make_tableau(As, Cs, Tableau0),
        Tableau0 = tableau(Obj0, Variables, Inds, Rows),
        foldl(proper_form(Variables, Rows), As, Obj0, Obj),
        simplex(tableau(Obj, Variables, Inds, Rows), Tableau1),
        maplist(var_zero(solved(Tableau1, _, _)), As),
        % phase 2: remove artificial variables and solve actual LP.
        tableau_rows(Tableau1, Rows2),
        eliminate_artificial(As, As, Variables, Rows2, Rows3),
        list_nths(As, Variables, Nths0),
        nths_to_zero(Nths0, Inds, Inds1),
        linsum_row(Variables, Z, Objective),
        all_times(Objective, -1, Objective1),
        foldl(proper_form(Variables, Rows3), Z, row(z, Objective1, 0), ObjRow),
        simplex(tableau(ObjRow, Variables, Inds1, Rows3), Tableau),
        S = solved(Tableau, Names, Is).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   If artificial variables are still in the basis, replace them with
   non-artificial variables if possible. If that is not possible, the
   constraint is ignored because it is redundant.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

eliminate_artificial([], _, _, Rows, Rows).
eliminate_artificial([_Coeff*A|Rest], As, Variables, Rows0, Rows) :-
        (   select(row(A, Left, 0), Rows0, Others) ->
            (   nth0(Col, Left, Coeff),
                Coeff =\= 0,
                nth0(Col, Variables, Var),
                \+ memberchk(_*Var, As) ->
                row_divide(row(A, Left, 0), Coeff, Row),
                gauss_elimination(Rows0, Row, Col, Rows1),
                swap_basic(Rows1, A, Var, Rows2)
            ;   Rows2 = Others
            )
        ;   Rows2 = Rows0
        ),
        eliminate_artificial(Rest, As, Variables, Rows2, Rows).

nths_to_zero([], Inds, Inds).
nths_to_zero([Nth|Nths], Inds0, Inds) :-
        nth_to_zero(Inds0, 0, Nth, Inds1),
        nths_to_zero(Nths, Inds1, Inds).

nth_to_zero([], _, _, []).
nth_to_zero([I|Is], Curr, Nth, [Z|Zs]) :-
        (   Curr =:= Nth -> [Z|Zs] = [0|Is]
        ;   Z = I,
            Next is Curr + 1,
            nth_to_zero(Is, Next, Nth, Zs)
        ).


list_nths([], _, []).
list_nths([_Coeff*A|As], Variables, [Nth|Nths]) :-
        list_first(Variables, A, Nth),
        list_nths(As, Variables, Nths).


linsum_negate(Coeff0*Var, Coeff*Var) :- Coeff is -Coeff0.

linsum_row([], _, []).
linsum_row([V|Vs], Ls, [C|Cs]) :-
        (   member(Coeff*V, Ls) -> C = Coeff
        ;   C = 0
        ),
        linsum_row(Vs, Ls, Cs).

constraints_rows([], _, []).
constraints_rows([C|Cs], Vars, [R|Rs]) :-
        C = c(Var, Left0, Right),
        linsum_row(Vars, Left0, Left),
        R = row(Var, Left, Right),
        constraints_rows(Cs, Vars, Rs).

constraints_normalize([], [], []) --> [].
constraints_normalize([C0|Cs0], [C|Cs], [A|As]) -->
        { constraint_op(C0, Op),
          constraint_left(C0, Left),
          constraint_right(C0, Right),
          constraint_name(C0, Name),
          Con =.. [Op, Left, Right] },
        constraint_normalize(Con, Name, C, A),
        constraints_normalize(Cs0, Cs, As).

constraint_normalize(As0 =< B0, Name, c(Slack, [1*Slack|As0], B0), []) -->
        state_next_var(Slack),
        state_add_name(Name, Slack).
constraint_normalize(As0 = B0, Name, c(AID, [1*AID|As0], B0), [-1*AID]) -->
        state_next_var(AID),
        state_add_name(Name, AID).
constraint_normalize(As0 >= B0, Name, c(AID, [-1*Slack,1*AID|As0], B0), [-1*AID]) -->
        state_next_var(Slack),
        state_next_var(AID),
        state_add_name(Name, AID).

coeff_one([], []).
coeff_one([L|Ls], [Coeff*Var|Rest]) :-
        (   L = A*B ->
            number_to_rational(A, Coeff),
            Var = B
        ;   Coeff = 1, Var = L
        ),
        coeff_one(Ls, Rest).


tableau_optimal(Tableau) :-
        tableau_objective(Tableau, Objective),
        tableau_indicators(Tableau, Indicators),
        Objective = row(_, Left, _),
        all_nonnegative(Left, Indicators).

all_nonnegative([], []).
all_nonnegative([Coeff|As], [I|Is]) :-
        (   I =:= 0 -> true
        ;   Coeff >= 0
        ),
        all_nonnegative(As, Is).

pivot_column(Tableau, PCol) :-
        tableau_objective(Tableau, row(_, Left, _)),
        tableau_indicators(Tableau, Indicators),
        first_negative(Left, Indicators, 0, Index0, Val, RestL, RestI),
        Index1 is Index0 + 1,
        pivot_column(RestL, RestI, Val, Index1, Index0, PCol).

first_negative([L|Ls], [I|Is], Index0, N, Val, RestL, RestI) :-
        Index1 is Index0 + 1,
        (   I =:= 0 -> first_negative(Ls, Is, Index1, N, Val, RestL, RestI)
        ;   (   L < 0 -> N = Index0, Val = L, RestL = Ls, RestI = Is
            ;   first_negative(Ls, Is, Index1, N, Val, RestL, RestI)
            )
        ).


pivot_column([], _, _, _, N, N).
pivot_column([L|Ls], [I|Is], Coeff0, Index0, N0, N) :-
        (   I =:= 0 -> Coeff1 = Coeff0, N1 = N0
        ;   (   L < Coeff0 -> Coeff1 = L, N1 = Index0
            ;   Coeff1 = Coeff0, N1 = N0
            )
        ),
        Index1 is Index0 + 1,
        pivot_column(Ls, Is, Coeff1, Index1, N1, N).


pivot_row(Tableau, PCol, PRow) :-
        tableau_rows(Tableau, Rows),
        pivot_row(Rows, PCol, false, _, 0, 0, PRow).

pivot_row([], _, Bounded, _, _, Row, Row) :- Bounded.
pivot_row([Row|Rows], PCol, Bounded0, Min0, Index0, PRow0, PRow) :-
        Row = row(_Var, Left, B),
        nth0(PCol, Left, Ae),
        (   Ae > 0 ->
            Bounded1 = true,
            Bound is B rdiv Ae,
            (   Bounded0 ->
                (   Bound < Min0 -> Min1 = Bound, PRow1 = Index0
                ;   Min1 = Min0, PRow1 = PRow0
                )
            ;   Min1 = Bound, PRow1 = Index0
            )
        ;   Bounded1 = Bounded0, Min1 = Min0, PRow1 = PRow0
        ),
        Index1 is Index0 + 1,
        pivot_row(Rows, PCol, Bounded1, Min1, Index1, PRow1, PRow).


row_divide(row(Var, Left0, Right0), Div, row(Var, Left, Right)) :-
        all_divide(Left0, Div, Left),
        Right is Right0 rdiv Div.


all_divide([], _, []).
all_divide([R|Rs], Div, [DR|DRs]) :-
        DR is R rdiv Div,
        all_divide(Rs, Div, DRs).

gauss_elimination([], _, _, []).
gauss_elimination([Row0|Rows0], PivotRow, Col, [Row|Rows]) :-
        PivotRow = row(PVar, _, _),
        Row0 = row(Var, _, _),
        (   PVar == Var -> Row = PivotRow
        ;   row_eliminate(Row0, PivotRow, Col, Row)
        ),
        gauss_elimination(Rows0, PivotRow, Col, Rows).

row_eliminate(row(Var, Ls0, R0), row(_, PLs, PR), Col, row(Var, Ls, R)) :-
        nth0(Col, Ls0, Coeff),
        (   Coeff =:= 0 -> Ls = Ls0, R = R0
        ;   MCoeff is -Coeff,
            all_times_plus([PR|PLs], MCoeff, [R0|Ls0], [R|Ls])
        ).

all_times_plus([], _, _, []).
all_times_plus([A|As], T, [B|Bs], [AT|ATs]) :-
        AT is A * T + B,
        all_times_plus(As, T, Bs, ATs).

all_times([], _, []).
all_times([A|As], T, [AT|ATs]) :-
        AT is A * T,
        all_times(As, T, ATs).

simplex(Tableau0, Tableau) :-
        (   tableau_optimal(Tableau0) -> Tableau0 = Tableau
        ;   pivot_column(Tableau0, PCol),
            pivot_row(Tableau0, PCol, PRow),
            Tableau0 = tableau(Obj0,Variables,Inds,Matrix0),
            nth0(PRow, Matrix0, Row0),
            Row0 = row(Leaving, Left0, _Right0),
            nth0(PCol, Left0, PivotElement),
            row_divide(Row0, PivotElement, Row1),
            gauss_elimination([Obj0|Matrix0], Row1, PCol, [Obj|Matrix1]),
            nth0(PCol, Variables, Entering),
            swap_basic(Matrix1, Leaving, Entering, Matrix),
            simplex(tableau(Obj,Variables,Inds,Matrix), Tableau)
        ).

swap_basic([Row0|Rows0], Old, New, Matrix) :-
        Row0 = row(Var, Left, Right),
        (   Var == Old -> Matrix = [row(New, Left, Right)|Rows0]
        ;   Matrix = [Row0|Rest],
            swap_basic(Rows0, Old, New, Rest)
        ).

constraints_variables([]) --> [].
constraints_variables([c(_,Left,_)|Cs]) -->
        variables(Left),
        constraints_variables(Cs).

variables([]) --> [].
variables([_Coeff*Var|Rest]) --> [Var], variables(Rest).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A dual algorithm ("algorithm alpha-beta" in Papadimitriou and
   Steiglitz) is used for transportation and assignment problems. The
   arising max-flow problem is solved with Edmonds-Karp, itself a dual
   algorithm.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   An attributed variable is introduced for each node. Attributes:
   node: Original name of the node.
   edges: arc_to(To,F,Capacity) (F has an attribute "flow") or
          arc_from(From,F,Capacity)
   parent: used in breadth-first search
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- attribute
        node/1,
        edges/1,
        flow/1,
        parent/1.

arcs([], Assoc, Assoc).
arcs([arc(From0,To0,C)|As], Assoc0, Assoc) :-
        (   get_assoc(From0, Assoc0, From) -> Assoc1 = Assoc0
        ;   put_assoc(From0, Assoc0, From, Assoc1),
            put_atts(From, node(From0))
        ),
        (   get_atts(From, edges(Es)) -> true
        ;   Es = []
        ),
        put_atts(F, flow(0)),
        put_atts(From, edges([arc_to(To,F,C)|Es])),
        (   get_assoc(To0, Assoc1, To) -> Assoc2 = Assoc1
        ;   put_assoc(To0, Assoc1, To, Assoc2),
            put_atts(To, node(To0))
        ),
        (   get_atts(To, edges(Es1)) -> true
        ;   Es1 = []
        ),
        put_atts(To, edges([arc_from(From,F,C)|Es1])),
        arcs(As, Assoc2, Assoc).


edmonds_karp(Arcs0, Arcs) :-
        empty_assoc(E),
        arcs(Arcs0, E, Assoc),
        get_assoc(s, Assoc, S),
        get_assoc(t, Assoc, T),
        maximum_flow(S, T),
        % fetch attvars before deleting visited edges
        term_attributed_variables(S, AttVars),
        phrase(flow_to_arcs(S), Ls),
        arcs_assoc(Ls, Arcs),
        maplist(del_attrs, AttVars).

del_attrs(V) :-
        put_atts(V, [-node(_),-edges(_),-flow(_),-parent(_)]).

flow_to_arcs(V) -->
        (   { get_atts(V, edges(Es)) } ->
            { put_atts(V, -edges(_)),
              get_atts(V, node(Name)) },
            flow_to_arcs_(Es, Name)
        ;   []
        ).

flow_to_arcs_([], _) --> [].
flow_to_arcs_([E|Es], Name) -->
        edge_to_arc(E, Name),
        flow_to_arcs_(Es, Name).

edge_to_arc(arc_from(_,_,_), _) --> [].
edge_to_arc(arc_to(To,F,C), Name) -->
        { get_atts(To, node(NTo)),
          get_atts(F, flow(Flow)) },
        [arc(Name,NTo,Flow,C)],
        flow_to_arcs(To).

arcs_assoc(Arcs, Hash) :-
        empty_assoc(E),
        arcs_assoc(Arcs, E, Hash).

arcs_assoc([], Hs, Hs).
arcs_assoc([arc(From,To,F,C)|Rest], Hs0, Hs) :-
        (   get_assoc(From, Hs0, As) -> Hs1 = Hs0
        ;   put_assoc(From, Hs0, [], Hs1),
            empty_assoc(As)
        ),
        put_assoc(To, As, arc(From,To,F,C), As1),
        put_assoc(From, Hs1, As1, Hs2),
        arcs_assoc(Rest, Hs2, Hs).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Strategy: Breadth-first search until we find a free right vertex in
   the value graph, then find an augmenting path in reverse.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

maximum_flow(S, T) :-
        (   augmenting_path([[S]], Levels, T) ->
            phrase(augmenting_path(S, T), Path),
            Path = [augment(_,First,_)|Rest],
            path_minimum(Rest, First, Min),
            % format("augmenting path: ~w\n", [Min]),
            maplist(augment(Min), Path),
            maplist(maplist(clear_parent), Levels),
            maximum_flow(S, T)
        ;   true
        ).

clear_parent(V) :- put_atts(V, -parent(_)).

augmenting_path(Levels0, Levels, T) :-
        Levels0 = [Vs|_],
        Levels1 = [Tos|Levels0],
        phrase(reachables(Vs), Tos),
        Tos = [_|_],
        (   member(To, Tos), To == T -> Levels = Levels1
        ;   augmenting_path(Levels1, Levels, T)
        ).

reachables([])     --> [].
reachables([V|Vs]) -->
        { get_atts(V, edges(Es)) },
        reachables_(Es, V),
        reachables(Vs).

reachables_([], _)     --> [].
reachables_([E|Es], V) -->
        reachable(E, V),
        reachables_(Es, V).

reachable(arc_from(V,F,_), P) -->
        (   { \+ get_atts(V, parent(_)),
              get_atts(F, flow(Flow)),
              Flow > 0 } ->
            { put_atts(V, parent(P-augment(F,Flow,-))) },
            [V]
        ;   []
        ).
reachable(arc_to(V,F,C), P) -->
        (   { \+ get_atts(V, parent(_)),
              get_atts(F, flow(Flow)),
              (   C == inf ; Flow < C )} ->
            { ( C == inf -> Diff = inf
              ;   Diff is C - Flow
              ),
              put_atts(V, parent(P-augment(F,Diff,+))) },
            [V]
        ;   []
        ).


path_minimum([], Min, Min).
path_minimum([augment(_,A,_)|As], Min0, Min) :-
        (   A == inf -> Min1 = Min0
        ;   Min1 is min(Min0,A)
        ),
        path_minimum(As, Min1, Min).

augment(Min, augment(F,_,Sign)) :-
        get_atts(F, flow(Flow0)),
        flow_(Sign, Flow0, Min, Flow),
        put_atts(F, flow(Flow)).

flow_(+, F0, A, F) :- F is F0 + A.
flow_(-, F0, A, F) :- F is F0 - A.

augmenting_path(S, V) -->
        (   { V == S } -> []
        ;   { get_atts(V, parent(V1-Augment)) },
            [Augment],
            augmenting_path(S, V1)
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

naive_init(Supplies, _, Costs, Alphas, Betas) :-
        same_length(Supplies, Alphas),
        maplist(=(0), Alphas),
        transpose(Costs, TCs),
        maplist(min_list, TCs, Betas).

min_list([L|Ls], Min) :-
        foldl(min_, Ls, L, Min).

min_(E, M0, M) :- M is min(E,M0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   TODO: use attributed variables throughout
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


%% transportation(+Supplies, +Demands, +Costs, -Transport)
%
% Solves a transportation problem. Supplies and Demands must be lists
% of non-negative integers. Their respective sums must be equal. Costs
% is a list of lists representing the cost matrix, where an entry
% (_i_,_j_) denotes the integer cost of transporting one unit from _i_
% to _j_. A transportation plan having minimum cost is computed and
% unified with Transport in the form of a list of lists that
% represents the transportation matrix, where element (_i_,_j_)
% denotes how many units to ship from _i_ to _j_.

transportation(Supplies, Demands, Costs, Transport) :-
        length(Supplies, LAs),
        length(Demands, LBs),
        naive_init(Supplies, Demands, Costs, Alphas, Betas),
        network_head(Supplies, 1, SArcs, []),
        network_tail(Demands, 1, DArcs, []),
        numlist(1, LAs, Sources),
        numlist(1, LBs, Sinks0),
        maplist(make_sink, Sinks0, Sinks),
        append(SArcs, DArcs, Torso),
        alpha_beta(Torso, Sources, Sinks, Costs, Alphas, Betas, Flow),
        flow_transport(Supplies, 1, Demands, Flow, Transport).

flow_transport([], _, _, _, []).
flow_transport([_|Rest], N, Demands, Flow, [Line|Lines]) :-
        transport_line(Demands, N, 1, Flow, Line),
        N1 is N + 1,
        flow_transport(Rest, N1, Demands, Flow, Lines).

transport_line([], _, _, _, []).
transport_line([_|Rest], I, J, Flow, [L|Ls]) :-
        (   get_assoc(I, Flow, As), get_assoc(p(J), As, arc(I,p(J),F,_)) -> L = F
        ;   L = 0
        ),
        J1 is J + 1,
        transport_line(Rest, I, J1, Flow, Ls).


make_sink(N, p(N)).

network_head([], _) --> [].
network_head([S|Ss], N) -->
        [arc(s,N,S)],
        { N1 is N + 1 },
        network_head(Ss, N1).

network_tail([], _) --> [].
network_tail([D|Ds], N) -->
        [arc(p(N),t,D)],
        { N1 is N + 1 },
        network_tail(Ds, N1).

network_connections([], _, _, _) --> [].
network_connections([A|As], Betas, [Cs|Css], N) -->
        network_connections(Betas, Cs, A, N, 1),
        { N1 is N + 1 },
        network_connections(As, Betas, Css, N1).

network_connections([], _, _, _, _) --> [].
network_connections([B|Bs], [C|Cs], A, N, PN) -->
        (   { C =:= A + B } -> [arc(N,p(PN),inf)]
        ;   []
        ),
        { PN1 is PN + 1 },
        network_connections(Bs, Cs, A, N, PN1).

alpha_beta(Torso, Sources, Sinks, Costs, Alphas, Betas, Flow) :-
        network_connections(Alphas, Betas, Costs, 1, Cons, []),
        append(Torso, Cons, Arcs),
        edmonds_karp(Arcs, MaxFlow),
        mark_hashes(MaxFlow, MArcs, MRevArcs),
        all_markable(MArcs, MRevArcs, Markable),
        mark_unmark(Sources, Markable, MarkSources, UnmarkSources),
        (   MarkSources == [] -> Flow = MaxFlow
        ;   mark_unmark(Sinks, Markable, MarkSinks0, UnmarkSinks0),
            maplist(un_p, MarkSinks0, MarkSinks),
            maplist(un_p, UnmarkSinks0, UnmarkSinks),
            MarkSources = [FirstSource|_],
            UnmarkSinks = [FirstSink|_],
            theta(FirstSource, FirstSink, Costs, Alphas, Betas, TInit),
            theta(MarkSources, UnmarkSinks, Costs, Alphas, Betas, TInit, Theta),
            duals_add(MarkSources, Alphas, Theta, Alphas1),
            duals_add(UnmarkSinks, Betas, Theta, Betas1),
            Theta1 is -Theta,
            duals_add(UnmarkSources, Alphas1, Theta1, Alphas2),
            duals_add(MarkSinks, Betas1, Theta1, Betas2),
            alpha_beta(Torso, Sources, Sinks, Costs, Alphas2, Betas2, Flow)
        ).

mark_hashes(MaxFlow, Arcs, RevArcs) :-
        assoc_to_list(MaxFlow, FlowList),
        maplist(un_arc, FlowList, FlowList1),
        flatten(FlowList1, FlowList2),
        empty_assoc(E),
        mark_arcs(FlowList2, E, Arcs),
        mark_revarcs(FlowList2, E, RevArcs).

un_arc(_-Ls0, Ls) :-
        assoc_to_list(Ls0, Ls1),
        maplist(un_arc_, Ls1, Ls).

un_arc_(_-Ls, Ls).

mark_arcs([], Arcs, Arcs).
mark_arcs([arc(From,To,F,C)|Rest], Arcs0, Arcs) :-
        (   get_assoc(From, Arcs0, As) -> true
        ;   As = []
        ),
        (   C == inf -> As1 = [To|As]
        ;   F < C -> As1 = [To|As]
        ;   As1 = As
        ),
        put_assoc(From, Arcs0, As1, Arcs1),
        mark_arcs(Rest, Arcs1, Arcs).

mark_revarcs([], Arcs, Arcs).
mark_revarcs([arc(From,To,F,_)|Rest], Arcs0, Arcs) :-
        (   get_assoc(To, Arcs0, Fs) -> true
        ;   Fs = []
        ),
        (   F > 0 -> Fs1 = [From|Fs]
        ;   Fs1 = Fs
        ),
        put_assoc(To, Arcs0, Fs1, Arcs1),
        mark_revarcs(Rest, Arcs1, Arcs).


un_p(p(N), N).

duals_add([], Alphas, _, Alphas).
duals_add([S|Ss], Alphas0, Theta, Alphas) :-
        add_to_nth(1, S, Alphas0, Theta, Alphas1),
        duals_add(Ss, Alphas1, Theta, Alphas).

add_to_nth(N, N, [A0|As], Theta, [A|As]) :- !,
        A is A0 + Theta.
add_to_nth(N0, N, [A|As0], Theta, [A|As]) :-
        N1 is N0 + 1,
        add_to_nth(N1, N, As0, Theta, As).


theta(Source, Sink, Costs, Alphas, Betas, Theta) :-
        nth1(Source, Costs, Row),
        nth1(Sink, Row, C),
        nth1(Source, Alphas, A),
        nth1(Sink, Betas, B),
        Theta is (C - A - B) rdiv 2.

theta([], _, _, _, _, Theta, Theta).
theta([Source|Sources], Sinks, Costs, Alphas, Betas, Theta0, Theta) :-
        theta_(Sinks, Source, Costs, Alphas, Betas, Theta0, Theta1),
        theta(Sources, Sinks, Costs, Alphas, Betas, Theta1, Theta).

theta_([], _, _, _, _, Theta, Theta).
theta_([Sink|Sinks], Source, Costs, Alphas, Betas, Theta0, Theta) :-
        theta(Source, Sink, Costs, Alphas, Betas, Theta1),
        Theta2 is min(Theta0, Theta1),
        theta_(Sinks, Source, Costs, Alphas, Betas, Theta2, Theta).


mark_unmark(Nodes, Hash, Mark, Unmark) :-
        mark_unmark(Nodes, Hash, Mark, [], Unmark, []).

mark_unmark([], _, Mark, Mark, Unmark, Unmark).
mark_unmark([Node|Nodes], Markable, Mark0, Mark, Unmark0, Unmark) :-
        (   memberchk(Node, Markable) ->
            Mark0 = [Node|Mark1],
            Unmark0 = Unmark1
        ;   Mark0 = Mark1,
            Unmark0 = [Node|Unmark1]
        ),
        mark_unmark(Nodes, Markable, Mark1, Mark, Unmark1, Unmark).

all_markable(Flow, RevArcs, Markable) :-
        phrase(markable(s, [], _, Flow, RevArcs), Markable).

all_markable([], Visited, Visited, _, _) --> [].
all_markable([To|Tos], Visited0, Visited, Arcs, RevArcs) -->
        (   { memberchk(To, Visited0) } -> { Visited0 = Visited1 }
        ;   markable(To, [To|Visited0], Visited1, Arcs, RevArcs)
        ),
        all_markable(Tos, Visited1, Visited, Arcs, RevArcs).

markable(Current, Visited0, Visited, Arcs, RevArcs) -->
        { (   Current = p(_) ->
              (   get_assoc(Current, RevArcs, Fs) -> true
              ;   Fs = []
              )
          ;   (   get_assoc(Current, Arcs, Fs) -> true
              ;   Fs = []
              )
          ) },
        [Current],
        all_markable(Fs, [Current|Visited0], Visited, Arcs, RevArcs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   solve(File) -- read input from File.

   Format (NS = number of sources, ND = number of demands):

   NS
   ND
   S1 S2 S3 ...
   D1 D2 D3 ...
   C11 C12 C13 ...
   C21 C22 C23 ...
   ... ... ... ...
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

input(Ss, Ds, Costs) -->
        integer(NS),
        integer(ND),
        n_integers(NS, Ss),
        n_integers(ND, Ds),
        n_kvectors(NS, ND, Costs).

n_kvectors(0, _, []) --> !.
n_kvectors(N, K, [V|Vs]) -->
        n_integers(K, V),
        { N1 is N - 1 },
        n_kvectors(N1, K, Vs).

n_integers(0, []) --> !.
n_integers(N, [I|Is]) --> integer(I), { N1 is N - 1 }, n_integers(N1, Is).


number([D|Ds]) --> digit(D), number(Ds).
number([D])    --> digit(D).

digit(D) --> [D], { char_type(D, decimal_digit) }.

integer(N) --> number(Ds), !, ws, { number_chars(N, Ds) }.

ws --> [W], { char_type(W, whitespace) }, !, ws.
ws --> [].

solve(File) :-
        time((phrase_from_file(input(Supplies, Demands, Costs), File),
              transportation(Supplies, Demands, Costs, Matrix),
              maplist(print_row, Matrix))),
        halt.

print_row(R) :- maplist(print_row_, R), nl.

print_row_(N) :- format("~w ", [N]).

%?- transportation([1,1], [1,1], [[1,1],[1,1]], Ms).

%?- transportation([12,7,14], [3,15,9,6], [[20,50,10,60],[70,40,60,30],[40,80,70,40]], Ms).

% ?- simplex:call_residue_vars(transportation([12,7,14], [3,15,9,6], [[20,50,10,60],[70,40,60,30],[40,80,70,40]], Ms), Vs).
%@    Ms = [[0,3,9,0],[0,7,0,0],[3,5,0,6]], Vs = [].


%?- call_residue_vars(simplex:solve('instance_80_80.txt'), Vs).

%?- call_residue_vars(simplex:solve('instance_3_4.txt'), Vs).

%?- call_residue_vars(simplex:solve('instance_100_100.txt'), Vs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% assignment(+Cost, -Assignment)
%
%  Solves a linear assignment problem. Cost is a list of lists
%  representing the quadratic cost matrix, where element (i,j) denotes
%  the integer cost of assigning entity $i$ to entity $j$. An
%  assignment with minimal cost is computed and unified with
%  Assignment as a list of lists, representing an adjacency matrix.


% Assignment problem - for now, reduce to transportation problem
assignment(Costs, Assignment) :-
        length(Costs, LC),
        length(Supply, LC),
        all_one(Supply),
        transportation(Supply, Supply, Costs, Assignment).

