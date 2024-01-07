/*  CLP(ℤ): Constraint Logic Programming over Integers.

    Author:        Markus Triska
    E-mail:        triska@metalevel.at
    WWW:           https://www.metalevel.at
    Copyright (C): 2016-2024 Markus Triska

    This library provides CLP(ℤ):

              Constraint Logic Programming over Integers
              ==========================================

    Highlights:

    -) DECLARATIVE implementation of integer arithmetic.
    -) Fully relational, MONOTONIC execution mode.
    -) Always TERMINATING labeling.


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


:- module(clpz, [
                 op(760, yfx, #<==>),
                 op(750, xfy, #==>),
                 op(750, yfx, #<==),
                 op(740, yfx, #\/),
                 op(730, yfx, #\),
                 op(720, yfx, #/\),
                 op(710,  fy, #\),
                 op(700, xfx, #>),
                 op(700, xfx, #<),
                 op(700, xfx, #>=),
                 op(700, xfx, #=<),
                 op(700, xfx, #=),
                 op(700, xfx, #\=),
                 op(700, xfx, in),
                 op(700, xfx, ins),
                 op(450, xfx, ..), % should bind more tightly than \/
                 op(150, fx, #),
                 (#>)/2,
                 (#<)/2,
                 (#>=)/2,
                 (#=<)/2,
                 (#=)/2,
                 (#\=)/2,
                 (#\)/1,
                 (#<==>)/2,
                 (#==>)/2,
                 (#<==)/2,
                 (#\/)/2,
                 (#\)/2,
                 (#/\)/2,
                 (in)/2,
                 (ins)/2,
                 all_different/1,
                 all_distinct/1,
                 nvalue/2,
                 sum/3,
                 scalar_product/4,
                 tuples_in/2,
                 labeling/2,
                 label/1,
                 indomain/1,
                 lex_chain/1,
                 serialized/2,
                 global_cardinality/2,
                 global_cardinality/3,
                 circuit/1,
                 cumulative/1,
                 cumulative/2,
                 disjoint2/1,
                 element/3,
                 automaton/3,
                 automaton/8,
                 zcompare/3,
                 chain/2,
                 fd_var/1,
                 fd_inf/2,
                 fd_sup/2,
                 fd_size/2,
                 fd_dom/2,

                 % for use in predicates from library(reif)
                 (#=)/3,
                 (#<)/3

                 % called from goal_expansion
                 % clpz_equal/2,
                 % clpz_geq/2
                ]).


:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(between)).
:- use_module(library(lists)).
:- use_module(library(atts)).
:- use_module(library(iso_ext)).
:- use_module(library(dcgs)).
:- use_module(library(terms)).
:- use_module(library(error), [domain_error/3, type_error/3, can_be/2]).
:- use_module(library(si)).
:- use_module(library(freeze)).
:- use_module(library(arithmetic)).
:- use_module(library(debug)).
:- use_module(library(format)).

% :- use_module(library(types)).

:- attribute
        clpz/1,
        clpz_aux/1,
        clpz_relation/1,
        edges/1,
        flow/1,
        parent/1,
        free/1,
        g0_edges/1,
        used/1,
        lowlink/1,
        value/1,
        visited/1,
        index/1,
        in_stack/1,
        clpz_gcc_vs/1,
        clpz_gcc_num/1,
        clpz_gcc_occurred/1,
        queue/2,
        disabled/0.

:- dynamic(monotonic/0).
:- dynamic(clpz_equal_/2).
:- dynamic(clpz_geq_/2).
:- dynamic(clpz_neq/2).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Compatibility predicates.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

cyclic_term(T) :-
        \+ acyclic_term(T).

must_be(What, Term) :- must_be(What, unknown(Term)-1, Term).

must_be(ground, _, Term) :- !,
        (   ground(Term) -> true
        ;   instantiation_error(Term)
        ).
must_be(acyclic, Where, Term) :- !,
        (   acyclic_term(Term) ->
            true
        ;   domain_error(acyclic_term, Term, Where)
        ).
must_be(list, Where, Term) :- !,
        (   list_si(Term) -> true
        ;   type_error(list, Term, Where)
        ).
must_be(list(What), Where, Term) :- !,
        must_be(list, Where, Term),
        maplist(must_be(What, Where), Term).
must_be(Type, _, Term) :-
        error:must_be(Type, Term).


instantiation_error(Term) :- instantiation_error(Term, unknown(Term)-1).

instantiation_error(_, Goal-Arg) :-
	throw(error(instantiation_error, instantiation_error(Goal, Arg))).


domain_error(Expectation, Term) :-
        domain_error(Expectation, Term, unknown(Term)-1).

type_error(Expectation, Term) :-
        type_error(Expectation, Term, unknown(Term)-1).


:- meta_predicate(partition(1, ?, ?, ?)).

partition(Pred, Ls0, As, Bs) :-
        include(Pred, Ls0, As),
        exclude(Pred, Ls0, Bs).


partition(Pred, Ls0, Ls, Es, Gs) :-
        partition_(Ls0, Pred, Ls, Es, Gs).

partition_([], _, [], [], []).
partition_([X|Xs], Pred, Ls0, Es0, Gs0) :-
        call(Pred, X, Cmp),
        (   Cmp = (<) -> Ls0 = [X|Rest], partition_(Xs, Pred, Rest, Es0, Gs0)
        ;   Cmp = (=) -> Es0 = [X|Rest], partition_(Xs, Pred, Ls0, Rest, Gs0)
        ;   Cmp = (>) -> Gs0 = [X|Rest], partition_(Xs, Pred, Ls0, Es0, Rest)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   include/3 and exclude/3
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

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

%:- discontiguous clpz:goal_expansion/5.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Public operators.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- op(760, yfx, #<==>).
:- op(750, xfy, #==>).
:- op(750, yfx, #<==).
:- op(740, yfx, #\/).
:- op(730, yfx, #\).
:- op(720, yfx, #/\).
:- op(710,  fy, #\).
:- op(700, xfx, #>).
:- op(700, xfx, #<).
:- op(700, xfx, #>=).
:- op(700, xfx, #=<).
:- op(700, xfx, #=).
:- op(700, xfx, #\=).
:- op(700, xfx, in).
:- op(700, xfx, ins).
:- op(450, xfx, ..). % should bind more tightly than \/
:- op(150, fx, #).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Privately needed operators.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- op(700, xfx, cis).
:- op(700, xfx, cis_geq).
:- op(700, xfx, cis_gt).
:- op(700, xfx, cis_leq).
:- op(700, xfx, cis_lt).
:- op(1200, xfx, ++>).

/** Constraint Logic Programming over Integers

## Introduction

This library provides CLP(ℤ): Constraint Logic Programming over
Integers.

CLP(ℤ) is an instance of the general CLP(_X_) scheme, extending logic
programming with reasoning over specialised domains. CLP(ℤ) lets us
reason about *integers* in a way that honors the relational nature
of Prolog.

There are two major use cases of CLP(ℤ) constraints:

    1. [*declarative integer arithmetic*](#clpz-integer-arith)

    2. solving *combinatorial problems* such as planning, scheduling
       and allocation tasks.

The predicates of this library can be classified as:

    * _arithmetic_ constraints like `(#=)/2`, `(#>)/2` and `(#\=)/2`
    * the _membership_ constraints `(in)/2` and `(ins)/2`
    * the _enumeration_ predicates `indomain/1`, `label/1` and `labeling/2`
    * _combinatorial_ constraints like `all_distinct/1` and `global_cardinality/2`
    * _reification_ predicates such as `(#<==>)/2`
    * _reflection_ predicates such as `fd_dom/2`

In most cases, [_arithmetic constraints_](#clpz-arith-constraints)
are the only predicates you will ever need from this library. When
reasoning over integers, simply replace low-level arithmetic
predicates like `(is)/2` and `(>)/2` by the corresponding CLP(ℤ)
constraints like `(#=)/2` and `(#>)/2` to honor and preserve declarative
properties of your programs. For satisfactory performance, arithmetic
constraints are implicitly rewritten at compilation time so that
low-level fallback predicates are automatically used whenever
possible.

Almost all Prolog programs also reason about integers. Therefore, it
is highly advisable that you make CLP(ℤ) constraints available in all
your programs. One way to do this is to put the following directive in
your `~/.scryerrc` initialisation file:

```
:- use_module(library(clpz)).
```

All example programs that appear in the CLP(ℤ) documentation assume
that you have done this.

Important concepts and principles of this library are illustrated by
means of usage examples that are available in a public git repository:
[*https://github.com/triska/clpz*](https://github.com/triska/clpz)

If you are used to the complicated operational considerations that
low-level arithmetic primitives necessitate, then moving to CLP(ℤ)
constraints may, due to their power and convenience, at first feel to
you excessive and almost like cheating. It _isn't_. Constraints are an
integral part of all popular Prolog systems, and they are designed
to help you eliminate and avoid the use of low-level and less general
primitives by providing declarative alternatives that are meant to be
used instead.

When teaching Prolog, CLP(ℤ) constraints should be introduced
_before_ explaining low-level arithmetic predicates and their
procedural idiosyncrasies. This is because constraints are easy to
explain, understand and use due to their purely relational nature. In
contrast, the modedness and directionality of low-level arithmetic
primitives are impure limitations that are better deferred to more
advanced lectures.

More information about CLP(ℤ) constraints and their implementation is
contained in: [*metalevel.at/drt.pdf*](https://www.metalevel.at/drt.pdf)

The best way to discuss applying, improving and extending CLP(ℤ)
constraints is to use the dedicated `clpz` tag on
[stackoverflow.com](http://stackoverflow.com). Several of the world's
foremost CLP(ℤ) experts regularly participate in these discussions
and will help you for free on this platform.

{#clpz-arith-constraints}
## Arithmetic constraints

In modern Prolog systems, *arithmetic constraints* subsume and
supersede low-level predicates over integers. The main advantage of
arithmetic constraints is that they are true _relations_ and can be
used in all directions. For most programs, arithmetic constraints are
the only predicates you will ever need from this library.

The most important arithmetic constraint is `(#=)/2`, which subsumes
both `(is)/2` and `(=:=)/2` over integers. Use `(#=)/2` to make your
programs more general.

In total, the arithmetic constraints are:

| Expr1 `#=`  Expr2  | Expr1 equals Expr2                       |
| Expr1 `#\=` Expr2  | Expr1 is not equal to Expr2              |
| Expr1 `#>=` Expr2  | Expr1 is greater than or equal to Expr2  |
| Expr1 `#=<` Expr2  | Expr1 is less than or equal to Expr2     |
| Expr1 `#>` Expr2   | Expr1 is greater than Expr2              |
| Expr1 `#<` Expr2   | Expr1 is less than Expr2                 |

`Expr1` and `Expr2` denote *arithmetic expressions*, which are:

| _integer_          | Given value                          |
| _variable_         | Unknown integer                      |
| #(_variable_)      | Unknown integer                      |
| -Expr              | Unary minus                          |
| Expr + Expr        | Addition                             |
| Expr * Expr        | Multiplication                       |
| Expr - Expr        | Subtraction                          |
| Expr ^ Expr        | Exponentiation                       |
| min(Expr,Expr)     | Minimum of two expressions           |
| max(Expr,Expr)     | Maximum of two expressions           |
| Expr `mod` Expr    | Modulo induced by floored division   |
| Expr `rem` Expr    | Modulo induced by truncated division |
| abs(Expr)          | Absolute value                       |
| sign(Expr)         | Sign (-1, 0, 1) of Expr              |
| Expr // Expr       | Truncated integer division           |
| Expr div Expr      | Floored integer division             |

where `Expr` again denotes an arithmetic expression.

The bitwise operations `(\)/1`, `(/\)/2`, `(\/)/2`, `(>>)/2`,
`(<<)/2`, `lsb/1`, `msb/1`, `popcount/1` and `(xor)/2` are also
supported.

{#clpz-integer-arith}
## Declarative integer arithmetic

The [_arithmetic constraints_](#clpz-arith-constraints) `(#=)/2`,
`(#>)/2` etc. are meant to be used _instead_ of the primitives
`(is)/2`, `(=:=)/2`, `(>)/2` etc. over integers. Almost all Prolog
programs also reason about integers. Therefore, it is recommended that
you put the following directive in your `~/.scryerrc` initialisation
file to make CLP(ℤ) constraints available in all your programs:

```
:- use_module(library(clpz)).
```

Throughout the following, it is assumed that you have done this.

The most basic use of CLP(ℤ) constraints is _evaluation_ of
arithmetic expressions involving integers. For example:

```
?- X #= 1+2.
   X = 3.
```

This could in principle also be achieved with the lower-level
predicate `(is)/2`. However, an important advantage of arithmetic
constraints is their purely relational nature: Constraints can be used
in _all directions_, also if one or more of their arguments are only
partially instantiated. For example:

```
?- 3 #= Y+2.
   Y = 1.
```

This relational nature makes CLP(ℤ) constraints easy to explain and
use, and well suited for beginners and experienced Prolog programmers
alike. In contrast, when using low-level integer arithmetic, we get:

```
?- 3 is Y+2.
   error(instantiation_error,(is)/2).

?- 3 =:= Y+2.
   error(instantiation_error,(is)/2).
```

Due to the necessary operational considerations, the use of these
low-level arithmetic predicates is considerably harder to understand
and should therefore be deferred to more advanced lectures.

For supported expressions, CLP(ℤ) constraints are drop-in
replacements of these low-level arithmetic predicates, often yielding
more general programs. See [`n_factorial/2`](#clpz-factorial) for an
example.

This library uses goal_expansion/2 to automatically rewrite
constraints at compilation time so that low-level arithmetic
predicates are _automatically_ used whenever possible. For example,
the predicate:

```
positive_integer(N) :- N #>= 1.
```

is executed as if it were written as:

```
positive_integer(N) :-
        (   integer(N)
        ->  N >= 1
        ;   N #>= 1
        ).
```

This illustrates why the performance of CLP(ℤ) constraints is almost
always completely satisfactory when they are used in modes that can be
handled by low-level arithmetic. To disable the automatic rewriting,
set the Prolog flag `clpz_goal_expansion` to `false`.

If you are used to the complicated operational considerations that
low-level arithmetic primitives necessitate, then moving to CLP(ℤ)
constraints may, due to their power and convenience, at first feel to
you excessive and almost like cheating. It _isn't_. Constraints are an
integral part of all popular Prolog systems, and they are designed
to help you eliminate and avoid the use of low-level and less general
primitives by providing declarative alternatives that are meant to be
used instead.


{#clpz-factorial}
## Example: Factorial relation

We illustrate the benefit of using `(#=)/2` for more generality with a
simple example.

Consider first a rather conventional definition of `n_factorial/2`,
relating each natural number _N_ to its factorial _F_:

```
n_factorial(0, 1).
n_factorial(N, F) :-
        N #> 0,
        N1 #= N - 1,
        n_factorial(N1, F1),
        F #= N * F1.
```

This program uses CLP(ℤ) constraints _instead_ of low-level
arithmetic throughout, and everything that _would have worked_ with
low-level arithmetic _also_ works with CLP(ℤ) constraints, retaining
roughly the same performance. For example:

```
?- n_factorial(47, F).
   F = 258623241511168180642964355153611979969197632389120000000000
;  false.
```

Now the point: Due to the increased flexibility and generality of
CLP(ℤ) constraints, we are free to _reorder_ the goals as follows:

```
n_factorial(0, 1).
n_factorial(N, F) :-
        N #> 0,
        N1 #= N - 1,
        F #= N * F1,
        n_factorial(N1, F1).
```

In this concrete case, _termination_ properties of the predicate are
improved. For example, the following queries now both terminate:

```
?- n_factorial(N, 1).
   N = 0
;  N = 1
;  false.

?- n_factorial(N, 3).
   false.
```

To make the predicate terminate if _any_ argument is instantiated, add
the (implied) constraint `F #\= 0` before the recursive call.
Otherwise, the query `n_factorial(N, 0)` is the only non-terminating
case of this kind.

The value of CLP(ℤ) constraints does _not_ lie in completely freeing
us from _all_ procedural phenomena. For example, the two programs do
not even have the same _termination properties_ in all cases.
Instead, the primary benefit of CLP(ℤ) constraints is that they allow
you to try different execution orders and apply [*declarative
debugging*](https://www.metalevel.at/prolog/debugging)
techniques _at all_!  Reordering goals (and clauses) can significantly
impact the performance of Prolog programs, and you are free to try
different variants if you use declarative approaches. Moreover, since
all CLP(ℤ) constraints _always terminate_, placing them earlier can
at most _improve_, never worsen, the termination properties of your
programs. An additional benefit of CLP(ℤ) constraints is that they
eliminate the complexity of introducing `(is)/2` and `(=:=)/2` to
beginners, since _both_ predicates are subsumed by `(#=)/2` when
reasoning over integers.

{#clpz-combinatorial}
## Combinatorial constraints

In addition to subsuming and replacing low-level arithmetic
predicates, CLP(ℤ) constraints are often used to solve combinatorial
problems such as planning, scheduling and allocation tasks. Among the
most frequently used *combinatorial constraints* are `all_distinct/1`,
`global_cardinality/2` and `cumulative/2`. This library also provides
several other constraints like `disjoint2/1` and `automaton/8`, which are
useful in more specialized applications.

{#clpz-domains}
## Domains

Each CLP(ℤ) variable has an associated set of admissible integers,
which we call the variable's *domain*. Initially, the domain of each
CLP(ℤ) variable is the set of _all_ integers. CLP(ℤ) constraints like
`(#=)/2`, `(#>)/2` and `(#\=)/2` can at most reduce, and never extend,
the domains of their arguments. The constraints `(in)/2` and `(ins)/2`
let us explicitly state domains of CLP(ℤ) variables. The process of
determining and adjusting domains of variables is called constraint
*propagation*, and it is performed automatically by this library. When
the domain of a variable contains only one element, then the variable
is automatically unified to that element.

Domains are taken into account when further constraints are stated,
and by enumeration predicates like labeling/2.

{#clpz-sudoku}
## Example: Sudoku

As another example, consider _Sudoku_: It is a popular puzzle
over integers that can be easily solved with CLP(ℤ) constraints.

```
sudoku(Rows) :-
        length(Rows, 9), maplist(same_length(Rows), Rows),
        append(Rows, Vs), Vs ins 1..9,
        maplist(all_distinct, Rows),
        transpose(Rows, Columns),
        maplist(all_distinct, Columns),
        Rows = [As,Bs,Cs,Ds,Es,Fs,Gs,Hs,Is],
        blocks(As, Bs, Cs),
        blocks(Ds, Es, Fs),
        blocks(Gs, Hs, Is).

blocks([], [], []).
blocks([N1,N2,N3|Ns1], [N4,N5,N6|Ns2], [N7,N8,N9|Ns3]) :-
        all_distinct([N1,N2,N3,N4,N5,N6,N7,N8,N9]),
        blocks(Ns1, Ns2, Ns3).

problem(1, [[_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,3,_,8,5],
            [_,_,1,_,2,_,_,_,_],
            [_,_,_,5,_,7,_,_,_],
            [_,_,4,_,_,_,1,_,_],
            [_,9,_,_,_,_,_,_,_],
            [5,_,_,_,_,_,_,7,3],
            [_,_,2,_,1,_,_,_,_],
            [_,_,_,_,4,_,_,_,9]]).
```

Sample query:

```
?- problem(1, Rows), sudoku(Rows), maplist(portray_clause, Rows).
[9,8,7,6,5,4,3,2,1].
[2,4,6,1,7,3,9,8,5].
[3,5,1,9,2,8,7,4,6].
[1,2,8,5,3,7,6,9,4].
[6,3,4,8,9,2,1,5,7].
[7,9,5,4,6,1,8,3,2].
[5,1,9,2,8,6,4,7,3].
[4,7,2,3,1,9,5,6,8].
[8,6,3,7,4,5,2,1,9].
   Rows = [[9,8,7,6,5,4,3,2,1]|...].
```

In this concrete case, the constraint solver is strong enough to find
the unique solution without any search.


{#clpz-residual-goals}
## Residual goals

Here is an example session with a few queries and their answers:

```
?- X #> 3.
   clpz:(X in 4..sup).

?- X #\= 20.
   clpz:(X in inf..19\/21..sup).

?- 2*X #= 10.
   X = 5.

?- X*X #= 144.
   clpz:(X in-12\/12)
;  false.

?- 4*X + 2*Y #= 24, X + Y #= 9, [X,Y] ins 0..sup.
   X = 3, Y = 6.

?- X #= Y #<==> B, X in 0..3, Y in 4..5.
   B = 0, clpz:(X in 0..3), clpz:(Y in 4..5).
```

The answers emitted by the toplevel are called _residual programs_,
and the goals that comprise each answer are called *residual goals*.
In each case above, and as for all pure programs, the residual program
is declaratively equivalent to the original query. From the residual
goals, it is clear that the constraint solver has deduced additional
domain restrictions in many cases.

To inspect residual goals, it is best to let the toplevel display them
for us. Wrap the call of your predicate into `call_residue_vars/2` to
make sure that all constrained variables are displayed. To make the
constraints a variable is involved in available as a Prolog term for
further reasoning within your program, use `copy_term/3`. For example:

```
?- X #= Y + Z, X in 0..5, copy_term([X,Y,Z], [X,Y,Z], Gs).
Gs = [clpz: (X in 0..5), clpz: (Y+Z#=X)],
X in 0..5,
Y+Z#=X.
```

This library also provides _reflection_ predicates (like `fd_dom/2`,
`fd_size/2` etc.) with which we can inspect a variable's current
domain. These predicates can be useful if you want to implement your
own labeling strategies.

{#clpz-search}
## Core relations and search

Using CLP(ℤ) constraints to solve combinatorial tasks typically
consists of two phases:

    1. First, all relevant constraints are stated.
    2. Second, if the domain of each involved variable is _finite_,
       then _enumeration predicates_ can be used to search for
       concrete solutions.

It is good practice to keep the modeling part, via a dedicated
predicate called the *core relation*, separate from the actual
search for solutions. This lets us observe termination and
determinism properties of the core relation in isolation from the
search, and more easily try different search strategies.

As an example of a constraint satisfaction problem, consider the
cryptoarithmetic puzzle SEND + MORE = MONEY, where different letters
denote distinct integers between 0 and 9. It can be modeled in CLP(ℤ)
as follows:

```
puzzle([S,E,N,D] + [M,O,R,E] = [M,O,N,E,Y]) :-
        Vars = [S,E,N,D,M,O,R,Y],
        Vars ins 0..9,
        all_different(Vars),
                  S*1000 + E*100 + N*10 + D +
                  M*1000 + O*100 + R*10 + E #=
        M*10000 + O*1000 + N*100 + E*10 + Y,
        M #\= 0, S #\= 0.
```

Notice that we are _not_ using `labeling/2` in this predicate, so that
we can first execute and observe the modeling part in isolation.
Sample query and its result (actual variables replaced for
readability):

```
?- puzzle(As+Bs=Cs).
As = [9, A2, A3, A4],
Bs = [1, 0, B3, A2],
Cs = [1, 0, A3, A2, C5],
A2 in 4..7,
all_different([9, A2, A3, A4, 1, 0, B3, C5]),
91*A2+A4+10*B3#=90*A3+C5,
A3 in 5..8,
A4 in 2..8,
B3 in 2..8,
C5 in 2..8.
```

From this answer, we see that this core relation _terminates_ and is in
fact _deterministic_. Moreover, we see from the residual goals that
the constraint solver has deduced more stringent bounds for all
variables. Such observations are only possible if modeling and search
parts are cleanly separated.

Labeling can then be used to search for solutions in a separate
predicate or goal:

```
?- puzzle(As+Bs=Cs), label(As).
   As = [9,5,6,7], Bs = [1,0,8,5], Cs = [1,0,6,5,2]
;  false.
```

In this case, it suffices to label a subset of variables to find the
puzzle's unique solution, since the constraint solver is strong enough
to reduce the domains of remaining variables to singleton sets. In
general though, it is necessary to label all variables to obtain
ground solutions.

{#clpz-n-queens}
## Example: Eight queens puzzle

We illustrate the concepts of the preceding sections by means of the
so-called _eight queens puzzle_. The task is to place 8 queens on an
8x8 chessboard such that none of the queens is under attack. This
means that no two queens share the same row, column or diagonal.

To express this puzzle via CLP(ℤ) constraints, we must first pick a
suitable representation. Since CLP(ℤ) constraints reason over
_integers_, we must find a way to map the positions of queens to
integers. Several such mappings are conceivable, and it is not
immediately obvious which we should use. On top of that, different
constraints can be used to express the desired relations. For such
reasons, _modeling_ combinatorial problems via CLP(ℤ) constraints
often necessitates some creativity and has been described as more of
an art than a science.

In our concrete case, we observe that there must be exactly one queen
per column. The following representation therefore suggests itself: We
are looking for 8 integers, one for each column, where each integer
denotes the _row_ of the queen that is placed in the respective
column, and which are subject to certain constraints.

In fact, let us now generalize the task to the so-called _N queens
puzzle_, which is obtained by replacing 8 by _N_ everywhere it occurs
in the above description. We implement the above considerations in the
*core relation* `n_queens/2`, where the first argument is the number
of queens (which is identical to the number of rows and columns of the
generalized chessboard), and the second argument is a list of _N_
integers that represents a solution in the form described above.

```
n_queens(N, Qs) :-
        length(Qs, N),
        Qs ins 1..N,
        safe_queens(Qs).

safe_queens([]).
safe_queens([Q|Qs]) :- safe_queens(Qs, Q, 1), safe_queens(Qs).

safe_queens([], _, _).
safe_queens([Q|Qs], Q0, D0) :-
        Q0 #\= Q,
        abs(Q0 - Q) #\= D0,
        D1 #= D0 + 1,
        safe_queens(Qs, Q0, D1).
```

Note that all these predicates can be used in _all directions_: We
can use them to _find_ solutions, _test_ solutions and _complete_
partially instantiated solutions.

The original task can be readily solved with the following query:

```
?- n_queens(8, Qs), label(Qs).
   Qs = [1,5,8,6,3,7,2,4]
;  ... .
```

Using suitable labeling strategies, we can easily find solutions with
80 queens and more:

```
?- n_queens(80, Qs), labeling([ff], Qs).
   Qs = [1,3,5,44,42,4,50,7,68,57,76,61,6,39,30,40,8,54,36,41|...]
;  ... .

?- time((n_queens(90, Qs), labeling([ff], Qs))).
   % CPU time: 2.382s
   Qs = [1,3,5,50,42,4,49,7,59,48,46,63,6,55,47,64,8,70,58,67|...]
;  ... .
```

Experimenting with different search strategies is easy because we have
separated the core relation from the actual search.



{#clpz-optimisation}
## Optimisation

We can use `labeling/2` to minimize or maximize the value of a CLP(ℤ)
expression, and generate solutions in increasing or decreasing order
of the value. See the labeling options `min(Expr)` and `max(Expr)`,
respectively.

Again, to easily try different labeling options in connection with
optimisation, we recommend to introduce a dedicated predicate for
posting constraints, and to use `labeling/2` in a separate goal. This
way, we can observe properties of the core relation in isolation,
and try different labeling options without recompiling our code.

If necessary, we can use `once/1` to commit to the first optimal
solution. However, it is often very valuable to see alternative
solutions that are _also_ optimal, so that we can choose among optimal
solutions by other criteria. For the sake of
[*purity*](https://www.metalevel.at/prolog/purity) and
completeness, we recommend to avoid `once/1` and other constructs that
lead to impurities in CLP(ℤ) programs.

Related to optimisation with CLP(ℤ) constraints are `library(simplex)`
and CLP(Q) which reason about _linear_ constraints over rational
numbers.

{#clpz-reification}
## Reification

The constraints `(in)/2`, `(#=)/2`, `(#\=)/2`, `(#<)/2`, `(#>)/2`,
`(#=<)/2`, and `(#>=)/2` can be _reified_, which means reflecting
their truth values into Boolean values represented by the integers 0
and 1. Let P and Q denote reifiable constraints or Boolean variables,
then:

| `#\ Q`      | True iff Q is false                  |
| `P #\/ Q`   | True iff either P or Q               |
| `P #/\ Q`   | True iff both P and Q                |
| `P #\ Q`    | True iff either P or Q, but not both |
| `P #<==> Q` | True iff P and Q are equivalent      |
| `P #==> Q`  | True iff P implies Q                 |
| `P #<== Q`  | True iff Q implies P                 |

The constraints of this table are reifiable as well.

When reasoning over Boolean variables, also consider using CLP(B)
constraints as provided by `library(clpb)`.

{#clpz-monotonicity}
## Enabling monotonic CLP(ℤ)

In the default execution mode, CLP(ℤ) constraints still exhibit some
non-relational properties. For example, _adding_ constraints can yield
new solutions:

```
?-          X #= 2, X = 1+1.
   false.

?- X = 1+1, X #= 2, X = 1+1.
   X = 1+1.
```

This behaviour is highly problematic from a logical point of view, and
it may render declarative debugging techniques inapplicable.

Assert `clpz:monotonic` to make CLP(ℤ) *monotonic*: This means
that _adding_ new constraints _cannot_ yield new solutions. When this
flag is `true`, we must wrap variables that occur in arithmetic
expressions with the functor `(?)/1` or `(#)/1`. For example:

```
?- assertz(clpz:monotonic).
   true.

?- #X #= #Y + #Z.
   clpz:(#Y+ #Z#= #X).

?-          X #= 2, X = 1+1.
   error(instantiation_error,instantiation_error(unknown(_408),1)).
```

The wrapper can be omitted for variables that are already constrained
to integers.

{#clpz-custom-constraints}
## Custom constraints

We can define custom constraints. The mechanism to do this is not yet
finalised, and we welcome suggestions and descriptions of use cases
that are important to you.

As an example of how it can be done currently, let us define a new
custom constraint `oneground(X,Y,Z)`, where Z shall be 1 if at least
one of X and Y is instantiated:

```
:- multifile clpz:run_propagator/2.

oneground(X, Y, Z) :-
        clpz:make_propagator(oneground(X, Y, Z), Prop),
        clpz:init_propagator(X, Prop),
        clpz:init_propagator(Y, Prop),
        clpz:trigger_once(Prop).

clpz:run_propagator(oneground(X, Y, Z), MState) :-
        (   integer(X) -> clpz:kill(MState), Z = 1
        ;   integer(Y) -> clpz:kill(MState), Z = 1
        ;   true
        ).
```

First, `clpz:make_propagator/2` is used to transform a user-defined
representation of the new constraint to an internal form. With
`clpz:init_propagator/2`, this internal form is then attached to X and
Y. From now on, the propagator will be invoked whenever the domains of
X or Y are changed. Then, `clpz:trigger_once/1` is used to give the
propagator its first chance for propagation even though the variables'
domains have not yet changed. Finally, `clpz:run_propagator/2` is
extended to define the actual propagator. As explained, this predicate
is automatically called by the constraint solver. The first argument
is the user-defined representation of the constraint as used in
`clpz:make_propagator/2`, and the second argument is a mutable state
that can be used to prevent further invocations of the propagator when
the constraint has become entailed, by using `clpz:kill/1`. An example
of using the new constraint:

```
?- oneground(X, Y, Z), Y = 5.
Y = 5,
Z = 1,
X in inf..sup.
```

@author [Markus Triska](https://www.metalevel.at)
*/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
                               Duo DCGs
                               ========

   A Duo DCG is like a DCG, except that it describes *two* lists at
   the same time.

   A Duo DCG rule has the form Head ++> Body.  The language construct
   As+Bs is used within Duo DCGs to describe that the elements in As
   occur in the first list, and the elements in Bs occur in the second
   list. Duo DCGs are compiled to Prolog code via term expansion. The
   interface predicates are:

     *) duophrase(NT, As, Bs)
     *) duophrase(NT, As0, As, Bs0, Bs) (difference list version).

   Duo DCGs could be used to efficiently describe scheduled
   propagators, taking into account the two possible propagator
   priorities. However, it turns out that passing around a single
   argument is more efficient than passing around multiple arguments,
   and therefore regular DCGs are used for propagator scheduling.

   Still, everything is completely pure: No global data structures are
   needed to schedule the propagators!
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- meta_predicate(duophrase(4, ?, ?)).
:- meta_predicate(duophrase(4, ?, ?, ?, ?)).

duophrase(NT, As, Bs) :-
        duophrase(NT, As, [], Bs, []).

duophrase(NT, As0, As, Bs0, Bs) :-
        call(NT, As0, As, Bs0, Bs).

%:- multifile user:term_expansion/6.
term_expansion(Term0, Term) :-
        nonvar(Term0),
        Term0 = (Head0 ++> Body0),
        Term = (Head :- Body),
        duodcg_head(Head0, Head, As0, As, Bs0, Bs),
        once(duodcg_body(Body0, Body, As0, As, Bs0, Bs)).

duodcg_body([], (As0=As,Bs0=Bs), As0, As, Bs0, Bs).
duodcg_body(Xs+Ys, (phrase(seq(Xs), As0, As),
                       phrase(seq(Ys), Bs0, Bs)), As0, As, Bs0, Bs).
duodcg_body({Goal}, call(Goal), As, As, Bs, Bs).
duodcg_body((A0,B0), (A,B), As0, As, Bs0, Bs) :-
        duodcg_body(A0, A, As0, As1, Bs0, Bs1),
        duodcg_body(B0, B, As1, As, Bs1, Bs).
duodcg_body((A0->B0;C0), (A->B;C), As0, As, Bs0, Bs) :-
        duodcg_body(A0, A, As0, As1, Bs0, Bs1),
        duodcg_body(B0, B, As1, As, Bs1, Bs),
        duodcg_body(C0, C, As0, As, Bs0, Bs).
duodcg_body((A->B), Body, As0, As, Bs0, Bs) :-
        duodcg_body((A->B;false), Body, As0, As, Bs0, Bs).
duodcg_body((A0;B0), (A;B), As0, As, Bs0, Bs) :-
        duodcg_body(A0, A, As0, As, Bs0, Bs),
        duodcg_body(B0, B, As0, As, Bs0, Bs).
duodcg_body(NT0, NT, As0, As, Bs0, Bs) :-
        duodcg_head(NT0, NT, As0, As, Bs0, Bs).

duodcg_head(Head0, Head, As0, As, Bs0, Bs) :-
        Head0 =.. [F|Args0],
        append(Args0, [As0,As,Bs0,Bs], Args),
        Head =.. [F|Args].


goal_expansion(get_attr(Var, Module, Value), (var(Var),get_atts(Var, Access))) :-
        Access =.. [Module,Value].

goal_expansion(put_attr(Var, Module, Value), put_atts(Var, Access)) :-
        Access =.. [Module,Value].

goal_expansion(del_attr(Var, Module), (var(Var) -> put_atts(Var, -Access);true)) :-
        Access =.. [Module,_].


goal_expansion(A cis B, Expansion) :-
        phrase(cis_goals(B, A), Goals),
        list_goal(Goals, Expansion).
goal_expansion(A cis_lt B, B cis_gt A).
goal_expansion(A cis_leq B, B cis_geq A).
goal_expansion(A cis_geq B, cis_leq_numeric(B, N)) :- nonvar(A), A = n(N).
goal_expansion(A cis_geq B, cis_geq_numeric(A, N)) :- nonvar(B), B = n(N).
goal_expansion(A cis_gt B, cis_lt_numeric(B, N))   :- nonvar(A), A = n(N).
goal_expansion(A cis_gt B, cis_gt_numeric(A, N))   :- nonvar(B), B = n(N).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A bound is either:

   n(N):    integer N
   inf:     infimum of Z (= negative infinity)
   sup:     supremum of Z (= positive infinity)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

is_bound(n(N)) :- integer(N).
is_bound(inf).
is_bound(sup).

defaulty_to_bound(D, P) :- ( integer(D) -> P = n(D) ; P = D ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Compactified is/2 and predicates for several arithmetic expressions
   with infinities, tailored for the modes needed by this solver.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

% cis_gt only works for terms of depth 0 on both sides
cis_gt(sup, B0) :- B0 \== sup.
cis_gt(n(N), B) :- cis_lt_numeric(B, N).

cis_lt_numeric(inf, _).
cis_lt_numeric(n(B), A) :- B < A.

cis_gt_numeric(sup, _).
cis_gt_numeric(n(B), A) :- B > A.

cis_geq(inf, inf).
cis_geq(sup, _).
cis_geq(n(N), B) :- cis_leq_numeric(B, N).

cis_leq_numeric(inf, _).
cis_leq_numeric(n(B), A) :- B =< A.

cis_geq_numeric(sup, _).
cis_geq_numeric(n(B), A) :- B >= A.

cis_min(inf, _, inf).
cis_min(sup, B, B).
cis_min(n(N), B, Min) :- cis_min_(B, N, Min).

cis_min_(inf, _, inf).
cis_min_(sup, N, n(N)).
cis_min_(n(B), A, n(M)) :- M is min(A,B).

cis_max(sup, _, sup).
cis_max(inf, B, B).
cis_max(n(N), B, Max) :- cis_max_(B, N, Max).

cis_max_(inf, N, n(N)).
cis_max_(sup, _, sup).
cis_max_(n(B), A, n(M)) :- M is max(A,B).

cis_plus(inf, _, inf).
cis_plus(sup, _, sup).
cis_plus(n(A), B, Plus) :- cis_plus_(B, A, Plus).

cis_plus_(sup, _, sup).
cis_plus_(inf, _, inf).
cis_plus_(n(B), A, n(S)) :- S is A + B.

cis_minus(inf, _, inf).
cis_minus(sup, _, sup).
cis_minus(n(A), B, M) :- cis_minus_(B, A, M).

cis_minus_(inf, _, sup).
cis_minus_(sup, _, inf).
cis_minus_(n(B), A, n(M)) :- M is A - B.

cis_uminus(inf, sup).
cis_uminus(sup, inf).
cis_uminus(n(A), n(B)) :- B is -A.

cis_abs(inf, sup).
cis_abs(sup, sup).
cis_abs(n(A), n(B)) :- B is abs(A).

cis_times(inf, B, P) :-
        (   B cis_lt n(0) -> P = sup
        ;   B cis_gt n(0) -> P = inf
        ;   P = n(0)
        ).
cis_times(sup, B, P) :-
        (   B cis_gt n(0) -> P = sup
        ;   B cis_lt n(0) -> P = inf
        ;   P = n(0)
        ).
cis_times(n(N), B, P) :- cis_times_(B, N, P).

cis_times_(inf, A, P)     :- cis_times(inf, n(A), P).
cis_times_(sup, A, P)     :- cis_times(sup, n(A), P).
cis_times_(n(B), A, n(P)) :- P is A * B.

cis_exp(inf, n(Y), R) :-
        (   even(Y) -> R = sup
        ;   R = inf
        ).
cis_exp(sup, _, sup).
cis_exp(n(N), Y, R) :- cis_exp_(Y, N, R).

cis_exp_(n(Y), N, n(R)) :- R is N^Y.
cis_exp_(sup, _, sup).
cis_exp_(inf, _, inf).

cis_goals(V, V)          --> { var(V) }, !.
cis_goals(n(N), n(N))    --> [].
cis_goals(inf, inf)      --> [].
cis_goals(sup, sup)      --> [].
cis_goals(sign(A0), R)   --> cis_goals(A0, A), [cis_sign(A, R)].
cis_goals(abs(A0), R)    --> cis_goals(A0, A), [cis_abs(A, R)].
cis_goals(-A0, R)        --> cis_goals(A0, A), [cis_uminus(A, R)].
cis_goals(A0+B0, R)      -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_plus(A, B, R)].
cis_goals(A0-B0, R)      -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_minus(A, B, R)].
cis_goals(min(A0,B0), R) -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_min(A, B, R)].
cis_goals(max(A0,B0), R) -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_max(A, B, R)].
cis_goals(A0*B0, R)      -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_times(A, B, R)].
cis_goals(div(A0,B0), R) -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_div(A, B, R)].
cis_goals(A0//B0, R)     -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_slash(A, B, R)].
cis_goals(A0^B0, R)      -->
        cis_goals(A0, A),
        cis_goals(B0, B),
        [cis_exp(A, B, R)].

list_goal([], true).
list_goal([G|Gs], Goal) :- foldl(list_goal_, Gs, G, Goal).

list_goal_(G, G0, (G0,G)).

cis_sign(sup, n(1)).
cis_sign(inf, n(-1)).
cis_sign(n(N), n(S)) :- S is sign(N).

cis_div(sup, Y, Z)  :- ( Y cis_geq n(0) -> Z = sup ; Z = inf ).
cis_div(inf, Y, Z)  :- ( Y cis_geq n(0) -> Z = inf ; Z = sup ).
cis_div(n(X), Y, Z) :- cis_div_(Y, X, Z).

cis_div_(sup, _, n(0)).
cis_div_(inf, _, n(0)).
cis_div_(n(Y), X, Z) :-
        (   Y =:= 0 -> (  X >= 0 -> Z = sup ; Z = inf )
        ;   Z0 is X // Y, Z = n(Z0)
        ).

cis_slash(sup, _, sup).
cis_slash(inf, _, inf).
cis_slash(n(N), B, S) :- cis_slash_(B, N, S).

cis_slash_(sup, _, n(0)).
cis_slash_(inf, _, n(0)).
cis_slash_(n(B), A, n(S)) :- S is A // B.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A domain is a finite set of disjoint intervals. Internally, domains
   are represented as trees. Each node is one of:

   empty: empty domain.

   split(N, Left, Right)
      - split on integer N, with Left and Right domains whose elements are
        all less than and greater than N, respectively. The domain is the
        union of Left and Right, i.e., N is a hole.

   from_to(From, To)
      - interval (From-1, To+1); From and To are bounds

   Desiderata: rebalance domains; singleton intervals.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Type definition and inspection of domains.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

check_domain(D) :-
        (   var(D) -> instantiation_error(D)
        ;   is_domain(D) -> true
        ;   domain_error(clpz_domain, D)
        ).

is_domain(empty).
is_domain(from_to(From,To)) :-
        is_bound(From), is_bound(To),
        From cis_leq To.
is_domain(split(S, Left, Right)) :-
        integer(S),
        is_domain(Left), is_domain(Right),
        all_less_than(Left, S),
        all_greater_than(Right, S).

all_less_than(empty, _).
all_less_than(from_to(From,To), S) :-
        From cis_lt n(S), To cis_lt n(S).
all_less_than(split(S0,Left,Right), S) :-
        S0 < S,
        all_less_than(Left, S),
        all_less_than(Right, S).

all_greater_than(empty, _).
all_greater_than(from_to(From,To), S) :-
        From cis_gt n(S), To cis_gt n(S).
all_greater_than(split(S0,Left,Right), S) :-
        S0 > S,
        all_greater_than(Left, S),
        all_greater_than(Right, S).

default_domain(from_to(inf,sup)).

domain_infimum(from_to(I, _), I).
domain_infimum(split(_, Left, _), I) :- domain_infimum(Left, I).

domain_supremum(from_to(_, S), S).
domain_supremum(split(_, _, Right), S) :- domain_supremum(Right, S).

domain_num_elements(empty, n(0)).
domain_num_elements(from_to(From,To), Num) :- Num cis To - From + n(1).
domain_num_elements(split(_, Left, Right), Num) :-
        domain_num_elements(Left, NL),
        domain_num_elements(Right, NR),
        Num cis NL + NR.

domain_direction_element(from_to(n(From), n(To)), Dir, E) :-
        (   Dir == up -> between(From, To, E)
        ;   between(From, To, E0),
            E is To - (E0 - From)
        ).
domain_direction_element(split(_, D1, D2), Dir, E) :-
        (   Dir == up ->
            (   domain_direction_element(D1, Dir, E)
            ;   domain_direction_element(D2, Dir, E)
            )
        ;   (   domain_direction_element(D2, Dir, E)
            ;   domain_direction_element(D1, Dir, E)
            )
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Test whether domain contains a given integer.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_contains(from_to(From,To), I) :- From cis_leq n(I), n(I) cis_leq To.
domain_contains(split(S, Left, Right), I) :-
        (   I < S -> domain_contains(Left, I)
        ;   I > S -> domain_contains(Right, I)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Test whether a domain contains another domain.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_subdomain(Dom, Sub) :- domain_subdomain(Dom, Dom, Sub).

domain_subdomain(from_to(_,_), Dom, Sub) :-
        domain_subdomain_fromto(Sub, Dom).
domain_subdomain(split(_, _, _), Dom, Sub) :-
        domain_subdomain_split(Sub, Dom, Sub).

domain_subdomain_split(empty, _, _).
domain_subdomain_split(from_to(From,To), split(S,Left0,Right0), Sub) :-
        (   To cis_lt n(S) -> domain_subdomain(Left0, Left0, Sub)
        ;   From cis_gt n(S) -> domain_subdomain(Right0, Right0, Sub)
        ).
domain_subdomain_split(split(_,Left,Right), Dom, _) :-
        domain_subdomain(Dom, Dom, Left),
        domain_subdomain(Dom, Dom, Right).

domain_subdomain_fromto(empty, _).
domain_subdomain_fromto(from_to(From,To), from_to(From0,To0)) :-
        From0 cis_leq From, To0 cis_geq To.
domain_subdomain_fromto(split(_,Left,Right), Dom) :-
        domain_subdomain_fromto(Left, Dom),
        domain_subdomain_fromto(Right, Dom).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Remove an integer from a domain. The domain is traversed until an
   interval is reached from which the element can be removed, or until
   it is clear that no such interval exists.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_remove(empty, _, empty).
domain_remove(from_to(L0, U0), X, D) :- domain_remove_(L0, U0, X, D).
domain_remove(split(S, Left0, Right0), X, D) :-
        (   X =:= S -> D = split(S, Left0, Right0)
        ;   X < S ->
            domain_remove(Left0, X, Left1),
            (   Left1 == empty -> D = Right0
            ;   D = split(S, Left1, Right0)
            )
        ;   domain_remove(Right0, X, Right1),
            (   Right1 == empty -> D = Left0
            ;   D = split(S, Left0, Right1)
            )
        ).

%?- domain_remove(from_to(n(0),n(5)), 3, D).

domain_remove_(inf, U0, X, D) :-
        (   U0 == n(X) -> U1 is X - 1, D = from_to(inf, n(U1))
        ;   U0 cis_lt n(X) -> D = from_to(inf,U0)
        ;   L1 is X + 1, U1 is X - 1,
            D = split(X, from_to(inf, n(U1)), from_to(n(L1),U0))
        ).
domain_remove_(n(N), U0, X, D) :- domain_remove_upper(U0, N, X, D).

domain_remove_upper(sup, L0, X, D) :-
        (   L0 =:= X -> L1 is X + 1, D = from_to(n(L1),sup)
        ;   L0 > X -> D = from_to(n(L0),sup)
        ;   L1 is X + 1, U1 is X - 1,
            D = split(X, from_to(n(L0),n(U1)), from_to(n(L1),sup))
        ).
domain_remove_upper(n(U0), L0, X, D) :-
        (   L0 =:= U0, X =:= L0 -> D = empty
        ;   L0 =:= X -> L1 is X + 1, D = from_to(n(L1), n(U0))
        ;   U0 =:= X -> U1 is X - 1, D = from_to(n(L0), n(U1))
        ;   between(L0, U0, X) ->
            U1 is X - 1, L1 is X + 1,
            D = split(X, from_to(n(L0), n(U1)), from_to(n(L1), n(U0)))
        ;   D = from_to(n(L0),n(U0))
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Remove all elements greater than / less than a constant.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_remove_greater_than(empty, _, empty).
domain_remove_greater_than(from_to(From0,To0), G, D) :-
        (   From0 cis_gt n(G) -> D = empty
        ;   To cis min(To0,n(G)), D = from_to(From0,To)
        ).
domain_remove_greater_than(split(S,Left0,Right0), G, D) :-
        (   S =< G ->
            domain_remove_greater_than(Right0, G, Right),
            (   Right == empty -> D = Left0
            ;   D = split(S, Left0, Right)
            )
        ;   domain_remove_greater_than(Left0, G, D)
        ).

domain_remove_smaller_than(empty, _, empty).
domain_remove_smaller_than(from_to(From0,To0), V, D) :-
        (   To0 cis_lt n(V) -> D = empty
        ;   From cis max(From0,n(V)), D = from_to(From,To0)
        ).
domain_remove_smaller_than(split(S,Left0,Right0), V, D) :-
        (   S >= V ->
            domain_remove_smaller_than(Left0, V, Left),
            (   Left == empty -> D = Right0
            ;   D = split(S, Left, Right0)
            )
        ;   domain_remove_smaller_than(Right0, V, D)
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Remove a whole domain from another domain. (Set difference.)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_subtract(Dom0, Sub, Dom) :- domain_subtract(Dom0, Dom0, Sub, Dom).

domain_subtract(empty, _, _, empty).
domain_subtract(from_to(From0,To0), Dom, Sub, D) :-
        (   Sub == empty -> D = Dom
        ;   Sub = from_to(From,To) ->
            (   From == To -> From = n(X), domain_remove(Dom, X, D)
            ;   From cis_gt To0 -> D = Dom
            ;   To cis_lt From0 -> D = Dom
            ;   From cis_leq From0 ->
                (   To cis_geq To0 -> D = empty
                ;   From1 cis To + n(1),
                    D = from_to(From1, To0)
                )
            ;   To1 cis From - n(1),
                (   To cis_lt To0 ->
                    From = n(S),
                    From2 cis To + n(1),
                    D = split(S,from_to(From0,To1),from_to(From2,To0))
                ;   D = from_to(From0,To1)
                )
            )
        ;   Sub = split(S, Left, Right) ->
            (   n(S) cis_gt To0 -> domain_subtract(Dom, Dom, Left, D)
            ;   n(S) cis_lt From0 -> domain_subtract(Dom, Dom, Right, D)
            ;   domain_subtract(Dom, Dom, Left, D1),
                domain_subtract(D1, D1, Right, D)
            )
        ).
domain_subtract(split(S, Left0, Right0), _, Sub, D) :-
        domain_subtract(Left0, Left0, Sub, Left),
        domain_subtract(Right0, Right0, Sub, Right),
        (   Left == empty -> D = Right
        ;   Right == empty -> D = Left
        ;   D = split(S, Left, Right)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Complement of a domain
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_complement(D, C) :-
        default_domain(Default),
        domain_subtract(Default, D, C).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Convert domain to a list of disjoint intervals From-To.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_intervals(D, Is) :- phrase(domain_intervals(D), Is).

domain_intervals(split(_, Left, Right)) -->
        domain_intervals(Left), domain_intervals(Right).
domain_intervals(empty)                 --> [].
domain_intervals(from_to(From,To))      --> [From-To].

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   To compute the intersection of two domains D1 and D2, we choose D1
   as the reference domain. For each interval of D1, we compute how
   far and to which values D2 lets us extend it.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domains_intersection(D1, D2, Intersection) :-
        domains_intersection_(D1, D2, Intersection),
        Intersection \== empty.

domains_intersection_(empty, _, empty).
domains_intersection_(from_to(L0,U0), D2, Dom) :-
        narrow(D2, L0, U0, Dom).
domains_intersection_(split(S,Left0,Right0), D2, Dom) :-
        domains_intersection_(Left0, D2, Left1),
        domains_intersection_(Right0, D2, Right1),
        (   Left1 == empty -> Dom = Right1
        ;   Right1 == empty -> Dom = Left1
        ;   Dom = split(S, Left1, Right1)
        ).

narrow(empty, _, _, empty).
narrow(from_to(L0,U0), From0, To0, Dom) :-
        From1 cis max(From0,L0), To1 cis min(To0,U0),
        (   From1 cis_gt To1 -> Dom = empty
        ;   Dom = from_to(From1,To1)
        ).
narrow(split(S, Left0, Right0), From0, To0, Dom) :-
        (   To0 cis_lt n(S) -> narrow(Left0, From0, To0, Dom)
        ;   From0 cis_gt n(S) -> narrow(Right0, From0, To0, Dom)
        ;   narrow(Left0, From0, To0, Left1),
            narrow(Right0, From0, To0, Right1),
            (   Left1 == empty -> Dom = Right1
            ;   Right1 == empty -> Dom = Left1
            ;   Dom = split(S, Left1, Right1)
            )
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Union of 2 domains.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domains_union(D1, D2, Union) :-
        domain_intervals(D1, Is1),
        domain_intervals(D2, Is2),
        append(Is1, Is2, IsU0),
        merge_intervals(IsU0, IsU1),
        intervals_to_domain(IsU1, Union).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Shift the domain by an offset.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_shift(empty, _, empty).
domain_shift(from_to(From0,To0), O, from_to(From,To)) :-
        From cis From0 + n(O), To cis To0 + n(O).
domain_shift(split(S0, Left0, Right0), O, split(S, Left, Right)) :-
        S is S0 + O,
        domain_shift(Left0, O, Left),
        domain_shift(Right0, O, Right).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   The new domain contains all values of the old domain,
   multiplied by a constant multiplier.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_expand(D0, M, D) :-
        (   M < 0 ->
            domain_negate(D0, D1),
            M1 is abs(M),
            domain_expand_(D1, M1, D)
        ;   M =:= 1 -> D = D0
        ;   domain_expand_(D0, M, D)
        ).

domain_expand_(empty, _, empty).
domain_expand_(from_to(From0, To0), M, from_to(From,To)) :-
        From cis From0*n(M),
        To cis To0*n(M).
domain_expand_(split(S0, Left0, Right0), M, split(S, Left, Right)) :-
        S is M*S0,
        domain_expand_(Left0, M, Left),
        domain_expand_(Right0, M, Right).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   similar to domain_expand/3, tailored for truncated division: an
   interval [From,To] is extended to [From*M, ((To+1)*M - 1)], i.e.,
   to all values that truncated integer-divided by M yield a value
   from interval.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_expand_more(D0, M, D) :-
        %format("expanding ~w by ~w\n", [D0,M]),
        (   M < 0 -> domain_negate(D0, D1), M1 is abs(M)
        ;   D1 = D0, M1 = M
        ),
        domain_expand_more_(D1, M1, D).
        %format("yield: ~w\n", [D]).

domain_expand_more_(empty, _, empty).
domain_expand_more_(from_to(From0, To0), M, from_to(From,To)) :-
        (   From0 cis_leq n(0) ->
            From cis (From0-n(1))*n(M) + n(1)
        ;   From cis From0*n(M)
        ),
        (   To0 cis_lt n(0) ->
            To cis To0*n(M)
        ;   To cis (To0+n(1))*n(M) - n(1)
        ).
domain_expand_more_(split(S0, Left0, Right0), M, split(S, Left, Right)) :-
        S is M*S0,
        domain_expand_more_(Left0, M, Left),
        domain_expand_more_(Right0, M, Right).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Scale a domain down by a constant multiplier. Assuming (//)/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_contract(D0, M, D) :-
        %format("contracting ~w by ~w\n", [D0,M]),
        (   M < 0 -> domain_negate(D0, D1), M1 is abs(M)
        ;   D1 = D0, M1 = M
        ),
        domain_contract_(D1, M1, D).

domain_contract_(empty, _, empty).
domain_contract_(from_to(From0, To0), M, from_to(From,To)) :-
        (   From0 cis_geq n(0) ->
            From cis (From0 + n(M) - n(1)) // n(M)
        ;   From cis From0 // n(M)
        ),
        (   To0 cis_geq n(0) ->
            To cis To0 // n(M)
        ;   To cis (To0 - n(M) + n(1)) // n(M)
        ).
domain_contract_(split(_,Left0,Right0), M, D) :-
        %  Scaled down domains do not necessarily retain any holes of
        %  the original domain.
        domain_contract_(Left0, M, Left),
        domain_contract_(Right0, M, Right),
        domains_union(Left, Right, D).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Similar to domain_contract, tailored for division, i.e.,
   {21,23} contracted by 4 is 5. It contracts "less".
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_contract_less(D0, M, D) :-
        (   M < 0 -> domain_negate(D0, D1), M1 is abs(M)
        ;   D1 = D0, M1 = M
        ),
        domain_contract_less_(D1, M1, D).

domain_contract_less_(empty, _, empty).
domain_contract_less_(from_to(From0, To0), M, from_to(From,To)) :-
        From cis From0 // n(M), To cis To0 // n(M).
domain_contract_less_(split(_,Left0,Right0), M, D) :-
        %  Scaled down domains do not necessarily retain any holes of
        %  the original domain.
        domain_contract_less_(Left0, M, Left),
        domain_contract_less_(Right0, M, Right),
        domains_union(Left, Right, D).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Negate the domain. Left and Right sub-domains and bounds switch sides.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

domain_negate(empty, empty).
domain_negate(from_to(From0, To0), from_to(From, To)) :-
        From cis -To0, To cis -From0.
domain_negate(split(S0, Left0, Right0), split(S, Left, Right)) :-
        S is -S0,
        domain_negate(Left0, Right),
        domain_negate(Right0, Left).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Construct a domain from a list of integers. Try to balance it.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

list_to_disjoint_intervals([], []).
list_to_disjoint_intervals([N|Ns], Is) :-
        list_to_disjoint_intervals(Ns, N, N, Is).

list_to_disjoint_intervals([], M, N, [n(M)-n(N)]).
list_to_disjoint_intervals([B|Bs], M, N, Is) :-
        (   B =:= N + 1 ->
            list_to_disjoint_intervals(Bs, M, B, Is)
        ;   Is = [n(M)-n(N)|Rest],
            list_to_disjoint_intervals(Bs, B, B, Rest)
        ).

list_to_domain(List0, D) :-
        (   List0 == [] -> D = empty
        ;   sort(List0, List),
            list_to_disjoint_intervals(List, Is),
            intervals_to_domain(Is, D)
        ).

intervals_to_domain([], empty) :- !.
intervals_to_domain([M-N], from_to(M,N)) :- !.
intervals_to_domain(Is, D) :-
        length(Is, L),
        FL is L // 2,
        length(Front, FL),
        append(Front, Tail, Is),
        Tail = [n(Start)-_|_],
        Hole is Start - 1,
        intervals_to_domain(Front, Left),
        intervals_to_domain(Tail, Right),
        D = split(Hole, Left, Right).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% in(?Var, +Domain)
%
%  Var is an element of Domain. Domain is one of:
%
%         * Integer
%           Singleton set consisting only of _Integer_.
%         * Lower..Upper
%           All integers _I_ such that _Lower_ =< _I_ =< _Upper_.
%           _Lower_ must be an integer or the atom *inf*, which
%           denotes negative infinity. _Upper_ must be an integer or
%           the atom *sup*, which denotes positive infinity.
%         * Domain1 `\/` Domain2
%           The union of Domain1 and Domain2.

Var in Dom :- clpz_in(Var, Dom).

clpz_in(V, D) :-
        fd_variable(V),
        drep_to_domain(D, Dom),
        domain(V, Dom).

fd_variable(V) :- can_be(integer, V).

%% ins(+Vars, +Domain)
%
%  The variables in the list Vars are elements of Domain.

Vs ins D :-
        fd_must_be_list(Vs),
        maplist(fd_variable, Vs),
        drep_to_domain(D, Dom),
        domains(Vs, Dom).

fd_must_be_list(Ls) :-
        (   fd_var(Ls) -> type_error(list, Ls)
        ;   must_be(list, Ls)
        ).

fd_must_be_list(Ls, Where) :-
        (   fd_var(Ls) -> type_error(list, Ls, Where)
        ;   must_be(list, Where, Ls)
        ).

%% indomain(?Var)
%
% Bind Var to all feasible values of its domain on backtracking. The
% domain of Var must be finite.

indomain(Var) :- label([Var]).

order_dom_next(up, Dom, Next)   :- domain_infimum(Dom, n(Next)).
order_dom_next(down, Dom, Next) :- domain_supremum(Dom, n(Next)).


%% label(+Vars)
%
% Equivalent to labeling([], Vars).

label(Vs) :- labeling([], Vs).

%% labeling(+Options, +Vars)
%
% Assign a value to each variable in Vars. Labeling means systematically
% trying out values for the finite domain   variables  Vars until all of
% them are ground. The domain of each   variable in Vars must be finite.
% Options is a list of options that   let  you exhibit some control over
% the search process. Several categories of options exist:
%
% The variable selection strategy lets you specify which variable of
% Vars is labeled next and is one of:
%
%   * leftmost
%   Label the variables in the order they occur in Vars. This is the
%   default.
%
%   * ff
%   _|First fail|_. Label the leftmost variable with smallest domain next,
%   in order to detect infeasibility early. This is often a good
%   strategy.
%
%   * ffc
%   Of the variables with smallest domains, the leftmost one
%   participating in most constraints is labeled next.
%
%   * min
%   Label the leftmost variable whose lower bound is the lowest next.
%
%   * max
%   Label the leftmost variable whose upper bound is the highest next.
%
% The value order is one of:
%
%   * up
%   Try the elements of the chosen variable's domain in ascending order.
%   This is the default.
%
%   * down
%   Try the domain elements in descending order.
%
% The branching strategy is one of:
%
%   * step
%   For each variable X, a choice is made between X = V and X #\= V,
%   where V is determined by the value ordering options. This is the
%   default.
%
%   * enum
%   For each variable X, a choice is made between X = V_1, X = V_2
%   etc., for all values V_i of the domain of X. The order is
%   determined by the value ordering options.
%
%   * bisect
%   For each variable X, a choice is made between X #=< M and X #> M,
%   where M is the midpoint of the domain of X.
%
% At most one option of each category can be specified, and an option
% must not occur repeatedly.
%
% The order of solutions can be influenced with:
%
%   * min(Expr)
%   * max(Expr)
%
% This generates solutions in ascending/descending order with respect
% to the evaluation of the arithmetic expression Expr. Labeling Vars
% must make Expr ground. If several such options are specified, they
% are interpreted from left to right, e.g.:
%
% ```
% ?- [X,Y] ins 10..20, labeling([max(X),min(Y)],[X,Y]).
% ```
%
% This generates solutions in descending order of X, and for each
% binding of X, solutions are generated in ascending order of Y. To
% obtain the incomplete behaviour that other systems exhibit with
% "maximize(Expr)" and "minimize(Expr)", use once/1, e.g.:
%
% ```
% once(labeling([max(Expr)], Vars))
% ```
%
% Labeling is always complete, always terminates, and yields no
% redundant solutions.
%

labeling(Options, Vars) :-
        must_be(list, labeling(Options, Vars)-1, Options),
        fd_must_be_list(Vars, labeling(Options, Vars)-2),
        maplist(finite_domain(labeling(Options, Vars), 2), Vars),
        label(Options, Options, default(leftmost), default(up), default(step), [], upto_ground, Vars).


finite_domain(Goal, Arg, Var) :-
        (   fd_get(Var, Dom, _) ->
            (   domain_infimum(Dom, n(_)), domain_supremum(Dom, n(_)) -> true
            ;   instantiation_error(Dom)
            )
        ;   integer(Var) -> true
        ;   must_be(integer, Goal-Arg, Var)
        ).

finite_domain(Var) :-
        finite_domain(finite_domain(Var), 1, Var).


label([O|Os], Options, Selection, Order, Choice, Optim, Consistency, Vars) :-
        (   var(O)-> instantiation_error(O)
        ;   override(selection, Selection, O, Options, S1) ->
            label(Os, Options, S1, Order, Choice, Optim, Consistency, Vars)
        ;   override(order, Order, O, Options, O1) ->
            label(Os, Options, Selection, O1, Choice, Optim, Consistency, Vars)
        ;   override(choice, Choice, O, Options, C1) ->
            label(Os, Options, Selection, Order, C1, Optim, Consistency, Vars)
        ;   optimisation(O) ->
            label(Os, Options, Selection, Order, Choice, [O|Optim], Consistency, Vars)
        ;   consistency(O, O1) ->
            label(Os, Options, Selection, Order, Choice, Optim, O1, Vars)
        ;   domain_error(labeling_option, O)
        ).
label([], _, Selection, Order, Choice, Optim0, Consistency, Vars) :-
        maplist(arg(1), [Selection,Order,Choice], [S,O,C]),
        (   Optim0 == [] ->
            label(Vars, S, O, C, Consistency)
        ;   reverse(Optim0, Optim),
            exprs_singlevars(Optim, SVs),
            call_cleanup(optimise(Vars, [S,O,C], SVs),
                         retractall(extremum(_)))
        ).

% Introduce new variables for each min/max expression to avoid
% reparsing expressions during optimisation.

exprs_singlevars([], []).
exprs_singlevars([E|Es], [SV|SVs]) :-
        E =.. [F,Expr],
        #Single #= Expr,
        SV =.. [F,Single],
        exprs_singlevars(Es, SVs).

all_dead(fd_props(Bs,Gs,Os)) :-
        all_dead_(Bs),
        all_dead_(Gs),
        all_dead_(Os).

all_dead_([]).
all_dead_([propagator(_, S)|Ps]) :- S == dead, all_dead_(Ps).

label([], _, _, _, Consistency) :- !,
        (   Consistency = upto_in(I0,I) -> I0 = I
        ;   true
        ).
label(Vars, Selection, Order, Choice, Consistency) :-
        (   Vars = [V|Vs], nonvar(V) -> label(Vs, Selection, Order, Choice, Consistency)
        ;   select_var(Selection, Vars, Var, RVars),
            (   var(Var) ->
                (   Consistency = upto_in(I0,I), fd_get(Var, _, Ps), all_dead(Ps) ->
                    fd_size(Var, Size),
                    I1 is I0*Size,
                    label(RVars, Selection, Order, Choice, upto_in(I1,I))
                ;   Consistency = upto_in, fd_get(Var, _, Ps), all_dead(Ps) ->
                    label(RVars, Selection, Order, Choice, Consistency)
                ;   choice_order_variable(Choice, Order, Var, RVars, Vars, Selection, Consistency)
                )
            ;   label(RVars, Selection, Order, Choice, Consistency)
            )
        ).

choice_order_variable(step, Order, Var, Vars, Vars0, Selection, Consistency) :-
        fd_get(Var, Dom, _),
        order_dom_next(Order, Dom, Next),
        (   Var = Next,
            label(Vars, Selection, Order, step, Consistency)
        ;   neq_num(Var, Next),
            label(Vars0, Selection, Order, step, Consistency)
        ).
choice_order_variable(enum, Order, Var, Vars, _, Selection, Consistency) :-
        fd_get(Var, Dom0, _),
        domain_direction_element(Dom0, Order, Var),
        label(Vars, Selection, Order, enum, Consistency).
choice_order_variable(bisect, Order, Var, _, Vars0, Selection, Consistency) :-
        fd_get(Var, Dom, _),
        domain_infimum(Dom, n(I)),
        domain_supremum(Dom, n(S)),
        Mid0 is (I + S) // 2,
        (   Mid0 =:= S -> Mid is Mid0 - 1 ; Mid = Mid0 ),
        (   Order == up -> ( Var #=< Mid ; Var #> Mid )
        ;   Order == down -> ( Var #> Mid ; Var #=< Mid )
        ;   domain_error(bisect_up_or_down, Order)
        ),
        label(Vars0, Selection, Order, bisect, Consistency).

override(What, Prev, Value, Options, Result) :-
        call(What, Value),
        override_(Prev, Value, Options, Result).

override_(default(_), Value, _, user(Value)).
override_(user(Prev), Value, Options, _) :-
        (   Value == Prev ->
            domain_error(nonrepeating_labeling_options, Options)
        ;   domain_error(consistent_labeling_options, Options)
        ).

selection(ff).
selection(ffc).
selection(min).
selection(max).
selection(leftmost).

choice(step).
choice(enum).
choice(bisect).

order(up).
order(down).

consistency(upto_in(I), upto_in(1, I)).
consistency(upto_in, upto_in).
consistency(upto_ground, upto_ground).

optimisation(min(_)).
optimisation(max(_)).

select_var(leftmost, [Var|Vars], Var, Vars).
select_var(min, [V|Vs], Var, RVars) :-
        find_min(Vs, V, Var),
        delete_eq([V|Vs], Var, RVars).
select_var(max, [V|Vs], Var, RVars) :-
        find_max(Vs, V, Var),
        delete_eq([V|Vs], Var, RVars).
select_var(ff, [V|Vs], Var, RVars) :-
        fd_size_(V, n(S)),
        find_ff(Vs, V, S, Var),
        delete_eq([V|Vs], Var, RVars).
select_var(ffc, [V|Vs], Var, RVars) :-
        find_ffc(Vs, V, Var),
        delete_eq([V|Vs], Var, RVars).

find_min([], Var, Var).
find_min([V|Vs], CM, Min) :-
        (   min_lt(V, CM) ->
            find_min(Vs, V, Min)
        ;   find_min(Vs, CM, Min)
        ).

find_max([], Var, Var).
find_max([V|Vs], CM, Max) :-
        (   max_gt(V, CM) ->
            find_max(Vs, V, Max)
        ;   find_max(Vs, CM, Max)
        ).

find_ff([], Var, _, Var).
find_ff([V|Vs], CM, S0, FF) :-
        (   nonvar(V) -> find_ff(Vs, CM, S0, FF)
        ;   (   fd_size_(V, n(S1)), S1 < S0 ->
                find_ff(Vs, V, S1, FF)
            ;   find_ff(Vs, CM, S0, FF)
            )
        ).

find_ffc([], Var, Var).
find_ffc([V|Vs], Prev, FFC) :-
        (   ffc_lt(V, Prev) ->
            find_ffc(Vs, V, FFC)
        ;   find_ffc(Vs, Prev, FFC)
        ).


ffc_lt(X, Y) :-
        (   fd_get(X, XD, XPs) ->
            domain_num_elements(XD, n(NXD))
        ;   NXD = 1, XPs = []
        ),
        (   fd_get(Y, YD, YPs) ->
            domain_num_elements(YD, n(NYD))
        ;   NYD = 1, YPs = []
        ),
        (   NXD < NYD -> true
        ;   NXD =:= NYD,
            props_number(XPs, NXPs),
            props_number(YPs, NYPs),
            NXPs > NYPs
        ).

min_lt(X,Y) :- bounds(X,LX,_), bounds(Y,LY,_), LX < LY.

max_gt(X,Y) :- bounds(X,_,UX), bounds(Y,_,UY), UX > UY.

bounds(X, L, U) :-
        (   fd_get(X, Dom, _) ->
            domain_infimum(Dom, n(L)),
            domain_supremum(Dom, n(U))
        ;   L = X, U = L
        ).

delete_eq([], _, []).
delete_eq([X|Xs], Y, List) :-
        (   nonvar(X) -> delete_eq(Xs, Y, List)
        ;   X == Y -> List = Xs
        ;   List = [X|Tail],
            delete_eq(Xs, Y, Tail)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   contracting/1 -- subject to change

   This can remove additional domain elements from the boundaries.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

contracting(Vs) :-
        must_be(list, contracting(Vs)-1, Vs),
        maplist(finite_domain(contracting(Vs), 1), Vs),
        contracting(Vs, false, Vs).

contracting([], Repeat, Vars) :-
        (   Repeat -> contracting(Vars, false, Vars)
        ;   true
        ).
contracting([V|Vs], Repeat, Vars) :-
        fd_inf(V, Min),
        (   \+ \+ (V = Min) ->
            fd_sup(V, Max),
            (   \+ \+ (V = Max) ->
                contracting(Vs, Repeat, Vars)
            ;   V #\= Max,
                contracting(Vs, true, Vars)
            )
        ;   V #\= Min,
            contracting(Vs, true, Vars)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fds_sespsize(Vs, S).

   S is an upper bound on the search space size with respect to finite
   domain variables Vs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

fds_sespsize(Vs, S) :-
        must_be(list, Vs),
        maplist(fd_variable, Vs),
        fds_sespsize(Vs, n(1), S1),
        bound_portray(S1, S).

fd_size_(V, S) :-
        (   fd_get(V, D, _) ->
            domain_num_elements(D, S)
        ;   S = n(1)
        ).

fds_sespsize([], S, S).
fds_sespsize([V|Vs], S0, S) :-
        fd_size_(V, S1),
        S2 cis S0*S1,
        fds_sespsize(Vs, S2, S).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Optimisation uses the clause database to save the computed extremum
   over backtracking. Failure is used to get rid of copies of
   attributed variables that are created in intermediate steps.

   Example:

     ?- X in 1..3, call_residue_vars(labeling([min(X)], [X]), Vs).
     %@    X = 1, Vs = []
     %@ ;  X = 2, Vs = []
     %@ ;  X = 3, Vs = []
     %@ ;  false.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- dynamic(extremum/1).

optimise(Vars, Options, Whats) :-
        Whats = [What|WhatsRest],
        asserta(extremum(mark)),
        (   catch(store_extremum(Vars, Options, What),
                  time_limit_exceeded,
                  false)
        ;   once(extremum(Val0)),
            retract_until_mark,
            Val0 = n(Val),
            arg(1, What, Expr),
            append(WhatsRest, Options, Options1),
            (   Expr #= Val,
                labeling(Options1, Vars)
            ;   Expr #\= Val,
                optimise(Vars, Options, Whats)
            )
        ).

retract_until_mark :-
        (   retract(extremum(E)), E == mark -> true
        ;   retract_until_mark
        ).

store_extremum(Vars, Options, What) :-
        catch((labeling(Options, Vars), throw(w(What))), w(What1), true),
        functor(What, Direction, _),
        maplist(arg(1), [What,What1], [Expr,Expr1]),
        optimise(Direction, Options, Vars, Expr1, Expr).

optimise(Direction, Options, Vars, Expr0, Expr) :-
        must_be(ground, Expr0),
        update_extremum(Expr0),
        catch((tighten(Direction, Expr, Expr0),
               labeling(Options, Vars),
               throw(v(Expr))), v(Expr1), true),
        optimise(Direction, Options, Vars, Expr1, Expr).


update_extremum(Expr) :-
        (   once(extremum(Prev)),
            Prev = n(_) ->
            once(retract(extremum(_)))
        ;   true
        ),
        asserta(extremum(n(Expr))).

tighten(min, E, V) :- E #< V.
tighten(max, E, V) :- E #> V.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% all_different(+Vars)
%
% Like all_distinct/1, but with weaker propagation.

all_different(Ls) :-
        fd_must_be_list(Ls, all_different(Ls)-1),
        maplist(fd_variable, Ls),
        Orig = original_goal(_, all_different(Ls)),
        new_queue(Q0),
        phrase((all_different(Ls, [], Orig),do_queue), [Q0], _).

all_different([], _, _) --> [].
all_different([X|Right], Left, Orig) -->
        (   { var(X) } ->
            { make_propagator(pdifferent(Left,Right,X,Orig), Prop) },
            init_propagator_([X], Prop),
            trigger_prop(Prop)
        ;   exclude_fire(Left, Right, X)
        ),
        all_different(Right, [X|Left], Orig).

%% all_distinct(+Vars).
%
%  True iff Vars are pairwise distinct. For example, all_distinct/1
%  can detect that not all variables can assume distinct values given
%  the following domains:
%
% ```
%  ?- maplist(in, Vs,
%             [1\/3..4, 1..2\/4, 1..2\/4, 1..3, 1..3, 1..6]),
%     all_distinct(Vs).
%  false.
% ```

all_distinct(Ls) :-
        fd_must_be_list(Ls, all_distinct(Ls)-1),
        maplist(fd_variable, Ls),
        make_propagator(pdistinct(Ls), Prop),
        new_queue(Q0),
        phrase((distinct_attach(Ls, Prop, []),trigger_prop(Prop),do_queue), [Q0], _),
        variables_same_queue(Ls).

%% nvalue(?N, +Vars).
%
%  True if N is the number of distinct values taken by Vars. Vars is a
%  list of domain variables, and N is a domain variable. Can be
%  thought of as a relaxed version of all_distinct/1.

nvalue(N, Vars) :-
        fd_must_be_list(Vars),
        maplist(fd_variable, Vars),
        length(Vars, Len),
        N in 0..Len,
        zero_or_more(Vars, N),
        propagator_init_trigger(Vars, pnvalue(N, Vars)).

zero_or_more([], 0).
zero_or_more([_|_], N) :- N #> 0.

%% sum(+Vars, +Rel, ?Expr)
%
% The sum of elements of the list Vars is in relation Rel to Expr.
% Rel is one of #=, #\=, #<, #>, #=< or #>=. For example:
%
% ```
% ?- [A,B,C] ins 0..sup, sum([A,B,C], #=, 100).
% A in 0..100,
% A+B+C#=100,
% B in 0..100,
% C in 0..100.
% ```

sum(Vs, Op, Value) :-
        must_be(list, Vs),
        same_length(Vs, Ones),
        maplist(=(1), Ones),
        scalar_product(Ones, Vs, Op, Value).

%% scalar_product(+Cs, +Vs, +Rel, ?Expr)
%
% True iff the scalar product of Cs and Vs is in relation Rel to Expr.
% Cs is a list of integers, Vs is a list of variables and integers.
% Rel is #=, #\=, #<, #>, #=< or #>=.

scalar_product(Cs, Vs, Op, Value) :-
        must_be(list(integer), Cs),
        must_be(list, Vs),
        maplist(fd_variable, Vs),
        (   Op = (#=), single_value(Value, Right), ground(Vs) ->
            foldl(coeff_int_linsum, Cs, Vs, 0, Right)
        ;   must_be(ground, Op),
            (   memberchk(Op, [#=,#\=,#<,#>,#=<,#>=]) -> true
            ;   domain_error(scalar_product_relation, Op)
            ),
            must_be(acyclic, Value),
            foldl(coeff_var_plusterm, Cs, Vs, 0, Left),
            (   left_right_linsum_const(Left, Value, Cs1, Vs1, Const) ->
                scalar_product_(Op, Cs1, Vs1, Const)
            ;   sum(Cs, Vs, 0, Op, Value)
            )
        ).

single_value(V, V)    :- var(V), !, non_monotonic(V).
single_value(V, V)    :- integer(V).
single_value(?(V), V) :- fd_variable(V).

coeff_var_plusterm(C, V, T0, T0+(C* #V)).

coeff_int_linsum(C, I, S0, S) :- S is S0 + C*I.

sum([], _, Sum, Op, Value) :- call(Op, Sum, Value).
sum([C|Cs], [X|Xs], Acc, Op, Value) :-
        #NAcc #= Acc + C* #X,
        sum(Cs, Xs, NAcc, Op, Value).

multiples([], [], _).
multiples([C|Cs], [V|Vs], Left) :-
        (   (   Cs = [N|_] ; Left = [N|_] ) ->
            (   N =\= 1, gcd(C,N) =:= 1 ->
                gcd(Cs, N, GCD0),
                gcd(Left, GCD0, GCD),
                (   GCD > 1 -> #V #= GCD * #_
                ;   true
                )
            ;   true
            )
        ;   true
        ),
        multiples(Cs, Vs, [C|Left]).

abs(N, A) :- A is abs(N).

divide(D, N, R) :- R is N // D.

scalar_product_(#=, Cs0, Vs, S0) :-
        (   Cs0 = [C|Rest] ->
            gcd(Rest, C, GCD),
            S0 mod GCD =:= 0,
            maplist(divide(GCD), [S0|Cs0], [S|Cs])
        ;   S0 =:= 0, S = S0, Cs = Cs0
        ),
        (   S0 =:= 0 ->
            maplist(abs, Cs, As),
            multiples(As, Vs, [])
        ;   true
        ),
        propagator_init_trigger(Vs, scalar_product_eq(Cs, Vs, S)).
scalar_product_(#\=, Cs, Vs, C) :-
        propagator_init_trigger(Vs, scalar_product_neq(Cs, Vs, C)).
scalar_product_(#=<, Cs, Vs, C) :-
        propagator_init_trigger(Vs, scalar_product_leq(Cs, Vs, C)).
scalar_product_(#<, Cs, Vs, C) :-
        C1 is C - 1,
        scalar_product_(#=<, Cs, Vs, C1).
scalar_product_(#>, Cs, Vs, C) :-
        C1 is C + 1,
        scalar_product_(#>=, Cs, Vs, C1).
scalar_product_(#>=, Cs, Vs, C) :-
        maplist(negative, Cs, Cs1),
        C1 is -C,
        scalar_product_(#=<, Cs1, Vs, C1).

negative(X0, X) :- X is -X0.

coeffs_variables_const([], [], [], [], I, I).
coeffs_variables_const([C|Cs], [V|Vs], Cs1, Vs1, I0, I) :-
        (   var(V) ->
            Cs1 = [C|CRest], Vs1 = [V|VRest], I1 = I0
        ;   I1 is I0 + C*V,
            Cs1 = CRest, Vs1 = VRest
        ),
        coeffs_variables_const(Cs, Vs, CRest, VRest, I1, I).

sum_finite_domains([], [], Inf, Sup, Inf, Sup) ++> [].
sum_finite_domains([C|Cs], [V|Vs], Inf0, Sup0, Inf, Sup) ++>
        { fd_get(V, _, Inf1, Sup1, _) },
        (   Inf1 = n(NInf) ->
            (   C < 0 ->
                Sup2 is Sup0 + C*NInf
            ;   Inf2 is Inf0 + C*NInf
            )
        ;   (   C < 0 ->
                Sup2 = Sup0,
                []+[C*V]
            ;   Inf2 = Inf0,
                [C*V]+[]
            )
        ),
        (   Sup1 = n(NSup) ->
            (   C < 0 ->
                Inf2 is Inf0 + C*NSup
            ;   Sup2 is Sup0 + C*NSup
            )
        ;   (   C < 0 ->
                Inf2 = Inf0,
                [C*V]+[]
            ;   Sup2 = Sup0,
                []+[C*V]
            )
        ),
        sum_finite_domains(Cs, Vs, Inf2, Sup2, Inf, Sup).

remove_dist_upper_lower([], _, _, _) --> [].
remove_dist_upper_lower([C|Cs], [V|Vs], D1, D2) -->
        (   { fd_get(V, VD, VPs) } ->
            (   C < 0 ->
                { domain_supremum(VD, n(Sup)),
                  L is Sup + D1//C,
                  domain_remove_smaller_than(VD, L, VD1),
                  domain_infimum(VD1, n(Inf)),
                  G is Inf - D2//C,
                  domain_remove_greater_than(VD1, G, VD2) }
            ;   { domain_infimum(VD, n(Inf)),
                  G is Inf + D1//C,
                  domain_remove_greater_than(VD, G, VD1),
                  domain_supremum(VD1, n(Sup)),
                  L is Sup - D2//C,
                  domain_remove_smaller_than(VD1, L, VD2) }
            ),
            fd_put(V, VD2, VPs)
        ;   true
        ),
        remove_dist_upper_lower(Cs, Vs, D1, D2).


remove_dist_upper_leq([], _, _) --> [].
remove_dist_upper_leq([C|Cs], [V|Vs], D1) -->
        (   { fd_get(V, VD, VPs) } ->
            (   C < 0 ->
                { domain_supremum(VD, n(Sup)),
                  L is Sup + D1//C,
                  domain_remove_smaller_than(VD, L, VD1) }
            ;   { domain_infimum(VD, n(Inf)),
                  G is Inf + D1//C,
                  domain_remove_greater_than(VD, G, VD1) }
            ),
            fd_put(V, VD1, VPs)
        ;   true
        ),
        remove_dist_upper_leq(Cs, Vs, D1).


remove_dist_upper([], _) --> [].
remove_dist_upper([C*V|CVs], D) -->
        (   { fd_get(V, VD, VPs) } ->
            (   C < 0 ->
                (   { domain_supremum(VD, n(Sup)) } ->
                    { L is Sup + D//C,
                      domain_remove_smaller_than(VD, L, VD1) }
                ;   VD1 = VD
                )
            ;   (   { domain_infimum(VD, n(Inf)) } ->
                    { G is Inf + D//C,
                      domain_remove_greater_than(VD, G, VD1) }
                ;   VD1 = VD
                )
            ),
            fd_put(V, VD1, VPs)
        ;   true
        ),
        remove_dist_upper(CVs, D).

remove_dist_lower([], _) --> [].
remove_dist_lower([C*V|CVs], D) -->
        (   { fd_get(V, VD, VPs) } ->
            (   C < 0 ->
                (   { domain_infimum(VD, n(Inf)) } ->
                    { G is Inf - D//C,
                      domain_remove_greater_than(VD, G, VD1) }
                ;   VD1 = VD
                )
            ;   (   { domain_supremum(VD, n(Sup)) } ->
                    { L is Sup - D//C,
                      domain_remove_smaller_than(VD, L, VD1) }
                ;   VD1 = VD
                )
            ),
            fd_put(V, VD1, VPs)
        ;   true
        ),
        remove_dist_lower(CVs, D).

remove_upper([], _) --> [].
remove_upper([C*X|CXs], Max) -->
        (   { fd_get(X, XD, XPs) } ->
            D is Max//C,
            (   C < 0 ->
                { domain_remove_smaller_than(XD, D, XD1) }
            ;   { domain_remove_greater_than(XD, D, XD1) }
            ),
            fd_put(X, XD1, XPs)
        ;   true
        ),
        remove_upper(CXs, Max).

remove_lower([], _) --> [].
remove_lower([C*X|CXs], Min) -->
        (   { fd_get(X, XD, XPs) } ->
            D is -Min//C,
            (   C < 0 ->
                { domain_remove_greater_than(XD, D, XD1) }
            ;   { domain_remove_smaller_than(XD, D, XD1) }
            ),
            fd_put(X, XD1, XPs)
        ;   true
        ),
        remove_lower(CXs, Min).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Parsing a CLP(ℤ) expression has two important side-effects: First,
   it constrains the variables occurring in the expression to
   integers. Second, it constrains some of them even more: For
   example, in X/Y and X mod Y, Y is constrained to be #\= 0.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

constrain_to_integer(Var) :-
        (   integer(Var) -> true
        ;   fd_get(Var, D, Ps),
            fd_put(Var, D, Ps)
        ).

power_var_num(P, X, N) :-
        (   var(P) -> X = P, N = 1
        ;   P = Left*Right,
            power_var_num(Left, XL, L),
            power_var_num(Right, XR, R),
            XL == XR,
            X = XL,
            N is L + R
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Given expression E, we obtain the finite domain variable R by
   interpreting a simple committed-choice language that is a list of
   conditions and bodies. In conditions, g(Goal) means literally Goal,
   and m(Match) means that E can be decomposed as stated. The
   variables are to be understood as the result of parsing the
   subexpressions recursively. In the body, g(Goal) means again Goal,
   and p(Propagator) means to attach and trigger once a propagator.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- op(800, xfx, =>).

parse_clpz(E, R,
            [g(cyclic_term(E)) => [g(domain_error(clpz_expression, E))],
             g(var(E))         => [g(non_monotonic(E)),
                                   g(constrain_to_integer(E)), g(E = R)],
             g(integer(E))     => [g(R = E)],
             ?(E)              => [g(must_be_fd_integer(E)), g(R = E)],
             #E                => [g(must_be_fd_integer(E)), g(R = E)],
             m(A+B)            => [p(pplus(A, B, R))],
             % power_var_num/3 must occur before */2 to be useful
             g(power_var_num(E, V, N)) => [p(pexp(V, N, R))],
             m(A*B)            => [p(ptimes(A, B, R))],
             m(A-B)            => [p(pplus(R,B,A))],
             m(-A)             => [p(pplus(A,R,0))],
             m(max(A,B))       => [g(A #=< #R), g(B #=< R), p(pmax(A, B, R))],
             m(min(A,B))       => [g(A #>= #R), g(B #>= R), p(pmin(A, B, R))],
             m(A mod B)        => [g(B #\= 0), p(pmod(A, B, R))],
             m(A rem B)        => [g(B #\= 0), p(prem(A, B, R))],
             m(abs(A))         => [g(#R #>= 0), p(pabs(A, R))],
             m(A/B)            => [g(B #\= 0), p(ptimes(R, B, A))],
             m(A//B)           => [g(B #\= 0), p(ptzdiv(A, B, R))],
             m(A div B)        => [g(#R #= (A - (A mod B)) // B)],
             m(A^B)            => [p(pexp(A, B, R))],
             m(sign(A))        => [g(R in -1..1), p(psign(A, R))],
             % bitwise operations
             m(\A)             => [p(pfunction(\, A, R))],
             m(msb(A))         => [p(pfunction(msb, A, R))],
             m(lsb(A))         => [p(pfunction(lsb, A, R))],
             m(popcount(A))    => [p(ppopcount(A, R))],
             m(A<<B)           => [p(pfunction(<<, A, B, R))],
             m(A>>B)           => [p(pfunction(>>, A, B, R))],
             m(A/\B)           => [p(pfunction(/\, A, B, R))],
             m(A\/B)           => [p(pfunction(\/, A, B, R))],
             m(xor(A, B))      => [p(pxor(A, B, R))],
             g(true)           => [g(domain_error(clpz_expression, E))]
            ]).

non_monotonic(X) :-
        (   \+ fd_var(X), monotonic ->
            instantiation_error(X)
        ;   true
        ).

% Here, we compile the committed choice language to a single
% predicate, parse_clpz/2.

make_parse_clpz(Clauses) :-
        parse_clpz_clauses(Clauses0),
        maplist(goals_goal, Clauses0, Clauses).

goals_goal((Head :- Goals), (Head :- Body)) :-
        list_goal(Goals, Body).

parse_clpz_clauses(Clauses) :-
        parse_clpz(E, R, Matchers),
        maplist(parse_matcher(E, R), Matchers, Clauses).

parse_matcher(E, R, Matcher, Clause) :-
        Matcher = (Condition0 => Goals0),
        phrase((parse_condition(Condition0, E, Head),
                parse_goals(Goals0)), Goals),
        Clause = (parse_clpz(Head, R) :- Goals).

parse_condition(g(Goal), E, E)       --> [Goal, !].
parse_condition(?(E), _, ?(E))       --> [!].
parse_condition(#E, _, #E)           --> [!].
parse_condition(m(Match), _, Match0) -->
        [!],
        { copy_term(Match, Match0),
          term_variables(Match0, Vs0),
          term_variables(Match, Vs)
        },
        parse_match_variables(Vs0, Vs).

parse_match_variables([], []) --> [].
parse_match_variables([V0|Vs0], [V|Vs]) -->
        [parse_clpz(V0, V)],
        parse_match_variables(Vs0, Vs).

parse_goals([]) --> [].
parse_goals([G|Gs]) --> parse_goal(G), parse_goals(Gs).

parse_goal(g(Goal)) --> [Goal].
parse_goal(p(Prop0)) -->
        { term_variables(Prop0, Vs),
          morphing_propagator(Prop0, Prop, _) },
        [make_propagator(Prop, P),
         new_queue(Q0),
         phrase(init_propagator_(Vs, P), [Q0], [Q]),
         variables_same_queue(Vs),
         trigger_once_(P, Q)].

morphing(pplus).
morphing(ptimes).
morphing(pexp).
morphing(ptzdiv).

morphing_propagator(P0, P, Target) :-
        P0 =.. [F|Args0],
        (   morphing(F) ->
            append(Args0, [Last], Args),
            Target = p(Last)
        ;   Args = Args0,
            Target = none
        ),
        P =.. [F|Args].

morph_into_propagator(MState, Vs, P0, Morph) -->
        kill(MState),
        { morphing_propagator(P0, P, _),
          make_propagator(P, Morph) },
        init_propagator_(Vs, Morph),
        trigger_prop(Morph).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- use_module(library(lists)),
   use_module(library(format)),
   clpz:parse_clpz_clauses(Clauses),
   maplist(portray_clause, Clauses).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trigger_once(Prop) :-
        new_queue(Q),
        trigger_once_(Prop, Q).

trigger_once_(Prop, Q) :-
        phrase((trigger_prop(Prop),do_queue), [Q], _).

neq(A, B) :- propagator_init_trigger(pneq(A, B)).

propagator_init_trigger(P) -->
        { term_variables(P, Vs) },
        propagator_init_trigger(Vs, P).

propagator_init_trigger(Vs, P) -->
        [p(Prop)],
        { make_propagator(P, Prop),
          new_queue(Q0),
          phrase(init_propagator_(Vs, Prop), [Q0], [Q]),
          variables_same_queue(Vs),
          trigger_once_(Prop, Q) }.

variables_same_queue(Vs0) :-
        include(var, Vs0, Vs),
        (   Vs == [] -> true
        ;   maplist(variable_queue, Vs, Qs0),
            sort(Qs0, [Q|Qs]),
            Q =.. [_|Args],
            append_queues_(Qs, Args, [append,append,append,ignore]),
            maplist(clear_queue, Qs),
            maplist(=(Q), Qs)
        ).

append_queues_([], _, _).
append_queues_([Q|Qs], Args0, Is) :-
        Q =.. [_|Args],
        maplist(append_queue, Is, Args0, Args),
        append_queues_(Qs, Args, Is).

append_queue(ignore, _, _).
append_queue(append, Q0, Q) :-
        (   get_atts(Q0, queue(Ls0,Ls)) ->
            (   get_atts(Q, queue(Ms0,Ms)) ->
                Ls = Ms0,
                put_atts(Q0, queue(Ls0,Ms))
            ;   true
            )
        ;   (   get_atts(Q, queue(Ms0,Ms)) ->
                put_atts(Q0, queue(Ms0,Ms))
            ;   true
            )
        ).

clear_queue(queue(Goals,Fast,Slow,Aux)) :-
        put_atts(Goals, -queue(_,_)),
        put_atts(Fast, -queue(_,_)),
        put_atts(Slow, -queue(_,_)),
        put_atts(Aux, -disabled).

variable_queue(Var, Q) :-
        get_attr(Var, clpz, Attr),
        Attr = clpz_attr(_Left,_Right,_Spread,_Dom,_Ps,Q).

propagator_init_trigger(P) :-
        phrase(propagator_init_trigger(P), _).

propagator_init_trigger(Vs, P) :-
        phrase(propagator_init_trigger(Vs, P), _).

prop_init(Prop, V) :- init_propagator(V, Prop).

geq(A, B) :-
        new_queue(Q),
        phrase((geq(A, B),do_queue), [Q], _).

geq(A, B) -->
        (   { fd_get(A, AD, APs) } ->
            { domain_infimum(AD, AI) },
            (   { fd_get(B, BD, _) } ->
                { domain_supremum(BD, BS) },
                (   { AI cis_geq BS } -> true
                ;   propagator_init_trigger(pgeq(A,B))
                )
            ;   (   { AI cis_geq n(B) } -> true
                ;   { domain_remove_smaller_than(AD, B, AD1) },
                    fd_put(A, AD1, APs)
                )
            )
        ;   { fd_get(B, BD, BPs) } ->
            { domain_remove_greater_than(BD, A, BD1) },
            fd_put(B, BD1, BPs)
        ;   A >= B
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Naive parsing of inequalities and disequalities can result in a lot
   of unnecessary work if expressions of non-trivial depth are
   involved: Auxiliary variables are introduced for sub-expressions,
   and propagation proceeds on them as if they were involved in a
   tighter constraint (like equality), whereas eventually only very
   little of the propagated information is actually used. For example,
   only extremal values are of interest in inequalities. Introducing
   auxiliary variables should be avoided when possible, and
   specialised propagators should be used for common constraints.

   We again use a simple committed-choice language for matching
   special cases of constraints. m_c(M,C) means that M matches and C
   holds. d(X, Y) means decomposition, i.e., it is short for
   g(parse_clpz(X, Y)). r(X, Y) means to rematch with X and Y.

   Two things are important: First, although the actual constraint
   functors (#\=2, #=/2 etc.) are used in the description, they must
   expand to the respective auxiliary predicates (match_expand/2)
   because the actual constraints are subject to goal expansion.
   Second, when specialised constraints (like scalar product) post
   simpler constraints on their own, these simpler versions must be
   handled separately and must occur before.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

match_expand(#>=, clpz_geq_).
match_expand(#=, clpz_equal_).
match_expand(#\=, clpz_neq).

symmetric(#=).
symmetric(#\=).

matches([
         m_c(any(X) #>= any(Y), left_right_linsum_const(X, Y, Cs, Vs, Const)) =>
            [g((   Cs = [1], Vs = [A] -> geq(A, Const)
               ;   Cs = [-1], Vs = [A] -> Const1 is -Const, geq(Const1, A)
               ;   Cs = [1,1], Vs = [A,B] -> #A + #B #= #S, geq(S, Const)
               ;   Cs = [1,-1], Vs = [A,B] ->
                   (   Const =:= 0 -> geq(A, B)
                   ;   C1 is -Const,
                       propagator_init_trigger(x_leq_y_plus_c(B, A, C1))
                   )
               ;   Cs = [-1,1], Vs = [A,B] ->
                   (   Const =:= 0 -> geq(B, A)
                   ;   C1 is -Const,
                       propagator_init_trigger(x_leq_y_plus_c(A, B, C1))
                   )
               ;   Cs = [-1,-1], Vs = [A,B] ->
                   #A + #B #= #S, Const1 is -Const, geq(Const1, S)
               ;   scalar_product_(#>=, Cs, Vs, Const)
               ))],
         m(any(X) - any(Y) #>= integer(C))     => [d(X, X1), d(Y, Y1), g(C1 is -C), p(x_leq_y_plus_c(Y1, X1, C1))],
         m(integer(X) #>= any(Z) + integer(A)) => [g(C is X - A), r(C, Z)],
         m(abs(any(X)-any(Y)) #>= any(Z))  =>
           [d(X, X1), d(Y, Y1), d(Z, Z1), g((abs(#A)#= #B,Y1+A#=X1,Z1#=<B))],
         m(abs(any(X)) #>= integer(I))         => [d(X, RX), g((I>0 -> I1 is -I, RX in inf..I1 \/ I..sup; true))],
         m(integer(I) #>= abs(any(X)))         => [d(X, RX), g(I>=0), g(I1 is -I), g(RX in I1..I)],
         m(any(X) #>= any(Y))                  => [d(X, RX), d(Y, RY), g(geq(RX, RY))],

         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

         m(var(X) #= var(Y))        => [g(constrain_to_integer(X)), g(X=Y)],
         m(var(X) #= var(Y)+var(Z)) => [p(pplus(Y,Z,X))],
         m(var(X) #= var(Y)-var(Z)) => [p(pplus(X,Z,Y))],
         m(var(X) #= var(Y)*var(Z)) => [p(ptimes(Y,Z,X))],
         m(var(X) #= -var(Y))       => [p(pplus(X,Y,0))],
         m_c(any(X) #= any(Y), left_right_linsum_const(X, Y, Cs, Vs, S)) =>
            [g(scalar_product_(#=, Cs, Vs, S))],
         m_c(var(X) #= abs(var(Y)) + any(V0), X == Y) => [d(V0,V),p(x_eq_abs_plus_v(X,V))],
         m_c(var(X) #= abs(var(Y)) - any(V0), X == Y) => [d(-V0,V),p(x_eq_abs_plus_v(X,V))],
         m(var(X) #= any(Y))       => [d(Y,X)],
         m(any(X) #= any(Y))       => [d(X, RX), d(Y, RX)],

         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
         %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

         m(var(X) #\= integer(Y))             => [g(neq_num(X, Y))],
         m(var(X) #\= var(Y))                 => [p(pneq(X,Y))],
         m(var(X) #\= var(Y) + var(Z))        => [p(x_neq_y_plus_z(X, Y, Z))],
         m(var(X) #\= var(Y) - var(Z))        => [p(x_neq_y_plus_z(Y, X, Z))],
         m(var(X) #\= var(Y)*var(Z))          => [p(ptimes(Y,Z,P)), g(neq(X,P))],
         m(integer(X) #\= abs(any(Y)-any(Z))) => [d(Y, Y1), d(Z, Z1), p(absdiff_neq(Y1, Z1, X))],
         m_c(any(X) #\= any(Y), left_right_linsum_const(X, Y, Cs, Vs, S)) =>
            [g(scalar_product_(#\=, Cs, Vs, S))],
         m(any(X) #\= any(Y) + any(Z))        => [d(X, X1), d(Y, Y1), d(Z, Z1), p(x_neq_y_plus_z(X1, Y1, Z1))],
         m(any(X) #\= any(Y) - any(Z))        => [d(X, X1), d(Y, Y1), d(Z, Z1), p(x_neq_y_plus_z(Y1, X1, Z1))],
         m(any(X) #\= any(Y)) => [d(X, RX), d(Y, RY), g(neq(RX, RY))]
        ]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   We again compile the committed-choice matching language to the
   intended auxiliary predicates. We now must take care not to
   unintentionally unify a variable with a complex term.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

make_matches(Clauses) :-
        matches(Ms),
        findall(F, (member(M=>_, Ms), arg(1, M, M1), functor(M1, F, _)), Fs0),
        sort(Fs0, Fs),
        maplist(prevent_cyclic_argument, Fs, PrevCyclicClauses),
        phrase(matchers(Ms), Clauses0),
        maplist(goals_goal, Clauses0, MatcherClauses),
        append(PrevCyclicClauses, MatcherClauses, Clauses1),
        sort_by_predicate(Clauses1, Clauses).

sort_by_predicate(Clauses, ByPred) :-
        map_list_to_pairs(predname, Clauses, Keyed),
        keysort(Keyed, KeyedByPred),
        pairs_values(KeyedByPred, ByPred).

predname((H:-_), Key)   :- !, predname(H, Key).
predname(M:H, M:Key)    :- !, predname(H, Key).
predname(H, Name/Arity) :- !, functor(H, Name, Arity).

prevent_cyclic_argument(F0, Clause) :-
        match_expand(F0, F),
        Head =.. [F,X,Y],
        Clause = (Head :- (   cyclic_term(X) ->
                              domain_error(clpz_expression, X)
                          ;   cyclic_term(Y) ->
                              domain_error(clpz_expression, Y)
                          ;   false
                          )).

matchers([]) --> [].
matchers([Condition => Goals|Ms]) -->
        matcher(Condition, Goals),
        matchers(Ms).

matcher(m(M), Gs) --> matcher(m_c(M,true), Gs).
matcher(m_c(Matcher,Cond), Gs) -->
        [(Head :- Goals0)],
        { Matcher =.. [F,A,B],
          match_expand(F, Expand),
          Head =.. [Expand,X,Y],
          phrase((match(A, X), match(B, Y)), Goals0, [Cond,!|Goals1]),
          phrase(match_goals(Gs, Expand), Goals1) },
        (   { symmetric(F), \+ (subsumes_term(A, B), subsumes_term(B, A)) } ->
            { Head1 =.. [Expand,Y,X] },
            [(Head1 :- Goals0)]
        ;   []
        ).

match(any(A), T)     --> [A = T].
match(var(V), T)     --> [( nonvar(T), ( T = ?(Var) ; T = #Var ) ->
                            must_be_fd_integer(Var), V = Var
                          ; v_or_i(T), V = T
                          )].
match(integer(I), T) --> [integer(T), I = T].
match(-X, T)         --> [nonvar(T), T = -A], match(X, A).
match(abs(X), T)     --> [nonvar(T), T = abs(A)], match(X, A).
match(X+Y, T)        --> [nonvar(T), T = A + B], match(X, A), match(Y, B).
match(X-Y, T)        --> [nonvar(T), T = A - B], match(X, A), match(Y, B).
match(X*Y, T)        --> [nonvar(T), T = A * B], match(X, A), match(Y, B).

match_goals([], _)     --> [].
match_goals([G|Gs], F) --> match_goal(G, F), match_goals(Gs, F).

match_goal(r(X,Y), F)  --> { G =.. [F,X,Y] }, [G].
match_goal(d(X,Y), _)  --> [parse_clpz(X, Y)].
match_goal(g(Goal), _) --> [Goal].
match_goal(p(Prop0), _) -->
        { term_variables(Prop0, Vs),
          morphing_propagator(Prop0, Prop, _) },
        [make_propagator(Prop, P),
         new_queue(Q0),
         phrase(init_propagator_(Vs, P), [Q0], [Q]),
         variables_same_queue(Vs),
         trigger_once_(P, Q)].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%% #>=(?X, ?Y)
%
% Same as Y #=< X. When reasoning over integers, replace (>=)/2 by (#>=)/2
% to obtain more general relations.

X #>= Y :- clpz_geq(X, Y).

clpz_geq(X, Y) :- clpz_geq_(X, Y), reinforce(X), reinforce(Y).

%% #=<(?X, ?Y)
%
% The arithmetic expression X is less than or equal to Y. When
% reasoning over integers, replace (=<)/2 by (#=<)/2 to obtain more
% general relations.

X #=< Y :- Y #>= X.

%% #=(?X, ?Y)
%
% The arithmetic expression X equals Y. When reasoning over integers,
% replace `(is)/2` by `(#=)/2` to obtain more general relations.

X #= Y :- clpz_equal(X, Y).

clpz_equal(X, Y) :- clpz_equal_(X, Y), reinforce(X).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Conditions under which an equality can be compiled to built-in
   arithmetic. Their order is significant. (/)/2 becomes (//)/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

expr_conds(E, E)                 --> [integer(E)],
        { var(E), !, \+ monotonic }.
expr_conds(E, E)                 --> { integer(E) }.
expr_conds(?(E), E)              --> [integer(E)].
expr_conds(#E, E)                --> [integer(E)].
expr_conds(-E0, -E)              --> expr_conds(E0, E).
expr_conds(abs(E0), abs(E))      --> expr_conds(E0, E).
expr_conds(A0+B0, A+B)           --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0*B0, A*B)           --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0-B0, A-B)           --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0//B0, A//B)         -->
        expr_conds(A0, A), expr_conds(B0, B),
        [B =\= 0].
%expr_conds(A0/B0, AB)            --> expr_conds(A0//B0, AB).
expr_conds(min(A0,B0), min(A,B)) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(max(A0,B0), max(A,B)) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0 mod B0, A mod B)   -->
        expr_conds(A0, A), expr_conds(B0, B),
        [B =\= 0].
expr_conds(A0^B0, A^B)           -->
        expr_conds(A0, A), expr_conds(B0, B),
        [(B >= 0 ; A =:= -1)].
% Bitwise operations, added to make CLP(ℤ) usable in more cases
expr_conds(\ A0, \ A) --> expr_conds(A0, A).
expr_conds(A0<<B0, A<<B) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0>>B0, A>>B) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0/\B0, A/\B) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(A0\/B0, A\/B) --> expr_conds(A0, A), expr_conds(B0, B).
expr_conds(xor(A0,B0), xor(A,B)) --> expr_conds(A0, A), expr_conds(B0, B).
% expr_conds(lsb(A0), lsb(A)) --> expr_conds(A0, A).
% expr_conds(msb(A0), msb(A)) --> expr_conds(A0, A).
expr_conds(popcount(A0), Count) -->
        expr_conds(A0, A),
        [I is A, arithmetic:popcount(I, Count)].

no_popcount_t(Gs, T) :-
        (   member(arithmetic:popcount(_, _), Gs) ->
            T = false
        ;   T = true
        ).

clpz_expandable(_ in _).
clpz_expandable(_ #= _).
clpz_expandable(_ #>= _).
clpz_expandable(_ #=< _).
clpz_expandable(_ #> _).
clpz_expandable(_ #< _).
clpz_expandable(_ #\= _).
clpz_expandable(_ #<==> _).

clpz_expansion(Var in Dom, In) :-
        (   ground(Dom), Dom = L..U, integer(L), integer(U) ->
            expansion_simpler(
                (   integer(Var) ->
                    between:between(L, U, Var)
                ;   clpz:clpz_in(Var, Dom)
                ), In)
        ;   In = clpz:clpz_in(Var, Dom)
        ).
clpz_expansion(A #<==> B, Reif) :-
        nonvar(A),
        A =.. [F0,X0,Y0],
        clpz_builtin(F0, F),
        phrase(expr_conds(X0, X), Cs0, Cs),
        phrase(expr_conds(Y0, Y), Cs),
        list_goal(Cs0, Cond),
        Expr =.. [F,X,Y],
        expansion_simpler(( Cond, ( var(B) ; integer(B), clpz:between(0, 1, B) ) ->
                            (   Expr ->
                                B = 1
                            ;   B = 0
                            )
                          ; clpz:reify(A, RA),
                            clpz:reify(B, RA)
                          ), Reif).
clpz_expansion(X0 #= Y0, Equal) :-
        phrase(expr_conds(X0, X), CsX),
        phrase(expr_conds(Y0, Y), CsY),
        list_goal(CsX, CondX),
        list_goal(CsY, CondY),
        no_popcount_t(CsY, YT),
        no_popcount_t(CsX, XT),
        expansion_simpler(
                (   CondX ->
                    (   YT, var(Y) -> Y is X
                    ;   CondY -> X =:= Y
                    ;   T is X, clpz:clpz_equal(T, Y0)
                    )
                ;   CondY ->
                    (   XT, var(X) -> X is Y
                    ;   T is Y, clpz:clpz_equal(X0, T)
                    )
                ;   clpz:clpz_equal(X0, Y0)
                ), Equal).
clpz_expansion(X0 #>= Y0, Geq) :-
        phrase(expr_conds(X0, X), CsX),
        phrase(expr_conds(Y0, Y), CsY),
        list_goal(CsX, CondX),
        list_goal(CsY, CondY),
        expansion_simpler(
              (   CondX ->
                  (   CondY -> X >= Y
                  ;   T is X, clpz:clpz_geq(T, Y0)
                  )
              ;   CondY -> T is Y, clpz:clpz_geq(X0, T)
              ;   clpz:clpz_geq(X0, Y0)
              ), Geq).
clpz_expansion(X #=< Y,  Leq) :- clpz_expansion(Y #>= X, Leq).
clpz_expansion(X #> Y, Gt)    :- clpz_expansion(X #>= Y+1, Gt).
clpz_expansion(X #< Y, Lt)    :- clpz_expansion(Y #> X, Lt).
clpz_expansion(X0 #\= Y0, Neq) :-
        phrase(expr_conds(X0, X), CsX),
        phrase(expr_conds(Y0, Y), CsY),
        list_goal(CsX, CondX),
        list_goal(CsY, CondY),
        expansion_simpler(
              (   CondX ->
                  (   CondY -> X =\= Y
                  ;   T is X, clpz:clpz_neq(T, Y0)
                  )
              ;   CondY -> T is Y, clpz:clpz_neq(X0, T)
              ;   clpz:clpz_neq(X0, Y0)
              ), Neq).


clpz_builtin(#=, =:=).
clpz_builtin(#\=, =\=).
clpz_builtin(#>, >).
clpz_builtin(#<, <).
clpz_builtin(#>=, >=).
clpz_builtin(#=<, =<).

expansion_simpler((True->Then0;_), Then) :-
        is_true(True), !,
        expansion_simpler(Then0, Then).
expansion_simpler((False->_;Else0), Else) :-
        is_false(False), !,
        expansion_simpler(Else0, Else).
expansion_simpler((If->Then0;Else0), (If->Then;Else)) :- !,
        expansion_simpler(Then0, Then),
        expansion_simpler(Else0, Else).
expansion_simpler((A0,B0), (A,B)) :- !,
        expansion_simpler(A0, A),
        expansion_simpler(B0, B).
expansion_simpler(Var is Expr0, Goal) :-
        ground(Expr0), !,
        phrase(expr_conds(Expr0, Expr), Gs),
        (   maplist(call, Gs) -> Value is Expr, Goal = (Var = Value)
        ;   Goal = false
        ).
expansion_simpler(Var =:= Expr0, Goal) :-
        ground(Expr0), !,
        phrase(expr_conds(Expr0, Expr), Gs),
        (   maplist(call, Gs) -> Value is Expr, Goal = (Var =:= Value)
        ;   Goal = false
        ).
expansion_simpler(between:between(L,U,V), Goal) :-
        maplist(integer, [L,U,V]),
        !,
        (   between(L,U,V) -> Goal = true
        ;   Goal = false
        ).
expansion_simpler(Goal, Goal).

is_true(true).
is_true(integer(I))  :- integer(I).
% :- if(current_predicate(var_property/2)).
% is_true(var(X))      :- var(X), var_property(X, fresh(true)).
% is_false(integer(X)) :- var(X), var_property(X, fresh(true)).
% :- endif.
is_false((A,B))      :- is_false(A) ; is_false(B).
is_false(var(X)) :- nonvar(X).

:- dynamic(goal_expansion/1).

user:goal_expansion(Goal0, Goal) :-
        \+ goal_expansion(false),
        clpz_expandable(Goal0),
        clpz_expansion(Goal0, Goal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

linsum(X, S, S)    --> { var(X), !, non_monotonic(X) }, [vn(X,1)].
linsum(I, S0, S)   --> { integer(I), S is S0 + I }.
linsum(?(X), S, S) --> { must_be_fd_integer(X) }, [vn(X,1)].
linsum(#X, S, S)   --> { must_be_fd_integer(X) }, [vn(X,1)].
linsum(-A, S0, S)  --> mulsum(A, -1, S0, S).
linsum(N*A, S0, S) --> { integer(N) }, !, mulsum(A, N, S0, S).
linsum(A*N, S0, S) --> { integer(N) }, !, mulsum(A, N, S0, S).
linsum(A+B, S0, S) --> linsum(A, S0, S1), linsum(B, S1, S).
linsum(A-B, S0, S) --> linsum(A, S0, S1), mulsum(B, -1, S1, S).

mulsum(A, M, S0, S) -->
        { phrase(linsum(A, 0, CA), As), S is S0 + M*CA },
        lin_mul(As, M).

lin_mul([], _)             --> [].
lin_mul([vn(X,N0)|VNs], M) --> { N is N0*M }, [vn(X,N)], lin_mul(VNs, M).

v_or_i(V) :- var(V), !, non_monotonic(V).
v_or_i(I) :- integer(I).

must_be_fd_integer(X) :-
        (   var(X) -> constrain_to_integer(X)
        ;   must_be(integer, X)
        ).

samsort(Ls0, Ls) :-
        maplist(as_key, Ls0, LKs0),
        keysort(LKs0, LKs),
        maplist(as_key, Ls, LKs).

as_key(E, E-t).

left_right_linsum_const(Left, Right, Cs, Vs, Const) :-
        phrase(linsum(Left, 0, CL), Lefts0, Rights),
        phrase(linsum(Right, 0, CR), Rights0),
        maplist(linterm_negate, Rights0, Rights),
        samsort(Lefts0, Lefts),
        Lefts = [vn(First,N)|LeftsRest],
        vns_coeffs_variables(LeftsRest, N, First, Cs0, Vs0),
        filter_linsum(Cs0, Vs0, Cs, Vs),
        Const is CR - CL.
        %format("linear sum: ~w ~w ~w\n", [Cs,Vs,Const]).

linterm_negate(vn(V,N0), vn(V,N)) :- N is -N0.

vns_coeffs_variables([], N, V, [N], [V]).
vns_coeffs_variables([vn(V,N)|VNs], N0, V0, Ns, Vs) :-
        (   V == V0 ->
            N1 is N0 + N,
            vns_coeffs_variables(VNs, N1, V0, Ns, Vs)
        ;   Ns = [N0|NRest],
            Vs = [V0|VRest],
            vns_coeffs_variables(VNs, N, V, NRest, VRest)
        ).

filter_linsum([], [], [], []).
filter_linsum([C0|Cs0], [V0|Vs0], Cs, Vs) :-
        (   C0 =:= 0 ->
            constrain_to_integer(V0),
            filter_linsum(Cs0, Vs0, Cs, Vs)
        ;   Cs = [C0|Cs1], Vs = [V0|Vs1],
            filter_linsum(Cs0, Vs0, Cs1, Vs1)
        ).

gcd([], G, G).
gcd([N|Ns], G0, G) :-
        G1 is gcd(N, G0),
        gcd(Ns, G1, G).

even(N) :- N mod 2 =:= 0.

odd(N) :- \+ even(N).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   k-th root of N, if N is a k-th power.

   TODO: Replace this when the GMP function becomes available.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

integer_kth_root(N, K, R) :-
        (   even(K) ->
            N >= 0
        ;   true
        ),
        (   K < 0 ->
            (   N =:= 1 -> R = 1
            ;   N =:= -1 -> odd(K), R = -1
            ;   false
            )
        ;   (   N < 0 ->
                odd(K),
                integer_kroot(N, 0, N, K, R)
            ;   integer_kroot(0, N, N, K, R)
            )
        ).

integer_kroot(L, U, N, K, R) :-
        (   L =:= U -> N =:= L^K, R = L
        ;   L + 1 =:= U ->
            (   L^K =:= N -> R = L
            ;   U^K =:= N -> R = U
            ;   false
            )
        ;   Mid is (L + U)//2,
            (   Mid^K > N ->
                integer_kroot(L, Mid, N, K, R)
            ;   integer_kroot(Mid, U, N, K, R)
            )
        ).

integer_log_b(N, B, Log0, Log) :-
        T is B^Log0,
        (   T =:= N -> Log = Log0
        ;   T < N,
            Log1 is Log0 + 1,
            integer_log_b(N, B, Log1, Log)
        ).

floor_integer_log_b(N, B, Log0, Log) :-
        T is B^Log0,
        (   T > N -> Log is Log0 - 1
        ;   T =:= N -> Log = Log0
        ;   T < N,
            Log1 is Log0 + 1,
            floor_integer_log_b(N, B, Log1, Log)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Largest R such that R^K =< N.

   TODO: Replace this when the GMP function becomes available.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

integer_kth_root_leq(N, K, R) :-
        (   even(K) ->
            N >= 0
        ;   true
        ),
        (   N < 0 ->
            odd(K),
            integer_kroot_leq(N, 0, N, K, R)
        ;   integer_kroot_leq(0, N, N, K, R)
        ).

integer_kroot_leq(L, U, N, K, R) :-
        (   L =:= U -> R = L
        ;   L + 1 =:= U ->
            (   U^K =< N -> R = U
            ;   R = L
            )
        ;   Mid is (L + U)//2,
            (   Mid^K > N ->
                integer_kroot_leq(L, Mid, N, K, R)
            ;   integer_kroot_leq(Mid, U, N, K, R)
            )
        ).

%% #\=(?X, ?Y)
%
% The arithmetic expressions X and Y evaluate to distinct integers.
% When reasoning over integers, replace (=\=)/2 by (#\=)/2 to obtain more
% general relations.

X #\= Y :- clpz_neq(X, Y).

% X #\= Y + Z

x_neq_y_plus_z(X, Y, Z) :-
        propagator_init_trigger(x_neq_y_plus_z(X,Y,Z)).

% X is distinct from the number N. This is used internally, and does
% not reinforce other constraints.

neq_num(X, N) :-
        (   fd_get(X, XD, XPs) ->
            domain_remove(XD, N, XD1),
            fd_put(X, XD1, XPs)
        ;   X =\= N
        ).

neq_num(X, N) -->
        (   { fd_get(X, XD, XPs) } ->
            { domain_remove(XD, N, XD1) },
            fd_put(X, XD1, XPs)
        ;   X =\= N
        ).


%% #>(?X, ?Y)
%
% Same as Y #< X.

X #> Y  :- X #>= Y + 1.

%% #<(?X, ?Y)
%
% The arithmetic expression X is less than Y. When reasoning over
% integers, replace `(<)/2` by `(#<)/2` to obtain more general relations.
%
% In addition to its regular use in tasks that require it, this
% constraint can also be useful to eliminate uninteresting symmetries
% from a problem. For example, all possible matches between pairs
% built from four players in total:
%
% ```
% ?- Vs = [A,B,C,D], Vs ins 1..4,
%         all_different(Vs),
%         A #< B, C #< D, A #< C,
%    findall(pair(A,B)-pair(C,D), label(Vs), Ms).
% Ms = [ pair(1, 2)-pair(3, 4),
%        pair(1, 3)-pair(2, 4),
%        pair(1, 4)-pair(2, 3)].
% ```

X #< Y  :- Y #> X.

%% #\(+Q)
%
% The reifiable constraint Q does _not_ hold. For example, to obtain
% the complement of a domain:
%
% ```
% ?- #\ X in -3..0\/10..80.
% X in inf.. -4\/1..9\/81..sup.
% ```

#\ Q       :- reify(Q, 0).

%% #<==>(?P, ?Q)
%
% P and Q are equivalent. For example:
%
% ```
% ?- X #= 4 #<==> B, X #\= 4.
% B = 0,
% X in inf..3\/5..sup.
% ```
% The following example uses reified constraints to relate a list of
% finite domain variables to the number of occurrences of a given value:
%
% ```
% vs_n_num(Vs, N, Num) :-
%         maplist(eq_b(N), Vs, Bs),
%         sum(Bs, #=, Num).
%
% eq_b(X, Y, B) :- X #= Y #<==> B.
% ```
%
% Sample queries and their results:
%
% ```
% ?- Vs = [X,Y,Z], Vs ins 0..1, vs_n_num(Vs, 4, Num).
% Vs = [X, Y, Z],
% Num = 0,
% X in 0..1,
% Y in 0..1,
% Z in 0..1.
%
% ?- vs_n_num([X,Y,Z], 2, 3).
% X = 2,
% Y = 2,
% Z = 2.
% ```

L #<==> R  :- reify(L, B), reify(R, B).

%% #==>(?P, ?Q)
%
% P implies Q.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Implication is special in that created auxiliary constraints can be
   retracted when the implication becomes entailed, for example:

   %?- X + 1 #= Y #==> Z, Z #= 1.
   %@ Z = 1,
   %@ X in inf..sup,
   %@ Y in inf..sup.

   We cannot use propagator_init_trigger/1 here because the states of
   auxiliary propagators are themselves part of the propagator.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

L #==> R   :-
        reify(L, LB, LPs),
        reify(R, RB, RPs),
        append(LPs, RPs, Ps),
        propagator_init_trigger([LB,RB], pimpl(LB,RB,Ps)).

%% #<==(?P, ?Q)
%
% Q implies P.

L #<== R   :- R #==> L.

%% #/\(?P, ?Q)
%
% P and Q hold.

L #/\ R    :- reify(L, 1), reify(R, 1).

conjunctive_neqs_var_drep(Eqs, Var, Drep) :-
        conjunctive_neqs_var(Eqs, Var),
        phrase(conjunctive_neqs_vals(Eqs), Vals),
        list_to_domain(Vals, Dom),
        domain_complement(Dom, C),
        domain_to_drep(C, Drep).

conjunctive_neqs_var(V, _) :- var(V), !, false.
conjunctive_neqs_var(L #\= R, Var) :-
        (   var(L), integer(R) -> Var = L
        ;   integer(L), var(R) -> Var = R
        ;   false
        ).
conjunctive_neqs_var(A #/\ B, VA) :-
        conjunctive_neqs_var(A, VA),
        conjunctive_neqs_var(B, VB),
        VA == VB.

conjunctive_neqs_vals(L #\= R) --> ( { integer(L) } -> [L] ; [R] ).
conjunctive_neqs_vals(A #/\ B) -->
        conjunctive_neqs_vals(A),
        conjunctive_neqs_vals(B).

%% #\/(?P, ?Q)
%
% P or Q holds. For example, the sum of natural numbers below 1000
% that are multiples of 3 or 5:
%
% ```
% ?- findall(N, (N mod 3 #= 0 #\/ N mod 5 #= 0, N in 0..999,
%                indomain(N)),
%            Ns),
%    sum(Ns, #=, Sum).
% Ns = [0, 3, 5, 6, 9, 10, 12, 15, 18|...],
% Sum = 233168.
% ```

L #\/ R :-
        (   disjunctive_eqs_var_drep(L #\/ R, Var, Drep) -> Var in Drep
        ;   reify(L, X, Ps1),
            reify(R, Y, Ps2),
            propagator_init_trigger([X,Y], reified_or(X,Ps1,Y,Ps2,1))
        ).

disjunctive_eqs_var_drep(Eqs, Var, Drep) :-
        disjunctive_eqs_var(Eqs, Var),
        phrase(disjunctive_eqs_vals(Eqs), Vals),
        list_to_drep(Vals, Drep).

disjunctive_eqs_var(V, _) :- var(V), !, false.
disjunctive_eqs_var(V in I, V) :- var(V), integer(I).
disjunctive_eqs_var(L #= R, Var) :-
        (   var(L), integer(R) -> Var = L
        ;   integer(L), var(R) -> Var = R
        ;   false
        ).
disjunctive_eqs_var(A #\/ B, VA) :-
        disjunctive_eqs_var(A, VA),
        disjunctive_eqs_var(B, VB),
        VA == VB.

disjunctive_eqs_vals(L #= R)  --> ( { integer(L) } -> [L] ; [R] ).
disjunctive_eqs_vals(_ in I)  --> [I].
disjunctive_eqs_vals(A #\/ B) -->
        disjunctive_eqs_vals(A),
        disjunctive_eqs_vals(B).

%% #\(?P, ?Q)
%
% Either P holds or Q holds, but not both.

L #\ R :- (L #\/ R) #/\ #\ (L #/\ R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A constraint that is being reified need not hold. Therefore, in
   X/Y, Y can as well be 0, for example. Note that it is OK to
   constrain the *result* of an expression (which does not appear
   explicitly in the expression and is not visible to the outside),
   but not the operands, except for requiring that they be integers.

   In contrast to parse_clpz/2, the result of an expression can now
   also be undefined, in which case the constraint cannot hold.
   Therefore, the committed-choice language is extended by an element
   d(D) that states D is 1 iff all subexpressions are defined. a(V)
   means that V is an auxiliary variable that was introduced while
   parsing a compound expression. a(X,V) means V is auxiliary unless
   it is (==)/2 X, and a(X,Y,V) means V is auxiliary unless it is
   (==)/2 X or Y. l(L) means the literal L occurs in the described
   list, and ls(Ls) means the literals Ls occur in the described list.

   When a constraint becomes entailed or subexpressions become
   undefined, created auxiliary constraints are killed, and the
   "clpz" attribute is removed from auxiliary variables.

   For (//)/2, (mod)/2 and (rem)/2, we create a skeleton propagator
   and remember it as an auxiliary constraint. The pskeleton
   propagator can use the skeleton when the constraint is defined.

   We cannot use a skeleton propagator for (/)/2, since (/)/2 can
   fail in cases such as 0 #==> X #= 1/2, where we expect success.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

parse_reified(E, R, D,
              [g(cyclic_term(E)) => [g(domain_error(clpz_expression, E))],
               g(var(E))     => [g(non_monotonic(E)),
                                 g(constrain_to_integer(E)), g(R = E), g(D=1)],
               g(integer(E)) => [g(R=E), g(D=1)],
               ?(E)          => [g(must_be_fd_integer(E)), g(R=E), g(D=1)],
               #E            => [g(must_be_fd_integer(E)), g(R=E), g(D=1)],
               m(A+B)        => [d(D), p(pplus(A,B,R)), a(A,B,R)],
               m(A*B)        => [d(D), p(ptimes(A,B,R)), a(A,B,R)],
               m(A-B)        => [d(D), p(pplus(R,B,A)), a(A,B,R)],
               m(-A)         => [d(D), p(pplus(A,R,0)), a(R)],
               m(max(A,B))   => [d(D), p(pgeq(R, A)), p(pgeq(R, B)), p(pmax(A,B,R)), a(A,B,R)],
               m(min(A,B))   => [d(D), p(pgeq(A, R)), p(pgeq(B, R)), p(pmin(A,B,R)), a(A,B,R)],
               m(abs(A))     => [d(D), g(#R#>=0), p(pabs(A, R)), a(A,R)],
               m(A^B)        => [d(D1), p(preified_exp(A,B,D2,R)),
                                 p(reified_and(D1,[],D2,[],D)),a(D2),a(A,B,R)],
               m(A/B)        => [d(D1), p(preified_slash(A,B,D2,R)),
                                 p(reified_and(D1,[],D2,[],D)),a(D2),a(A,B,R)],
               m(A div B)    => [d(D1),
                                 g(phrase(parse_reified_clpz(((A-(A mod B)) // B), R, D2), Ps)),
                                 ls(Ps),
                                 p(reified_and(D1,[],D2,[],D)),a(D2),a(A,B,R)],
               m(A//B)       => [skeleton(A,B,D,R,ptzdiv)],
               m(A mod B)    => [skeleton(A,B,D,R,pmod)],
               m(A rem B)    => [skeleton(A,B,D,R,prem)],
               % bitwise operations
               m(\A)         => [function(D,\,A,R)],
               m(msb(A))     => [g(#A#>0) ,function(D,msb,A,R)],
               m(lsb(A))     => [g(#A#>0), function(D,lsb,A,R)],
               m(popcount(A)) => [d(D), p(ppopcount(A, R)), a(A,R)],
               m(sign(A))    => [d(D), p(psign(A, R)), a(A,R)],
               m(A<<B)       => [function(D,<<,A,B,R)],
               m(A>>B)       => [function(D,>>,A,B,R)],
               m(A/\B)       => [function(D,/\,A,B,R)],
               m(A\/B)       => [function(D,\/,A,B,R)],
               m(xor(A, B))  => [skeleton(A,B,D,R,pxor)],
               g(true)       => [g(domain_error(clpz_expression, E))]]
             ).

% Again, we compile this to a predicate, parse_reified_clpz//3. This
% time, it is a DCG that describes the list of auxiliary variables and
% propagators for the given expression, in addition to relating it to
% its reified (Boolean) finite domain variable and its Boolean
% definedness.

make_parse_reified(Clauses) :-
        parse_reified_clauses(Clauses0),
        maplist(goals_goal_dcg, Clauses0, Clauses).

goals_goal_dcg((Head --> Goals), Clause) :-
        list_goal(Goals, Body),
        expand_term((Head --> Body), Clause).

parse_reified_clauses(Clauses) :-
        parse_reified(E, R, D, Matchers),
        maplist(parse_reified(E, R, D), Matchers, Clauses).

parse_reified(E, R, D, Matcher, Clause) :-
        Matcher = (Condition0 => Goals0),
        phrase((reified_condition(Condition0, E, Head, Ds),
                reified_goals(Goals0, Ds)), Goals, [a(D)]),
        Clause = (parse_reified_clpz(Head, R, D) --> Goals).

reified_condition(g(Goal), E, E, []) --> [{Goal}, !].
reified_condition(?(E), _, ?(E), []) --> [!].
reified_condition(#E, _, #E, [])     --> [!].
reified_condition(m(Match), _, Match0, Ds) -->
        [!],
        { copy_term(Match, Match0),
          term_variables(Match0, Vs0),
          term_variables(Match, Vs)
        },
        reified_variables(Vs0, Vs, Ds).

reified_variables([], [], []) --> [].
reified_variables([V0|Vs0], [V|Vs], [D|Ds]) -->
        [parse_reified_clpz(V0, V, D)],
        reified_variables(Vs0, Vs, Ds).

reified_goals([], _) --> [].
reified_goals([G|Gs], Ds) --> reified_goal(G, Ds), reified_goals(Gs, Ds).

reified_goal(d(D), Ds) -->
        (   { Ds = [X] } -> [{D=X}]
        ;   { Ds = [X,Y] } ->
            { phrase(reified_goal(p(reified_and(X,[],Y,[],D)), _), Gs),
              list_goal(Gs, Goal) },
            [( {X==1, Y==1} -> {D = 1} ; Goal )]
        ;   { domain_error(one_or_two_element_list, Ds) }
        ).
reified_goal(g(Goal), _) --> [{Goal}].
reified_goal(p(Vs, Prop0), _) -->
        { morphing_propagator(Prop0, Prop, Target) },
        [{make_propagator(Prop, P)}],
        target_propagator(Target),
        parse_init_dcg(Vs, P),
        [{variables_same_queue(Vs),
          trigger_once(P)}],
        [( { propagator_state(P, S), S == dead } -> [] ; [p(P)])].
reified_goal(p(Prop), Ds) -->
        { term_variables(Prop, Vs) },
        reified_goal(p(Vs,Prop), Ds).
reified_goal(function(D,Op,A,B,R), Ds) -->
        reified_goals([d(D),p(pfunction(Op,A,B,R)),a(A,B,R)], Ds).
reified_goal(function(D,Op,A,R), Ds) -->
        reified_goals([d(D),p(pfunction(Op,A,R)),a(A,R)], Ds).
reified_goal(skeleton(A,B,D,R,F), Ds) -->
        { Prop0 =.. [F,X,Y,Z],
          morphing_propagator(Prop0, Prop, Target) },
        target_propagator(Target),
        reified_goals([d(D1),l(p(P)),g(make_propagator(Prop, P)),
                       p([A,B,D2,R], pskeleton(A,B,D2,[X,Y,Z]-P,R,F)),
                       p(reified_and(D1,[],D2,[],D)),a(D2),a(A,B,R)], Ds).
reified_goal(a(V), _)     --> [a(V)].
reified_goal(a(X,V), _)   --> [a(X,V)].
reified_goal(a(X,Y,V), _) --> [a(X,Y,V)].
reified_goal(l(L), _)     --> [[L]].
reified_goal(ls(Ls), _)   --> [Ls].

target_propagator(p(Prop)) --> [[p(Prop)]].
target_propagator(none)    --> [].

parse_init_dcg([], _)     --> [].
parse_init_dcg([V|Vs], P) --> [{init_propagator(V, P)}], parse_init_dcg(Vs, P).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- use_module(library(lists)),
   use_module(library(format)),
   clpz:parse_reified_clauses(Cs),
   maplist(portray_clause, Cs).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

reify(E, B) :- reify(E, B, _).

reify(Expr, B, Ps) :-
        (   acyclic_term(Expr), reifiable(Expr) -> phrase(reify(Expr, B), Ps)
        ;   domain_error(clpz_reifiable_expression, Expr)
        ).

reifiable(E)      :- var(E), non_monotonic(E).
reifiable(E)      :- integer(E), E in 0..1.
reifiable(?(E))   :- must_be_fd_integer(E).
reifiable(#E)     :- must_be_fd_integer(E).
reifiable(V in _) :- fd_variable(V).
reifiable(Expr)   :-
        Expr =.. [Op,Left,Right],
        (   memberchk(Op, [#>=,#>,#=<,#<,#=,#\=])
        ;   memberchk(Op, [#==>,#<==,#<==>,#/\,#\/,#\]),
            reifiable(Left),
            reifiable(Right)
        ).
reifiable(#\ E) :- reifiable(E).
reifiable(tuples_in(Tuples, Relation)) :-
        must_be(list(list), Tuples),
        maplist(maplist(fd_variable), Tuples),
        must_be(list(list(integer)), Relation).
reifiable(finite_domain(V)) :- fd_variable(V).

reify(E, B) --> { B in 0..1 }, reify_(E, B).

reify_(E, B) --> { var(E), !, E = B }.
reify_(E, B) --> { integer(E), E = B }.
reify_(?(B), B) --> [].
reify_(#B, B) --> [].
reify_(V in Drep, B) -->
        { drep_to_domain(Drep, Dom) },
        propagator_init_trigger(reified_in(V,Dom,B)),
        a(B).
reify_(tuples_in(Tuples, Relation), B) -->
        { maplist(relation_tuple_b_prop(Relation), Tuples, Bs, Ps),
          maplist(monotonic, Bs, Bs1),
          fold_statement(conjunction, Bs1, And),
          #B #<==> And },
        propagator_init_trigger([B], tuples_not_in(Tuples, Relation, B)),
        kill_reified_tuples(Bs, Ps, Bs),
        seq(Ps),
        as([B|Bs]).
reify_(finite_domain(V), B) -->
        propagator_init_trigger(reified_fd(V,B)),
        a(B).
reify_(L #>= R, B) --> arithmetic(L, R, B, reified_geq).
reify_(L #= R, B)  --> arithmetic(L, R, B, reified_eq).
reify_(L #\= R, B) --> arithmetic(L, R, B, reified_neq).
reify_(L #> R, B)  --> reify_(L #>= (R+1), B).
reify_(L #=< R, B) --> reify_(R #>= L, B).
reify_(L #< R, B)  --> reify_(R #>= (L+1), B).
reify_(L #==> R, B)  --> reify_((#\ L) #\/ R, B).
reify_(L #<== R, B)  --> reify_(R #==> L, B).
reify_(L #<==> R, B) --> reify_((L #==> R) #/\ (R #==> L), B).
reify_(L #\ R, B) --> reify_((L #\/ R) #/\ #\ (L #/\ R), B).
reify_(L #/\ R, B)   -->
        (   { conjunctive_neqs_var_drep(L #/\ R, V, D) } -> reify_(V in D, B)
        ;   boolean(L, R, B, reified_and)
        ).
reify_(L #\/ R, B) -->
        (   { disjunctive_eqs_var_drep(L #\/ R, V, D) } -> reify_(V in D, B)
        ;   boolean(L, R, B, reified_or)
        ).
reify_(#\ Q, B) -->
        reify(Q, QR),
        propagator_init_trigger(reified_not(QR,B)),
        a(B).

arithmetic(L, R, B, Functor) -->
        { phrase((parse_reified_clpz(L, LR, LD),
                  parse_reified_clpz(R, RR, RD)), Ps),
          Prop =.. [Functor,LD,LR,RD,RR,Ps,B] },
        seq(Ps),
        propagator_init_trigger([LD,LR,RD,RR,B], Prop),
        a(B).

boolean(L, R, B, Functor) -->
        { reify(L, LR, Ps1), reify(R, RR, Ps2),
          Prop =.. [Functor,LR,Ps1,RR,Ps2,B] },
        seq(Ps1), seq(Ps2),
        propagator_init_trigger([LR,RR,B], Prop),
        a(LR, RR, B).

a(X,Y,B) -->
        (   nonvar(X) -> a(Y, B)
        ;   nonvar(Y) -> a(X, B)
        ;   [a(X,Y,B)]
        ).

a(X, B) -->
        (   { var(X) } -> [a(X, B)]
        ;   a(B)
        ).

a(B) -->
        (   { var(B) } -> [a(B)]
        ;   []
        ).

as([])     --> [].
as([B|Bs]) --> a(B), as(Bs).

kill_reified_tuples([], _, _) --> [].
kill_reified_tuples([B|Bs], Ps, All) -->
        propagator_init_trigger([B], kill_reified_tuples(B, Ps, All)),
        kill_reified_tuples(Bs, Ps, All).

relation_tuple_b_prop(Relation, Tuple, B, p(Prop)) :-
        put_attr(R, clpz_relation, Relation),
        make_propagator(reified_tuple_in(Tuple, R, B), Prop),
        new_queue(Q0),
        phrase((tuple_freeze_(Tuple, Prop),
                init_propagator_([B], Prop),
                do_queue), [Q0], _).


tuples_in_conjunction(Tuples, Relation, Conj) :-
        maplist(tuple_in_disjunction(Relation), Tuples, Disjs),
        fold_statement(conjunction, Disjs, Conj).

tuple_in_disjunction(Relation, Tuple, Disj) :-
        maplist(tuple_in_conjunction(Tuple), Relation, Conjs),
        fold_statement(disjunction, Conjs, Disj).

tuple_in_conjunction(Tuple, Element, Conj) :-
        maplist(var_eq, Tuple, Element, Eqs),
        fold_statement(conjunction, Eqs, Conj).

fold_statement(Operation, List, Statement) :-
        (   List = [] -> Statement = 1
        ;   List = [First|Rest],
            foldl(Operation, Rest, First, Statement)
        ).

conjunction(E, Conj, Conj #/\ E).

disjunction(E, Disj, Disj #\/ E).

var_eq(V, N, #V #= N).

% Match variables to created skeleton.

skeleton(Vs, Vs-Prop) :-
        (   propagator_state(Prop, State), State == dead ->
            true
        ;   maplist(prop_init(Prop), Vs),
            trigger_once(Prop)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A drep is a user-accessible and visible domain representation. N,
   N..M, and D1 \/ D2 are dreps, if D1 and D2 are dreps.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

is_drep(N)      :- integer(N).
is_drep(N..M)   :- drep_bound(N), drep_bound(M), N \== sup, M \== inf.
is_drep(D1\/D2) :- is_drep(D1), is_drep(D2).
is_drep({AI})   :- is_and_integers(AI).
is_drep(\D)     :- is_drep(D).

is_and_integers(I)     :- integer(I).
is_and_integers((A,B)) :- is_and_integers(A), is_and_integers(B).

drep_bound(I)   :- integer(I).
drep_bound(sup).
drep_bound(inf).

drep_to_intervals(I)        --> { integer(I) }, [n(I)-n(I)].
drep_to_intervals(N..M)     -->
        (   { defaulty_to_bound(N, N1), defaulty_to_bound(M, M1),
              N1 cis_leq M1} -> [N1-M1]
        ;   []
        ).
drep_to_intervals(D1 \/ D2) -->
        drep_to_intervals(D1), drep_to_intervals(D2).
drep_to_intervals(\D0) -->
        { drep_to_domain(D0, D1),
          domain_complement(D1, D),
          domain_to_drep(D, Drep) },
        drep_to_intervals(Drep).
drep_to_intervals({AI}) -->
        and_integers_(AI).

and_integers_(I)     --> { integer(I) }, [n(I)-n(I)].
and_integers_((A,B)) --> and_integers_(A), and_integers_(B).

drep_to_domain(DR, D) :-
        must_be(ground, DR),
        (   is_drep(DR) -> true
        ;   domain_error(clpz_domain, DR)
        ),
        phrase(drep_to_intervals(DR), Is0),
        merge_intervals(Is0, Is1),
        intervals_to_domain(Is1, D).

merge_intervals(Is0, Is) :-
        keysort(Is0, Is1),
        merge_overlapping(Is1, Is).

merge_overlapping([], []).
merge_overlapping([A-B0|ABs0], [A-B|ABs]) :-
        merge_remaining(ABs0, B0, B, Rest),
        merge_overlapping(Rest, ABs).

merge_remaining([], B, B, []).
merge_remaining([N-M|NMs], B0, B, Rest) :-
        Next cis B0 + n(1),
        (   N cis_gt Next -> B = B0, Rest = [N-M|NMs]
        ;   B1 cis max(B0,M),
            merge_remaining(NMs, B1, B, Rest)
        ).

domain(V, Dom) :-
        (   fd_get(V, Dom0, VPs) ->
            domains_intersection(Dom, Dom0, Dom1),
            %format("intersected\n: ~w\n ~w\n==> ~w\n\n", [Dom,Dom0,Dom1]),
            fd_put(V, Dom1, VPs),
            reinforce(V)
        ;   domain_contains(Dom, V)
        ).

domains([], _).
domains([V|Vs], D) :- domain(V, D), domains(Vs, D).

props_number(fd_props(Gs,Bs,Os), N) :-
        length(Gs, N1),
        length(Bs, N2),
        length(Os, N3),
        N is N1 + N2 + N3.

fd_get(X, Dom, Ps) :-
        (   get_attr(X, clpz, Attr) -> Attr = clpz_attr(_,_,_,Dom,Ps,_)
        ;   var(X) -> default_domain(Dom), Ps = fd_props([],[],[])
        ).

fd_get(X, Dom, Inf, Sup, Ps) :-
        fd_get(X, Dom, Ps),
        domain_infimum(Dom, Inf),
        domain_supremum(Dom, Sup).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Constraint propagation always terminates. Currently, this is
   ensured by allowing the left and right boundaries, as well as the
   distance between the smallest and largest number occurring in the
   domain representation to be changed at most once after a constraint
   is posted, unless the domain is bounded.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

fd_put(X, Dom, Ps) --> put_terminating(X, Dom, Ps).

fd_put(X, Dom, Ps) :-
        new_queue(Q),
        phrase((put_terminating(X, Dom, Ps),
%                { portray_clause(done_terminating) },
                do_queue), [Q], _).

put_terminating(X, Dom, Ps) -->
        Dom \== empty,
        (   Dom = from_to(F, F) -> queue_goal(F = n(X))
        ;   (   { get_attr(X, clpz, Attr) } ->
                { Attr = clpz_attr(Left,Right,Spread,OldDom, _OldPs,Q),
                  put_attr(X, clpz, clpz_attr(Left,Right,Spread,Dom,Ps,Q)) },
                (   { OldDom == Dom } -> []
                ;   { (   Left == (.) -> Bounded = yes
                      ;   domain_infimum(Dom, Inf),
                          domain_supremum(Dom, Sup),
                          (   Inf = n(_), Sup = n(_) ->
                              Bounded = yes
                          ;   Bounded = no
                          )
                    ) },
                    (   { Bounded == yes } ->
                        { put_attr(X, clpz, clpz_attr(.,.,.,Dom,Ps,Q)) },
                        trigger_props(Ps, X, OldDom, Dom)
                    ;   % infinite domain; consider border and spread changes
                        { domain_infimum(OldDom, OldInf),
                          (   Inf == OldInf -> LeftP = Left
                          ;   LeftP = yes
                          ),
                          domain_supremum(OldDom, OldSup),
                          (   Sup == OldSup -> RightP = Right
                          ;   RightP = yes
                          ),
                          domain_spread(OldDom, OldSpread),
                          domain_spread(Dom, NewSpread),
                          (   NewSpread == OldSpread -> SpreadP = Spread
                          ;   NewSpread cis_lt OldSpread -> SpreadP = no
                          ;   SpreadP = yes
                          ),
                          put_attr(X, clpz, clpz_attr(LeftP,RightP,SpreadP,Dom,Ps,Q)) },
                        (   { RightP == yes, Right = yes } -> []
                        ;   { LeftP == yes, Left = yes } -> []
                        ;   { SpreadP == yes, Spread = yes } -> []
                        ;   trigger_props(Ps, X, OldDom, Dom)
                        )
                    )
                )
            ;   { var(X) } ->
                { new_queue(Q),
                  put_attr(X, clpz, clpz_attr(no,no,no,Dom,Ps,Q)) }
            ;   []
            )
        ).

new_queue(queue(_Goals,_Fast,_Slow,_Aux)).

queue_goal(Goal) --> insert_queue(Goal, 1).
queue_fast(Prop) --> insert_queue(Prop, 2).
queue_slow(Prop) --> insert_queue(Prop, 3).

insert_queue(Element, Which) -->
        state(Queue),
        { arg(Which, Queue, Arg),
          (   get_atts(Arg, queue(Head0,Tail0)) ->
              Head = Head0,
              Tail0 = [Element|Tail]
          ;   Head = [Element|Tail]
          ),
          put_atts(Arg, queue(Head,Tail)) }.


domain_spread(Dom, Spread) :-
        domain_smallest_finite(Dom, S),
        domain_largest_finite(Dom, L),
        Spread cis L - S.

smallest_finite(inf, Y, Y).
smallest_finite(n(N), _, n(N)).

domain_smallest_finite(from_to(F,T), S)   :- smallest_finite(F, T, S).
domain_smallest_finite(split(_, L, _), S) :- domain_smallest_finite(L, S).

largest_finite(sup, Y, Y).
largest_finite(n(N), _, n(N)).

domain_largest_finite(from_to(F,T), L)   :- largest_finite(T, F, L).
domain_largest_finite(split(_, _, R), L) :- domain_largest_finite(R, L).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   All relevant constraints get a propagation opportunity whenever a
   new constraint is posted.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

reinforce(X) :-
        term_variables(X, Vs),
        maplist(reinforce_, Vs).

reinforce_(X) :-
        (   fd_var(X), fd_get(X, Dom, Ps) ->
            put_full(X, Dom, Ps)
        ;   true
        ).

put_full(X, Dom, Ps) :-
        Dom \== empty,
        (   Dom = from_to(F, F) -> F = n(X)
        ;   (   get_attr(X, clpz, Attr) ->
                Attr = clpz_attr(_,_,_,OldDom, _OldPs,Q),
                put_attr(X, clpz, clpz_attr(no,no,no,Dom,Ps,Q)),
                %format("putting dom: ~w\n", [Dom]),
                (   OldDom == Dom -> true
                ;   new_queue(Q), % TODO: queue?
                    phrase((trigger_props(Ps, X, OldDom, Dom),
                            do_queue), [Q], _)
                )
            ;   var(X) -> %format('\t~w in ~w .. ~w\n',[X,L,U]),
                new_queue(Q),
                put_attr(X, clpz, clpz_attr(no,no,no,Dom,Ps,Q))
            ;   true
            )
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   A propagator is a term of the form propagator(C, State), where C
   represents a constraint, and State is a free variable that can be
   used to destructively change the state of the propagator via
   attributes. This can be used to avoid redundant invocation of the
   same propagator, or to disable the propagator.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

make_propagator(C, propagator(C, _)).

propagator_state(propagator(_,S), S).

trigger_props(fd_props(Gs,Bs,Os), X, D0, D) -->
        (   { ground(X) } ->
            trigger_props_(Gs),
            trigger_props_(Bs)
        ;   Bs \== [] ->
            { domain_infimum(D0, I0),
              domain_infimum(D, I) },
            (   { I == I0 } ->
                { domain_supremum(D0, S0),
                  domain_supremum(D, S) },
                (   { S == S0 } -> []
                ;   trigger_props_(Bs)
                )
            ;   trigger_props_(Bs)
            )
        ;   []
        ),
        trigger_props_(Os).

trigger_props(fd_props(Gs,Bs,Os), X) -->
        trigger_props_(Os),
        trigger_props_(Bs),
        (   { ground(X) } ->
            trigger_props_(Gs)
        ;   []
        ).

trigger_props(fd_props(Gs,Bs,Os)) -->
        trigger_props_(Gs),
        trigger_props_(Bs),
        trigger_props_(Os).

trigger_props_([]) --> [].
trigger_props_([P|Ps]) --> trigger_prop(P), trigger_props_(Ps).

trigger_prop(P) :- trigger_once(P).

trigger_prop(Propagator) -->
        { propagator_state(Propagator, State) },
        (   { State == dead } -> []
        ;   { get_attr(State, clpz_aux, queued) } -> []
        ;   { bb_get('$clpz_current_propagator', C), C == State } -> []
        ;   % passive
            %{ format("triggering: ~w\n", [Propagator]) },
            { put_attr(State, clpz_aux, queued) },
            (   { arg(1, Propagator, C), functor(C, F, _), global_constraint(F) } ->
                queue_slow(Propagator)
            ;   queue_fast(Propagator)
            )
        ).

all_propagators(fd_props(Gs,Bs,Os)) -->
        propagators_(Gs),
        propagators_(Bs),
        propagators_(Os).

propagators_([]) --> [].
propagators_([P|Ps]) --> propagator_(P), propagators_(Ps).

propagator_(Propagator) -->
        { propagator_state(Propagator, State) },
        (   { State == dead } -> []
        ;   { get_attr(State, clpz_aux, queued) } -> []
        ;   % passive
            % format("triggering: ~w\n", [Propagator]),
            [clpz:trigger_prop(Propagator)]
        ).

% DCG variants

kill(State) --> { kill(State) }.

kill(State, Ps) --> { kill(State, Ps) }.

T =.. Ls --> { T =.. Ls }.

A = A --> [].

A == B --> { A == B }.

A \== B --> { A \== B }.

integer(I) --> { integer(I) }.
nonvar(X) --> { nonvar(X) }.
var(V) --> { var(V) }.
ground(T) --> { ground(T) }.

true --> [].

X >= Y	--> { X >= Y }.
X =< Y  --> { X =< Y }.
X =:= Y --> { X =:= Y }.
X =\= Y --> { X =\= Y }.
X is E	--> { X is E }.
X > Y   --> { X > Y }.
X < Y   --> { X < Y }.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Duo DCG variants
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

A = B ++> { A = B }.
A < B ++> { A < B }.
A is B ++> { A is B }.

kill(State) :- del_attr(State, clpz_aux), State = dead.

kill(State, Ps) :-
        kill(State),
        maplist(kill_entailed, Ps).

kill_entailed(p(Prop)) :-
        propagator_state(Prop, State),
        kill(State).
kill_entailed(a(V)) :-
        del_attr(V, clpz).
kill_entailed(a(X,B)) :-
        (   X == B -> true
        ;   del_attr(B, clpz)
        ).
kill_entailed(a(X,Y,B)) :-
        (   X == B -> true
        ;   Y == B -> true
        ;   del_attr(B, clpz)
        ).

no_reactivation(rel_tuple(_,_)).
no_reactivation(pdistinct(_)).
no_reactivation(pnvalue(_)).
no_reactivation(pgcc(_,_,_)).
no_reactivation(pgcc_single(_,_)).
%no_reactivation(scalar_product(_,_,_,_)).

activate_propagator(propagator(P,State)) -->
        % { portray_clause(running(P)) },
        (   State == dead -> []
        ;   { del_attr(State, clpz_aux) },
            (   { no_reactivation(P) } ->
                { bb_b_put('$clpz_current_propagator', State) },
                run_propagator(P, State),
                { bb_b_put('$clpz_current_propagator', []) }
            ;   run_propagator(P, State)
            )
        ).

%do_queue --> print_queue, { false }.
do_queue -->
        (   queue_enabled ->
            (   queue_get_goal(Goal) -> { call(Goal) }, do_queue
            ;   queue_get_fast(Fast) -> activate_propagator(Fast), do_queue
            ;   queue_get_slow(Slow) -> activate_propagator(Slow), do_queue
            ;   true
            )
        ;   true
        ).

:- meta_predicate(ignore(0)).

ignore(Goal) :- ( Goal -> true ; true ).

print_queue -->
        state(queue(Goal,Fast,Slow,_)),
        { ignore(get_atts(Goal, queue(GHs,_))),
          ignore(get_atts(Fast, queue(FHs,_))),
          ignore(get_atts(Slow, queue(SHs,_))),
          format("Current queue:~n   goal: ~q~n   fast: ~q~n   slow: ~q~n~n", [GHs,FHs,SHs]) }.



queue_get_goal(Goal) --> queue_get_arg(1, Goal).
queue_get_fast(Fast) --> queue_get_arg(2, Fast).
queue_get_slow(Slow) --> queue_get_arg(3, Slow).

queue_get_arg(Which, Element) -->
        state(Queue),
        { queue_get_arg_(Queue, Which, Element) }.

queue_get_arg_(Queue, Which, Element) :-
        arg(Which, Queue, Arg),
        get_atts(Arg, queue([Element|Elements],Tail)),
        (   var(Elements) ->
            put_atts(Arg, -queue(_,_))
        ;   put_atts(Arg, queue(Elements,Tail))
        ).

queue_enabled --> state(queue(_,_,_,Aux)), { \+ get_atts(Aux, disabled) }.
disable_queue --> state(queue(_,_,_,Aux)), { put_atts(Aux, disabled) }.
enable_queue --> state(queue(_,_,_,Aux)), { put_atts(Aux, -disabled) }.

portray_propagator(propagator(P,_), F) :- functor(P, F, _).

init_propagator_([], _) --> [].
init_propagator_([V|Vs], Prop) -->
        (   { fd_get(V, Dom, Ps0) } ->
            { insert_propagator(Prop, Ps0, Ps) },
            fd_put(V, Dom, Ps)
        ;   []
        ),
        init_propagator_(Vs, Prop).

init_propagator(Var, Prop) :-
        (   fd_get(Var, Dom, Ps0) ->
            insert_propagator(Prop, Ps0, Ps),
            fd_put(Var, Dom, Ps)
        ;   true
        ).

constraint_wake(pneq, ground).
constraint_wake(x_neq_y_plus_z, ground).
constraint_wake(absdiff_neq, ground).
constraint_wake(pdifferent, ground).
constraint_wake(pexclude, ground).
constraint_wake(scalar_product_neq, ground).
constraint_wake(x_eq_abs_plus_v, ground).

constraint_wake(x_leq_y_plus_c, bounds).
constraint_wake(scalar_product_eq, bounds).
constraint_wake(scalar_product_leq, bounds).
constraint_wake(pplus, bounds).
constraint_wake(pgeq, bounds).
constraint_wake(pgcc_single, bounds).
constraint_wake(pgcc_check_single, bounds).

global_constraint(pdistinct).
global_constraint(pnvalue).
global_constraint(pgcc).
global_constraint(pgcc_single).
global_constraint(pcircuit).
%global_constraint(rel_tuple).
%global_constraint(scalar_product_eq).

insert_propagator(Prop, Ps0, Ps) :-
        Ps0 = fd_props(Gs,Bs,Os),
        arg(1, Prop, Constraint),
        functor(Constraint, F, _),
        (   constraint_wake(F, ground) ->
            Ps = fd_props([Prop|Gs], Bs, Os)
        ;   constraint_wake(F, bounds) ->
            Ps = fd_props(Gs, [Prop|Bs], Os)
        ;   Ps = fd_props(Gs, Bs, [Prop|Os])
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% lex_chain(+Lists)
%
% Lists are lexicographically non-decreasing.

lex_chain(Lss) :-
        must_be(list(list), lex_chain(Lss)-1, Lss),
        maplist(maplist(fd_variable), Lss),
        (   Lss == [] -> true
        ;   Lss = [First|Rest],
            make_propagator(presidual(lex_chain(Lss)), Prop),
            foldl(lex_chain_(Prop), Rest, First, _)
        ).

lex_chain_(Prop, Ls, Prev, Ls) :-
        maplist(prop_init(Prop), Ls),
        lex_le(Prev, Ls).

lex_le([], []).
lex_le([V1|V1s], [V2|V2s]) :-
        #V1 #=< #V2,
        (   integer(V1) ->
            (   integer(V2) ->
                (   V1 =:= V2 -> lex_le(V1s, V2s) ;  true )
            ;   freeze(V2, lex_le([V1|V1s], [V2|V2s]))
            )
        ;   freeze(V1, lex_le([V1|V1s], [V2|V2s]))
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% tuples_in(+Tuples, +Relation).
%
% True iff all Tuples are elements of Relation. Each element of the
% list Tuples is a list of integers or finite domain variables.
% Relation is a list of lists of integers. Arbitrary finite relations,
% such as compatibility tables, can be modeled in this way. For
% example, if 1 is compatible with 2 and 5, and 4 is compatible with 0
% and 3:
%
% ```
% ?- tuples_in([[X,Y]], [[1,2],[1,5],[4,0],[4,3]]), X = 4.
% X = 4,
% Y in 0\/3.
% ```
%
% As another example, consider a train schedule represented as a list
% of quadruples, denoting departure and arrival places and times for
% each train. In the following program, Ps is a feasible journey of
% length 3 from A to D via trains that are part of the given schedule.
%
% ```
% trains([[1,2,0,1],
%         [2,3,4,5],
%         [2,3,0,1],
%         [3,4,5,6],
%         [3,4,2,3],
%         [3,4,8,9]]).
%
% threepath(A, D, Ps) :-
%         Ps = [[A,B,_T0,T1],[B,C,T2,T3],[C,D,T4,_T5]],
%         T2 #> T1,
%         T4 #> T3,
%         trains(Ts),
%         tuples_in(Ps, Ts).
% ```
%
% In this example, the unique solution is found without labeling:
%
% ```
% ?- threepath(1, 4, Ps).
% Ps = [[1, 2, 0, 1], [2, 3, 4, 5], [3, 4, 8, 9]].
% ```

tuples_in(Tuples, Relation) :-
        must_be(list(list), Tuples),
        maplist(maplist(fd_variable), Tuples),
        must_be(list(list(integer)), Relation),
        new_queue(Q0),
        phrase(tuples_relation(Tuples, Relation), [Q0], [Q]),
        append(Tuples, Vs),
        variables_same_queue(Vs),
        phrase(do_queue, [Q], _).

tuples_relation([], _) --> [].
tuples_relation([Tuple|Tuples], Relation) -->
        { relation_unifiable(Relation, Tuple, Us, _, _) },
        (   ground(Tuple) -> { memberchk(Tuple, Relation) }
        ;   tuple_domain(Tuple, Us),
            (   Tuple = [_,_|_] -> tuple_freeze(Tuple, Us)
            ;   []
            )
        ),
        tuples_relation(Tuples, Relation).

list_first_rest([L|Ls], L, Ls).

tuple_domain([], _) --> [].
tuple_domain([T|Ts], Relation0) -->
        { maplist(list_first_rest, Relation0, Firsts, Relation1) },
        (   Firsts = [Unique] -> T = Unique
        ;   (   var(T) ->
                { list_to_domain(Firsts, FDom),
                  fd_get(T, TDom, TPs),
                  domains_intersection(TDom, FDom, TDom1) },
                fd_put(T, TDom1, TPs)
            ;   []
            )
        ),
        tuple_domain(Ts, Relation1).

tuple_freeze(Tuple, Relation) -->
        (   ground(Tuple) -> { memberchk(Tuple, Relation) }
        ;   { put_attr(R, clpz_relation, Relation),
              make_propagator(rel_tuple(R, Tuple), Prop) },
            tuple_freeze_(Tuple, Prop)
        ).

tuple_freeze_([], _) --> [].
tuple_freeze_([T|Ts], Prop) -->
        (   var(T) ->
            init_propagator_([T], Prop),
            trigger_prop(Prop)
        ;   []
        ),
        tuple_freeze_(Ts, Prop).

relation_unifiable([], _, [], Changed, Changed).
relation_unifiable([R|Rs], Tuple, Us, Changed0, Changed) :-
        (   all_in_domain(R, Tuple) ->
            Us = [R|Rest],
            relation_unifiable(Rs, Tuple, Rest, Changed0, Changed)
        ;   relation_unifiable(Rs, Tuple, Us, true, Changed)
        ).

all_in_domain([], []).
all_in_domain([A|As], [T|Ts]) :-
        (   fd_get(T, Dom, _) ->
            domain_contains(Dom, A)
        ;   T =:= A
        ),
        all_in_domain(As, Ts).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%run_propagator(P, _) --> { portray_clause(run_propagator(P)), false }.
% trivial propagator, used only to remember pending constraints
run_propagator(presidual(_), _) --> [].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(pdifferent(Left,Right,X,_), MState) -->
        run_propagator(pexclude(Left,Right,X), MState).

run_propagator(pexclude(Left,Right,X), _) -->
        (   ground(X) ->
            disable_queue,
            exclude_fire(Left, Right, X),
            enable_queue
        ;   true
        ).

run_propagator(pdistinct(Ls), _MState) --> distinct(Ls).

run_propagator(pnvalue(N, Vars), _MState) --> { propagate_nvalue(N, Vars) }.

run_propagator(check_distinct(Left,Right,X), _) -->
        { \+ list_contains(Left, X),
          \+ list_contains(Right, X) }.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(pelement(N, Is, V), MState) -->
        (   { fd_get(N, NDom, _) } ->
            (   { fd_get(V, VDom, VPs) } ->
                { integers_remaining(Is, 1, NDom, empty, VDom1),
                  domains_intersection(VDom, VDom1, VDom2) },
                fd_put(V, VDom2, VPs)
            ;   []
            )
        ;   { kill(MState), nth1(N, Is, V) }
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(pgcc_single(Vs, Pairs), _) --> gcc_global(Vs, Pairs).

run_propagator(pgcc_check_single(Pairs), _) --> gcc_check(Pairs).

run_propagator(pgcc_check(Pairs), _) --> gcc_check(Pairs).

run_propagator(pgcc(Vs, _, Pairs), _) --> gcc_global(Vs, Pairs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(pcircuit(Vs), _MState) -->
        distinct(Vs),
        { propagate_circuit(Vs) }.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(pgeq(A,B), MState) -->
        (   A == B -> kill(MState)
        ;   nonvar(A) ->
            (   nonvar(B) -> kill(MState), A >= B
            ;   { fd_get(B, BD, BPs),
                  domain_remove_greater_than(BD, A, BD1) },
                kill(MState),
                fd_put(B, BD1, BPs)
            )
        ;   nonvar(B) ->
            { fd_get(A, AD, APs),
              domain_remove_smaller_than(AD, B, AD1) },
            kill(MState),
            fd_put(A, AD1, APs)
        ;   { fd_get(A, AD, AL, AU, APs),
              fd_get(B, _, BL, BU, _),
              AU cis_geq BL },
            (   { AL cis_geq BU } -> kill(MState)
            ;   AU == BL -> kill(MState), A = B
            ;   { NAL cis max(AL,BL),
                  domains_intersection(AD, from_to(NAL,AU), NAD) },
                fd_put(A, NAD, APs),
                (   { fd_get(B, BD2, BL2, BU2, BPs2) } ->
                    { NBU cis min(BU2, AU),
                      domains_intersection(BD2, from_to(BL2,NBU), NBD) },
                    fd_put(B, NBD, BPs2)
                ;   []
                )
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(rel_tuple(R, Tuple), MState) -->
        { get_attr(R, clpz_relation, Relation) },
        (   { ground(Tuple) } ->
            kill(MState),
            { del_attr(R, clpz_relation),
              memberchk(Tuple, Relation) }
        ;   { relation_unifiable(Relation, Tuple, Us, false, Changed),
              Us = [_|_] },
            (   { Tuple = [First,Second], ( ground(First) ; ground(Second) ) } ->
                kill(MState)
            ;   []
            ),
            (   { Us = [Single] } ->
                kill(MState),
                { del_attr(R, clpz_relation) },
                Single = Tuple
            ;   { Changed } ->
                { put_attr(R, clpz_relation, Us) },
                disable_queue,
                tuple_domain(Tuple, Us),
                enable_queue
            ;   []
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(pserialized(S_I, D_I, S_J, D_J, _), MState) -->
        (   nonvar(S_I), nonvar(S_J) ->
            kill(MState),
            (   S_I + D_I =< S_J -> []
            ;   S_J + D_J =< S_I -> []
            ;   { false }
            )
        ;   serialize_lower_upper(S_I, D_I, S_J, D_J, MState),
            serialize_lower_upper(S_J, D_J, S_I, D_I, MState)
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% X #\= Y
run_propagator(pneq(A, B), MState) -->
        (   nonvar(A) ->
            (   nonvar(B) -> A =\= B, kill(MState)
            ;   { fd_get(B, BD0, BExp0),
                  domain_remove(BD0, A, BD1),
                  kill(MState) },
                fd_put(B, BD1, BExp0)
            )
        ;   nonvar(B) -> run_propagator(pneq(B, A), MState)
        ;   A \== B,
            { fd_get(A, _, AI, AS, _),
              fd_get(B, _, BI, BS, _) },
            (   { AS cis_lt BI } -> kill(MState)
            ;   { AI cis_gt BS } -> kill(MState)
            ;   []
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Y = abs(X)
run_propagator(pabs(X,Y), MState) -->
        (   nonvar(X) -> kill(MState), Y is abs(X)
        ;   nonvar(Y) ->
            kill(MState),
            Y >= 0,
            YN is -Y,
            { X in YN \/ Y }
	;   X == Y -> kill(MState)
        ;   { fd_get(X, XD, XPs),
              fd_get(Y, YD, _),
              domain_negate(YD, YDNegative),
              domains_union(YD, YDNegative, XD1),
              domains_intersection(XD, XD1, XD2) },
            fd_put(X, XD2, XPs),
            (   { fd_get(Y, YD1, YPs1) } ->
                { domain_negate(XD2, XD2Neg),
                  domains_union(XD2, XD2Neg, YD2),
                  domain_remove_smaller_than(YD2, 0, YD3),
                  domains_intersection(YD1, YD3, YD4) },
                fd_put(Y, YD4, YPs1)
            ;   []
            )
        ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abs(X-Y) #\= C
run_propagator(absdiff_neq(X,Y,C), MState) -->
        (   C < 0 -> kill(MState)
        ;   nonvar(X) ->
            kill(MState),
            (   nonvar(Y) -> abs(X - Y) =\= C
            ;   V1 is X - C, neq_num(Y, V1),
                V2 is C + X, neq_num(Y, V2)
            )
        ;   nonvar(Y) -> kill(MState),
            V1 is C + Y, neq_num(X, V1),
            V2 is Y - C, neq_num(X, V2)
        ;   []
        ).


% X #= abs(X) + V
run_propagator(x_eq_abs_plus_v(X,V), MState) -->
        (   nonvar(V) ->
            (   V =:= 0 -> kill(MState), { X in 0..sup }
            ;   V < 0 -> kill(MState), { X #= V / 2 }
            ;   V > 0 -> { false }
            )
        ;   nonvar(X) ->
            kill(MState),
            { V #= X - abs(X) }
        ;   true
        ).

% X #\= Y + Z
run_propagator(x_neq_y_plus_z(X,Y,Z), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) ->
                (   nonvar(Z) -> kill(MState), X =\= Y + Z
                ;   kill(MState), XY is X - Y, neq_num(Z, XY)
                )
            ;   nonvar(Z) -> kill(MState), XZ is X - Z, neq_num(Y, XZ)
            ;   []
            )
        ;   nonvar(Y) ->
            (   nonvar(Z) ->
                kill(MState), YZ is Y + Z, neq_num(X, YZ)
            ;   Y =:= 0 -> kill(MState), { neq(X, Z) }
            ;   []
            )
        ;   Z == 0 -> kill(MState), { neq(X, Y) }
        ;   true
        ).

% X #=< Y + C
run_propagator(x_leq_y_plus_c(X,Y,C), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), X =< Y + C
            ;   kill(MState),
                R is X - C,
                { fd_get(Y, YD, YPs),
                  domain_remove_smaller_than(YD, R, YD1) },
                fd_put(Y, YD1, YPs)
            )
        ;   nonvar(Y) ->
            kill(MState),
            R is Y + C,
            { fd_get(X, XD, XPs),
              domain_remove_greater_than(XD, R, XD1) },
            fd_put(X, XD1, XPs)
        ;   (   X == Y -> C >= 0, kill(MState)
            ;   { fd_get(Y, YD, _) },
                (   { domain_supremum(YD, n(YSup)) } ->
                    YS1 is YSup + C,
                    { fd_get(X, XD, XPs),
                      domain_remove_greater_than(XD, YS1, XD1) },
                    fd_put(X, XD1, XPs)
                ;   []
                ),
                (   { fd_get(X, XD2, _), domain_infimum(XD2, n(XInf)) } ->
                    XI1 is XInf - C,
                    (   { fd_get(Y, YD1, YPs1) } ->
                        { domain_remove_smaller_than(YD1, XI1, YD2),
                          (   domain_infimum(YD2, n(YInf)),
                              domain_supremum(XD2, n(XSup)),
                              XSup =< YInf + C ->
                              kill(MState)
                          ;   true
                          ) },
                        fd_put(Y, YD2, YPs1)
                    ;   []
                    )
                ;   []
                )
            )
        ).

run_propagator(scalar_product_neq(Cs0,Vs0,P0), MState) -->
        { coeffs_variables_const(Cs0, Vs0, Cs, Vs, 0, I),
          P is P0 - I,
          (   Vs = [] -> kill(MState), P =\= 0
          ;   Vs = [V], Cs = [C] ->
              kill(MState),
              (   C =:= 1 -> neq_num(V, P)
              ;   C*V #\= P
              )
          ;   Cs == [1,-1] -> kill(MState), Vs = [A,B], x_neq_y_plus_z(A, B, P)
          ;   Cs == [-1,1] -> kill(MState), Vs = [A,B], x_neq_y_plus_z(B, A, P)
          ;   P =:= 0, Cs = [1,1,-1] ->
              kill(MState), Vs = [A,B,C], x_neq_y_plus_z(C, A, B)
          ;   P =:= 0, Cs = [1,-1,1] ->
              kill(MState), Vs = [A,B,C], x_neq_y_plus_z(B, A, C)
          ;   P =:= 0, Cs = [-1,1,1] ->
              kill(MState), Vs = [A,B,C], x_neq_y_plus_z(A, B, C)
          ;   true
          ) }.

run_propagator(scalar_product_leq(Cs0,Vs0,P0), MState) -->
        { coeffs_variables_const(Cs0, Vs0, Cs, Vs, 0, I) },
        P is P0 - I,
        (   Vs = [] -> kill(MState), P >= 0
        ;   { duophrase(sum_finite_domains(Cs, Vs, 0, 0, Inf, Sup), Infs, Sups) },
            D1 is P - Inf,
            disable_queue,
            (   Infs == [], Sups == [] ->
                Inf =< P,
                (   Sup =< P -> kill(MState)
                ;   remove_dist_upper_leq(Cs, Vs, D1)
                )
            ;   Infs == [] -> Inf =< P, remove_dist_upper(Sups, D1)
            ;   Infs = [_] -> remove_upper(Infs, D1)
            ;   true
            ),
            enable_queue
        ).

run_propagator(scalar_product_eq(Cs0,Vs0,P0), MState) -->
        { coeffs_variables_const(Cs0, Vs0, Cs, Vs, 0, I) },
        P is P0 - I,
        (   Vs = [] -> kill(MState), P =:= 0
        ;   Vs = [V], Cs = [C] -> kill(MState), P mod C =:= 0, V is P // C
        ;   Cs == [1,1] -> kill(MState), Vs = [A,B], { A + B #= P }
        ;   Cs == [1,-1] -> kill(MState), Vs = [A,B], { A #= P + B }
        ;   Cs == [-1,1] -> kill(MState), Vs = [A,B], { B #= P + A }
        ;   Cs == [-1,-1] -> kill(MState), Vs = [A,B], P1 is -P, { A + B #= P1 }
        ;   P =:= 0, Cs == [1,1,-1] -> kill(MState), Vs = [A,B,C], { A + B #= C }
        ;   P =:= 0, Cs == [1,-1,1] -> kill(MState), Vs = [A,B,C], { A + C #= B }
        ;   P =:= 0, Cs == [-1,1,1] -> kill(MState), Vs = [A,B,C], { B + C #= A }
        ;   { duophrase(sum_finite_domains(Cs, Vs, 0, 0, Inf, Sup), Infs, Sups) },
            % { nl, writeln(Infs-Sups-Inf-Sup) },
            D1 is P - Inf,
            D2 is Sup - P,
            disable_queue,
            (   Infs == [], Sups == [] ->
                { between(Inf, Sup, P) },
                remove_dist_upper_lower(Cs, Vs, D1, D2)
            ;   Sups = [] -> P =< Sup, remove_dist_lower(Infs, D2)
            ;   Infs = [] -> Inf =< P, remove_dist_upper(Sups, D1)
            ;   Sups = [_], Infs = [_] ->
                remove_lower(Sups, D2),
                remove_upper(Infs, D1)
            ;   Infs = [_] -> remove_upper(Infs, D1)
            ;   Sups = [_] -> remove_lower(Sups, D2)
            ;   true
            ),
            enable_queue
        ).

% X + Y = Z
run_propagator(pplus(X,Y,Z,Morph), MState) -->
        (   nonvar(X) ->
            (   X =:= 0 -> kill(MState), Y = Z
            ;   Y == Z -> kill(MState), X =:= 0
            ;   nonvar(Y) -> kill(MState), Z is X + Y
            ;   nonvar(Z) -> kill(MState), Y is Z - X
            ;   { fd_get(Z, ZD, ZPs),
                  fd_get(Y, YD, _),
                  domain_shift(YD, X, Shifted_YD),
                  domains_intersection(ZD, Shifted_YD, ZD1) },
                fd_put(Z, ZD1, ZPs),
                (   { fd_get(Y, YD1, YPs) } ->
                    O is -X,
                    { domain_shift(ZD1, O, YD2),
                      domains_intersection(YD1, YD2, YD3) },
                    fd_put(Y, YD3, YPs)
                ;   []
                )
            )
        ;   nonvar(Y) -> run_propagator(pplus(Y,X,Z,Morph), MState)
        ;   nonvar(Z) ->
            (   X == Y -> kill(MState), { even(Z), X is Z // 2 }
            ;   { fd_get(X, XD, _),
                  fd_get(Y, YD, YPs),
                  domain_negate(XD, XDN),
                  domain_shift(XDN, Z, YD1),
                  domains_intersection(YD, YD1, YD2) },
                fd_put(Y, YD2, YPs),
                (   { fd_get(X, XD1, XPs) } ->
                    { domain_negate(YD2, YD2N),
                      domain_shift(YD2N, Z, XD2),
                      domains_intersection(XD1, XD2, XD3) },
                      fd_put(X, XD3, XPs)
                ;   []
                )
            )
        ;   (   X == Y ->
                morph_into_propagator(MState, [X,Z], ptimes(2,X,Z), Morph)
            ;   X == Z -> kill(MState), Y = 0
            ;   Y == Z -> kill(MState), X = 0
            ;   { fd_get(X, XD, XL, XU, XPs),
                  fd_get(Y, _, YL, YU, _),
                  fd_get(Z, _, ZL, ZU, _),
                  NXL cis max(XL, ZL-YU),
                  NXU cis min(XU, ZU-YL) },
                  update_bounds(X, XD, XPs, XL, XU, NXL, NXU),
                (   { fd_get(Y, YD2, YL2, YU2, YPs2) } ->
                    { NYL cis max(YL2, ZL-NXU),
                      NYU cis min(YU2, ZU-NXL) },
                    update_bounds(Y, YD2, YPs2, YL2, YU2, NYL, NYU)
                ;   NYL = n(Y), NYU = n(Y)
                ),
                (   { fd_get(Z, ZD2, ZL2, ZU2, ZPs2) } ->
                    { NZL cis max(ZL2,NXL+NYL),
                      NZU cis min(ZU2,NXU+NYU) },
                    update_bounds(Z, ZD2, ZPs2, ZL2, ZU2, NZL, NZU)
                ;   []
                )
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(ptimes(X,Y,Z,Morph), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), Z is X * Y
            ;   X =:= 0 -> kill(MState), Z = 0
            ;   X =:= 1 -> kill(MState), Z = Y
            ;   nonvar(Z) -> kill(MState), 0 =:= Z mod X, Y is Z // X
            ;   (   Y == Z -> kill(MState), Y = 0
                ;   { fd_get(Y, YD, _),
                      fd_get(Z, ZD, ZPs),
                      domain_expand(YD, X, Scaled_YD),
                      domains_intersection(ZD, Scaled_YD, ZD1) },
                    fd_put(Z, ZD1, ZPs),
                    (   { fd_get(Y, YDom2, YPs2) } ->
                        { domain_contract(ZD1, X, Contract),
                          domains_intersection(YDom2, Contract, NYDom) },
                        fd_put(Y, NYDom, YPs2)
                    ;   kill(MState), Z is X * Y
                    )
                )
            )
        ;   nonvar(Y) -> run_propagator(ptimes(Y,X,Z,Morph), MState)
        ;   nonvar(Z) ->
            (   X == Y ->
                kill(MState),
                { integer_kth_root(Z, 2, R),
                  NR is -R,
                  X in NR \/ R }
            ;   { fd_get(X, XD, XL, XU, XPs),
                  fd_get(Y, YD, YL, YU, _),
                  min_max_factor(n(Z), n(Z), YL, YU, XL, XU, NXL, NXU) },
                update_bounds(X, XD, XPs, XL, XU, NXL, NXU),
                (   { fd_get(Y, YD2, YL2, YU2, YPs2) } ->
                    { min_max_factor(n(Z), n(Z), NXL, NXU, YL2, YU2, NYL, NYU) },
                    update_bounds(Y, YD2, YPs2, YL2, YU2, NYL, NYU)
                ;   (   Y =\= 0 -> 0 =:= Z mod Y, kill(MState), X is Z // Y
                    ;   kill(MState), Z = 0
                    )
                ),
                (   Z =:= 0 ->
                    (   { \+ domain_contains(XD, 0) } -> kill(MState), Y = 0
                    ;   { \+ domain_contains(YD, 0) } -> kill(MState), X = 0
                    ;   []
                    )
                ;  neq_num(X, 0), neq_num(Y, 0)
                )
            )
        ;   (   X == Y ->
                morph_into_propagator(MState, [X,Z], pexp(X,2,Z), Morph)
            ;   { fd_get(X, XD, XL, XU, XPs),
                  fd_get(Y, _, YL, YU, _),
                  fd_get(Z, ZD, ZL, ZU, _) },
                (   { Y == Z, \+ domain_contains(ZD, 0) } -> kill(MState), X = 1
                ;   { X == Z, \+ domain_contains(ZD, 0) } -> kill(MState), Y = 1
                ;   { min_max_factor(ZL, ZU, YL, YU, XL, XU, NXL, NXU) },
                    update_bounds(X, XD, XPs, XL, XU, NXL, NXU),
                    (   { fd_get(Y, YD2, YL2, YU2, YPs2) } ->
                        { min_max_factor(ZL, ZU, NXL, NXU, YL2, YU2, NYL, NYU) },
                        update_bounds(Y, YD2, YPs2, YL2, YU2, NYL, NYU)
                    ;   NYL = n(Y), NYU = n(Y)
                    ),
                    (   { fd_get(Z, ZD2, ZL2, ZU2, ZPs2) } ->
                        { min_product(NXL, NXU, NYL, NYU, NZL),
                          max_product(NXL, NXU, NYL, NYU, NZU) },
                        (   { NZL cis_leq ZL2, NZU cis_geq ZU2 } -> ZD3 = ZD2
                        ;   { domains_intersection(ZD2, from_to(NZL,NZU), ZD3) },
                            fd_put(Z, ZD3, ZPs2)
                        ),
                        (   { domain_contains(ZD3, 0) } -> []
                        ;   neq_num(X, 0), neq_num(Y, 0)
                        )
                    ;   []
                    )
                )
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% X // Y = Z (round towards zero)
run_propagator(ptzdiv(X,Y,Z,Morph), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), Y =\= 0, Z is X // Y
            ;   { fd_get(Y, YD, YL, YU, YPs) },
                (   nonvar(Z) ->
                    (   Z =:= 0 ->
                        NYL is -abs(X) - 1,
                        NYU is abs(X) + 1,
                        { domains_intersection(YD, split(0, from_to(inf,n(NYL)),
                                                       from_to(n(NYU), sup)),
                                             NYD) },
                        fd_put(Y, NYD, YPs)
                    ;   (   sign(X) =:= sign(Z) ->
                            { NYL cis max(n(X) // (n(Z)+sign(n(Z))) + n(1), YL),
                              NYU cis min(n(X) // n(Z), YU) }
                        ;   { NYL cis max(n(X) // n(Z), YL),
                              NYU cis min(n(X) // (n(Z)+sign(n(Z))) - n(1), YU) }
                        ),
                        update_bounds(Y, YD, YPs, YL, YU, NYL, NYU)
                    )
                ;   { fd_get(Z, ZD, ZL, ZU, ZPs),
                      (   X >= 0, ( YL cis_gt n(0) ; YU cis_lt n(0) )->
                          NZL cis max(n(X)//YU, ZL),
                          NZU cis min(n(X)//YL, ZU)
                      ;   X < 0, ( YL cis_gt n(0) ; YU cis_lt n(0) ) ->
                          NZL cis max(n(X)//YL, ZL),
                          NZU cis min(n(X)//YU, ZU)
                      ;   % TODO: more stringent bounds, cover Y
                          NZL cis max(-abs(n(X)), ZL),
                          NZU cis min(abs(n(X)), ZU)
                      ) },
                    update_bounds(Z, ZD, ZPs, ZL, ZU, NZL, NZU),
                    (   { X >= 0, NZL cis_gt n(0), fd_get(Y, YD1, YPs1) } ->
                        { NYL cis n(X) // (NZU + n(1)) + n(1),
                          NYU cis n(X) // NZL,
                          domains_intersection(YD1, from_to(NYL, NYU), NYD1) },
                        fd_put(Y, NYD1, YPs1)
                    ;   true
                    )
                )
            )
        ;   nonvar(Y) ->
            Y =\= 0,
            (   Y =:= 1 -> kill(MState), X = Z
            ;   Y =:= -1 ->
                morph_into_propagator(MState, [X,Z], pplus(X,Z,0), Morph)
            ;   { fd_get(X, XD, XL, XU, XPs) },
                (   nonvar(Z) ->
                    kill(MState),
                    (   sign(Z) =:= sign(Y) ->
                        { NXL cis max(n(Z)*n(Y), XL),
                          NXU cis min((abs(n(Z))+n(1))*abs(n(Y))-n(1), XU) }
                    ;   Z =:= 0 ->
                        { NXL cis max(-abs(n(Y)) + n(1), XL),
                          NXU cis min(abs(n(Y)) - n(1), XU) }
                    ;   { NXL cis max((n(Z)+sign(n(Z)))*n(Y)+n(1), XL),
                          NXU cis min(n(Z)*n(Y), XU) }
                    ),
                    update_bounds(X, XD, XPs, XL, XU, NXL, NXU)
                ;   { fd_get(Z, ZD, ZPs),
                      domain_contract_less(XD, Y, Contracted),
                      domains_intersection(ZD, Contracted, NZD) },
                    fd_put(Z, NZD, ZPs),
                    (   { fd_get(X, XD2, XPs2) } ->
                        { domain_expand_more(NZD, Y, Expanded),
                          domains_intersection(XD2, Expanded, NXD2) },
                        fd_put(X, NXD2, XPs2)
                    ;   true
                    )
                )
            )
        ;   nonvar(Z) ->
            { fd_get(X, XD, XL, XU, XPs),
              fd_get(Y, _, YL, YU, _),
              (   YL cis_geq n(0), XL cis_geq n(0) ->
                  NXL cis max(YL*n(Z), XL),
                  NXU cis min(YU*(n(Z)+n(1))-n(1), XU)
              ;   %TODO: cover more cases
                  NXL = XL, NXU = XU
              ) },
            update_bounds(X, XD, XPs, XL, XU, NXL, NXU)
        ;   (   X == Y -> kill(MState), Z = 1
            ;   { fd_get(X, _, XL, XU, _),
                  fd_get(Y, _, YL, _, _),
                  fd_get(Z, ZD, ZPs),
                  NZU cis max(abs(XL), XU),
                  NZL cis -NZU,
                  domains_intersection(ZD, from_to(NZL,NZU), NZD0),
                  (   XL cis_geq n(0), YL cis_geq n(0) ->
                      domain_remove_smaller_than(NZD0, 0, NZD1)
                  ;   % TODO: cover more cases
                      NZD1 = NZD0
                  ) },
                fd_put(Z, NZD1, ZPs)
            )
        ).


%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Z = X mod Y

run_propagator(pmod(X,Y,Z), MState) -->
        (   Y == 0 -> { false }
        ;   Y == Z -> { false }
        ;   X == Y -> kill(MState), queue_goal(Z = 0)
        ;   true
        ),
        (   nonvar(X), nonvar(Y) ->
            kill(MState),
            Z is X mod Y
        ;   nonvar(Y), nonvar(Z) ->
            (   Y > 0 -> Z >= 0, Z < Y
            ;   Y < 0 -> Z =< 0, Z > Y
            ),
            (   { fd_get(X, _, n(XL), _, _) } ->
                (   (XL - Z) mod Y =\= 0 ->
                    XMin is Z + Y * ((XL - Z) div Y + 1)
                ;   XMin is XL
                ),
                { fd_get(X, XD0, XPs),
                  domain_remove_smaller_than(XD0, XMin, XD2) },
                fd_put(X, XD2, XPs)
                % queue_goal(X #>= XMin)
            ;   true
            ),
            (   { fd_get(X, _, _, n(XU), _) } ->
                XMax is Z + Y * ((XU - Z) div Y),
                { fd_get(X, XD1, XPs),
                  domain_remove_greater_than(XD1, XMax, XD3) },
                fd_put(X, XD3, XPs)
                % queue_goal(X #=< XMax)
            ;   true
            )
        ;   nonvar(Z), nonvar(X) ->
            (   Z > 0 ->
                (   X < 0 -> true
                ;   X >= Z
                )
            ;   Z < 0 ->
                (   X > 0 -> true
                ;   X =< Z
                )
            ;   Z =:= 0 % Multiple solutions so do nothing special.
            ),
            (   { fd_get(Y, _, _, n(YU), _),
                  YU < X, X =< 0 } -> kill(MState), Z =:= X
            ;   { fd_get(Y, _, n(YL), _, _),
                  YL > X, X >= 0 } -> kill(MState), Z =:= X
            ;   (   Z > 0 ->
                    { fd_get(Y, YD, YPs),
                      YMin is Z + 1,
                      domain_remove_smaller_than(YD, YMin, YD1) },
                    fd_put(Y, YD1, YPs)
                    % queue_goal(Y #> Z)
                ;   Z < 0 ->
                    { fd_get(Y, YD, YPs),
                      YMax is Z - 1,
                      domain_remove_greater_than(YD, YMax, YD1) },
                    fd_put(Y, YD1, YPs)
                    % queue_goal(Y #< Z)
                ;   true
                )
            )
        ;   run_propagator(pmodz(X,Y,Z), MState),
            run_propagator(pmody(X,Y,Z), MState),
            true
        ).

run_propagator(pmodz(X,Y,Z), MState) -->
        (   nonvar(Z) -> true % Nothing to do.
        ;   nonvar(X) ->
            (   X =:= 0 -> kill(MState), queue_goal(Z = X)
            ;   (   X > 0 ->
                    (   { fd_get(Y, _, n(YL), _, _), YL > X } ->
                        kill(MState),
                        queue_goal(Z = X)
                    ;   { fd_get(Z, ZD0, ZPs),
                          domain_remove_greater_than(ZD0, X, ZD2) },
                        fd_put(Z, ZD2, ZPs)
                        % queue_goal(Z #=< X)
                    )
                ;   X < 0 ->
                    (   { fd_get(Y, _, _, n(YU), _), YU < X } ->
                        kill(MState),
                        queue_goal(Z = X)
                    ;   { fd_get(Z, ZD0, ZPs),
                          domain_remove_smaller_than(ZD0, X, ZD2) },
                        fd_put(Z, ZD2, ZPs)
                        % queue_goal(Z #>= X)
                    )
                ),
                (   { fd_get(Y, _, n(YL), n(YU), _), YL > 0 } ->
                    ZMax is YU - 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_smaller_than(ZD1, 0, ZD3),
                      domain_remove_greater_than(ZD3, ZMax, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in 0..ZMax)
                ;   { fd_get(Y, _, n(YL), n(YU), _), YU < 0 } ->
                    ZMin is YL + 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_greater_than(ZD1, 0, ZD3),
                      domain_remove_smaller_than(ZD3, ZMin, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in ZMin..0)
                ;   true
                )
            )
        ;   nonvar(Y) ->
            (   abs(Y) =:= 1 -> kill(MState), queue_goal(Z = 0)
            ;   Y < 0 ->
                (   { fd_get(X, _, n(XL), n(XU), _), XU =< 0, Y < XL } ->
                    kill(MState),
                    queue_goal(Z = X)
                ;   ZMin is Y + 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_greater_than(ZD1, 0, ZD3),
                      domain_remove_smaller_than(ZD3, ZMin, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in ZMin..0)
                )
            ;   Y > 0 ->
                (   { fd_get(X, _, n(XL), n(XU), _), XL >= 0, Y > XU } ->
                    kill(MState),
                    queue_goal(Z = X)
                ;   ZMax is Y - 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_smaller_than(ZD1, 0, ZD3),
                      domain_remove_greater_than(ZD3, ZMax, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in 0..ZMax)
                )
            )
        ;   (   { fd_get(X, _, n(XL), n(XU), _), XL >= 0,
                  fd_get(Y, _, n(YL), _, _), XU < YL } ->
                kill(MState),
                queue_goal(Z = X)
            ;   { fd_get(X, _, n(XL), n(XU), _), XU =< 0,
                  fd_get(Y, _, _, n(YU), _), XL > YU } ->
                kill(MState),
                queue_goal(Z = X)
            ;   (   { fd_get(X, _, n(XL), n(XU), _), XL >= 0 } ->
                    { fd_get(Z, ZD0, ZPs),
                      domain_remove_greater_than(ZD0, XU, ZD2) },
                    fd_put(Z, ZD2, ZPs)
                    % queue_goal(Z #=< XU)
                ;   { fd_get(X, _, n(XL), n(XU), _), XU =< 0 } ->
                    { fd_get(Z, ZD0, ZPs),
                      domain_remove_smaller_than(ZD0, XL, ZD2) },
                    fd_put(Z, ZD2, ZPs)
                    % queue_goal(Z #>= XL)
                ;   true
                ),
                (   { fd_get(Y, _, n(YL), n(YU), _), YL > 0 } ->
                    ZMax is YU - 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_smaller_than(ZD1, 0, ZD3),
                      domain_remove_greater_than(ZD3, ZMax, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in 0..ZMax)
                ;   { fd_get(Y, _, n(YL), n(YU), _), YU < 0 } ->
                    ZMin is YL + 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_greater_than(ZD1, 0, ZD3),
                      domain_remove_smaller_than(ZD3, ZMin, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in ZMin..0)
                ;   { fd_get(Y, _, n(YL), n(YU), _), YL < 0, YU > 0 } ->
                    ZMin is YL + 1,
                    ZMax is YU - 1,
                    { fd_get(Z, ZD1, ZPs),
                      domain_remove_greater_than(ZD1, ZMax, ZD3),
                      domain_remove_smaller_than(ZD3, ZMin, ZD5) },
                    fd_put(Z, ZD5, ZPs)
                    % queue_goal(Z in ZMin..ZMax)
                ;   { fd_get(Y, _, _, n(YU), _), YU > 0 } ->
                    { fd_get(Z, ZD1, ZPs),
                      ZMax is YU - 1,
                      domain_remove_greater_than(ZD1, ZMax, ZD3) },
                    fd_put(Z, ZD3, ZPs)
                    % queue_goal(Z #< YU)
                ;   { fd_get(Y, _, n(YL), _, _), YL < 0 } ->
                    { fd_get(Z, ZD1, ZPs),
                      ZMin is YL + 1,
                      domain_remove_smaller_than(ZD1, ZMin, ZD3) },
                    fd_put(Z, ZD3, ZPs)
                    % queue_goal(Z #> YL)
                ;   true
                )
            )
        ).

run_propagator(pmody(_X,Y,Z), _MState) -->
        (   nonvar(Y) -> true % Nothing to do.
        % ;   nonvar(X) -> true
        ;   nonvar(Z) ->
            (   Z > 0 ->
                { fd_get(Y, YD, YPs),
                  YMin is Z + 1,
                  domain_remove_smaller_than(YD, YMin, YD1) },
                fd_put(Y, YD1, YPs)
                % queue_goal(Y #> Z)
            ;   Z < 0 ->
                { fd_get(Y, YD, YPs),
                  YMax is Z - 1,
                  domain_remove_greater_than(YD, YMax, YD1) },
                fd_put(Y, YD1, YPs)
                % queue_goal(Y #< Z)
            ;   Z =:= 0 % Multiple solutions so do nothing special.
            )
        ;   (   { fd_get(Z, _, n(ZL), _, _), ZL > 0 } ->
                { fd_get(Y, YD, YPs),
                  YMin is ZL + 1,
                  domain_remove_smaller_than(YD, YMin, YD1) },
                fd_put(Y, YD1, YPs)
                % queue_goal(Y #> ZL)
            ;   { fd_get(Z, _, _, n(ZU), _), ZU < 0 } ->
                { fd_get(Y, YD, YPs),
                  YMax is ZU - 1,
                  domain_remove_greater_than(YD, YMax, YD1) },
                fd_put(Y, YD1, YPs)
                % queue_goal(Y #< ZU)
            ;   true
            )
        ).


%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Z = X rem Y

run_propagator(prem(X,Y,Z), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), Y =\= 0, Z is X rem Y
            ;   U is abs(X),
                { fd_get(Y, YD, _) },
                (   X >=0, { domain_infimum(YD, n(Min)), Min >= 0 } -> L = 0
                ;   L is -U
                ),
                { Z in L..U }
            )
        ;   nonvar(Y) ->
            Y =\= 0,
            (   abs(Y) =:= 1 -> kill(MState), Z = 0
            ;   var(Z) ->
                YP is abs(Y) - 1,
                YN is -YP,
                (   Y > 0, { fd_get(X, _, n(XL), n(XU), _) } ->
                    (   abs(XL) < Y, XU < Y -> kill(MState), Z = X, ZL = XL
                    ;   XL < 0, abs(XL) < Y -> ZL = XL
                    ;   XL >= 0 -> ZL = 0
                    ;   ZL = YN
                    ),
                    (   XU > 0, XU < Y -> ZU = XU
                    ;   XU < 0 -> ZU = 0
                    ;   ZU = YP
                    )
                ;   ZL = YN, ZU = YP
                ),
                (   { fd_get(Z, ZD, ZPs) } ->
                    { domains_intersection(ZD, from_to(n(ZL), n(ZU)), ZD1) },
                    fd_put(Z, ZD1, ZPs)
                ;   ZD1 = from_to(n(Z), n(Z))
                ),
                (   { fd_get(X, XD, _), domain_infimum(XD, n(Min)) } ->
                    Z1 is Min rem Y,
                    (   { domain_contains(ZD1, Z1) } -> true
                    ;   neq_num(X, Min)
                    )
                ;   true
                ),
                (   { fd_get(X, XD1, _), domain_supremum(XD1, n(Max)) } ->
                    Z2 is Max rem Y,
                    (   { domain_contains(ZD1, Z2) } -> true
                    ;   neq_num(X, Max)
                    )
                ;   true
                )
            ;   { fd_get(X, XD1, XPs1) },
                % if possible, propagate at the boundaries
                (   { domain_infimum(XD1, n(Min)) } ->
                    (   Min rem Y =:= Z -> true
                    ;   Y > 0, Min > 0 ->
                        Next is ((Min - Z + Y - 1) div Y)*Y + Z,
                        { domain_remove_smaller_than(XD1, Next, XD2) },
                        fd_put(X, XD2, XPs1)
                    ;   % TODO: bigger steps in other cases as well
                        neq_num(X, Min)
                    )
                ;   true
                ),
                (   { fd_get(X, XD3, XPs3) } ->
                    (   { domain_supremum(XD3, n(Max)) } ->
                        (   Max rem Y =:= Z -> true
                        ;   Y > 0, Max > 0  ->
                            Prev is ((Max - Z) div Y)*Y + Z,
                            { domain_remove_greater_than(XD3, Prev, XD4) },
                            fd_put(X, XD4, XPs3)
                        ;   % TODO: bigger steps in other cases as well
                            neq_num(X, Max)
                        )
                    ;   true
                    )
                ;   true
                )
            )
        ;   X == Y -> kill(MState), Z = 0
        ;   { fd_get(Z, ZD, ZPs) } ->
            { fd_get(Y, _, YInf, YSup, _),
              fd_get(X, _, XInf, XSup, _),
              M cis max(abs(YInf),YSup),
              (   XInf cis_geq n(0) -> Inf0 = n(0)
              ;   Inf0 = XInf
              ),
              (   XSup cis_leq n(0) -> Sup0 = n(0)
              ;   Sup0 = XSup
              ),
              NInf cis max(max(Inf0, -M + n(1)), min(XInf,-XSup)),
              NSup cis min(min(Sup0, M - n(1)), max(abs(XInf),XSup)),
              domains_intersection(ZD, from_to(NInf,NSup), ZD1) },
            fd_put(Z, ZD1, ZPs)
        ;   true % TODO: propagate more
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Z = max(X,Y)

run_propagator(pmax(X,Y,Z), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), queue_goal(Z is max(X,Y))
            ;   nonvar(Z) ->
                (   Z =:= X -> kill(MState), queue_goal(X #>= Y)
                ;   Z > X -> queue_goal(Z = Y)
                ;   { false } % Z < X
                )
            ;   { fd_get(Y, _, YInf, YSup, _) },
                (   { YInf cis_gt n(X) } -> queue_goal(Z = Y)
                ;   { YSup cis_lt n(X) } -> queue_goal(Z = X)
                ;   YSup = n(M) ->
                    { fd_get(Z, ZD, ZPs),
                      domain_remove_greater_than(ZD, M, ZD1) },
                    fd_put(Z, ZD1, ZPs)
                ;   []
                )
            )
        ;   nonvar(Y) -> run_propagator(pmax(Y,X,Z), MState)
        ;   { fd_get(Z, ZD, ZPs) } ->
            { fd_get(X, _, XInf, XSup, _),
              fd_get(Y, _, YInf, YSup, _) },
            (   { YInf cis_gt XSup } -> kill(MState), queue_goal(Z = Y)
            ;   { YSup cis_lt XInf } -> kill(MState), queue_goal(Z = X)
            ;   { n(M) cis max(XSup, YSup) } ->
                { domain_remove_greater_than(ZD, M, ZD1) },
                fd_put(Z, ZD1, ZPs)
            ;   []
            )
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Z = min(X,Y)

run_propagator(pmin(X,Y,Z), MState) -->
        (   nonvar(X) ->
            (   nonvar(Y) -> kill(MState), Z is min(X,Y)
            ;   nonvar(Z) ->
                (   Z =:= X -> kill(MState), { X #=< Y }
                ;   Z < X -> Z = Y
                ;   { false } % Z > X
                )
            ;   { fd_get(Y, _, YInf, YSup, _) },
                (   { YSup cis_lt n(X) } -> Z = Y
                ;   { YInf cis_gt n(X) } -> Z = X
                ;   YInf = n(M) ->
                    { fd_get(Z, ZD, ZPs),
                      domain_remove_smaller_than(ZD, M, ZD1) },
                    fd_put(Z, ZD1, ZPs)
                ;   []
                )
            )
        ;   nonvar(Y) -> run_propagator(pmin(Y,X,Z), MState)
        ;   { fd_get(Z, ZD, ZPs) } ->
            { fd_get(X, _, XInf, XSup, _),
              fd_get(Y, _, YInf, YSup, _) },
            (   { YSup cis_lt XInf } -> kill(MState), Z = Y
            ;   { YInf cis_gt XSup } -> kill(MState), Z = X
            ;   { n(M) cis min(XInf, YInf) } ->
                { domain_remove_smaller_than(ZD, M, ZD1) },
                fd_put(Z, ZD1, ZPs)
            ;   []
            )
        ;   []
        ).
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Z = X ^ Y

run_propagator(pexp(X,Y,Z,Morph), MState) -->
        (   X == 1 -> kill(MState), Z = 1
        ;   X == 0 ->
            queue_goal((Z in 0..1, Y #>= 0)),
            morph_into_propagator(MState, [Y,Z], reified_eq(1,Y,1,0,[],Z), Morph)
        ;   Y == 0 -> kill(MState), Z = 1
        ;   Y == 1 -> kill(MState), Z = X
        ;   nonvar(X) ->
            (   nonvar(Y) ->
                (   Y >= 0 -> true ; X =:= -1 ),
                kill(MState),
                Z is X^Y
            ;   nonvar(Z) ->
                (   Z > 1 ->
                    abs(X) > 1,
                    kill(MState),
                    { integer_log_b(Z, X, 1, Y) }
                ;   true
                )
            ;   { fd_get(Y, _, YL, YU, _),
                  fd_get(Z, ZD, ZPs) },
                (   { X > 0, YL cis_geq n(0) } ->
                    { NZL cis n(X)^YL,
                      NZU cis n(X)^YU,
                      domains_intersection(ZD, from_to(NZL,NZU), NZD) },
                    fd_put(Z, NZD, ZPs)
                ;   true
                ),
                (   { X > 0,
                      fd_get(Z, _, _, n(ZMax), _),
                      ZMax > 0 } ->
                    { floor_integer_log_b(ZMax, X, 1, YCeil) },
                    queue_goal(Y in inf..YCeil)
                ;   true
                )
            )
        ;   nonvar(Z) ->
            (   nonvar(Y) ->
                { integer_kth_root(Z, Y, R) },
                kill(MState),
                (   { even(Y) } ->
                    N is -R,
                    { X in N \/ R }
                ;   X = R
                )
            ;   { fd_get(X, _, n(NXL), _, _), NXL > 1 } ->
                (   { Z > 1, between(NXL, Z, Exp), NXL^Exp > Z } ->
                    Exp1 is Exp - 1,
                    { fd_get(Y, YD, YPs),
                      domains_intersection(YD, from_to(n(1),n(Exp1)), YD1) },
                    fd_put(Y, YD1, YPs),
                    (   { fd_get(X, XD, XPs) } ->
                        { domain_infimum(YD1, n(YL)),
                          integer_kth_root_leq(Z, YL, RU),
                          domains_intersection(XD, from_to(n(NXL),n(RU)), XD1) },
                        fd_put(X, XD1, XPs)
                    ;   true
                    )
                ;   true
                )
            ;   true
            )
        ;   nonvar(Y), Y > 0 ->
            (   { even(Y) } ->
                { fd_get(Z, ZD0, ZPs0),
                  domain_remove_smaller_than(ZD0, 0, ZDG0) },
                fd_put(Z, ZDG0, ZPs0)
            ;   true
            ),
            (   { fd_get(X, XD, XL, XU, _), fd_get(Z, ZD, ZL, ZU, ZPs) } ->
                (   { domain_contains(ZD, 0) } -> XD1 = XD
                ;   { domain_remove(XD, 0, XD1) }
                ),
                (   { domain_contains(XD, 0) } -> ZD1 = ZD
                ;   { domain_remove(ZD, 0, ZD1) }
                ),
                (   { even(Y) } ->
                    (   { XL cis_geq n(0) } ->
                        { NZL cis XL^n(Y) }
                    ;   { XU cis_leq n(0) } ->
                        { NZL cis XU^n(Y) }
                    ;   NZL = n(0)
                    ),
                    { NZU cis max(abs(XL),abs(XU))^n(Y),
                      domains_intersection(ZD1, from_to(NZL,NZU), ZD2) }
                ;   (   { finite(XL) } ->
                        { NZL cis XL^n(Y),
                          NZU cis XU^n(Y) },
                        { domains_intersection(ZD1, from_to(NZL,NZU), ZD2) }
                    ;   ZD2 = ZD1
                    )
                ),
                fd_put(Z, ZD2, ZPs),
                { (   even(Y), ZU = n(Num) ->
                    integer_kth_root_leq(Num, Y, RU),
                    (   XL cis_geq n(0), ZL = n(Num1) ->
                        integer_kth_root_leq(Num1, Y, RL0),
                        (   RL0^Y < Num1 -> RL is RL0 + 1
                        ;   RL = RL0
                        )
                    ;   RL is -RU
                    ),
                    RL =< RU,
                    NXD = from_to(n(RL),n(RU))
                ;   odd(Y), ZL cis_geq n(0), ZU = n(Num) ->
                    integer_kth_root_leq(Num, Y, RU),
                    ZL = n(Num1),
                    integer_kth_root_leq(Num1, Y, RL0),
                    (   RL0^Y < Num1 -> RL is RL0 + 1
                    ;   RL = RL0
                    ),
                    RL =< RU,
                    NXD = from_to(n(RL),n(RU))
                ;   NXD = XD1   % TODO: propagate more
                ) },
                (   { fd_get(X, XD2, XPs) } ->
                    { domains_intersection(XD2, XD1, XD3),
                      domains_intersection(XD3, NXD, XD4) },
                    fd_put(X, XD4, XPs)
                ;   true
                )
            ;   true
            )
        ;   { fd_get(X, _, XL, _, _),
              XL cis_gt n(0),
              fd_get(Y, _, YL, _, _),
              YL cis_gt n(0),
              fd_get(Z, ZD, ZPs) } ->
            { n(NZL) cis XL^YL,
              domain_remove_smaller_than(ZD, NZL, ZD1) },
            fd_put(Z, ZD1, ZPs)
        ;   true
        ).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Y = sign(X)

run_propagator(psign(X,Y), MState) -->
        (   nonvar(X) -> kill(MState), queue_goal(Y is sign(X))
        ;   Y == -1 -> kill(MState), queue_goal(X #< 0)
        ;   Y == 0 -> kill(MState), queue_goal(X = 0)
        ;   Y == 1 -> kill(MState), queue_goal(X #> 0)
        ;   { fd_get(X, _, XL, XU, _) },
            (   { XL = n(L), L > 0 } -> kill(MState), queue_goal(Y = 1)
            ;   { XU = n(U), U < 0 } -> kill(MState), queue_goal(Y = -1)
            ;   true
            )
        ).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Y = popcount(X)

run_propagator(ppopcount(X,Y), MState) -->
        (   nonvar(X) ->
            kill(MState),
            queue_goal(popcount(X, Y))
        ;   true
        ).


%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Z = X xor Y

run_propagator(pxor(X,Y,Z), MState) -->
        (   nonvar(X), nonvar(Y) ->
            kill(MState),
            Z is xor(X, Y)
        ;   nonvar(Y), nonvar(Z) ->
            kill(MState),
            X is xor(Y, Z)
        ;   nonvar(Z), nonvar(X) ->
            kill(MState),
            Y is xor(Z, X)
        ;   X == Y ->
            kill(MState),
            queue_goal(Z = 0)
        ;   Y == Z ->
            kill(MState),
            queue_goal(X = 0)
        ;   Z == X ->
            kill(MState),
            queue_goal(Y = 0)
        ;   X == 0 ->
            kill(MState),
            queue_goal(Y = Z)
        ;   Y == 0 ->
            kill(MState),
            queue_goal(Z = X)
        ;   Z == 0 ->
            kill(MState),
            queue_goal(X = Y)
        ;   true
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(pzcompare(Order, A, B), MState) -->
        (   A == B -> kill(MState), Order = (=)
        ;   (   nonvar(A) ->
                (   nonvar(B) ->
                    kill(MState),
                    (   A > B -> Order = (>)
                    ;   Order = (<)
                    )
                ;   { fd_get(B, _, BL, BU, _) },
                    (   { BL cis_gt n(A) } -> kill(MState), Order = (<)
                    ;   { BU cis_lt n(A) } -> kill(MState), Order = (>)
                    ;   []
                    )
                )
            ;   nonvar(B) ->
                { fd_get(A, _, AL, AU, _) },
                (   { AL cis_gt n(B) } -> kill(MState), Order = (>)
                ;   { AU cis_lt n(B) } -> kill(MState), Order = (<)
                ;   []
                )
            ;   { fd_get(A, _, AL, AU, _),
                  fd_get(B, _, BL, BU, _) },
                (   { AL cis_gt BU } -> kill(MState), Order = (>)
                ;   { AU cis_lt BL } -> kill(MState), Order = (<)
                ;   []
                )
            )
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% reified constraints

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(reified_in(V,Dom,B), MState) -->
        (   integer(V) ->
            kill(MState),
            (   { domain_contains(Dom, V) } -> B = 1
            ;   B = 0
            )
        ;   B == 1 -> kill(MState), { domain(V, Dom) }
        ;   B == 0 ->
            kill(MState), { domain_complement(Dom, C), domain(V, C) }
        ;   { fd_get(V, VD, _) },
            (   { domains_intersection(VD, Dom, I) } ->
                (   I == VD -> kill(MState), B = 1
                ;   []
                )
            ;   kill(MState), B = 0
            )
        ).

run_propagator(reified_tuple_in(Tuple, R, B), MState) -->
        { get_attr(R, clpz_relation, Relation) },
        (   B == 1 -> kill(MState), { tuples_in([Tuple], Relation) }
        ;   (   ground(Tuple) ->
                kill(MState),
                (   { memberchk(Tuple, Relation) } -> B = 1
                ;   B = 0
                )
            ;   { relation_unifiable(Relation, Tuple, Us, _, _) },
                (   Us = [] -> kill(MState), B = 0
                ;   []
                )
            )
        ).

run_propagator(tuples_not_in(Tuples, Relation, B), MState) -->
        (   B == 0 ->
            kill(MState),
            { tuples_in_conjunction(Tuples, Relation, Conj),
              #\ Conj }
        ;   []
        ).

run_propagator(kill_reified_tuples(B, Ps, Bs), _) -->
        (   B == 0 ->
            { maplist(kill_entailed, Ps),
              phrase(as(Bs), As),
              maplist(kill_entailed, As) }
        ;   []
        ).

run_propagator(reified_fd(V,B), MState) -->
        (   { fd_inf(V, I), I \== inf, fd_sup(V, S), S \== sup } ->
            kill(MState),
            B = 1
        ;   { B == 0 } ->
            (   { fd_inf(V, inf) } -> []
            ;   { fd_sup(V, sup) } -> []
            ;   { false }
            )
        ;   []
        ).

% The result of X/Y, X mod Y, and X rem Y is undefined iff Y is 0.

run_propagator(pskeleton(X,Y,D,Skel,Z,_), MState) -->
        (   Y == 0 -> kill(MState), D = 0
        ;   D == 1 ->
            kill(MState), neq_num(Y, 0), { skeleton([X,Y,Z], Skel) }
        ;   integer(Y), Y =\= 0 ->
            kill(MState), D = 1, { skeleton([X,Y,Z], Skel) }
        ;   { fd_get(Y, YD, _), \+ domain_contains(YD, 0) } ->
            kill(MState), D = 1, { skeleton([X,Y,Z], Skel) }
        ;   []
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Propagators for arithmetic functions that only propagate
   functionally. These are currently the bitwise operations.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

run_propagator(pfunction(Op,A,B,R), MState) -->
        (   integer(A), integer(B) ->
            kill(MState),
            Expr =.. [Op,A,B],
            R is Expr
        ;   []
        ).
run_propagator(pfunction(Op,A,R), MState) -->
        (   integer(A) ->
            kill(MState),
            (   Op == msb -> { msb(A, R) }
            ;   Op == lsb -> { lsb(A, R) }
            ;   Expr =.. [Op,A],
                R is Expr
            )
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(reified_geq(DX,X,DY,Y,Ps,B), MState) -->
        (   DX == 0 -> kill(MState, Ps), B = 0
        ;   DY == 0 -> kill(MState, Ps), B = 0
        ;   B == 1 ->  kill(MState), DX = 1, DY = 1, { geq(X, Y) }
        ;   DX == 1, DY == 1 ->
            (   var(B) ->
                (   nonvar(X) ->
                    (   nonvar(Y) ->
                        kill(MState),
                        (   X >= Y -> B = 1 ; B = 0 )
                    ;   { fd_get(Y, _, YL, YU, _) },
                        (   { n(X) cis_geq YU } -> kill(MState, Ps), B = 1
                        ;   { n(X) cis_lt YL } -> kill(MState, Ps), B = 0
                        ;   []
                        )
                    )
                ;   nonvar(Y) ->
                    { fd_get(X, _, XL, XU, _) },
                    (   { XL cis_geq n(Y) } -> kill(MState, Ps), B = 1
                    ;   { XU cis_lt n(Y) } -> kill(MState, Ps), B = 0
                    ;   []
                    )
                ;   X == Y -> kill(MState, Ps), B = 1
                ;   { fd_get(X, _, XL, XU, _),
                      fd_get(Y, _, YL, YU, _) },
                    (   { XL cis_geq YU } -> kill(MState, Ps), B = 1
                    ;   { XU cis_lt YL } -> kill(MState, Ps), B = 0
                    ;   []
                    )
                )
            ;   B =:= 0 -> { kill(MState), X #< Y }
            ;   []
            )
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(reified_eq(DX,X,DY,Y,Ps,B), MState) -->
        (   DX == 0 -> kill(MState, Ps), B = 0
        ;   DY == 0 -> kill(MState, Ps), B = 0
        ;   B == 1 -> kill(MState), DX = 1, DY = 1, X = Y
        ;   DX == 1, DY == 1 ->
            (   var(B) ->
                (   nonvar(X) ->
                    (   nonvar(Y) ->
                        kill(MState),
                        (   X =:= Y -> B = 1 ; B = 0)
                    ;   { fd_get(Y, YD, _) },
                        (   { domain_contains(YD, X) } -> []
                        ;   kill(MState, Ps), B = 0
                        )
                    )
                ;   nonvar(Y) ->
                    run_propagator(reified_eq(DY,Y,DX,X,Ps,B), MState)
                ;   X == Y -> kill(MState), B = 1
                ;   { fd_get(X, _, XL, XU, _),
                      fd_get(Y, _, YL, YU, _) },
                    (   { XL cis_gt YU } -> kill(MState, Ps), B = 0
                    ;   { YL cis_gt XU } -> kill(MState, Ps), B = 0
                    ;   []
                    )
                )
            ;   B =:= 0 -> kill(MState), { X #\= Y }
            ;   []
            )
        ;   []
        ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(reified_neq(DX,X,DY,Y,Ps,B), MState) -->
        (   DX == 0 -> kill(MState, Ps), B = 0
        ;   DY == 0 -> kill(MState, Ps), B = 0
        ;   B == 1 -> { kill(MState), DX = 1, DY = 1, X #\= Y }
        ;   DX == 1, DY == 1 ->
            (   var(B) ->
                (   nonvar(X) ->
                    (   nonvar(Y) ->
                        kill(MState),
                        (   X =\= Y -> B = 1 ; B = 0)
                    ;   { fd_get(Y, YD, _) },
                        (   { domain_contains(YD, X) } -> []
                        ;   kill(MState, Ps), B = 1
                        )
                    )
                ;   nonvar(Y) ->
                    run_propagator(reified_neq(DY,Y,DX,X,Ps,B), MState)
                ;   X == Y -> kill(MState), B = 0
                ;   { fd_get(X, _, XL, XU, _),
                      fd_get(Y, _, YL, YU, _) },
                    (   { XL cis_gt YU } -> kill(MState, Ps), B = 1
                    ;   { YL cis_gt XU } -> kill(MState, Ps), B = 1
                    ;   []
                    )
                )
            ;   B =:= 0 -> kill(MState), X = Y
            ;   []
            )
        ;   []
        ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(reified_and(X,Ps1,Y,Ps2,B), MState) -->
        (   nonvar(X) ->
            kill(MState),
            (   X =:= 0 -> { maplist(kill_entailed, Ps2), B = 0 }
            ;   B = Y
            )
        ;   nonvar(Y) -> run_propagator(reified_and(Y,Ps2,X,Ps1,B), MState)
        ;   B == 1 -> kill(MState), X = 1, Y = 1
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(reified_or(X,Ps1,Y,Ps2,B), MState) -->
        (   nonvar(X) ->
            kill(MState),
            (   X =:= 1 -> { maplist(kill_entailed, Ps2), B = 1 }
            ;   B = Y
            )
        ;   nonvar(Y) -> run_propagator(reified_or(Y,Ps2,X,Ps1,B), MState)
        ;   B == 0 -> kill(MState), X = 0, Y = 0
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(reified_not(X,Y), MState) -->
        (   X == 0 -> kill(MState), Y = 1
        ;   X == 1 -> kill(MState), Y = 0
        ;   Y == 0 -> kill(MState), X = 1
        ;   Y == 1 -> kill(MState), X = 0
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
run_propagator(pimpl(X, Y, Ps), MState) -->
        (   nonvar(X) ->
            kill(MState),
            (   X =:= 1 -> Y = 1
            ;   { maplist(kill_entailed, Ps) }
            )
        ;   nonvar(Y) ->
            kill(MState),
            (   Y =:= 0 -> X = 0
            ;   { maplist(kill_entailed, Ps) }
            )
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(preified_slash(X, Y, D, R), MState) -->
        (   Y == 0 ->
            kill(MState),
            D = 0
        ;   Y == 1 ->
            kill(MState),
            D = 1,
            R = X
        ;   nonvar(X),
            nonvar(Y) ->
            kill(MState),
            (   X mod Y =:= 0 ->
                D = 1,
                R is X // Y
            ;   D = 0
            )
        ;   D == 1 ->
            kill(MState),
            queue_goal(X/Y #= R)
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_propagator(preified_exp(X, Y, D, R), MState) -->
        (   X == 1 ->
            kill(MState),
            D = 1,
            R = 1
        ;   Y == 0 ->
            kill(MState),
            D = 1,
            R = 1
        ;   Y == 1 ->
            kill(MState),
            D = 1,
            R = X
        ;   nonvar(X),
            nonvar(Y) ->
            kill(MState),
            (   ( abs(X) =:= 1 ; Y >= 0 ) ->
                D = 1,
                R is X^Y
            ;   D = 0
            )
        ;   D == 1 ->
            kill(MState),
            queue_goal(X^Y #= R)
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_bounds(X, XD, XPs, XL, XU, NXL, NXU) -->
        (   NXL == XL, NXU == XU -> []
        ;   { domains_intersection(XD, from_to(NXL, NXU), NXD) },
            fd_put(X, NXD, XPs)
        ).

min_product(L1, U1, L2, U2, Min) :-
        Min cis min(min(L1*L2,L1*U2),min(U1*L2,U1*U2)).
max_product(L1, U1, L2, U2, Max) :-
        Max cis max(max(L1*L2,L1*U2),max(U1*L2,U1*U2)).

finite(n(_)).

in_(L, U, X) :-
        fd_get(X, XD, XPs),
        domains_intersection(XD, from_to(L,U), NXD),
        fd_put(X, NXD, XPs).

min_max_factor(L1, U1, L2, U2, L3, U3, Min, Max) :-
        % use findall/3 to forget auxiliary constraints that are only
        % needed temporarily for reasoning about domain boundaries
        findall(Min-Max, min_max_factor_(L1, U1, L2, U2, L3, U3, Min, Max), [Min-Max]).

min_max_factor_(L1, U1, L2, U2, L3, U3, Min, Max) :-
        (   U1 cis_lt n(0),
            L2 cis_lt n(0), U2 cis_gt n(0),
            L3 cis_lt n(0), U3 cis_gt n(0) ->
            maplist(in_(L1,U1), [Z1,Z2]),
            in_(L2, n(-1), X1), in_(n(1), U3, Y1),
            (   X1*Y1 #= Z1 ->
                (   fd_get(Y1, _, Inf1, Sup1, _) -> true
                ;   Inf1 = n(Y1), Sup1 = n(Y1)
                )
            ;   Inf1 = inf, Sup1 = n(-1)
            ),
            in_(n(1), U2, X2), in_(L3, n(-1), Y2),
            (   X2*Y2 #= Z2 ->
                (   fd_get(Y2, _, Inf2, Sup2, _) -> true
                ;   Inf2 = n(Y2), Sup2 = n(Y2)
                )
            ;   Inf2 = n(1), Sup2 = sup
            ),
            Min cis max(min(Inf1,Inf2), L3),
            Max cis min(max(Sup1,Sup2), U3)
        ;   L1 cis_gt n(0),
            L2 cis_lt n(0), U2 cis_gt n(0),
            L3 cis_lt n(0), U3 cis_gt n(0) ->
            maplist(in_(L1,U1), [Z1,Z2]),
            in_(L2, n(-1), X1), in_(L3, n(-1), Y1),
            (   X1*Y1 #= Z1 ->
                (   fd_get(Y1, _, Inf1, Sup1, _) -> true
                ;   Inf1 = n(Y1), Sup1 = n(Y1)
                )
            ;   Inf1 = n(1), Sup1 = sup
            ),
            in_(n(1), U2, X2), in_(n(1), U3, Y2),
            (   X2*Y2 #= Z2 ->
                (   fd_get(Y2, _, Inf2, Sup2, _) -> true
                ;   Inf2 = n(Y2), Sup2 = n(Y2)
                )
            ;   Inf2 = inf, Sup2 = n(-1)
            ),
            Min cis max(min(Inf1,Inf2), L3),
            Max cis min(max(Sup1,Sup2), U3)
        ;   min_factor(L1, U1, L2, U2, Min0),
            Min cis max(L3,Min0),
            max_factor(L1, U1, L2, U2, Max0),
            Max cis min(U3,Max0)
        ).

min_factor(L1, U1, L2, U2, Min) :-
        (   L1 cis_geq n(0), L2 cis_gt n(0), finite(U2) ->
            Min cis div(L1+U2-n(1),U2)
        ;   L1 cis_gt n(0), U2 cis_lt n(0) -> Min cis div(U1,U2)
        ;   L1 cis_gt n(0), L2 cis_geq n(0) -> Min = n(1)
        ;   L1 cis_gt n(0) -> Min cis -U1
        ;   U1 cis_lt n(0), U2 cis_leq n(0) ->
            (   finite(L2) -> Min cis div(U1+L2+n(1),L2)
            ;   Min = n(1)
            )
        ;   U1 cis_lt n(0), L2 cis_geq n(0) -> Min cis div(L1,L2)
        ;   U1 cis_lt n(0) -> Min = L1
        ;   L2 cis_leq n(0), U2 cis_geq n(0) -> Min = inf
        ;   Min cis min(min(div(L1,L2),div(L1,U2)),min(div(U1,L2),div(U1,U2)))
        ).
max_factor(L1, U1, L2, U2, Max) :-
        (   L1 cis_geq n(0), L2 cis_geq n(0) -> Max cis div(U1,L2)
        ;   L1 cis_gt n(0), U2 cis_leq n(0) ->
            (   finite(L2) -> Max cis div(L1-L2-n(1),L2)
            ;   Max = n(-1)
            )
        ;   L1 cis_gt n(0) -> Max = U1
        ;   U1 cis_lt n(0), U2 cis_lt n(0) -> Max cis div(L1,U2)
        ;   U1 cis_lt n(0), L2 cis_geq n(0) ->
            (   finite(U2) -> Max cis div(U1-U2+n(1),U2)
            ;   Max = n(-1)
            )
        ;   U1 cis_lt n(0) -> Max cis -L1
        ;   L2 cis_leq n(0), U2 cis_geq n(0) -> Max = sup
        ;   Max cis max(max(div(L1,L2),div(L1,U2)),max(div(U1,L2),div(U1,U2)))
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   J-C. Régin: "A filtering algorithm for constraints of difference in
   CSPs", AAAI-94, Seattle, WA, USA, pp 362--367, 1994
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

distinct_attach([], _, _) --> [].
distinct_attach([X|Xs], Prop, Right) -->
        (   var(X) ->
            init_propagator_([X], Prop),
            { make_propagator(pexclude(Xs,Right,X), P1) },
            init_propagator_([X], P1),
            trigger_prop(P1)
        ;   exclude_fire(Xs, Right, X)
        ),
        distinct_attach(Xs, Prop, [X|Right]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   For each integer of the union of domains, an attributed variable is
   introduced, to benefit from constant-time access. Attributes are:

   value ... integer corresponding to the node
   free  ... whether this (right) node is still free
   edges ... [flow_from(F,From)] and [flow_to(F,To)] where F has an
             attribute "flow" that is either 0 or 1 and an attribute "used"
             if it is part of a maximum matching
   parent ... used in breadth-first search
   g0_edges ... [flow_to(F,To)] as above
   visited ... true if node was visited in DFS
   index, in_stack, lowlink ... used in Tarjan's SCC algorithm
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

difference_arcs(Vars, FreeLeft, FreeRight) :-
        empty_assoc(E),
        phrase(difference_arcs(Vars, FreeLeft), [E], [NumVar]),
        assoc_to_list(NumVar, LsNumVar),
        pairs_values(LsNumVar, FreeRight).

domain_to_list(Domain, List) :- phrase(domain_to_list(Domain), List).

domain_to_list(split(_, Left, Right)) -->
        domain_to_list(Left), domain_to_list(Right).
domain_to_list(empty)                 --> [].
domain_to_list(from_to(n(F),n(T)))    --> { numlist(F, T, Ns) }, seq(Ns).

difference_arcs([], []) --> [].
difference_arcs([V|Vs], FL0) -->
        (   { fd_get(V, Dom, _), domain_to_list(Dom, Ns) } ->
            { FL0 = [V|FL] },
            enumerate(Ns, V),
            difference_arcs(Vs, FL)
        ;   difference_arcs(Vs, FL0)
        ).

writeln(T) :- write(T), nl.

:- meta_predicate must_succeed(0).

must_succeed(G) :-
        (   G -> true
        ;   throw(failed-G)
        ).

enumerate([], _) --> [].
enumerate([N|Ns], V) -->
        state(NumVar0, NumVar),
        { (   get_assoc(N, NumVar0, Y) -> NumVar0 = NumVar
          ;   put_assoc(N, NumVar0, Y, NumVar),
              put_attr(Y, value, N)
          ),
          put_attr(F, flow, 0),
          must_succeed(append_edge(Y, edges, flow_from(F,V))),
          must_succeed(append_edge(V, edges, flow_to(F,Y))) },
        enumerate(Ns, V).

append_edge(V, Attr, E) :-
        (   get_attr_(Attr, V, Es) ->
            put_attr_(Attr, V, [E|Es])
        ;   put_attr_(Attr, V, [E])
        ).

get_attr_(edges, V, Es) :- get_attr(V, edges, Es).
get_attr_(g0_edges, V, Es) :- get_attr(V, g0_edges, Es).

put_attr_(edges, V, E) :- put_attr(V, edges, E).
put_attr_(g0_edges, V, E) :- put_attr(V, g0_edges, E).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Strategy: Breadth-first search until we find a free right vertex in
   the value graph, then find an augmenting path in reverse.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

clear_parent(V) :- del_attr(V, parent).

maximum_matching([]).
maximum_matching([FL|FLs]) :-
        augmenting_path_to([[FL]], Levels, To),
        phrase(augmenting_path(FL, To), Path),
        maplist(maplist(clear_parent), Levels),
        del_attr(To, free),
        adjust_alternate_1(Path),
        maximum_matching(FLs).

reachables([]) --> [].
reachables([V|Vs]) -->
        { get_attr(V, edges, Es) },
        reachables_(Es, V),
        reachables(Vs).

reachables_([], _) --> [].
reachables_([E|Es], V) -->
        edge_reachable(E, V),
        reachables_(Es, V).

edge_reachable(flow_to(F,To), V) -->
        (   { get_attr(F, flow, 0),
              \+ get_attr(To, parent, _) } ->
            { put_attr(To, parent, V-F) },
            [To]
        ;   []
        ).
edge_reachable(flow_from(F,From), V) -->
        (   { get_attr(F, flow, 1),
              \+ get_attr(From, parent, _) } ->
            { put_attr(From, parent, V-F) },
            [From]
        ;   []
        ).

augmenting_path_to(Levels0, Levels, Right) :-
        Levels0 = [Vs|_],
        Levels1 = [Tos|Levels0],
        phrase(reachables(Vs), Tos),
        Tos = [_|_],
        (   member(Right, Tos), get_attr(Right, free, true) ->
            Levels = Levels1
        ;   augmenting_path_to(Levels1, Levels, Right)
        ).

augmenting_path(S, V) -->
        (   { V == S } -> []
        ;   { get_attr(V, parent, V1-Augment) },
            [Augment],
            augmenting_path(S, V1)
        ).

adjust_alternate_1([A|Arcs]) :-
        put_attr(A, flow, 1),
        adjust_alternate_0(Arcs).

adjust_alternate_0([]).
adjust_alternate_0([A|Arcs]) :-
        put_attr(A, flow, 0),
        adjust_alternate_1(Arcs).

% Instead of applying Berge's property directly, we can translate the
% problem in such a way, that we have to search for the so-called
% strongly connected components of the graph.

g_g0(V) :-
        get_attr(V, edges, Es),
        maplist(g_g0_(V), Es).

g_g0_(V, flow_to(F,To)) :-
        (   get_attr(F, flow, 1) ->
            append_edge(V, g0_edges, flow_to(F,To))
        ;   append_edge(To, g0_edges, flow_to(F,V))
        ).


g0_successors(V, Tos) :-
        (   get_attr(V, g0_edges, Tos0) ->
            maplist(arg(2), Tos0, Tos)
        ;   Tos = []
        ).

put_free(F) :- put_attr(F, free, true).

free_node(F) :- get_attr(F, free, true).

:- meta_predicate with_local_attributes(?, 0, ?).

:- dynamic(nat_copy/1).

with_local_attributes(Vars, Goal, Result) :-
        catch((Goal,
               % Create a copy where all attributes are removed. Only
               % the result and its relation to Vars matters. We throw
               % an exception to undo all modifications to attributes
               % we made during propagation, and unify the variables
               % in the thrown copy with Vars in order to get the
               % intended variables in Result.
               copy_term_nat(Vars-Result, Copy),
               throw(local_attributes(Copy))),
              local_attributes(Vars-Result),
              true).

distinct(Vars) -->
        { with_local_attributes(Vars,
           (   difference_arcs(Vars, FreeLeft, FreeRight0),
               length(FreeLeft, LFL),
               length(FreeRight0, LFR),
               LFL =< LFR,
               maplist(put_free, FreeRight0),
               maximum_matching(FreeLeft),
               include(free_node, FreeRight0, FreeRight),
               maplist(g_g0, FreeLeft),
               scc(FreeLeft, g0_successors),
               maplist(dfs_used, FreeRight),
               phrase(distinct_goals(FreeLeft), Gs)), Gs) },
        disable_queue,
        neq_nums(Gs),
        enable_queue.

neq_nums([]) --> [].
neq_nums([neq_num(V,N)|VNs]) -->
        % { portray_clause(neq_num(V, N)) },
        neq_num(V, N), neq_nums(VNs).

distinct_goals([]) --> [].
distinct_goals([V|Vs]) -->
        { get_attr(V, edges, Es) },
        distinct_goals_(Es, V),
        distinct_goals(Vs).

distinct_goals_([], _) --> [].
distinct_goals_([flow_to(F,To)|Es], V) -->
        (   { get_attr(F, flow, 0),
              \+ get_attr(F, used, true),
              get_attr(V, lowlink, L1),
              get_attr(To, lowlink, L2),
              L1 =\= L2 } ->
            { get_attr(To, value, N) },
            [neq_num(V, N)]
        ;   []
        ),
        distinct_goals_(Es, V).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Mark used edges.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

dfs_used(V) :-
        (   get_attr(V, visited, true) -> true
        ;   put_attr(V, visited, true),
            (   get_attr(V, g0_edges, Es) ->
                dfs_used_edges(Es)
            ;   true
            )
        ).

dfs_used_edges([]).
dfs_used_edges([flow_to(F,To)|Es]) :-
        put_attr(F, used, true),
        dfs_used(To),
        dfs_used_edges(Es).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Tarjan's strongly connected components algorithm.

   DCGs are used to implicitly pass around the global index, stack
   and the predicate relating a vertex to its successors.

   For more information about this technique, see:

                 https://www.metalevel.at/prolog/dcg
                 ===================================

   A Prolog implementation of this algorithm is also available as a
   standalone library from:

                   https://www.metalevel.at/scc.pl
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

scc(Vs, Succ) :- phrase(scc(Vs), [s(0,[],Succ)], _).

scc([])     --> [].
scc([V|Vs]) -->
        (   vindex_defined(V) -> scc(Vs)
        ;   scc_(V), scc(Vs)
        ).

vindex_defined(V) --> { get_attr(V, index, _) }.

vindex_is_index(V) -->
        state(s(Index,_,_)),
        { put_attr(V, index, Index) }.

vlowlink_is_index(V) -->
        state(s(Index,_,_)),
        { put_attr(V, lowlink, Index) }.

index_plus_one -->
        state(s(I,Stack,Succ), s(I1,Stack,Succ)),
        { I1 is I+1 }.

s_push(V)  -->
        state(s(I,Stack,Succ), s(I,[V|Stack],Succ)),
        { put_attr(V, in_stack, true) }.

vlowlink_min_lowlink(V, VP) -->
        { get_attr(V, lowlink, VL),
          get_attr(VP, lowlink, VPL),
          VL1 is min(VL, VPL),
          put_attr(V, lowlink, VL1) }.

successors(V, Tos) --> state(s(_,_,Succ)), { call(Succ, V, Tos) }.

scc_(V) -->
        vindex_is_index(V),
        vlowlink_is_index(V),
        index_plus_one,
        s_push(V),
        successors(V, Tos),
        each_edge(Tos, V),
        (   { get_attr(V, index, VI),
              get_attr(V, lowlink, VI) } -> pop_stack_to(V, VI)
        ;   []
        ).

pop_stack_to(V, N) -->
        state(s(I,[First|Stack],Succ), s(I,Stack,Succ)),
        { del_attr(First, in_stack) },
        (   { First == V } -> []
        ;   { put_attr(First, lowlink, N) },
            pop_stack_to(V, N)
        ).

each_edge([], _) --> [].
each_edge([VP|VPs], V) -->
        (   vindex_defined(VP) ->
            (   v_in_stack(VP) ->
                vlowlink_min_lowlink(V, VP)
            ;   []
            )
        ;   scc_(VP),
            vlowlink_min_lowlink(V, VP)
        ),
        each_edge(VPs, V).

state(S), [S] --> [S].

state(S0, S), [S] --> [S0].

v_in_stack(V) --> { get_attr(V, in_stack, true) }.

node_lowlink(V, L) :- get_attr(V, lowlink, L).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   nvalue/2: A relaxed version of all_distinct/1.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


maximal_matching([]) --> [].
maximal_matching([FL|FLs]) -->
        (   { augmenting_path_to([[FL]], Levels, To) } ->
            { phrase(augmenting_path(FL, To), Path),
              maplist(maplist(clear_parent), Levels),
              del_attr(To, free),
              adjust_alternate_1(Path) },
            [FL]
        ;   []
        ),
        maximal_matching(FLs).

propagate_nvalue(N, Vars0) :-
        sort(Vars0, Vars),
        include(integer, Vars, Ints),
        length(Ints, Distinct),
        vars_num_infinite(Vars, NumInfinite),
        N #>= Distinct,
        with_local_attributes(Vars,
           (   difference_arcs(Vars, FreeLeft, FreeRight0),
               maplist(put_free, FreeRight0),
               phrase(maximal_matching(FreeLeft), MatchedLeft),
               length(MatchedLeft, MaxFurther) ),
            MaxFurther),
        N #=< NumInfinite + Distinct + MaxFurther.

vars_num_infinite(Vars, Num) :-
        foldl(num_infinite, Vars, 0, Num).

num_infinite(Var, N0, N) :-
        (   integer(Var) -> N = N0
        ;   fd_get(Var, Dom, _),
            (   domain_infimum(Dom, n(_)),
                domain_supremum(Dom, n(_)) -> N = N0
            ;   N #= N0 + 1
            )
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Weak arc consistent constraint of difference, currently only
   available internally. Candidate for all_different/2 option.

   See Neng-Fa Zhou: "Programming Finite-Domain Constraint Propagators
   in Action Rules", Theory and Practice of Logic Programming, Vol.6,
   No.5, pp 483-508, 2006
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

weak_arc_all_distinct(Ls) :-
        must_be(list, Ls),
        Orig = original_goal(_, weak_arc_all_distinct(Ls)),
        all_distinct(Ls, [], Orig).

all_distinct([], _, _).
all_distinct([X|Right], Left, Orig) :-
        %\+ list_contains(Right, X),
        (   var(X) ->
            make_propagator(weak_distinct(Left,Right,X,Orig), Prop),
            init_propagator(X, Prop),
            trigger_prop(Prop)
%             make_propagator(check_distinct(Left,Right,X), Prop2),
%             init_propagator(X, Prop2),
%             trigger_prop(Prop2)
        ;   exclude_fire(Left, Right, X)
        ),
        outof_reducer(Left, Right, X),
        all_distinct(Right, [X|Left], Orig).

exclude_fire(Left, Right, E) :-
        all_neq(Left, E),
        all_neq(Right, E).

exclude_fire(Left, Right, E) -->
        all_neq(Left, E),
        all_neq(Right, E).

list_contains([X|Xs], Y) :-
        (   X == Y -> true
        ;   list_contains(Xs, Y)
        ).

kill_if_isolated(Left, Right, X, MState) :-
        append(Left, Right, Others),
        fd_get(X, XDom, _),
        (   all_empty_intersection(Others, XDom) -> kill(MState)
        ;   true
        ).

all_empty_intersection([], _).
all_empty_intersection([V|Vs], XDom) :-
        (   fd_get(V, VDom, _) ->
            domains_intersection_(VDom, XDom, empty),
            all_empty_intersection(Vs, XDom)
        ;   all_empty_intersection(Vs, XDom)
        ).

outof_reducer(Left, Right, Var) :-
        (   fd_get(Var, Dom, _) ->
            append(Left, Right, Others),
            domain_num_elements(Dom, N),
            num_subsets(Others, Dom, 0, Num, NonSubs),
            (   n(Num) cis_geq N -> false
            ;   n(Num) cis N - n(1) ->
                reduce_from_others(NonSubs, Dom)
            ;   true
            )
        ;   %\+ list_contains(Right, Var),
            %\+ list_contains(Left, Var)
            true
        ).

reduce_from_others([], _).
reduce_from_others([X|Xs], Dom) :-
        (   fd_get(X, XDom, XPs) ->
            domain_subtract(XDom, Dom, NXDom),
            fd_put(X, NXDom, XPs)
        ;   true
        ),
        reduce_from_others(Xs, Dom).

num_subsets([], _Dom, Num, Num, []).
num_subsets([S|Ss], Dom, Num0, Num, NonSubs) :-
        (   fd_get(S, SDom, _) ->
            (   domain_subdomain(Dom, SDom) ->
                Num1 is Num0 + 1,
                num_subsets(Ss, Dom, Num1, Num, NonSubs)
            ;   NonSubs = [S|Rest],
                num_subsets(Ss, Dom, Num0, Num, Rest)
            )
        ;   num_subsets(Ss, Dom, Num0, Num, NonSubs)
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% serialized(+Starts, +Durations)
%
%  Describes a set of non-overlapping tasks.
%  Starts = [S_1,...,S_n], is a list of variables or integers,
%  Durations = [D_1,...,D_n] is a list of non-negative integers.
%  Constrains Starts and Durations to denote a set of
%  non-overlapping tasks, i.e.: S_i + D_i =< S_j or S_j + D_j =<
%  S_i for all 1 =< i < j =< n. Example:
%
% ```
% ?- length(Vs, 3),
%    Vs ins 0..3,
%    serialized(Vs, [1,2,3]),
%    label(Vs).
%    Vs = [0,1,3]
% ;  Vs = [2,0,3]
% ;  false.
% ```
%
%  @see Dorndorf et al. 2000, "Constraint Propagation Techniques for the
%       Disjunctive Scheduling Problem"

serialized(Starts, Durations) :-
        must_be(list(integer), Durations),
        pairs_keys_values(SDs, Starts, Durations),
        Orig = original_goal(_, serialized(Starts, Durations)),
        serialize(SDs, Orig).

serialize([], _).
serialize([S-D|SDs], Orig) :-
        D >= 0,
        serialize(SDs, S, D, Orig),
        serialize(SDs, Orig).

serialize([], _, _, _).
serialize([S-D|Rest], S0, D0, Orig) :-
        D >= 0,
        propagator_init_trigger([S0,S], pserialized(S,D,S0,D0,Orig)),
        serialize(Rest, S0, D0, Orig).

% consistency check / propagation
% Currently implements 2-b-consistency

earliest_start_time(Start, EST) :-
        (   fd_get(Start, D, _) ->
            domain_infimum(D, EST)
        ;   EST = n(Start)
        ).

latest_start_time(Start, LST) :-
        (   fd_get(Start, D, _) ->
            domain_supremum(D, LST)
        ;   LST = n(Start)
        ).

serialize_lower_upper(S_I, D_I, S_J, D_J, MState) -->
        (   { var(S_I) } ->
            serialize_lower_bound(S_I, D_I, S_J, D_J, MState),
            (   { var(S_I) } ->
                serialize_upper_bound(S_I, D_I, S_J, D_J, MState)
            ;   []
            )
        ;   []
        ).

serialize_lower_bound(I, D_I, J, D_J, MState) -->
        { fd_get(I, DomI, Ps) },
        (   { domain_infimum(DomI, n(EST_I)),
              latest_start_time(J, n(LST_J)),
              EST_I + D_I > LST_J,
              earliest_start_time(J, n(EST_J)) } ->
            (   nonvar(J) -> kill(MState)
            ;   []
            ),
            { EST is EST_J+D_J,
              domain_remove_smaller_than(DomI, EST, DomI1) },
            fd_put(I, DomI1, Ps)
        ;   []
        ).

serialize_upper_bound(I, D_I, J, D_J, MState) -->
        { fd_get(I, DomI, Ps) },
        (   { domain_supremum(DomI, n(LST_I)),
              earliest_start_time(J, n(EST_J)),
              EST_J + D_J > LST_I,
              latest_start_time(J, n(LST_J)) } ->
            (   nonvar(J) -> kill(MState)
            ;   []
            ),
            { LST is LST_J-D_I,
              domain_remove_greater_than(DomI, LST, DomI1) },
            fd_put(I, DomI1, Ps)
        ;   []
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% element(?N, +Vs, ?V)
%
%  The N-th element of the list of finite domain variables Vs is V.
%  Analogous to nth1/3.

element(N, Is, V) :-
        must_be(list, Is),
        length(Is, L),
        N in 1..L,
        element_(Is, 1, N, V),
        propagator_init_trigger([N|Is], pelement(N,Is,V)).

element_domain(V, VD) :-
        (   fd_get(V, VD, _) -> true
        ;   VD = from_to(n(V), n(V))
        ).

element_([], _, _, _).
element_([I|Is], N0, N, V) :-
        #I #\= #V #==> #N #\= N0,
        N1 is N0 + 1,
        element_(Is, N1, N, V).

integers_remaining([], _, _, D, D).
integers_remaining([V|Vs], N0, Dom, D0, D) :-
        (   domain_contains(Dom, N0) ->
            element_domain(V, VD),
            domains_union(D0, VD, D1)
        ;   D1 = D0
        ),
        N1 is N0 + 1,
        integers_remaining(Vs, N1, Dom, D1, D).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% global_cardinality(+Vs, +Pairs)
%
%  Global      Cardinality      constraint.        Equivalent      to
%  `global_cardinality(Vs, Pairs, [])`. Example:
%
% ```
% ?- Vs = [_,_,_], global_cardinality(Vs, [1-2,3-_]), label(Vs).
%    Vs = [1,1,3]
% ;  Vs = [1,3,1]
% ;  Vs = [3,1,1]
% ;  false.
% ```

global_cardinality(Xs, Pairs) :- global_cardinality(Xs, Pairs, []).

%% global_cardinality(+Vs, +Pairs, +Options)
%
%  Global Cardinality constraint. Vs  is  a   list  of  finite domain
%  variables, Pairs is a list  of  Key-Num   pairs,  where  Key is an
%  integer and Num is a finite  domain variable. The constraint holds
%  iff each V in Vs is equal to   some key, and for each Key-Num pair
%  in Pairs, the number of occurrences of   Key in Vs is Num. Options
%  is a list of options. Supported options are:
%
%  `consistency(value)`
%  A weaker form of consistency is used.
%
%  `cost(Cost, Matrix)`
%  Matrix is a list of rows, one for each variable, in the order
%  they occur in Vs. Each of these rows is a list of integers, one
%  for each key, in the order these keys occur in Pairs. When
%  variable v\_i is assigned the value of key k\_j, then the
%  associated cost is Matrix\_{ij}. Cost is the sum of all costs.

global_cardinality(Xs, Pairs, Options) :-
        must_be(list(list), [Xs,Pairs,Options]),
        maplist(fd_variable, Xs),
        maplist(gcc_pair, Pairs),
        pairs_keys_values(Pairs, Keys, Nums),
        (   sort(Keys, Keys1), same_length(Keys, Keys1) -> true
        ;   domain_error(gcc_unique_key_pairs, Pairs)
        ),
        length(Xs, L),
        Nums ins 0..L,
        list_to_drep(Keys, Drep),
        Xs ins Drep,
        gcc_pairs(Pairs, Xs, Pairs1),
        % pgcc_check must be installed before triggering other
        % propagators
        propagator_init_trigger(Xs, pgcc_check(Pairs1)),
        propagator_init_trigger(Nums, pgcc_check_single(Pairs1)),
        (   member(OD, Options), OD == consistency(value) -> true
        ;   propagator_init_trigger(Nums, pgcc_single(Xs, Pairs1)),
            propagator_init_trigger(Xs, pgcc(Xs, Pairs, Pairs1))
        ),
        (   member(OC, Options), functor(OC, cost, 2) ->
            OC = cost(Cost, Matrix),
            must_be(list(list(integer)), Matrix),
            maplist(keys_costs(Keys), Xs, Matrix, Costs),
            sum(Costs, #=, Cost)
        ;   true
        ).

keys_costs(Keys, X, Row, C) :-
        element(N, Keys, X),
        element(N, Row, C).

gcc_pair(Pair) :-
        (   Pair = Key-Val ->
            must_be(integer, Key),
            fd_variable(Val)
        ;   domain_error(gcc_pair, Pair)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   For each Key-Num0 pair, we introduce an auxiliary variable Num and
   attach the following attributes to it:

   clpz_gcc_num: equal Num0, the user-visible counter variable
   clpz_gcc_vs: the remaining variables in the constraint that can be
   equal Key.
   clpz_gcc_occurred: stores how often Key already occurred in vs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

gcc_pairs([], _, []).
gcc_pairs([Key-Num0|KNs], Vs, [Key-Num|Rest]) :-
        put_attr(Num, clpz_gcc_num, Num0),
        put_attr(Num, clpz_gcc_vs, Vs),
        put_attr(Num, clpz_gcc_occurred, 0),
        gcc_pairs(KNs, Vs, Rest).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    J.-C. Régin: "Generalized Arc Consistency for Global Cardinality
    Constraint", AAAI-96 Portland, OR, USA, pp 209--215, 1996
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

gcc_global(Vs, KNs) -->
        % at this point, all elements of clpz_gcc_vs must be
        % variables, which a previously scheduled and called
        % gcc_check//1 ensures. Note that gcc_check//1 disables the
        % queue and accumulates constraints in the queue. Do we need
        % to insert a call of do_queue//0 here to reach a fixpoint?  I
        % think not, because verify_attributes/3 gives each variable
        % that is involved in a unification an opportunity to schedule
        % its propagators, even if the unifications happen
        % simultaneously (such as [A,B] = [0,1], which can happen in
        % the propagator of tuples_in/2). Hence: We need this only if
        % an example shows it, ideally found by a systematic search
        % that can be used to test the implementation.
        { with_local_attributes(Vs,
              (gcc_arcs(KNs, S, Vals),
               variables_with_num_occurrences(Vs, VNs),
               maplist(target_to_v(T), VNs),
               (   get_attr(S, edges, Es) ->
                   put_attr(S, parent, none), % Mark S as seen to avoid going back to S.
                   feasible_flow(Es, S, T), % First construct a feasible flow (if any)
                   maximum_flow(S, T),      % only then, maximize it.
                   gcc_consistent(T),
                   scc(Vals, gcc_successors),
                   phrase(gcc_goals(Vals), Gs)
               ;   Gs = [] )), Gs) },
        disable_queue,
        neq_nums(Gs),
        enable_queue.

gcc_consistent(T) :-
        get_attr(T, edges, Es),
        maplist(saturated_arc, Es).

saturated_arc(arc_from(_,U,_,Flow)) :- get_attr(Flow, flow, U).

gcc_goals([]) --> [].
gcc_goals([Val|Vals]) -->
        { get_attr(Val, edges, Es) },
        gcc_edges_goals(Es, Val),
        gcc_goals(Vals).

gcc_edges_goals([], _) --> [].
gcc_edges_goals([E|Es], Val) -->
        gcc_edge_goal(E, Val),
        gcc_edges_goals(Es, Val).

gcc_edge_goal(arc_from(_,_,_,_), _) --> [].
gcc_edge_goal(arc_to(_,_,V,F), Val) -->
        (   { get_attr(F, flow, 0),
              get_attr(V, lowlink, L1),
              get_attr(Val, lowlink, L2),
              L1 =\= L2,
              get_attr(Val, value, Value) } ->
            [neq_num(V, Value)]
        ;   []
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Like in all_distinct/1, first use breadth-first search, then
   construct an augmenting path in reverse.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

maximum_flow(S, T) :-
        (   gcc_augmenting_path([[S]], Levels, T) ->
            phrase(augmenting_path(S, T), Path),
            Path = [augment(_,First,_)|Rest],
            path_minimum(Rest, First, Min),
            maplist(gcc_augment(Min), Path),
            maplist(maplist(clear_parent), Levels),
            maximum_flow(S, T)
        ;   true
        ).

feasible_flow([], _, _).
feasible_flow([A|As], S, T) :-
        make_arc_feasible(A, S, T),
        feasible_flow(As, S, T).

make_arc_feasible(A, S, T) :-
        A = arc_to(L,_,V,F),
        get_attr(F, flow, Flow),
        (   Flow >= L -> true
        ;   Diff is L - Flow,
            put_attr(V, parent, S-augment(F,Diff,+)),
            gcc_augmenting_path([[V]], Levels, T),
            phrase(augmenting_path(S, T), Path),
            path_minimum(Path, Diff, Min),
            maplist(gcc_augment(Min), Path),
            maplist(maplist(clear_parent), Levels),
            make_arc_feasible(A, S, T)
        ).

gcc_augmenting_path(Levels0, Levels, T) :-
        Levels0 = [Vs|_],
        Levels1 = [Tos|Levels0],
        phrase(gcc_reachables(Vs), Tos),
        Tos = [_|_],
        (   member(To, Tos), To == T -> Levels = Levels1
        ;   gcc_augmenting_path(Levels1, Levels, T)
        ).

gcc_reachables([])     --> [].
gcc_reachables([V|Vs]) -->
        { get_attr(V, edges, Es) },
        gcc_reachables_(Es, V),
        gcc_reachables(Vs).

gcc_reachables_([], _)     --> [].
gcc_reachables_([E|Es], V) -->
        gcc_reachable(E, V),
        gcc_reachables_(Es, V).

gcc_reachable(arc_from(_,_,V,F), P) -->
        (   { \+ get_attr(V, parent, _),
              get_attr(F, flow, Flow),
              Flow > 0 } ->
            { put_attr(V, parent, P-augment(F,Flow,-)) },
            [V]
        ;   []
        ).
gcc_reachable(arc_to(_L,U,V,F), P) -->
        (   { \+ get_attr(V, parent, _),
              get_attr(F, flow, Flow),
              Flow < U } ->
            { Diff is U - Flow,
              put_attr(V, parent, P-augment(F,Diff,+)) },
            [V]
        ;   []
        ).


path_minimum([], Min, Min).
path_minimum([augment(_,A,_)|As], Min0, Min) :-
        Min1 is min(Min0,A),
        path_minimum(As, Min1, Min).

gcc_augment(Min, augment(F,_,Sign)) :-
        get_attr(F, flow, Flow0),
        gcc_flow_(Sign, Flow0, Min, Flow),
        put_attr(F, flow, Flow).

gcc_flow_(+, F0, A, F) :- F is F0 + A.
gcc_flow_(-, F0, A, F) :- F is F0 - A.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Build value network for global cardinality constraint.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

gcc_arcs([], _, []).
gcc_arcs([Key-Num0|KNs], S, Vals) :-
        (   get_attr(Num0, clpz_gcc_vs, Vs) ->
            get_attr(Num0, clpz_gcc_num, Num),
            get_attr(Num0, clpz_gcc_occurred, Occ),
            (   nonvar(Num) -> U is Num - Occ, U = L
            ;   fd_get(Num, _, n(L0), n(U0), _),
                L is L0 - Occ, U is U0 - Occ
            ),
            put_attr(Val, value, Key),
            Vals = [Val|Rest],
            put_attr(F, flow, 0),
            append_edge(S, edges, arc_to(L, U, Val, F)),
            put_attr(Val, edges, [arc_from(L, U, S, F)]),
            variables_with_num_occurrences(Vs, VNs),
            maplist(val_to_v(Val), VNs)
        ;   Vals = Rest
        ),
        gcc_arcs(KNs, S, Rest).

variables_with_num_occurrences(Vs0, VNs) :-
        include(var, Vs0, Vs1),
        samsort(Vs1, Vs),
        (   Vs == [] -> VNs = []
        ;   Vs = [V|Rest],
            variables_with_num_occurrences(Rest, V, 1, VNs)
        ).

variables_with_num_occurrences([], Prev, Count, [Prev-Count]).
variables_with_num_occurrences([V|Vs], Prev, Count0, VNs) :-
        (   V == Prev ->
            Count1 is Count0 + 1,
            variables_with_num_occurrences(Vs, Prev, Count1, VNs)
        ;   VNs = [Prev-Count0|Rest],
            variables_with_num_occurrences(Vs, V, 1, Rest)
        ).


target_to_v(T, V-Count) :-
        put_attr(F, flow, 0),
        append_edge(V, edges, arc_to(0, Count, T, F)),
        append_edge(T, edges, arc_from(0, Count, V, F)).

val_to_v(Val, V-Count) :-
        put_attr(F, flow, 0),
        append_edge(V, edges, arc_from(0, Count, Val, F)),
        append_edge(Val, edges, arc_to(0, Count, V, F)).


gcc_successors(V, Tos) :-
        get_attr(V, edges, Tos0),
        phrase(gcc_successors_(Tos0), Tos).

gcc_successors_([])     --> [].
gcc_successors_([E|Es]) --> gcc_succ_edge(E), gcc_successors_(Es).

gcc_succ_edge(arc_to(_,U,V,F)) -->
        (   { get_attr(F, flow, Flow),
              Flow < U } -> [V]
        ;   []
        ).
gcc_succ_edge(arc_from(_,_,V,F)) -->
        (   { get_attr(F, flow, Flow),
              Flow > 0 } -> [V]
        ;   []
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Simple consistency check, run before global propagation.
   Importantly, it removes all ground values from clpz_gcc_vs.

   The pgcc_check/1 propagator in itself suffices to ensure
   consistency.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

gcc_check(Pairs) -->
        disable_queue,
        gcc_check_(Pairs),
        enable_queue.

gcc_done(Num) :-
        del_attr(Num, clpz_gcc_vs),
        del_attr(Num, clpz_gcc_num),
        del_attr(Num, clpz_gcc_occurred).

gcc_check_([]) --> [].
gcc_check_([Key-Num0|KNs]) -->
        (   { get_attr(Num0, clpz_gcc_vs, Vs) } ->
            { get_attr(Num0, clpz_gcc_num, Num),
              get_attr(Num0, clpz_gcc_occurred, Occ0),
              vs_key_min_others(Vs, Key, 0, Min, Os),
              put_attr(Num0, clpz_gcc_vs, Os),
              put_attr(Num0, clpz_gcc_occurred, Occ1),
              Occ1 is Occ0 + Min },
            geq(Num, Occ1),
            % The queue is disabled for efficiency here in any case.
            % If it were enabled, make sure to retain the invariant
            % that gcc_global is never triggered during an
            % inconsistent state (after gcc_done/1 but before all
            % relevant constraints are posted).
            (   Occ1 == Num -> all_neq(Os, Key), { gcc_done(Num0) }
            ;   Os == [] -> { gcc_done(Num0) }, Num = Occ1
            ;   { length(Os, L),
                  Max is Occ1 + L },
                geq(Max, Num),
                (   { nonvar(Num) } -> Diff is Num - Occ1
                ;   { fd_get(Num, ND, _),
                      domain_infimum(ND, n(NInf)) },
                    Diff is NInf - Occ1
                ),
                L >= Diff,
                (   L =:= Diff ->
                    Num is Occ1 + Diff,
                    { maplist(=(Key), Os),
                      gcc_done(Num0) }
                ;   true
                )
            )
        ;   true
        ),
        gcc_check_(KNs).

vs_key_min_others([], _, Min, Min, []).
vs_key_min_others([V|Vs], Key, Min0, Min, Others) :-
        (   fd_get(V, VD, _) ->
            (   domain_contains(VD, Key) ->
                Others = [V|Rest],
                vs_key_min_others(Vs, Key, Min0, Min, Rest)
            ;   vs_key_min_others(Vs, Key, Min0, Min, Others)
            )
        ;   (   V =:= Key ->
                Min1 is Min0 + 1,
                vs_key_min_others(Vs, Key, Min1, Min, Others)
            ;   vs_key_min_others(Vs, Key, Min0, Min, Others)
            )
        ).

all_neq([], _) --> [].
all_neq([X|Xs], C) -->
        neq_num(X, C),
        all_neq(Xs, C).

all_neq([], _).
all_neq([X|Xs], C) :-
        neq_num(X, C),
        all_neq(Xs, C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% circuit(+Vs)
%
% True iff the list Vs of finite domain variables induces a
% Hamiltonian circuit. The k-th element of Vs denotes the
% successor of node k. Node indexing starts with 1. Examples:
%
% ```
% ?- length(Vs, _), circuit(Vs), label(Vs).
%    Vs = []
% ;  Vs = [1]
% ;  Vs = [2,1]
% ;  Vs = [2,3,1]
% ;  Vs = [3,1,2]
% ;  Vs = [2,3,4,1]
% ;  ... .
% ```

circuit(Vs) :-
        must_be(list, Vs),
        maplist(fd_variable, Vs),
        length(Vs, L),
        Vs ins 1..L,
        (   L =:= 1 -> true
        ;   neq_index(Vs, 1),
            make_propagator(pcircuit(Vs), Prop),
            new_queue(Q0),
            phrase((distinct_attach(Vs, Prop, []),trigger_prop(Prop),do_queue), [Q0], _)
        ).

neq_index([], _).
neq_index([X|Xs], N) :-
        neq_num(X, N),
        N1 is N + 1,
        neq_index(Xs, N1).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Necessary condition for existence of a Hamiltonian circuit: The
   graph has a single strongly connected component. If the list is
   ground, the condition is also sufficient.

   Ts are used as temporary variables to attach attributes:

   lowlink, index: used for SCC
   [arc_to(V)]: possible successors
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

propagate_circuit(Vs) :-
        with_local_attributes([],
            (same_length(Vs, Ts),
             circuit_graph(Vs, Ts, Ts),
             scc(Ts, circuit_successors),
             maplist(single_component, Ts)), _).

single_component(V) :- get_attr(V, lowlink, 0).

circuit_graph([], _, _).
circuit_graph([V|Vs], Ts0, [T|Ts]) :-
        (   nonvar(V) -> Ns = [V]
        ;   fd_get(V, Dom, _),
            domain_to_list(Dom, Ns)
        ),
        phrase(circuit_edges(Ns, Ts0), Es),
        put_attr(T, edges, Es),
        circuit_graph(Vs, Ts0, Ts).

circuit_edges([], _) --> [].
circuit_edges([N|Ns], Ts) -->
        { nth1(N, Ts, T) },
        [arc_to(T)],
        circuit_edges(Ns, Ts).

circuit_successors(V, Tos) :-
        get_attr(V, edges, Tos0),
        maplist(arg(1), Tos0, Tos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% cumulative(+Tasks)
%
%  Equivalent to cumulative(Tasks, [limit(1)]).

cumulative(Tasks) :- cumulative(Tasks, [limit(1)]).

%% cumulative(+Tasks, +Options)
%
%  Schedule with a limited resource. Tasks is a list of tasks, each of
%  the form task(S_i, D_i, E_i, C_i, T_i). S_i denotes the start time,
%  D_i the positive duration, E_i the end time, C_i the non-negative
%  resource consumption, and T_i the task identifier. Each of these
%  arguments must be a finite domain variable with bounded domain, or
%  an integer. The constraint holds iff at each time slot during the
%  start and end of each task, the total resource consumption of all
%  tasks running at that time does not exceed the global resource
%  limit. Options is a list of options. Currently, the only supported
%  option is:
%
%    * limit(L)
%      The integer L is the global resource limit. Default is 1.
%
%  For example, given the following predicate that relates three tasks
%  of durations 2 and 3 to a list containing their starting times:
%
% ```
%  tasks_starts(Tasks, [S1,S2,S3]) :-
%          Tasks = [task(S1,3,_,1,_),
%                   task(S2,2,_,1,_),
%                   task(S3,2,_,1,_)].
% ```
%
%  We can use cumulative/2 as follows, and obtain a schedule:
%
% ```
%  ?- tasks_starts(Tasks, Starts), Starts ins 0..10,
%     cumulative(Tasks, [limit(2)]), label(Starts).
%  Tasks = [task(0, 3, 3, 1, _G36), task(0, 2, 2, 1, _G45), ...],
%  Starts = [0, 0, 2] .
% ```

cumulative(Tasks, Options) :-
        must_be(list(list), [Tasks,Options]),
        (   Options = [] -> L = 1
        ;   Options = [limit(L)] -> must_be(integer, L)
        ;   domain_error(cumulative_options_empty_or_limit, Options)
        ),
        (   Tasks = [] -> true
        ;   fully_elastic_relaxation(Tasks, L),
            maplist(task_bs, Tasks, Bss),
            maplist(arg(1), Tasks, Starts),
            maplist(fd_inf, Starts, MinStarts),
            maplist(arg(3), Tasks, Ends),
            maplist(fd_sup, Ends, MaxEnds),
            MinStarts = [Min|Mins],
            foldl(min_, Mins, Min, Start),
            MaxEnds = [Max|Maxs],
            foldl(max_, Maxs, Max, End),
            resource_limit(Start, End, Tasks, Bss, L)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Trivial lower and upper bounds, assuming no gaps and not necessarily
   retaining the rectangular shape of each task.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

fully_elastic_relaxation(Tasks, Limit) :-
        maplist(task_duration_consumption, Tasks, Ds, Cs),
        maplist(area, Ds, Cs, As),
        sum(As, #=, #Area),
        #MinTime #= (Area + Limit - 1) // Limit,
        tasks_minstart_maxend(Tasks, MinStart, MaxEnd),
        MaxEnd #>= MinStart + MinTime.

task_duration_consumption(task(_,D,_,C,_), D, C).

area(X, Y, Area) :- #Area #= #X * #Y.

tasks_minstart_maxend(Tasks, Start, End) :-
        maplist(task_start_end, Tasks, [Start0|Starts], [End0|Ends]),
        foldl(min_, Starts, Start0, Start),
        foldl(max_, Ends, End0, End).

max_(E, M0, M) :- #M #= max(E, M0).

min_(E, M0, M) :- #M #= min(E, M0).

task_start_end(task(Start,_,End,_,_), #Start, #End).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   All time slots must respect the resource limit.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

resource_limit(T, T, _, _, _) :- !.
resource_limit(T0, T, Tasks, Bss, L) :-
        maplist(contribution_at(T0), Tasks, Bss, Cs),
        sum(Cs, #=<, L),
        T1 is T0 + 1,
        resource_limit(T1, T, Tasks, Bss, L).

task_bs(Task, InfStart-Bs) :-
        Task = task(Start,D,End,_,_Id),
        #D #> 0,
        #End #= #Start + #D,
        maplist(finite_domain, [End,Start,D]),
        fd_inf(Start, InfStart),
        fd_sup(End, SupEnd),
        L is SupEnd - InfStart,
        length(Bs, L),
        task_running(Bs, Start, End, InfStart).

task_running([], _, _, _).
task_running([B|Bs], Start, End, T) :-
        ((T #>= Start) #/\ (T #< End)) #<==> #B,
        T1 is T + 1,
        task_running(Bs, Start, End, T1).

contribution_at(T, Task, Offset-Bs, Contribution) :-
        Task = task(Start,_,End,C,_),
        #C #>= 0,
        fd_inf(Start, InfStart),
        fd_sup(End, SupEnd),
        (   T < InfStart -> Contribution = 0
        ;   T >= SupEnd -> Contribution = 0
        ;   Index is T - Offset,
            nth0(Index, Bs, B),
            #Contribution #= B*C
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% disjoint2(+Rectangles)
%
%  True iff Rectangles are not overlapping. Rectangles is a list of
%  terms of the form F(X_i, W_i, Y_i, H_i), where F is any functor,
%  and the arguments are finite domain variables or integers that
%  denote, respectively, the X coordinate, width, Y coordinate and
%  height of each rectangle.

disjoint2(Rs0) :-
        must_be(list, Rs0),
        maplist(=.., Rs0, Rs),
        non_overlapping(Rs).

non_overlapping([]).
non_overlapping([R|Rs]) :-
        maplist(non_overlapping_(R), Rs),
        non_overlapping(Rs).

non_overlapping_(A, B) :-
        a_not_in_b(A, B),
        a_not_in_b(B, A).

a_not_in_b([_,AX,AW,AY,AH], [_,BX,BW,BY,BH]) :-
        #AX #=< #BX #/\ #BX #< #AX + #AW #==>
                   #AY + #AH #=< #BY #\/ #BY + #BH #=< #AY,
        #AY #=< #BY #/\ #BY #< #AY + #AH #==>
                   #AX + #AW #=< #BX #\/ #BX + #BW #=< #AX.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% automaton(+Vs, +Nodes, +Arcs)
%
%  Describes a list of finite domain variables with a finite
%  automaton. Equivalent to automaton(Vs, _, Vs, Nodes, Arcs,
%  [], [], _), a common use case of automaton/8. In the following
%  example, a list of binary finite domain variables is constrained to
%  contain at least two consecutive ones:
%
% ```
% two_consecutive_ones(Vs) :-
%         automaton(Vs, [source(a),sink(c)],
%                       [arc(a,0,a), arc(a,1,b),
%                        arc(b,0,a), arc(b,1,c),
%                        arc(c,0,c), arc(c,1,c)]).
% ```
%
%  Example query:
%
% ```
% ?- length(Vs, 3), two_consecutive_ones(Vs), label(Vs).
%    Vs = [0,1,1]
% ;  Vs = [1,1,0]
% ;  Vs = [1,1,1]
% ;  false.
% ```

automaton(Sigs, Ns, As) :- automaton(_, _, Sigs, Ns, As, [], [], _).


%% automaton(+Sequence, ?Template, +Signature, +Nodes, +Arcs, +Counters, +Initials, ?Finals)
%
%  Describes a list of finite domain variables with a finite
%  automaton. True iff the finite automaton induced by Nodes and Arcs
%  (extended with Counters) accepts Signature. Sequence is a list of
%  terms, all of the same shape. Additional constraints must link
%  Sequence to Signature, if necessary. Nodes is a list of
%  source(Node) and sink(Node) terms. Arcs is a list of
%  arc(Node,Integer,Node) and arc(Node,Integer,Node,Exprs) terms that
%  denote the automaton's transitions. Each node is represented by an
%  arbitrary term. Transitions that are not mentioned go to an
%  implicit failure node. `Exprs` is a list of arithmetic expressions,
%  of the same length as Counters. In each expression, variables
%  occurring in Counters symbolically refer to previous counter
%  values, and variables occurring in Template refer to the current
%  element of Sequence. When a transition containing arithmetic
%  expressions is taken, each counter is updated according to the
%  result of the corresponding expression. When a transition without
%  arithmetic expressions is taken, all counters remain unchanged.
%  Counters is a list of variables. Initials is a list of finite
%  domain variables or integers denoting, in the same order, the
%  initial value of each counter. These values are related to Finals
%  according to the arithmetic expressions of the taken transitions.
%
%  The following example is taken from Beldiceanu, Carlsson, Debruyne
%  and Petit: "Reformulation of Global Constraints Based on
%  Constraints Checkers", Constraints 10(4), pp 339-362 (2005). It
%  relates a sequence of integers and finite domain variables to its
%  number of inflexions, which are switches between strictly ascending
%  and strictly descending subsequences:
%
% ```
%  sequence_inflexions(Vs, N) :-
%          variables_signature(Vs, Sigs),
%          automaton(Sigs, _, Sigs,
%                    [source(s),sink(i),sink(j),sink(s)],
%                    [arc(s,0,s), arc(s,1,j), arc(s,2,i),
%                     arc(i,0,i), arc(i,1,j,[C+1]), arc(i,2,i),
%                     arc(j,0,j), arc(j,1,j),
%                     arc(j,2,i,[C+1])],
%                    [C], [0], [N]).
%
%  variables_signature([], []).
%  variables_signature([V|Vs], Sigs) :-
%          variables_signature_(Vs, V, Sigs).
%
%  variables_signature_([], _, []).
%  variables_signature_([V|Vs], Prev, [S|Sigs]) :-
%          V #= Prev #<==> S #= 0,
%          Prev #< V #<==> S #= 1,
%          Prev #> V #<==> S #= 2,
%          variables_signature_(Vs, V, Sigs).
% ```
%
%  Example queries:
%
% ```
%  ?- sequence_inflexions([1,2,3,3,2,1,3,0], N).
%  N = 3.
%
%  ?- length(Ls, 5), Ls ins 0..1,
%     sequence_inflexions(Ls, 3), label(Ls).
%  Ls = [0, 1, 0, 1, 0] ;
%  Ls = [1, 0, 1, 0, 1].
% ```

template_var_path(V, Var, []) :- var(V), !, V == Var.
template_var_path(T, Var, [N|Ns]) :-
        arg(N, T, Arg),
        template_var_path(Arg, Var, Ns).

path_term_variable([], V, V).
path_term_variable([P|Ps], T, V) :-
        arg(P, T, Arg),
        path_term_variable(Ps, Arg, V).

initial_expr(_, []-1).

automaton(Seqs, Template, Sigs, Ns, As0, Cs, Is, Fs) :-
        must_be(list(list), [Sigs,Ns,As0,Cs,Is]),
        (   var(Seqs) ->
            (   monotonic ->
                instantiation_error(Seqs)
            ;   Seqs = Sigs
            )
        ;   must_be(list, Seqs)
        ),
        maplist(monotonic, Cs, CsM),
        maplist(arc_normalized(CsM), As0, As),
        include_args1(sink, Ns, Sinks),
        include_args1(source, Ns, Sources),
        maplist(initial_expr, Cs, Exprs0),
        phrase((arcs_relation(As, Relation),
                nodes_nums(Sinks, SinkNums0),
                nodes_nums(Sources, SourceNums0)),
               [s([]-0, Exprs0)], [s(_,Exprs1)]),
        maplist(expr0_expr, Exprs1, Exprs),
        phrase(transitions(Seqs, Template, Sigs, Start, End, Exprs, Cs, Is, Fs), Tuples),
        list_to_drep(SourceNums0, SourceDrep),
        Start in SourceDrep,
        list_to_drep(SinkNums0, SinkDrep),
        End in SinkDrep,
        tuples_in(Tuples, Relation).

expr0_expr(Es0-_, Es) :-
        pairs_keys(Es0, Es1),
        reverse(Es1, Es).

transitions([], _, [], S, S, _, _, Cs, Cs) --> [].
transitions([Seq|Seqs], Template, [Sig|Sigs], S0, S, Exprs, Counters, Cs0, Cs) -->
        [[S0,Sig,S1|Is]],
        { phrase(exprs_next(Exprs, Is, Cs1), [s(Seq,Template,Counters,Cs0)], _) },
        transitions(Seqs, Template, Sigs, S1, S, Exprs, Counters, Cs1, Cs).

exprs_next([], [], []) --> [].
exprs_next([Es|Ess], [I|Is], [C|Cs]) -->
        exprs_values(Es, Vs),
        { element(I, Vs, C) },
        exprs_next(Ess, Is, Cs).

exprs_values([], []) --> [].
exprs_values([E0|Es], [V|Vs]) -->
        { term_variables(E0, EVs0),
          copy_term(E0, E),
          term_variables(E, EVs),
          #V #= E },
        match_variables(EVs0, EVs),
        exprs_values(Es, Vs).

match_variables([], _) --> [].
match_variables([V0|Vs0], [V|Vs]) -->
        state(s(Seq,Template,Counters,Cs0)),
        { (   template_var_path(Template, V0, Ps) ->
              path_term_variable(Ps, Seq, V)
          ;   template_var_path(Counters, V0, Ps) ->
              path_term_variable(Ps, Cs0, V)
          ;   domain_error(variable_from_template_or_counters, V0)
          ) },
        match_variables(Vs0, Vs).

nodes_nums([], []) --> [].
nodes_nums([Node|Nodes], [Num|Nums]) -->
        node_num(Node, Num),
        nodes_nums(Nodes, Nums).

arcs_relation([], []) --> [].
arcs_relation([arc(S0,L,S1,Es)|As], [[From,L,To|Ns]|Rs]) -->
        node_num(S0, From),
        node_num(S1, To),
        state(s(Nodes, Exprs0), s(Nodes, Exprs)),
        { exprs_nums(Es, Ns, Exprs0, Exprs) },
        arcs_relation(As, Rs).

exprs_nums([], [], [], []).
exprs_nums([E|Es], [N|Ns], [Ex0-C0|Exs0], [Ex-C|Exs]) :-
        (   member(Exp-N, Ex0), Exp == E -> C = C0, Ex = Ex0
        ;   N = C0, C is C0 + 1, Ex = [E-C0|Ex0]
        ),
        exprs_nums(Es, Ns, Exs0, Exs).

node_num(Node, Num) -->
        state(s(Nodes0-C0, Exprs), s(Nodes-C, Exprs)),
        { (   member(N-Num, Nodes0), N == Node -> C = C0, Nodes = Nodes0
          ;   Num = C0, C is C0 + 1, Nodes = [Node-C0|Nodes0]
          )
        }.

include_args1(Goal, Ls0, As) :-
        include(Goal, Ls0, Ls),
        maplist(arg(1), Ls, As).

source(source(_)).

sink(sink(_)).

monotonic(Var, #Var).

arc_normalized(Cs, Arc0, Arc) :- arc_normalized_(Arc0, Cs, Arc).

arc_normalized_(arc(S0,L,S,Cs), _, arc(S0,L,S,Cs)).
arc_normalized_(arc(S0,L,S), Cs, arc(S0,L,S,Cs)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% zcompare(?Order, ?A, ?B)
%
% Analogous to compare/3, with finite domain variables A and B.
%
% This predicate allows you to make several predicates over integers
% deterministic while preserving their generality and completeness.
% For example:
%
% ```
% n_factorial(N, F) :-
%         zcompare(C, N, 0),
%         n_factorial_(C, N, F).
%
% n_factorial_(=, _, 1).
% n_factorial_(>, N, F) :-
%         F #= F0*N, N1 #= N - 1,
%         n_factorial(N1, F0).
% ```
%
% This version is deterministic if the first argument is instantiated,
% because first argument indexing can distinguish the two different
% clauses:
%
% ```
% ?- n_factorial(30, F).
%    F = 265252859812191058636308480000000.
% ```
%
% The predicate can still be used in all directions, including the
% most general query:
%
% ```
% ?- n_factorial(N, F).
%    N = 0, F = 1
% ;  N = 1, F = 1
% ;  N = 2, F = 2
% ;  ... .
% ```

zcompare(Order, A, B) :-
        (   nonvar(Order) ->
            zcompare_(Order, A, B)
        ;   integer(A), integer(B) ->
            compare(Order, A, B)
        ;   freeze(Order, zcompare_(Order, A, B)),
            fd_variable(A),
            fd_variable(B),
            propagator_init_trigger([A,B], pzcompare(Order, A, B))
        ).

zcompare_(O, A, B) :-
        (   member(O, "<=>") -> true
        ;   domain_error(order, O, zcompare/3)
        ),
        zcompare__(O, A, B).

zcompare__(=, A, B) :- #A #= #B.
zcompare__(<, A, B) :- #A #< #B.
zcompare__(>, A, B) :- #A #> #B.

%% chain(+Relation, +Zs)
%
% Zs form a chain with respect to Relation. Zs is a list of finite
% domain variables that are a chain with respect to the partial order
% Relation, in the order they appear in the list. Relation must be #=,
% #=<, #>=, #< or #>. For example:
%
% ```
% ?- chain(#>=, [X,Y,Z]).
% X#>=Y,
% Y#>=Z.
% ```

chain(Relation, Zs) :-
        must_be(list, Zs),
        maplist(fd_variable, Zs),
        must_be(ground, Relation),
        (   chain_relation(Relation) -> true
        ;   domain_error(chain_relation, Relation)
        ),
        chain_(Zs, Relation).

chain_([], _).
chain_([X|Xs], Relation) :- foldl(chain(Relation), Xs, X, _).

chain_relation(#=).
chain_relation(#<).
chain_relation(#=<).
chain_relation(#>).
chain_relation(#>=).

chain(Relation, X, Prev, X) :- call(Relation, #Prev, #X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Reflection predicates
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% fd_var(+Var)
%
%  True iff Var is a CLP(ℤ) variable.

fd_var(X) :- get_attr(X, clpz, _).

%% fd_inf(+Var, -Inf)
%
%  Inf is the infimum of the current domain of Var.

fd_inf(X, Inf) :-
        (   fd_get(X, XD, _) ->
            domain_infimum(XD, Inf0),
            bound_portray(Inf0, Inf)
        ;   must_be(integer, X),
            Inf = X
        ).

%% fd_sup(+Var, -Sup)
%
%  Sup is the supremum of the current domain of Var.

fd_sup(X, Sup) :-
        (   fd_get(X, XD, _) ->
            domain_supremum(XD, Sup0),
            bound_portray(Sup0, Sup)
        ;   must_be(integer, X),
            Sup = X
        ).

%% fd_size(+Var, -Size)
%
%  Size is the number of elements of the current domain of Var, or the
%  atom *sup* if the domain is unbounded.

fd_size(X, S) :-
        (   fd_get(X, XD, _) ->
            domain_num_elements(XD, S0),
            bound_portray(S0, S)
        ;   must_be(integer, X),
            S = 1
        ).

%% fd_dom(+Var, -Dom)
%
%  Dom is the current domain (see `(in)/2`) of Var. This predicate is
%  useful if you want to reason about domains. It is _not_ needed if
%  you only want to display remaining domains; instead, separate your
%  model from the search part and let the toplevel display this
%  information via residual goals.
%
%  For example, to implement a custom labeling strategy, you may need
%  to inspect the current domain of a finite domain variable. With the
%  following code, you can convert a _finite_ domain to a list of
%  integers:
%
% ```
%  dom_integers(D, Is) :- phrase(dom_integers_(D), Is).
%
%  dom_integers_(I)      --> { integer(I) }, [I].
%  dom_integers_(L..U)   --> { numlist(L, U, Is) }, Is.
%  dom_integers_(D1\/D2) --> dom_integers_(D1), dom_integers_(D2).
% ```
%
%  Example:
%
% ```
%  ?- X in 1..5, X #\= 4, fd_dom(X, D), dom_integers(D, Is).
%  D = 1..3\/5,
%  Is = [1,2,3,5],
%  X in 1..3\/5.
% ```

fd_dom(X, Drep) :-
        (   fd_get(X, XD, _) ->
            domain_to_drep(XD, Drep)
        ;   must_be(integer, X),
            Drep = X..X
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Entailment detection. Subject to change.

   Currently, Goals entail E if posting ({#\ E} U Goals), then
   labeling all variables, fails. E must be reifiable. Examples:

   %?- clpz:goals_entail([X#>2], X #> 3).
   %@ false.

   %?- clpz:goals_entail([X#>1, X#<3], X #= 2).
   %@ true.

   %?- clpz:goals_entail([X#=Y+1], X #= Y+1).
   %@ ERROR: Arguments are not sufficiently instantiated
   %@    Exception: (15) throw(error(instantiation_error, _G2680)) ?

   %?- clpz:goals_entail([[X,Y] ins 0..10, X#=Y+1], X #= Y+1).
   %@ true.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

goals_entail(Goals, E) :-
        must_be(list, Goals),
        \+ (   maplist(call, Goals), #\ E,
               term_variables(Goals-E, Vs),
               label(Vs)
           ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Unification hook and constraint projection
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

verify_attributes(Var, Other, Gs) :-
        % portray_clause(Var = Other),
        (   get_atts(Var, clpz(CLPZ)) ->
            CLPZ = clpz_attr(_,_,_,Dom,Ps,Q),
            (   nonvar(Other) ->
                (   integer(Other) -> true
                ;   type_error(integer, Other)
                ),
                domain_contains(Dom, Other),
                phrase(trigger_props(Ps), [Q], [_]),
                Gs = [phrase(do_queue, [Q], _)]
            ;   (   get_atts(Other, clpz(clpz_attr(_,_,_,OD,OPs,_))) ->
                    domains_intersection(OD, Dom, Dom1),
                    append_propagators(Ps, OPs, Ps1),
                    new_queue(Q0),
                    variables_same_queue([Var,Other]),
                    phrase((fd_put(Other,Dom1,Ps1),
                            trigger_props(Ps1)), [Q0], _),
                    Gs = [phrase(do_queue, [Q0], _)]
                ;   put_atts(Other, clpz(CLPZ)),
                    Gs = []
                )
            )
        ;   Gs = []
        ).

append_propagators(fd_props(Gs0,Bs0,Os0), fd_props(Gs1,Bs1,Os1), fd_props(Gs,Bs,Os)) :-
        maplist(append, [Gs0,Bs0,Os0], [Gs1,Bs1,Os1], [Gs,Bs,Os]).

bound_portray(inf, inf).
bound_portray(sup, sup).
bound_portray(n(N), N).

list_to_drep(List, Drep) :-
        list_to_domain(List, Dom),
        domain_to_drep(Dom, Drep).

domain_to_drep(Dom, Drep) :-
        domain_intervals(Dom, [A0-B0|Rest]),
        bound_portray(A0, A),
        bound_portray(B0, B),
        (   A == B -> Drep0 = A
        ;   Drep0 = A..B
        ),
        intervals_to_drep(Rest, Drep0, Drep).

intervals_to_drep([], Drep, Drep).
intervals_to_drep([A0-B0|Rest], Drep0, Drep) :-
        bound_portray(A0, A),
        bound_portray(B0, B),
        (   A == B -> D1 = A
        ;   D1 = A..B
        ),
        intervals_to_drep(Rest, Drep0 \/ D1, Drep).

attribute_goals(X) -->
        % { get_attr(X, clpz, Attr), format("A: ~w\n", [Attr]) },
        { get_attr(X, clpz, clpz_attr(_,_,_,Dom,fd_props(Gs,Bs,Os),_)),
          append(Gs, Bs, Ps0),
          append(Ps0, Os, Ps),
          domain_to_drep(Dom, Drep) },
        (   { default_domain(Dom), \+ all_dead_(Ps) } -> []
        ;   [clpz:(X in Drep)]
        ),
        attributes_goals(Ps),
        { del_attr(X, clpz) }.

attributes_goals([]) --> [].
attributes_goals([propagator(P, State)|As]) -->
        (   { ground(State) } -> []
        ;   { phrase(attribute_goal_(P), Gs) } ->
            { del_attr(State, clpz_aux), State = processed,
              (   monotonic ->
                  maplist(unwrap_with(bare_integer), Gs, Gs1)
              ;   maplist(unwrap_with(=), Gs, Gs1)
              ),
              maplist(with_clpz, Gs1, Gs2) },
            seq(Gs2)
        ;   [P] % possibly user-defined constraint
        ),
        attributes_goals(As).

with_clpz(G, clpz:G).

unwrap_with(_, V, V)           :- var(V), !.
unwrap_with(Goal, #V0, V)    :- !, call(Goal, V0, V).
unwrap_with(Goal, Term0, Term) :-
        Term0 =.. [F|Args0],
        maplist(unwrap_with(Goal), Args0, Args),
        Term =.. [F|Args].

bare_integer(V0, V)    :- ( integer(V0) -> V = V0 ; V = #V0 ).

attribute_goal_(presidual(Goal))       --> [Goal].
attribute_goal_(pgeq(A,B))             --> [#A #>= #B].
attribute_goal_(pplus(X,Y,Z,_))        --> [#X + #Y #= #Z].
attribute_goal_(pneq(A,B))             --> [#A #\= #B].
attribute_goal_(ptimes(X,Y,Z,_))       --> [#X * #Y #= #Z].
attribute_goal_(absdiff_neq(X,Y,C))    --> [abs(#X - #Y) #\= C].
attribute_goal_(x_eq_abs_plus_v(X,V))  --> [#X #= abs(#X) + #V].
attribute_goal_(x_neq_y_plus_z(X,Y,Z)) --> [#X #\= #Y + #Z].
attribute_goal_(x_leq_y_plus_c(X,Y,C)) --> [#X #=< #Y + C].
attribute_goal_(ptzdiv(X,Y,Z,_))       --> [#X // #Y #= #Z].
attribute_goal_(pexp(X,Y,Z,_))         --> [#X ^ #Y #= #Z].
attribute_goal_(psign(X,Y))            --> [#Y #= sign(#X)].
attribute_goal_(pabs(X,Y))             --> [#Y #= abs(#X)].
attribute_goal_(pmod(X,M,K))           --> [#X mod #M #= #K].
attribute_goal_(prem(X,Y,Z))           --> [#X rem #Y #= #Z].
attribute_goal_(pmax(X,Y,Z))           --> [#Z #= max(#X,#Y)].
attribute_goal_(pmin(X,Y,Z))           --> [#Z #= min(#X,#Y)].
attribute_goal_(pxor(X,Y,Z))           --> [#Z #= xor(#X, #Y)].
attribute_goal_(ppopcount(X,Y))        --> [#Y #= popcount(#X)].
attribute_goal_(scalar_product_neq(Cs,Vs,C)) -->
        [Left #\= Right],
        { scalar_product_left_right([-1|Cs], [C|Vs], Left, Right) }.
attribute_goal_(scalar_product_eq(Cs,Vs,C)) -->
        [Left #= Right],
        { scalar_product_left_right([-1|Cs], [C|Vs], Left, Right) }.
attribute_goal_(scalar_product_leq(Cs,Vs,C)) -->
        [Left #=< Right],
        { scalar_product_left_right([-1|Cs], [C|Vs], Left, Right) }.
attribute_goal_(pdifferent(_,_,_,O))    --> original_goal(O).
attribute_goal_(weak_distinct(_,_,_,O)) --> original_goal(O).
attribute_goal_(pdistinct(Vs))          --> [all_distinct(Vs)].
attribute_goal_(pnvalue(N, Vs))         --> [nvalue(N, Vs)].
attribute_goal_(pexclude(_,_,_))  --> [].
attribute_goal_(pelement(N,Is,V)) --> [element(N, Is, V)].
attribute_goal_(pgcc(Vs, Pairs, _))   --> [global_cardinality(Vs, Pairs)].
attribute_goal_(pgcc_single(_,_))     --> [].
attribute_goal_(pgcc_check_single(_)) --> [].
attribute_goal_(pgcc_check(Pairs))    -->
        { pairs_values(Pairs, Nums),
          maplist(gcc_done, Nums) }.
attribute_goal_(pcircuit(Vs))       --> [circuit(Vs)].
attribute_goal_(pserialized(_,_,_,_,O)) --> original_goal(O).
attribute_goal_(rel_tuple(R, Tuple)) -->
        { get_attr(R, clpz_relation, Rel) },
        [tuples_in([Tuple], Rel)].
attribute_goal_(pzcompare(O,A,B)) --> [zcompare(O,A,B)].
% reified constraints
attribute_goal_(reified_in(V, D, B)) -->
        [V in Drep #<==> #B],
        { domain_to_drep(D, Drep) }.
attribute_goal_(reified_tuple_in(Tuple, R, B)) -->
        { get_attr(R, clpz_relation, Rel) },
        [tuples_in([Tuple], Rel) #<==> #B].
attribute_goal_(kill_reified_tuples(_,_,_)) --> [].
attribute_goal_(tuples_not_in(_,_,_)) --> [].
attribute_goal_(reified_fd(V,B)) --> [finite_domain(V) #<==> #B].
attribute_goal_(pskeleton(X,Y,D,_,Z,F)) -->
        { Prop =.. [F,X,Y,Z],
          phrase(attribute_goal_(Prop), Goals), list_goal(Goals, Goal) },
        [#D #= 1 #==> Goal, #Y #\= 0 #==> #D #= 1].
attribute_goal_(reified_neq(DX,X,DY,Y,_,B)) -->
        conjunction(DX, DY, #X #\= #Y, B).
attribute_goal_(reified_eq(DX,X,DY,Y,_,B))  -->
        conjunction(DX, DY, #X #= #Y, B).
attribute_goal_(reified_geq(DX,X,DY,Y,_,B)) -->
        conjunction(DX, DY, #X #>= #Y, B).
attribute_goal_(reified_and(X,_,Y,_,B))    --> [#X #/\ #Y #<==> #B].
attribute_goal_(reified_or(X, _, Y, _, B)) --> [#X #\/ #Y #<==> #B].
attribute_goal_(reified_not(X, Y))         --> [#\ #X #<==> #Y].
attribute_goal_(preified_slash(X, Y, _, R)) --> [#X/ #Y #= R].
attribute_goal_(preified_exp(X, Y, _, R))  --> [#X^ #Y #= R].
attribute_goal_(pimpl(X, Y, _))            --> [#X #==> #Y].
attribute_goal_(pfunction(Op, A, B, R)) -->
        { Expr =.. [Op,#A,#B] },
        [#R #= Expr].
attribute_goal_(pfunction(Op, A, R)) -->
        { Expr =.. [Op,#A] },
        [#R #= Expr].

conjunction(A, B, G, D) -->
        (   { A == 1, B == 1 } -> [G #<==> #D]
        ;   { A == 1 } -> [(#B #/\ G) #<==> #D]
        ;   { B == 1 } -> [(#A #/\ G) #<==> #D]
        ;   [(#A #/\ #B #/\ G) #<==> #D]
        ).

original_goal(original_goal(State, Goal)) -->
        (   { var(State) } ->
            { State = processed },
            [Goal]
        ;   []
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Projection of scalar product.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

scalar_product_left_right(Cs, Vs, Left, Right) :-
        pairs_keys_values(Pairs0, Cs, Vs),
        partition(ground, Pairs0, Grounds, Pairs),
        maplist(pair_product, Grounds, Prods),
        sum_list(Prods, Const),
        NConst is -Const,
        partition(compare_coeff0, Pairs, Negatives, _, Positives),
        maplist(negate_coeff, Negatives, Rights),
        scalar_plusterm(Rights, Right0),
        scalar_plusterm(Positives, Left0),
        (   Const =:= 0 -> Left = Left0, Right = Right0
        ;   Right0 == 0 -> Left = Left0, Right = NConst
        ;   Left0 == 0 ->  Left = Const, Right = Right0
        ;   (   Const < 0 ->
                Left = Left0,       Right = Right0+NConst
            ;   Left = Left0+Const, Right = Right0
            )
        ).

negate_coeff(A0-B, A-B) :- A is -A0.

pair_product(A-B, Prod) :- Prod is A*B.

compare_coeff0(Coeff-_, Compare) :- compare(Compare, Coeff, 0).

scalar_plusterm([], 0).
scalar_plusterm([CV|CVs], T) :-
        coeff_var_term(CV, T0),
        foldl(plusterm_, CVs, T0, T).

plusterm_(CV, T0, T0+T) :- coeff_var_term(CV, T).

coeff_var_term(C-V, T) :- ( C =:= 1 -> T = #V ; T = C * #V ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Reified predicates for use with predicates from library(reif).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

#=(X, Y, T) :-
        X #= Y #<==> #B,
        zo_t(B, T).

#<(X, Y, T) :-
        X #< Y #<==> #B,
        zo_t(B, T).

zo_t(0, false).
zo_t(1, true).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Generated predicates
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

term_expansion(make_parse_clpz, Clauses)    :- make_parse_clpz(Clauses).
term_expansion(make_parse_reified, Clauses) :- make_parse_reified(Clauses).
term_expansion(make_matches, Clauses)       :- make_matches(Clauses).

make_parse_clpz.
make_parse_reified.
make_matches.
