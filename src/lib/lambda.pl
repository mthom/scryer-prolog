/*
    Author:        Ulrich Neumerkel
    E-mail:        ulrich@complang.tuwien.ac.at
    Copyright (C): 2009 Ulrich Neumerkel. All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY Ulrich Neumerkel ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL Ulrich Neumerkel OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation
are those of the authors and should not be interpreted as representing
official policies, either expressed or implied, of Ulrich Neumerkel.



*/

:- module(lambda, [
		   (^)/3, (^)/4, (^)/5, (^)/6, (^)/7, (^)/8, (^)/9, (^)/10,
		   (\)/1, (\)/2, (\)/3, (\)/4, (\)/5, (\)/6, (\)/7, (\)/8,
		   (+\)/2, (+\)/3, (+\)/4, (+\)/5, (+\)/6, (+\)/7, (+\)/8,
			(+\)/9, op(201,xfx,+\)]).

:- use_module(library(iso_ext)).

/** <module> Lambda expressions

This library provides lambda expressions to simplify higher order
programming based on call/N.

Lambda expressions are represented by ordinary Prolog terms.
There are two kinds of lambda expressions:

```
    Free+\X1^X2^ ..^XN^Goal

         \X1^X2^ ..^XN^Goal
```

The second is a shorthand for `t+\X1^X2^..^XN^Goal`.

Xi are the parameters.

Goal is a goal or continuation. Syntax note: Operators within Goal
require parentheses due to the low precedence of the ^ operator.

Free contains variables that are valid outside the scope of the lambda
expression. They are thus free variables within.

All other variables of Goal are considered local variables. They must
not appear outside the lambda expression. This restriction is
currently not checked. Violations may lead to unexpected bindings.

In the following example the parentheses around X>3 are necessary.

```
?- use_module(library(lambda)).
?- use_module(library(lists)).

?- maplist(\X^(X>3),[4,5,9]).
   true.
```

In the following X is a variable that is shared by both instances of
the lambda expression. The second query illustrates the cooperation of
continuations and lambdas. The lambda expression is in this case a
continuation expecting a further argument.

```
?- use_module(library(dif)).
   true.

?- Xs = [A,B], maplist(X+\Y^dif(X,Y), Xs).
   Xs = [A,B], dif:dif(X,A), dif:dif(X,B).

?- Xs = [A,B], maplist(X+\dif(X), Xs).
   Xs = [A,B], dif:dif(X,A), dif:dif(X,B).
```

The following queries are all equivalent. To see this, use
the fact `f(x,y)`.

```
?- call(f,A1,A2).
?- call(\X^f(X),A1,A2).
?- call(\X^Y^f(X,Y), A1,A2).
?- call(\X^(X+\Y^f(X,Y)), A1,A2).
?- call(call(f, A1),A2).
?- call(f(A1),A2).
?- f(A1,A2).
   A1 = x, A2 = y.
```

Further discussions
[http://www.complang.tuwien.ac.at/ulrich/Prolog-inedit/ISO-Hiord](http://www.complang.tuwien.ac.at/ulrich/Prolog-inedit/ISO-Hiord)

@tbd Static expansion similar to apply_macros.
@author Ulrich Neumerkel
*/

:- meta_predicate ^(?,0,?).
:- meta_predicate ^(?,1,?,?).
:- meta_predicate ^(?,2,?,?,?).
:- meta_predicate ^(?,3,?,?,?,?).
:- meta_predicate ^(?,4,?,?,?,?,?).
:- meta_predicate ^(?,5,?,?,?,?,?,?).
:- meta_predicate ^(?,6,?,?,?,?,?,?,?).
:- meta_predicate ^(?,7,?,?,?,?,?,?,?,?).
:- meta_predicate \(0).
:- meta_predicate \(1,?).
:- meta_predicate \(2,?,?).
:- meta_predicate \(3,?,?,?).
:- meta_predicate \(4,?,?,?,?).
:- meta_predicate \(5,?,?,?,?,?).
:- meta_predicate \(6,?,?,?,?,?,?).
:- meta_predicate \(7,?,?,?,?,?,?,?).
:- meta_predicate +\(?,0).
:- meta_predicate +\(?,1,?).
:- meta_predicate +\(?,2,?,?).
:- meta_predicate +\(?,3,?,?,?).
:- meta_predicate +\(?,4,?,?,?,?).
:- meta_predicate +\(?,5,?,?,?,?,?).
:- meta_predicate +\(?,6,?,?,?,?,?,?).
:- meta_predicate +\(?,7,?,?,?,?,?,?,?).

:- meta_predicate no_hat_call(0).

^(V1,C_0,V1) :-
   no_hat_call(C_0).
^(V1,C_1,V1,V2) :-
   call(C_1,V2).
^(V1,C_2,V1,V2,V3) :-
   call(C_2,V2,V3).
^(V1,C_3,V1,V2,V3,V4) :-
   call(C_3,V2,V3,V4).
^(V1,C_4,V1,V2,V3,V4,V5) :-
   call(C_4,V2,V3,V4,V5).
^(V1,C_5,V1,V2,V3,V4,V5,V6) :-
   call(C_5,V2,V3,V4,V5,V6).
^(V1,C_6,V1,V2,V3,V4,V5,V6,V7) :-
   call(C_6,V2,V3,V4,V5,V6,V7).
^(V1,C_7,V1,V2,V3,V4,V5,V6,V7,V8) :-
   call(C_7,V2,V3,V4,V5,V6,V7,V8).

\(FC_0) :-
   copy_term_nat(FC_0,C_0),
   no_hat_call(C_0).
\(FC_1,V1) :-
   copy_term_nat(FC_1,C_1),
   call(C_1,V1).
\(FC_2,V1,V2) :-
   copy_term_nat(FC_2,C_2),
   call(C_2,V1,V2).
\(FC_3,V1,V2,V3) :-
   copy_term_nat(FC_3,C_3),
   call(C_3,V1,V2,V3).
\(FC_4,V1,V2,V3,V4) :-
   copy_term_nat(FC_4,C_4),
   call(C_4,V1,V2,V3,V4).
\(FC_5,V1,V2,V3,V4,V5) :-
   copy_term_nat(FC_5,C_5),
   call(C_5,V1,V2,V3,V4,V5).
\(FC_6,V1,V2,V3,V4,V5,V6) :-
   copy_term_nat(FC_6,C_6),
   call(C_6,V1,V2,V3,V4,V5,V6).
\(FC_7,V1,V2,V3,V4,V5,V6,V7) :-
   copy_term_nat(FC_7,C_7),
   call(C_7,V1,V2,V3,V4,V5,V6,V7).


+\(GV,FC_0) :-
   copy_term_nat(GV+FC_0,GV+C_0),
   no_hat_call(C_0).
+\(GV,FC_1,V1) :-
   copy_term_nat(GV+FC_1,GV+C_1),
   call(C_1,V1).
+\(GV,FC_2,V1,V2) :-
   copy_term_nat(GV+FC_2,GV+C_2),
   call(C_2,V1,V2).
+\(GV,FC_3,V1,V2,V3) :-
   copy_term_nat(GV+FC_3,GV+C_3),
   call(C_3,V1,V2,V3).
+\(GV,FC_4,V1,V2,V3,V4) :-
   copy_term_nat(GV+FC_4,GV+C_4),
   call(C_4,V1,V2,V3,V4).
+\(GV,FC_5,V1,V2,V3,V4,V5) :-
   copy_term_nat(GV+FC_5,GV+C_5),
   call(C_5,V1,V2,V3,V4,V5).
+\(GV,FC_6,V1,V2,V3,V4,V5,V6) :-
   copy_term_nat(GV+FC_6,GV+C_6),
   call(C_6,V1,V2,V3,V4,V5,V6).
+\(GV,FC_7,V1,V2,V3,V4,V5,V6,V7) :-
   copy_term_nat(GV+FC_7,GV+C_7),
   call(C_7,V1,V2,V3,V4,V5,V6,V7).


%% no_hat_call(:Goal_0)
%
% Like call, but issues an error for a goal (^)/2.  Such goals are
% likely the result of an insufficient number of arguments.

no_hat_call(MGoal_0) :-
   strip_module(MGoal_0, _, Goal_0),
   (  nonvar(Goal_0),
      Goal_0 = (_^_)
   -> throw(
			error(
				existence_error(lambda_parameter,MGoal_0),
				_))
	;	call(MGoal_0)
   ).

% I would like to replace this by:
% V1^Goal :- throw(error(existence_error(lambda_parameter,V1^Goal),_)).
