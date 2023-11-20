/** Declarative debugging.

  This library provides three predicates with associated operators.
  The operators can be placed in front of goals to debug Prolog
  programs.

  Of these predicates, the most frequently used is `(*)/1`, with
  associated prefix operator `*` (star). Placing `*` in front of a
  goal means to _generalize away_ the goal. `* Goal` acts as if `Goal`
  did not appear at all in the source code. It is declaratively
  equivalent to _commenting out_ the goal, and easier to write,
  because `*` can also be placed in front of the last goal in a clause
  without any additional changes.

  Source: [https://stackoverflow.com/a/30791637](https://stackoverflow.com/a/30791637)

*/



:- module(debug, [
    op(900, fx, $),
    op(900, fx, $-),
    op(950, fy, *),
    (*)/1,
    ($)/1,
    ($-)/1
]).

:- use_module(library(format), [portray_clause/1]).

:- meta_predicate *(0).
:- meta_predicate $(0).
:- meta_predicate $-(0).

%% $-(Goal)
%
%  Portray exceptions thrown by Goal.

$-(G_0) :-
   catch(G_0, Ex, ( portray_clause(exception:Ex:G_0), throw(Ex) ) ).

%% $(Goal)
%
%  Provide a _trace_ for calls of Goal.

$(G_0) :-
   portray_clause(call:G_0),
   $-G_0,
   portray_clause(exit:G_0).

%% *(Goal)
%
%  Generalize away Goal.


*(_).
