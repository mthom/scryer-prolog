/** For accurate information, please read [*Indexing dif/2*](https://arxiv.org/abs/1607.01590).
Reification, to put in simple terms, is to treat a more abstract thing 
(unification, backtracking, etc) as 
if it were something concrete. In this library, an indexing technique is
employed to reify concepts like synactic equality (see dif/2) into boolean
values, `true` and `false`. By converting such concepts to concrete objects
using indexing, `library(reif)` provides methods to arrive at more correct and
efficient code.
 

Example:

```
?- tfilter(=(a), [X,Y], Es).
   X = a, Y = a, Es = "aa"
;  X = a, Es = "a", dif:dif(a,Y)
;  Y = a, Es = "a", dif:dif(a,X)
;  Es = [], dif:dif(a,X), dif:dif(a,Y).
```
*/

:- module(reif, [if_/3, (=)/3, (',')/3, (;)/3, cond_t/3, dif/3,
		         memberd_t/3, tfilter/3, tmember/2, tmember_t/3,
		         tpartition/4]).

:- use_module(library(dif)).

:- meta_predicate(if_(1, 0, 0)).

if_(If_1, Then_0, Else_0) :-
    call(If_1, T),
    (  T == true  -> call(Then_0)
    ;  T == false -> call(Else_0)
    ;  nonvar(T) -> throw(error(type_error(boolean, T), _))
    ;  throw(error(instantiation_error, _))
    ).

=(X, Y, T) :-
    (  X == Y -> T = true
    ;  X \= Y -> T = false
    ;  T = true, X = Y
    ;  T = false, dif(X, Y)
    ).

dif(X, Y, T) :-
  =(X, Y, NT),
  non(NT, T).

non(true, false).
non(false, true).

:- meta_predicate(tfilter(2, ?, ?)).

tfilter(_, [], []).
tfilter(C_2, [E|Es], Fs0) :-
   if_(call(C_2, E), Fs0 = [E|Fs], Fs0 = Fs),
   tfilter(C_2, Es, Fs).

:- meta_predicate(tpartition(2, ?, ?, ?)).

tpartition(P_2, Xs, Ts, Fs) :-
   i_tpartition(Xs, P_2, Ts, Fs).

i_tpartition([], _P_2, [], []).
i_tpartition([X|Xs], P_2, Ts0, Fs0) :-
   if_( call(P_2, X)
      , ( Ts0 = [X|Ts], Fs0 = Fs )
      , ( Fs0 = [X|Fs], Ts0 = Ts ) ),
   i_tpartition(Xs, P_2, Ts, Fs).

:- meta_predicate(','(1, 1, ?)).

','(A_1, B_1, T) :-
    if_(A_1, call(B_1, T), T = false).

:- meta_predicate(';'(1, 1, ?)).

';'(A_1, B_1, T) :-
    if_(A_1, T = true, call(B_1, T)).

:- meta_predicate(cond_t(1, 0, ?)).

cond_t(If_1, Then_0, T) :-
   if_(If_1, ( Then_0, T = true ), T = false ).

memberd_t(E, Xs, T) :-
   i_memberd_t(Xs, E, T).

i_memberd_t([], _, false).
i_memberd_t([X|Xs], E, T) :-
   if_( X = E, T = true, i_memberd_t(Xs, E, T) ).

:- meta_predicate(tmember(2, ?)).

tmember(P_2, [X|Xs]) :-
   if_( call(P_2, X), true, tmember(P_2, Xs) ).

:- meta_predicate(tmember_t(2, ?, ?)).

tmember_t(_P_2, [], false).
tmember_t(P_2, [X|Xs], T) :-
   if_( call(P_2, X), T = true, tmember_t(P_2, Xs, T) ).

%% if_(+If_1, +Then_0, +Else_0)
%
%  A monotonic if-then-else. If_1 must be a reified predicate i.e. its last
%  argument must be either true/false.

%% =(?X, ?Y, ?T)
%
%  Reifies syntactic inequality. See [dif/2](./dif#dif/2).
%
%  True iff X and Y are not different terms, and T describes whether they are
%  different terms.
%  Useful in conjunction with if_/3.

%% ','(+A_1, +B_1, -T)
%
%  Similar to ,/2.

%% ';'(+A_1, +B_1, -T)
%
%  A version of ;/2 that avoids.

%% cond_t(+If_1, +Then_0, -T)
%
%  A monotonic if-then.
%  
%  Similar to if_ without the Else predicate.

%% dif(?X, ?Y, ?T)
%
%  The complement of (=)/3. True iff X and Y are different terms, and T
%  describes whether they are different terms.

%% memberd_t(?E, ?Xs, ?T)
%
%  True iff T describes whether Xs is a member of E.

%% tfilter(+C_2, E, Fs0)
%
%  A predicate for filtering items of a list that uses a reified condition C.

%% tmember(+P_2, ?X) 
%
%  True iff any of the members of X satisfy predicate P. Avoids visiting all
%  members of the list when possible.

%% tmember_t(+P_2, ?X, -T)
%
%  Similar to tmember.

%% tpartition(+P_2, ?Xs, ?Ts, ?Fs)
%  
%  Similar to tfilter/3, except the members for which P does not succeed are
%  represented by Fs.
%
%  ```
%  ?- tpartition(=(1), [1,2,4,5,1], X, Y).
%     X = [1,1], Y = [2,4,5].
%  ```

