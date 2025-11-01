:- module(reif,
    [if_/3,
     cond_t/3,
     (=)/3,
     dif/3,
     (',')/3,
     (;)/3,
     memberd_t/3,
     tmember/2,
     tmember_t/3,
     tfilter/3,
     tpartition/4
%
    ]).
%
%
%

/** <module> Reified if, reification library v3

@author Ulrich Neumerkel
see Indexing dif/2
U. Neumerkel and S. Kral. https://arxiv.org/abs/1607.01590 [cs.PL]. July 2016.
*/

:- use_module(library(dif)).
:- use_module(library(loader), [goal_sanitized/2]).

:- meta_predicate(if_(1, 0, 0)).
:- meta_predicate(cond_t(1, 0, ?)).
:- meta_predicate(tfilter(2, ?, ?)).
:- meta_predicate(tpartition(2, ?, ?, ?)).
:- meta_predicate(','(1, 1, ?)).
:- meta_predicate(;(1, 1, ?)).
:- meta_predicate(tmember(2, ?)).
:- meta_predicate(tmember_t(2, ?, ?)).

:- op(900, fy, [$]).

% uwnportray(T) :- write_term(T,[quoted(true)]),nl.

uwnportray(T) :- portray_clause(T).  % Item#539

$(X) :- uwnportray(call-X),X,uwnportray(exit-X).
$(C,V1) :-
   $call(C,V1).
$(C,V1,V2) :-
   $call(C,V1,V2).
$(C,V1,V2,V3) :-
   $call(C,V1,V2,V3).
$(C,V1,V2,V3,V4) :-
   $call(C,V1,V2,V3,V4).
$(C,V1,V2,V3,V4,V5) :-
   $call(C,V1,V2,V3,V4,V5).
$(C,V1,V2,V3,V4,V5,V6) :-
   $call(C,V1,V2,V3,V4,V5,V6).
$(C,V1,V2,V3,V4,V5,V6,V7) :-
   $call(C,V1,V2,V3,V4,V5,V6,V7).

goal_expanded(MG_0, MGx_0) :-
   var(MG_0),
   !,
   MG_0 = MGx_0.
goal_expanded(call(MG_1, X), MGx_0) :-
   MG_1 = M:G_1, atom(M), callable(G_1), G_1 \= (_:_),
   functor_(G_1, G_0, X),
   \+ predicate_property(M:G_0, (meta_predicate _)),
   !,
   MGx_0 = M:G_0.
goal_expanded(call(G_0), Gx_0) :-
   acyclic_term(G_0),
   nonvar(G_0),
   % more conditions
   !,
   G_0 = Gx_0.
goal_expanded(MG_0, MG_0).


functor_(T, TA, A) :-
   functor(T, F, N0),
   N1 is N0+1,
   functor(TA, F, N1),
   arg(N1, TA, A),
   sameargs(N0, T, TA).

sameargs(N0, S, T) :-
   N0 > 0,
   N1 is N0-1,
   arg(N0, S, A),
   arg(N0, T, A),
   sameargs(N1, S, T).
sameargs(0, _, _).




/* 2do: unqualified If_1: error
*/

%
user:goal_expansion(if_(If_1, Then_0, Else_0), G_0) :-
   goal_sanitized(Then_0, SanitizedThen_0),
   goal_sanitized(Else_0, SanitizedElse_0),
   ugoal_expansion(if_(If_1, SanitizedThen_0, SanitizedElse_0), G_0).

%
%
%
%
%
%
%
%
%
%
%
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
    nonvar(If_1), If_1 = (X = Y),
   goal_expanded(call(Then_0), Thenx_0),
   goal_expanded(call(Else_0), Elsex_0),
   !,
   Goal_0 =
      ( X \= Y -> Elsex_0
      ; X == Y -> Thenx_0
      ; X = Y,    Thenx_0
      ; dif(X,Y), Elsex_0
      ).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal) :-
   nonvar(If_1), If_1 = dif(X, Y),
   goal_expanded(call(Then_0), Thenx_0),
   goal_expanded(call(Else_0), Elsex_0),
   !,
   Goal =
      ( X \= Y -> Thenx_0
      ; X == Y -> Elsex_0
      ; X = Y,    Elsex_0
      ; dif(X,Y), Thenx_0
      ).
% if_((A_1;B_1), Then_0, Else_0)
% => if_(A_1, Then_0, if_(B_1, Then_0, Else_0))
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal) :-
   subsumes_term((A_1;B_1), If_1),
   (A_1;B_1) = If_1,
   !,
   Goal = if_(A_1, Then_0, if_(B_1, Then_0, Else_0)).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
   subsumes_term((A_1,B_1), If_1),
   (A_1,B_1) = If_1,
   !,
   Goal_0 = if_(A_1, if_(B_1, Then_0, Else_0), Else_0).
ugoal_expansion(if_(If_1, Then_0, Else_0), Goal_0) :-
   goal_expanded(call(If_1, T), Ifx_0),
   goal_expanded(call(Then_0), Thenx_0),
   goal_expanded(call(Else_0), Elsex_0),
   Goal_0 =
      (  Ifx_0,
         (  T == true -> Thenx_0
         ;  T == false -> Elsex_0
         ;  nonvar(T) -> throw(error(type_error(boolean,T),
                               type_error(call(If_1,T),2,boolean,T)))
         ;  throw(error(instantiation_error,
                               instantiation_error(call(If_1,T),2)))
         )
      ).
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%
%

if_(If_1, Then_0, Else_0) :-
   call(If_1, T),
   (  T == true -> Then_0
   ;  T == false -> Else_0
   ;  nonvar(T) -> throw(error(type_error(boolean,T),
                               type_error(call(If_1,T),2,boolean,T)))
   ;  throw(error(instantiation_error,instantiation_error(call(If_1,T),2)))
   ).


tfilter(C_2, Es, Fs) :-
   i_tfilter(Es, C_2, Fs).

i_tfilter([], _, []).
i_tfilter([E|Es], C_2, Fs0) :-
   if_(call(C_2, E), Fs0 = [E|Fs], Fs0 = Fs),
   i_tfilter(Es, C_2, Fs).

tpartition(P_2, Xs, Ts, Fs) :-
   i_tpartition(Xs, P_2, Ts, Fs).

i_tpartition([], _P_2, [], []).
i_tpartition([X|Xs], P_2, Ts0, Fs0) :-
   if_( call(P_2, X)
      , ( Ts0 = [X|Ts], Fs0 = Fs )
      , ( Fs0 = [X|Fs], Ts0 = Ts ) ),
   i_tpartition(Xs, P_2, Ts, Fs).

=(X, Y, T) :-
   (  X == Y -> T = true
   ;  X \= Y -> T = false
   ;  T = true, X = Y
   ;  T = false,
      dif(X, Y)
   ).

dif(X, Y, T) :-
  =(X, Y, NT),
  non(NT, T).

non(true, false).
non(false, true).

','(A_1, B_1, T) :-
   if_(A_1, call(B_1, T), T = false).

;(A_1, B_1, T) :-
   if_(A_1, T = true, call(B_1, T)).

cond_t(If_1, Then_0, T) :-
   if_(If_1, ( Then_0, T = true ), T = false ).

memberd_t(E, Xs, T) :-
   i_memberd_t(Xs, E, T).

i_memberd_t([], _, false).
i_memberd_t([X|Xs], E, T) :-
   if_( X = E, T = true, i_memberd_t(Xs, E, T) ).

tmember(P_2, [X|Xs]) :-
   if_( call(P_2, X), true, tmember(P_2, Xs) ).

tmember_t(_P_2, [], false).
tmember_t(P_2, [X|Xs], T) :-
   if_( call(P_2, X), T = true, tmember_t(P_2, Xs, T) ).
