:- module(reif, [if_/3, (=)/3, (',')/3, (;)/3, cond_t/3, dif/3,
		 memberd_t/3, tfilter/3, tmember/2, tmember_t/3,
		 tpartition/4]).

:- use_module(library(dif)).

:- meta_predicate if_(1, 0, 0).

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

:- meta_predicate tfilter(1, ?, ?).

tfilter(C_2, Es, Fs) :-
   i_tfilter(Es, C_2, Fs).

i_tfilter([], _, []).
i_tfilter([E|Es], C_2, Fs0) :-
   if_(call(C_2, E), Fs0 = [E|Fs], Fs0 = Fs),
   i_tfilter(Es, C_2, Fs).

:- meta_predicate tpartition(1, ?, ?).

tpartition(P_2, Xs, Ts, Fs) :-
   i_tpartition(Xs, P_2, Ts, Fs).

i_tpartition([], _P_2, [], []).
i_tpartition([X|Xs], P_2, Ts0, Fs0) :-
   if_( call(P_2, X)
      , ( Ts0 = [X|Ts], Fs0 = Fs )
      , ( Fs0 = [X|Fs], Ts0 = Ts ) ),
   i_tpartition(Xs, P_2, Ts, Fs).

:- meta_predicate ','(0, 0, ?).

','(A_1, B_1, T) :-
    if_(A_1, call(B_1, T), T = false).

:- meta_predicate ';'(0, 0, ?).

';'(A_1, B_1, T) :-
    if_(A_1, T = true, call(B_1, T)).

:- meta_predicate cond_t(0, 0, ?).

cond_t(If_1, Then_0, T) :-
   if_(If_1, ( Then_0, T = true ), T = false ).

memberd_t(E, Xs, T) :-
   i_memberd_t(Xs, E, T).

i_memberd_t([], _, false).
i_memberd_t([X|Xs], E, T) :-
   if_( X = E, T = true, i_memberd_t(Xs, E, T) ).

:- meta_predicate tmember(1, ?).

tmember(P_2, [X|Xs]) :-
   if_( call(P_2, X), true, tmember(P_2, Xs) ).

:- meta_predicate tmember_t(1, ?).

tmember_t(P_2, [X|Xs], T) :-
   if_( call(P_2, X), T = true, tmember_t(P_2, Xs, T) ).
