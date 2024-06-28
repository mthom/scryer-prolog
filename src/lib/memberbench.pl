:- module(memberbench,[run/0]).

:- use_module(library(reif)).

:- meta_predicate fif_(1,0,0).


:- set_prolog_flag(double_quotes,chars).

:- op(900, fy, [$]).

% uwnportray(T) :- write_term(T,[quoted(true)]),nl.



uwnportray(T) :- portray_clause(T).  % Item#539

$(X) :- uwnportray(call-X),X,uwnportray(exit-X).


en_memberchk(N, E, Es) :-
  exptrue(N),
  \+ memberchk(E, Es)
; true.

memberchk_once(E, Es) :-
   once(member(E, Es)).

en_memberchk_once(N, E, Es) :-
  exptrue(N),
  \+ memberchk_once(E, Es)
; true.

memberd(X, [X|_Es]).
memberd(X, [E|Es]) :-
   dif(X, E),
   memberd(X, Es).

en_memberd(N, E, Es) :-
  exptrue(N),
  \+ memberd(E, Es)
; true.

memberd2(X, [E|Es]) :-
   (  X = E
   ;  dif(X, E),
      memberd2(X, Es)
   ).

en_memberd2(N, E, Es) :-
  exptrue(N),
  \+ memberd2(E, Es)
; true.

memberd3(X, [E|Es]) :-
   memberd3(X, E, Es).

memberd3(X, X, _Es).
memberd3(X, E, Es) :-
   dif(X, E),
   Es = [F|Fs],
   memberd3(X, F, Fs).

en_memberd3(N, E, Es) :-
  exptrue(N),
  \+ memberd3(E, Es)
; true.


memberdc(X, [X|_Es]).
memberdc(X, [E|Es]) :-
   call(dif(X, E)),
   memberdc(X, Es).

en_memberdc(N, E, Es) :-
  exptrue(N),
  \+ memberdc(E, Es)
; true.

memberdo(X, [X|_Es]).
memberdo(X, [E|Es]) :-
   once((dif(X, E),(fail,true;true))),
   memberdo(X, Es).

en_memberdo(N, E, Es) :-
  exptrue(N),
  \+ memberdo(E, Es)
; true.


memberd_ifc(X, [E|Es]) :-
   if_(X = E, true, memberd_ifc(X, Es) ).

en_memberd_ifc(N, E, Es) :-
  exptrue(N),
  \+ memberd_ifc(E, Es)
; true.

memberd_fif(X, [E|Es]) :-
   fif_(X = E, true, memberd_fif(X, Es) ).

en_memberd_fif(N, E, Es) :-
  exptrue(N),
  \+ memberd_fif(E, Es)
; true.


memberd_if1(X, [E|Es]) :-
   ( X == E -> true
   ; X \= E -> memberd_if1(X, Es)
   ; X = E
   ; dif(X, E),
     memberd_if1(X, Es)
   ).

en_memberd_if1(N, E, Es) :-
  exptrue(N),
  \+ memberd_if1(E, Es)
; true.

memberd_if2(X, [E|Es]) :-
   ( X \= E -> memberd_if2(X, Es)
   ; X == E -> true
   ; X = E
   ; dif(X, E),
     memberd_if2(X, Es)
   ).

en_memberd_if2(N, E, Es) :-
  exptrue(N),
  \+ memberd_if2(E, Es)
; true.

% if3bad: This serves only to estimate the unnecessary overheads
% currently created by \= compared to \==

memberd_if3bad(X, [E|Es]) :-
   ( X \== E -> memberd_if3bad(X, Es)  % actually wrong
   ; X == E -> true
   ; X = E
   ; dif(X, E),
     memberd_if3bad(X, Es)
   ).

en_memberd_if3bad(N, E, Es) :-
  exptrue(N),
  \+ memberd_if3bad(E, Es)
; true.

memberd_if3bad2(X, [E|Es]) :-
   memberd_if3bad2(X, E, Es).

memberd_if3bad2(X, E, Es) :-
   X \== E, % should be rather X \== E, ?=(X,E) -
   !,
	Es = [F|Fs],
	memberd_if3bad2(X, F, Fs).
memberd_if3bad2(X, E, _Es) :-
   X == E,
   !.
memberd_if3bad2(X, E, Es) :-
   (  X \= E
	-> Es = [F|Fs],
      memberd_if3bad2(X, F, Fs)
   ;  X = E
   ;  dif(X, E),
      memberd_if3bad2(X, Es)
   ).

en_memberd_if3bad2(N, E, Es) :-
  exptrue(N),
  \+ memberd_if3bad2(E, Es)
; true.

memberd_if3bad3(X, [E|Es]) :-
   ( X \== E -> memberd_if3bad3(X, Es)  % actually wrong
   ; X == E -> true
   ; (  X \= E -> memberd_if3bad3(X, Es)
     ;  X = E
     ;  dif(X, E),
        memberd_if3bad3(X, Es)
     )
   ).

en_memberd_if3bad3(N, E, Es) :-
  exptrue(N),
  \+ memberd_if3bad3(E, Es)
; true.






notequal(X,X) :- !, fail.
notequal(_,_).

memberd_if4(X, [E|Es]) :-
   ( notequal(X,E) -> memberd_if4(X, Es)  % actually wrong
   ; X == E -> true
   ; X = E
   ; dif(X, E),
     memberd_if4(X, Es)
   ).

en_memberd_if4(N, E, Es) :-
  exptrue(N),
  \+ memberd_if4(E, Es)
; true.

% ifopti: A version that might be best, provided X \== E, ?=(X, E) is one
% efficient conditional built-in

memberd_ifopti(X, [E|Es]) :-
   ( X \== E, ?=(X,E) -> memberd_ifopti(X, Es)
   ; X == E -> true
	; X \= E -> memberd_ifopti(X, Es)
   ; X = E
   ; dif(X, E),
     memberd_ifopti(X, Es)
   ).

en_memberd_ifopti(N, E, Es) :-
  exptrue(N),
  \+ memberd_ifopti(E, Es)
; true.


% perfect: A compiler that is able to perfectly compile the disjunction,
% thus not creating any CP in the beginning for simple tests

memberd_ifperfect(X, [E|Es]) :-
   ( X = E
   ; dif(X, E),
     memberd_ifperfect(X, Es)
   ).

en_memberd_ifperfect(N, E, Es) :-
  exptrue(N),
  \+ memberd_ifperfect(E, Es)
; true.


en_bassoc(N, K,KVs,V) :-
   exptrue(N),
   \+ get_bassoc(K, KVs, V)
;  true.

get_bassoc(K, KVs, V) :-
   memberchk(K-V, KVs).

en_lassoc(N, K,KVs,V) :-
   exptrue(N),
   \+ get_lassoc(K, KVs, V)
;  true.

get_lassoc(K, KVs, V) :-
   once(member(K-V, KVs)).


en_memberk(N, K,V, KVs) :-
   exptrue(N),
   \+ memberk(K, V, KVs)
;  true.


memberk(K0,V0, [K-V|KVs]) :-
   if_(K0 = K, V0 = V, memberk(K0,V0, KVs)).

en_fmemberk(N, K,V, KVs) :-
   exptrue(N),
   \+ fmemberk(K, V, KVs)
;  true.


fmemberk(K0,V0, [K-V|KVs]) :-
   fif_(K0 = K, V0 = V, fmemberk(K0,V0, KVs)).

fif_(If_1, Then_0, Else_0) :-
   call(If_1, T),
   (  T == true -> Then_0
   ;  T == false -> Else_0
   ;  nonvar(T) -> throw(error(type_error(boolean,T),
                               type_error(call(If_1,T),2,boolean,T)))
   ;  throw(error(instantiation_error,instantiation_error(call(If_1,T),2)))
   ).

time(G_0, Tms) :-
   statistics(runtime, [T0|_]),
   G_0,
   statistics(runtime, [T1|_]),
   Tms is T1-T0.

time(G_0) :-
   time(G_0, Tms),
   functor(G_0, F, N),
   format('~q: t=~3ds~n',[F/N,Tms]).

ten.
ten.
ten.
ten.
ten.
ten.
ten.
ten.
ten.
ten.

exptrue(0).
exptrue(1) :-
  ten.
exptrue(2) :-
  ten,
  ten.
exptrue(3) :-
  ten,
  ten,
  ten.
exptrue(4) :-
  ten,
  ten,
  ten,
  ten.
exptrue(5) :-
  ten,
  ten,
  ten,
  ten,
  ten.
exptrue(6) :-
  ten,
  ten,
  ten,
  ten,
  ten,
  ten.

run :-
   E = z, Es = "abcdefghijklmnopqrstuvwxyz ",
   N = 5,
   time(en_memberchk(N, E, Es)),
   time(en_memberchk_once(N, E, Es)),
   time(en_memberd(N, E, Es)),
   time(en_memberd2(N, E, Es)),
   time(en_memberd3(N, E, Es)),
%   time(en_memberdc(N, E, Es)),
%   time(en_memberdo(N, E, Es)),
   time(en_memberd_fif(N, E, Es)),
   time(en_memberd_ifc(N, E, Es)),
   time(en_memberd_if1(N, E, Es)),
   time(en_memberd_if2(N, E, Es)),
   time(en_memberd_if4(N, E, Es)),
   time(en_memberd_if3bad(N, E, Es)),
   time(en_memberd_if3bad2(N, E, Es)),
   time(en_memberd_if3bad3(N, E, Es)),
   time(en_memberd_if4(N, E, Es)),
   time(en_memberd_ifopti(N, E, Es)),
   time(en_memberd_ifperfect(N, E, Es)),
   time(en_memberd_ifperfect(N, E, Es)),
   K = c,
   \+ (  member(Len,[10,20,10,20]),
         writeq(len=Len),nl,
         n_kvs(Len,KVs),
         \+ (
            time(en_bassoc(N, K, KVs, _)),
            time(en_lassoc(N, K, KVs, _)),
            time(en_fmemberk(N, K,_,KVs)),
            time(en_memberk(N, K,_,KVs)),
            time(en_bassoc(N, K, KVs, _)),
            time(en_lassoc(N, K, KVs, _)),
            time(en_fmemberk(N, K,_,KVs)),
            time(en_memberk(N, K,_,KVs))
         )
   ).


n_kvs(Len, KVs) :-
   length(Pre,Len),
   maplist(=(b-v),Pre),
   append(Pre,[c-w,d-e],KVs).

maplist(_P_1, []).
maplist(P_1, [E|Es]):-
   call(P_1, E),
   maplist(P_1, Es).


