:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(reif)).

%% Proof-of-concept arithmetic expression expander
%
% TODO: Don't use DCG's, because they aren't available in loader.pl
% TODO: Don't hardcode invalid expression
test :- test(Clause), nl, portray_clause(Clause), nl.
test((f(V is Expr) :- Sequence)) :-
    length(Removed, _),
    phrase(ae(Expr,Repl), Removed),
    append(Removed, [V is Repl], X),
    list_sequence(X, Sequence).

ae(A, R) --> ex(A, R).
ae(F, FR) --> ey(F, A, R, FR), ae(A, R).
ae(F, FR) --> ez(F, A, B, AR, BR, FR), ae(A, AR), ae(B, BR).

ex([]         , R      ) --> [R = []].
ex([H|T]      , R      ) --> [R = [H|T]].
ex(zeta(A)    , R      ) --> [R = zeta(A)].
ex(A          , A      ) --> t, { var(A) }.
ex(e          , e      ) --> t.
ex(pi         , pi     ) --> t.

ey(-A     ,A, AR,-AR) --> t.
ey(sqrt(A),A, AR,sqrt(AR)) --> t.
ey(log(A) ,A, AR,log(AR)) --> t.

ez(A+B,A,B, AR,BR,AR+BR) --> t.
ez(A-B,A,B, AR,BR,AR-BR) --> t.
ez(A*B,A,B, AR,BR,AR*BR) --> t.
ez(A/B,A,B, AR,BR,AR/BR) --> t.
ez(A^B,A,B, AR,BR,AR^BR) --> t.

t --> [true].

%% list_sequence(List, Sequence).
%
list_sequence([H|T], S) :- ls_aux(T, H, S).
ls_aux([],    H, (H)).
ls_aux([A|T], H, (H,X)) :- list_sequence([A|T], X).
