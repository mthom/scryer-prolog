:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(reif)).

tt :-
    tt(Clause),
    nl, portray_clause(Clause), nl.
tt((f(V is Expr) :- Sequence)) :-
    sample("ttttffft", _ is Expr),
    once(phrase(ae(Expr,Repl), Removed)),
    append(Removed, [V is Repl], X),
    list_sequence(X, Sequence).


sample(Template, R) :-
    setof(E, phrase(arith_relation(E), Template), Es),
    length(Es, L),
    repeat,
    random_integer(0, L, I),
    format("~n% Info: Selected ~dth out of ~d found aritmetic relations that satisfy ~s template:~n\t", [I,L,Template]),
    nth0(I, Es, R).

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

ae(F, FR) --> ez(F, A, B, AR, BR, FR), ae(A, AR), ae(B, BR).
ae(F, FR) --> ey(F, A, R, FR), ae(A, R).
ae(A, R) --> ex(A, R).

ex(A          , R      ) --> [R = A], { nonvar(A), \+number(A), A \= e, A \= pi}.
ex(A          , A      ) --> t, { var(A) }.
ex(A          , A      ) --> t, { number(A) }.
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

t --> [].

%% list_sequence(List, Sequence).
%
list_sequence([H|T], S) :- ls_aux(T, H, S).
ls_aux([],    H, (H)).
ls_aux([A|T], H, (H,X)) :- list_sequence([A|T], X).
