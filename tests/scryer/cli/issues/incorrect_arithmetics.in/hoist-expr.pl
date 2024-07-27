:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(reif)).
:- use_module(library(debug)).

tt :-
    tt(Clause),
    nl, portray_clause(Clause), nl.
tt((f(V is Expr) :- Sequence)) :-
    sample("tttffft", _ is Expr),
    phrase(ae(Expr,Repl), Removed),
    append(Removed, [V is Repl], X),
    list_sequence(X, Sequence).


sample(Template, R) :-
    setof(E, phrase(arith_relation(E), Template), Es),
    length(Es, L),
    repeat,
    random_integer(0, L, I),
    nth0(I, Es, R),
    format("~n% Info: Selected ~dth out of ~d found aritmetic relations that satisfy ~s template:~n\t~w~n", [I,L,Template,R]).

%% Proof-of-concept arithmetic expression expander
%
% TODO: Don't use DCG's, because they aren't available in loader.pl
test :- test(Clause), nl, portray_clause(Clause), nl.
test((f(V is Expr) :- Sequence)) :-
    length(Removed, _),
    phrase(ae(Expr,Repl), Removed),
    append(Removed, [V is Repl], X),
    list_sequence(X, Sequence).

ae(A, R) --> ex(A, R).
ae(F, FR) --> ey(F, A, R, FR), ae(A, R).
ae(F, FR) --> ez(F, A, B, AR, BR, FR), ae(A, AR), ae(B, BR).

ex(A, R) --> {ok_var(A,R)} -> proceed(A,R); [R=A].

proceed(e,e) --> t.
proceed(pi,pi) --> t.
proceed(epsilon,epsilon) --> t.
proceed(A,A) --> {var(A)}.
proceed(A,A) --> {number(A)}.

ey(-A     ,A, AR,-AR) --> t.
ey(+A     ,A, AR,+AR) --> t.
ey(\A     ,A, AR,\AR) --> t.
ey(sqrt(A),A, AR,sqrt(AR)) --> t.
ey(log(A) ,A, AR,log(AR)) --> t.
ey(abs(A) ,A, AR,abs(AR)) --> t.
ey(cos(A) ,A, AR,cos(AR)) --> t.
ey(sin(A) ,A, AR,sin(AR)) --> t.
ey(tan(A) ,A, AR,tan(AR)) --> t.
ey(exp(A) ,A, AR,exp(AR)) --> t.
ey(acos(A) ,A, AR,acos(AR)) --> t.
ey(asin(A) ,A, AR,asin(AR)) --> t.
ey(atan(A) ,A, AR,atan(AR)) --> t.
ey(float(A) ,A, AR,float(AR)) --> t.
ey(truncate(A) ,A, AR,truncate(AR)) --> t.
ey(round(A) ,A, AR,round(AR)) --> t.
ey(ceiling(A) ,A, AR,ceiling(AR)) --> t.
ey(floor(A) ,A, AR,floor(AR)) --> t.
ey(float_integer_part(A) ,A, AR,float_integer_part(AR)) --> t.
ey(float_fractional_part(A) ,A, AR,float_fractional_part(AR)) --> t.
ey(sign(A) ,A, AR,sign(AR)) --> t.

ez(A+B,A,B, AR,BR,AR+BR) --> t.
ez(A-B,A,B, AR,BR,AR-BR) --> t.
ez(A*B,A,B, AR,BR,AR*BR) --> t.
ez(A/B,A,B, AR,BR,AR/BR) --> t.
ez(A^B,A,B, AR,BR,AR^BR) --> t.
ez(A**B,A,B, AR,BR,AR**BR) --> t.
ez(A/\B,A,B, AR,BR,AR/\BR) --> t.
ez(A\/B,A,B, AR,BR,AR\/BR) --> t.
ez(A xor B,A,B, AR,BR,AR xor BR) --> t.
ez(A div B,A,B, AR,BR,AR div BR) --> t.
ez(A // B,A,B, AR,BR,AR // BR) --> t.
ez(A rdiv B,A,B, AR,BR,AR rdiv BR) --> t.
ez(A << B,A,B, AR,BR,AR << BR) --> t.
ez(A >> B,A,B, AR,BR,AR >> BR) --> t.
ez(A mod B,A,B, AR,BR,AR mod BR) --> t.
ez(A rem B,A,B, AR,BR,AR rem BR) --> t.
ez(max(A,B),A,B, AR,BR,max(AR,BR)) --> t.
ez(min(A,B),A,B, AR,BR,min(AR,BR)) --> t.
ez(gcd(A,B),A,B, AR,BR,gcd(AR,BR)) --> t.
ez(atan2(A,B),A,B, AR,BR,atan2(AR,BR)) --> t.

t --> [].

ok_var(A, A) :-
    var(A); number(A); (nonvar(A), arithmetic_term(A)).

arithmetic_term(e).
arithmetic_term(pi).
arithmetic_term(epsilon).
arithmetic_term(-_).
arithmetic_term(+_).
arithmetic_term(\_).
arithmetic_term(sqrt(_)).
arithmetic_term(log(_)).
arithmetic_term(abs(_)).
arithmetic_term(cos(_)).
arithmetic_term(sin(_)).
arithmetic_term(tan(_)).
arithmetic_term(exp(_)).
arithmetic_term(acos(_)).
arithmetic_term(asin(_)).
arithmetic_term(atan(_)).
arithmetic_term(float(_)).
arithmetic_term(truncate(_)).
arithmetic_term(round(_)).
arithmetic_term(ceiling(_)).
arithmetic_term(floor(_)).
arithmetic_term(float_integer_part(_)).
arithmetic_term(float_fractional_part(_)).
arithmetic_term(sign(_)).
arithmetic_term(_+_).
arithmetic_term(_-_).
arithmetic_term(_*_).
arithmetic_term(_/_).
arithmetic_term(_^_).
arithmetic_term(_**_).
arithmetic_term(_/\_).
arithmetic_term(_\/_).
arithmetic_term(_ xor _).
arithmetic_term(_ div _).
arithmetic_term(_ // _).
arithmetic_term(_ rdiv _).
arithmetic_term(_ << _).
arithmetic_term(_ >> _).
arithmetic_term(_ mod _).
arithmetic_term(_ rem _).
arithmetic_term(max(_,_)).
arithmetic_term(min(_,_)).
arithmetic_term(gcd(_,_)).
arithmetic_term(atan2(_,_)).

%% list_sequence(List, Sequence).
%
list_sequence([H|T], S) :- ls_aux(T, H, S).
ls_aux([],    H, (H)).
ls_aux([A|T], H, (H,X)) :- list_sequence([A|T], X).
