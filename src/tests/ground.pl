/**/

:- module(ground_tests, []).

:- use_module(library(atts)).

:- use_module(test_framework).

:- attribute a/1.

a(Var) :- put_atts(Var, +a(hello)).

test("ground#239", (
    % double negate to avoid residual goal being printed
    \+ \+ (a(X), var(X), \+ ground(X))
)).

test("ground#1411",(
    G_0 = ( A=s(A) ), G_0,
    ground(A), ground(G_0)
)).

test("ground#2065",(
    A = [B|_C], B = [A], \+ ground(B), \+ground([B])
)).

test("ground#2073",(
    \+ ground(_-1+_-1),
    \+ ground(1-1-_)
)).

test("ground#2075",(
    G_0 = (_,_,ground(_)),
    G_0 = (D=[D|_],_=D*[],ground(D)),
    \+ G_0,
    _=_B*_,_D=_B*_A,_B=_B*_D,\+ ground(_B),
    A=[A|B],B=A*B,ground(A)
)).
