:- use_module(library(lists)).
:- use_module(library(random)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).
:- use_module(library(debug)).

% Asserting and consulting of erroneous arithmetic relation shall succeed,
% but then it must fail at runtime.
main :-
    template_relation("tttftt", R),
    findall(T, test(R, T), [assert,consult]).

test(Relation, TestVariant) :-
    load_and_call(TestVariant, (rznvivy :- false, Relation), \+rznvivy).

load_and_call(assert, Clause, Query) :-
    setup_call_cleanup(
        ignore_exception(assertz(Clause)),
        $-Query,
        retract(Clause)
    ).
load_and_call(consult, Clause, Query) :-
    T = 'chnytjl.pl',
    setup_call_cleanup(
        open(T, write, S),
        portray_clause(S, Clause),
        close(S)
    ),
    ignore_exception(consult(T)),
    $-Query.

template_relation(Template, R) :-
    setof(E, phrase(arith_relation(E), Template), Es),
    length(Es, L),
    random_integer(0, L, I),
    format("% Info: Selected ~dth out of ~d found aritmetic relations that satisfy ~s template:~n\t", [I,L,Template]),
    nth0(I, Es, R),
    portray_clause(R).

%% phrase(arith_relation(Relation), Template).
%
% `Relation` is valid or invalid arithmetic relation (like `A is 3`) according
% to a template: `t` means correct term, `f` – incorrect. Position of template
% elements correspond to position of a term in the same relation written in
% Polish notation. Given expression: `1 < [] + 3` its template is: `"tttft"`,
% because it can be written as `< 1 + [] 3` using PN.
%
% Not all possible terms can be utilized and are commented out or otherwise not
% included, because it unnecessarily increases solution space.
arith_relation(F) --> rel(expr(F,A)), arith_expression(A).
arith_relation(F) --> rel(expr(F,A,B)), arith_expression(A), arith_expression(B).
arith_expression(A) --> func(expr(A)).
arith_expression(F) --> func(expr(F,A)), arith_expression(A).
arith_expression(F) --> func(expr(F,A,B)), arith_expression(A), arith_expression(B).

func(Expr) --> {fn(T, Expr)}, [T].
rel(Expr)  --> {rl(T, Expr)}, [T].

rl(t, expr(F,A,B)) :- member(F, [A<B,A=:=B]).
rl(t, expr(F,A))   :- member(F, [_ is A]).

fn(t, expr(A))     :- rnd(A).
fn(t, expr(A))     :- member(A, [e,pi]).
fn(t, expr(F,A))   :- member(F, [+(A),-(A),sqrt(A),log(A)]).
fn(t, expr(F,A,B)) :- member(F, [A+B,A-B,A*B,A/B,A^B]).
fn(f, expr(F))     :- member(F, [[],phi,[_|_]]).
%fn(f, expr(F,A))   :- member(F, [zeta(A)]).
%fn(f, expr(F,A,B)) :- member(F, [[A,B]]).

%% rnd(N).
%
% N sometimes can be an integer or a floating point number.
rnd(N) :-
    nonvar(N) -> number(N); (maybe -> random(N); random_integer(-1000, 1000, N)).

ignore_exception(G) :- catch($-G, _, true).
