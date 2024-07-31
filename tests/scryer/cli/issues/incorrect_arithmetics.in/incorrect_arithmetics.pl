:- use_module(library(lists)).
:- use_module(library(random)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(time)).
:- use_module(library(gensym)).

% Asserting and consulting of erroneous arithmetic relation shall succeed,
% but then it must fail at runtime.
main :-
    template_relation("tttft", R),
    load_test(assertz, R),
    load_test(reconsult, R).

load_test(Setup, Body) :-
    portray_clause(start:Setup),
    gensym(test, Test),
    setup_call_cleanup(
        ignore_exception(call(Setup, (Test :- false, Body))),
        (
            (ignore_exception(listing(Test/0)),!;true),
            \+ignore_exception(Test) -> Result = pass; Result = fail
        ),
        ignore_exception(retractall(Test))
    ),
    portray_clause(Result:Setup).

reconsult(Clause) :-
    Clause = (Head :- Body),
    File = 'chnytjl.pl',
    portray_consult(File, (canary :- Body)),
    setup_call_cleanup(
        assertz(Head),
        portray_consult(File, Clause),
        retract(Head)
    ).

portray_consult(File, Clause) :-
    setup_call_cleanup(
        open(File, write, S),
        portray_clause(S, Clause),
        close(S)
    ),
    consult(File).

template_relation(Template, R) :-
    time(setof(E, phrase(arith_relation(E), Template), Es)),
    length(Es, L),
    random_integer(0, L, I),
    format("   % Info: Selected ~d/~d aritmetic terms that satisfy ~s template:~n\t", [I,L,Template]),
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
fn(t, expr(F,A))   :- member(F, [-A,sqrt(A),log(A),tan(A),\A,+A]).
fn(t, expr(F,A,B)) :- member(F, [A+B,A-B,A*B,A/B,A^B,max(A,B)]).
fn(f, expr(F))     :- member(F, [[],phi,[_|_]]).
fn(f, expr(F,A))   :- member(F, [zeta(A)]).
fn(f, expr(F,A,B)) :- member(F, [[A,B],[A|B]]).

%% rnd(N).
%
% N sometimes can be an integer or a floating point number.
rnd(N) :-
    nonvar(N) -> number(N); (maybe -> random(N); random_integer(-1000, 1000, N)).

ignore_exception(G) :- catch($-G, _, true).
