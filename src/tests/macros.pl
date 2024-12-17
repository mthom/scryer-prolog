:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).

:- use_module(library(string_macros)).
:- use_module(library(macros)).
:- use_module(library(clpz)).

clpz:monotonic.

% Numeric enums
fep#window                  ==> 100.
    fep#create              ==> 101.
    fep#create_with_buffer  ==> 102.
    fep#get_max_size        ==> 103.
        fep#getl            ==> 110.
        fep#putb            ==> 111.
        fep#flush           ==> 112.
        fep#beep            ==> 113.

% Conditional compilation
string_num.
bignum#(A < B) ==> N :-
    string_num -> N = bignum_lt(A,B); N = (A < B).
bignum#(A > B) ==> N :-
    \+string_num -> N = bignum_gt(A,B); N = (A > B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Test functions
double(A, B) :- B is 2 * A.
baz(A, B, C, D) :- B is 2 * A, C is 3 * A, D is 3 * B.


:- dynamic(example/1).
example(formated_string(X)) :-
    expand#(
        X = inline_last#(\L^phrase(format_("This is my term ~w", [foo(1)]), L))
    ).
example(bignum_example(A,B,P)) :-
    bignum#(
        A < B,
        !,
        A > 0;
        B + 1 < P
    ),
    compute(A,B).
example(numeric_enum_example) :-
    expand#(
        foo(fep#window, fep#create),
        bar([fep#getl, fep#putb|_])
    ).
example(ascii_examples) :-
    expand#(
        foo(tel#null) -> foo(tel#bell); foo(tel#bs)
    ).
example(base_conversion) :-
    expand#(
        foo(16#"ABCDEF01234560")
    ).
example(quotated_goals_are_not_expanded(A)) :-
    quote#(bignum#(A<2)).
example(quotation_works_in_nested_terms(A)) :-
    expand#(
        A = [fep#putb,_,quote#fep#putb]
    ).
example(expands_arithmetic_functions(A,B)) :-
    expand#(
        B is A + fep#beep / inline_last#double(12)
    ).
example(doesnt_expand_uninstantiated_macros(X)) :-
    expand#(
        _ = fep#X
    ).
example(compilation([A,B,C])) :-
    compile#baz(12, A, B, C).
example(modules(L)) :-
    compile#(lists:length(L, 5)).
example(clpz_operators_compatibility(X,Y)) :-
    expand#(
        #X #= #Y * inline_last#double(4)
    ).
