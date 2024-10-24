:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).

:- use_module(library(string_macros)).
:- use_module(library(macros)).

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
%string_num.
bignum#(A < B) ==> N :-
    catch(string_num, _, false) -> N = bignum_lt(A,B); N = (A < B).
bignum#(A > B) ==> N :-
    catch(string_num, _, false) -> N = bignum_gt(A,B); N = (A > B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic(example/1).
example(formated_string(X)) :-
    X = inline_last#(\L^phrase(format_("This is my term ~w", [foo(1)]), L)).
example(bignum_example(A,B,P)) :-
    bignum#(
        A < B,
        !,
        A > 0;
        B + 1 < P
    ),
    compute(A,B).
example(numeric_enum_example) :-
    foo(fep#create).
example(ascii_examples) :-
    foo(tel#null),
    foo(tel#bell),
    foo(tel#bs).
example(base_conversion) :-
    foo(16#"ABCDEF01234560").
