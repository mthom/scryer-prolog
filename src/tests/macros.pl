:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).

:- use_module(library(string_macros), [tel/0,cat/0]). % <- Macros can be imported selectively
:- use_module(library(macros)).
:- use_module(library(clpz)).

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
    \+string_num -> N = (A > B); N = bignum_gt(A,B).

% Should bad macro bodies generate exceptions? If so at which point: expansion
% time, compile time or runtime?
bad#macro ==> 1 :- _.

% TODO: Should implementation detect discontinuous macro definitions?
fep#too_late ==> 999.

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
%example(doesnt_expand_uninstantiated_macros(X)) :-
%    expand#(
%        _ = fep#X
%    ).
example(compilation([A,B,C])) :-
    compile#baz(12, A, B, C).
% What is the preferred operator precedence? Should parenthesis be required here?
example(modules(L)) :-
    compile#(lists:length(L, 5)).
example(clpz_operators_compatibility(X,Y)) :-
    expand#(
        #X #= #Y * inline_last#double(4)
    ).
example(concatenation(Name)) :-
    expand#write(cat#("Hello "-Name)).
example(unknown_macros) :-
    fep#hello,
    foo#bar,
    foo#fep#window. % <- Should it expand fep#window if foo is unknown?
%example(incorrect_macros) :-
%    b(a)#x, % <- Is it a good idea to support any ground term as a macro name?
%    b(_)#x,
%    _#t,
%    fep#_.
example(tbd) :-
    a(b#c)#d, % <- Should it expand b#c? If b/0 and a/1 are registered macros?
    a#b#c#d. % <- In which order macros should be expanded?

% Should macros be expanded in clauses heads?
example(macro_in_heads(16#"ABCD")).

% Should it be possible to rename predicate name using macros?
(my_macro#example(macro_names)) :-
    write('Hello'), nl.

% Should it be possible to expand whole clauses in-place?
my_macro#(my_example(X) :- hello(X)).
