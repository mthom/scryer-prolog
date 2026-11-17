/** Macro system inspired by KL1 and PMOS from 5th Gen Computer Systems.

## Quick tutorial

Define your own:

```
number#one ==> 1.
```

It will replace all occurrences of `number#one` with an actual number `1`.

You can have a more complex rules too:

```
math#double(X) ==> Y :- Y is 2 * X.
```

It will replace all occurrences of `math#double(...)` with computed concrete value.

You can use them by simply referencing in a goal:

```
    print#S ==> format("~s", [S]).

    predicate(X) :-
        print#"STRING",
        my_macro#atom,
        expand#(
            X = number#one
        ).
==>
    predicate(X) :-
        format("~s", ["STRING"]),
        my_macro#atom,
        X = 1.
```

Please notice that unknown macros (`my_macro`) will be left intact and you will
observe a compilation warning.

You can disable macro expansion by quoting it:

```
    predicate(X, Y) :-
        expand#(
            X = quote#math#double(42),
            Y = math#double(23)
        ).
==>
    predicate(X, Y) :-
        X = quote#math#double(42),
        Y = 46.
````

You can selectively import macros from any module that defines them:

```
:- use_module(macros_collection, [number/0, double/0]).
```

It will enable only macros that were explicitly imported, and warn if you use
others.

There is a little quirk though: if your macro has a numeric name, then it will
be always imported. For example the following macro will always be imported if
you import a module containing it:

```
8#String ==> Bytes :- octal_bytes(String, Bytes).
```

The only way to make it go away is to disable all macros from that module
completely:

```
:- use_module(my_macros, []).
```

*/


:- module(macros, [
    op(199, xfy, (#)),
    op(1200, xfy, (==>)),
    expand/0,
    inline_last/0,
    compile/0
]).

:- use_module(library(si), [atomic_si/1,when_si/2]).
:- use_module(library(error), [instantiation_error/1]).
:- use_module(library(loader), [prolog_load_context/2]).
:- use_module(library(goals), [call_unifiers/2,expand_subgoals/3]).
:- use_module(library(warnings), [warn/2]).
:- use_module(library(debug)).

:- discontiguous(macro/3).
:- multifile(macro/3).

load_module_context(Module) :- prolog_load_context(module, Module), !.
load_module_context(user).


% FIXME: Rework this mess
user:term_expansion((M#A ==> B), X) :-
    (var(M); number(M)),
    (   nonvar(B),
        B = (H :- G) ->
            X = (macros:macro(M, A, H) :- G)
        ;   X =  macros:macro(M, A, B)
    ).
user:term_expansion((M#A ==> B), [Module:M,X]) :-
    atom(M),
    load_module_context(Module),
    \+ catch(Module:M, error(existence_error(_,_),_), false),
    (   nonvar(B),
        B = (H :- G) ->
            X = (macros:macro(M, A, H) :- G)
        ;   X =  macros:macro(M, A, B)
    ).
user:term_expansion((M#A ==> B), X) :-
    atom(M),
    load_module_context(Module),
    call(Module:M),
    (   nonvar(B),
        B = (H :- G) ->
            X = (macros:macro(M, A, H) :- G)
        ;   X =  macros:macro(M, A, B)
    ).


% All macros distribute over common operators.
M#(A,B)  ==> M#A, M#B.
M#(A;B)  ==> M#A; M#B.
M#(A->B) ==> M#A -> M#B.
M#(\+ A) ==> \+ M#A.
M#{A}    ==> {M#A}.

% Cut is never expanded.
_#! ==> !.

%% expand # ?G_0.
%
% Sub-goal expansion.
%
% Wrap any expression to recursively expand any found macros, used explicitly
% to avoid heavy penalty of scanning all terms for possible macros:
%
% ```
%     expand#(
%         X = foo#42,
%         bar#baz(X),
%         \+ some#macro
%     );
% ```
%
% All following examples assume they are wrapped in `expand#(...)`.
%
expand#A ==> X :-
    expand_subgoals(_, A, X).


%% inline_last # ?G_1.
%
% Inline last argument at compile time.
%
% Useful if you want to have a formatted string as a variable:
%
% ```
%     Greeting = inline_last#phrase(format_("Hello ~s~a", ["World",!])).
% ==>
%     Greeting = "Hello World!".
% ```
%
% Perform some numeric calculations at compile time to avoid doing them in runtime:
%
% Two machines with with cycle time 7 and 5 need to start a task simultaneously.
% Find the next start time:
%
% ```
%     Time is inline_last#lcm(7, 5).
% ==>
%     Time is 35.
% ```
%
% It even works with CLP(Z):
%
% ```
%     #X #= inline_last#my_value * #Y.
% ==>
%     #X #= 2354235 * #Y.
% ```
%
inline_last#G ==> [X] :-
    load_module_context(M),
    M:call(G, X).


%% compile # ?G_0.
%
% Evaluates G and if it succeeds replaces it with a first solution represented
% as a sequence of unifications. For example:
%
% ```
%     compile#my_goal(A, B, C).
% ==>
%     A = 1,
%     B = 2,
%     C = 3.
% ```
%
compile#G ==> Us :-
    load_module_context(M),
    call_unifiers(M:G, Us).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

macro_wrapper(quote, _, _) :- !, false.
macro_wrapper(M, A, X) :-
    load_module_context(Module),
    (atom(M) -> Module:M; true),
    macro(M, A, X).
macro_wrapper(M, A, _) :-
    warn("Unknown macro ~a # ~q", [M,A]),
    throw(error(existence_error(macro/3, goal_expansion/2), [culprit-(M#A)])).

user:goal_expansion(M#A, X) :-
    atomic_si(M),
    when_si(nonvar(A),
        macro_wrapper(M, A, X)
    ).
