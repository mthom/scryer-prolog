/*
Copied from^W^W Inspired by memberbench[1], but has only benchmarks relevant to
goal expansion of if_/3 and is adapted to be better integrated into Scryer's
benchmarking subsystem: which doesn't need time reporting, and supports only
single test at a time.

[1]: http://www.complang.tuwien.ac.at/ulrich/Prolog-inedit/sicstus/memberbench.pl
*/

:- use_module(library(reif)).
:- use_module(library(lists)).
:- use_module(library(si)).


run(Test, Count) :-
   atom_si(Test),
   integer_si(Count),
   exptrue(Count),
   \+ benchmark(Test, z, "abcdefghijklmnopqrstuvwxyz ")
   ; true.


% Baseline test – the fastest possible implementation
benchmark(memberchk,   E, Es) :- memberchk(E, Es).

% Expanded if_/3
benchmark(memberd_ifc, E, Es) :- memberd_ifc(E, Es).

% Non-expanded if_/3
benchmark(memberd_fif, E, Es) :- memberd_fif(E, Es).


memberd_ifc(X, [E|Es]) :-
   if_(X = E, true, memberd_ifc(X, Es)).

memberd_fif(X, [E|Es]) :-
   fif_(X = E, true, memberd_fif(X, Es)).


% Copy of _if/3, but with a different name, so it won't be expanded
fif_(If_1, Then_0, Else_0) :-
    call(If_1, T),
    (  T == true  -> Then_0
    ;  T == false -> Else_0
    ;  nonvar(T) -> throw(error(type_error(boolean, T), _))
    ;  throw(error(instantiation_error, _))
    ).


%% exptrue(N).
%
% Succeeds 10^N times if N is ground, usefull as a cheap way to repeat a given
% predicate many times in benchmarks. There are many more ways to generate
% choice points, but this one by far has the lowest overhead.
exptrue(0).
exptrue(1) :- ten.
exptrue(2) :- ten, ten.
exptrue(3) :- ten, ten, ten.
exptrue(4) :- ten, ten, ten, ten.
exptrue(5) :- ten, ten, ten, ten, ten.
exptrue(6) :- ten, ten, ten, ten, ten, ten.

ten. ten. ten. ten. ten. ten. ten. ten. ten. ten.
