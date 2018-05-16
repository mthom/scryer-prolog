:- use_module(library(builtins)).

:- module(control, [(\=)/2, (\+)/1, between/3, once/1, repeat/0]).

:- op(900, fy, \+).
:- op(700, xfx, \=).

once(G) :- G, !.

\+ G :- G, !, false.
\+ _.

X \= X :- !, false.
_ \= _.

% call_cleanup(G, C) :- setup_call_cleanup(true, G, C).

between(Lower, Upper, Lower) :-
    Lower =< Upper.
between(Lower1, Upper, X) :-
    Lower1 < Upper,
    Lower2 is Lower1 + 1,
    between(Lower2, Upper, X).

repeat.
repeat :- repeat.
