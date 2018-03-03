:- module(control, [(\=)/2, between/3, call_cleanup/2, once/1]).

:- op(700, xfx, \=).

once(G) :- G, !.

X \= X :- !, false.
_ \= _.

call_cleanup(G, C) :- setup_call_cleanup(true, G, C).

between(Lower, Upper, Lower) :-
    Lower =< Upper.
between(Lower1, Upper, X) :-
    Lower1 < Upper,
    Lower2 is Lower1 + 1,
    between(Lower2, Upper, X).
