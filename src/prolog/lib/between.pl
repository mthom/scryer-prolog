:- module(between, [between/3, gen_int/1, gen_nat/1, numlist/2, repeat/1]).

%% TODO: numlist/3, numlist/5.

:- use_module(library(lists), [length/2]).

between(Lower, Upper, Lower) :-
    Lower =< Upper.
between(Lower1, Upper, X) :-
    Lower1 < Upper,
    Lower2 is Lower1 + 1,
    between(Lower2, Upper, X).

enumerate_nats(I, I).
enumerate_nats(I0, N) :-
    I1 is I0 + 1,
    enumerate_nats(I1, N).

gen_nat(N) :-
    integer(N), !, N >= 0.
gen_nat(N) :-
    var(N), enumerate_nats(0, N).

enumerate_ints(I, I).
enumerate_ints(I0, N) :-
    I0 > 0,
    N is -I0.
enumerate_ints(I0, N) :-
    I1 is I0 + 1,
    enumerate_ints(I1, N).

gen_int(N) :-
    integer(N), !.
gen_int(N) :-
    var(N), enumerate_ints(0, N).

repeat_integer(N) :-
    N > 0.
repeat_integer(N0) :-
    N0 > 0, N1 is N0 - 1, repeat_integer(N1).

repeat(N) :-
    integer(N), N > 0, repeat_integer(N).

numlist(Upper, List) :-
    (  integer(Upper) -> findall(X, between(1, Upper, X), List)
    ;  List = [_|_], length(List, Upper), findall(X, between(1, Upper, X), List)
    ).
