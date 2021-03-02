:- use_module(library(debug)).
:- use_module(library(format)).
:- use_module(library(lists)).
:- use_module(library(tabling)).
:- use_module('../../lib/clpz').
:- use_module(combination).
:- use_module(permutation).

nat(N) :-
    nat_(0, N).

nat_(N, N).
nat_(N0, N) :-
    N1 #= N0 + 1,
    nat_(N1, N).

n_factorial(0, 1).
n_factorial(N, F) :-
    F #= N * F1,
    N1 #= N - 1,
    n_factorial(N1, F1).

pmod(G, X, Y, Z) :- G = (X mod Y #= Z).
pplus(G, X, Y, Z) :- G = (X + Y #= Z).
rel(G, X, Y) :- G = (X #=< Y).

operation(2, Op, [X, Y], G) :-
    call(Op, G, X, Y).

operation(3, Op, [X, Y, Z], G) :-
    call(Op, G, X, Y, Z).

/*
operation(Op, Vs, G) :-
    Goal =.. [Op, G|Vs],
    call(Goal).
% */

conjonction(G1, G2, G) :-
    G = (G2, G1).

run :-
    $nat(N),
    NegN #= -N,
    Settings = [Nv, Niv, Nr, Nm],

    Settings ins 0..N,
    Nm #> 0, % Testing Powers.

    label([Nv]),
    length(Vs, Nv),
    Vs ins inf..sup, % No labeling.
    (   Nv > 1 ->
        bagof(Pr, (length(Pr, 2), arrangement(Vs, Pr)), V2s) % No repetitions.
    ;   % Allow repetitions.
        bagof(Pr, (length(Pr, 2), arrangementr(Vs, Pr)), V2s)
    ),
    bagof(Pr, (length(Pr, 3), arrangementr(Vs, Pr)), V3s),

    (   Nv > 1 ->
        Nr #=< Nv
    ;   Nr #= 0
    ),
    label([Nm, Nr]),
    length(Gs1, Nm),
    (   Nv > 1 ->
        length(Gs3, Nr)
    ;   length(Gs3, 0)
    ),
    append(Gs3, Gs1, Gs4),

    length(MVs, Nm),
    combinationr(V3s, MVs),
    maplist(operation(3, pmod), MVs, Gs1),

    (   Nv > 1 ->
        length(RVs, Nr),
        combination(V2s, RVs),
        maplist(operation(2, rel), RVs, Gs3)
    ;   true
    ),

    label([Niv]),
    length(Vs1, Niv),
    length(Vs2, Niv),
    combination(Vs, Vs1),
    Vs2 ins NegN..N,
    label(Vs2),
    Vs1 = Vs2,

    % portray_clause([N, Settings, Vs, Gs4]), nl,
    catch(
        findall(
            Ds,
            (   permutation(Gs4, Gs),
                foldl(conjonction, Gs, true, G),
                call(G),
                maplist(fd_dom, Vs, Ds)
            ),
            Dss
        ),
        E,
        (   write('caugth: '), write(E), nl,
            portray_clause([N, Settings, Vs, Gs4, Dss]), nl,
            false
        )
    ),
    length(Dss, Dn),
    length(Gs4, Gs4n),
    (   Dn == 0 -> true % All false.
    ;   (   n_factorial(Gs4n, Dn) -> true
        ;   write('Not a factorial: '), write([Gs4n, Dn]), nl,
            portray_clause([N, Settings, Vs, Gs4, Dss]), nl,
            *halt(1)
        )
    ),
    (   \+ maplist(=(_), Dss) ->
        write('Bound issue:'), nl,
        write(Dss), nl,
        transpose(Dss, Dss1),
        maplist(sort, Dss1, Dss2),
        portray_clause(Dss2),
        portray_clause([N, Settings, Vs, Gs4]), nl,
        % Not easy to solve due to the fact that multiple variables
        % can not have the right bound.
        *halt(1)
    ;   true
    ),
    false.
