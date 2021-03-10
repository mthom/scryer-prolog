:- use_module(library(debug)).
:- use_module(library(clpz)).
% :- use_module('../../lib/clpz').
:- use_module(library(format)).
:- use_module(library(lists)).
:- use_module(library(time)).
:- use_module(combination).
:- use_module(permutation).

nat(N) :-
    nat(0, N).

nat(N, N).
nat(N0, N) :-
    N1 is N0 + 1,
    nat(N1, N).

bound(X, L, U) :- L #=< X, X #=< U.

/*
 * This test stops only if there is an mistake in the propagator.
 * This test is general enough to quickly test other operators.
 * This test does not test if permutating the clause changes the final result.
 */
run(N) :-
    Vs = [X0, X1, X2, L0, L1, L2, U0, U1, U2],

    Xs = [X0, X1, X2],
    Ls = [L0, L1, L2],
    Us = [U0, U1, U2],

    Bs = [L0, L1, L2, U0, U1, U2],

    % maplist(#=<, Ls, Us),
    maplist(#\=(0), [X1, L1, U1]),
    maplist(bound, Xs, Ls, Us),

    % nat(N),
    format("~d\n", [N]),
    NegN is -N - 1,
    Domain = NegN..N,

    I in 0..6,
    indomain(I),
    length(Is, I),
    combination(Bs, Is),
    Is ins Domain,
    labeling([], Is),

    (   % Every solution is generated and only solution.
        X2 #= X0 mod X1,
        Xs ins Domain,
        labeling([], Xs),
        (   catch(X2 is X0 mod X1, _, false) ->
            true
        ;   format("~q\n", [error0([N, Vs, Ys])]) % Found a non-solution.
        )
    ;   % Every solution is found and only solution.
        copy_term(Xs, Ys),
        Ys = [Y0, Y1, Y2],
        Ys ins Domain,
        labeling([], Ys),
        (   catch(Y2 is Y0 mod Y1, _, false) ->
            (   X2 #= X0 mod X1 ->
                (   maplist(=, Ys, Xs) ->
                    % Find a specific solution.
                    true
                ;   format("~q\n", [error1([N, Vs, Ys])])
                )
            ;   format("~q\n", [error2([N, Vs, Ys])])
            )
        ;   X2 #= X0 mod X1,
            (   maplist(=, Ys, Xs) ->
                % Found a non-solution.
                format("~q\n", [error3([N, Vs, Ys])])
            ;   true
            )
        )
    ),
    false.
