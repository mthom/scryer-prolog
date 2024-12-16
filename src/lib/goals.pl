:- module(goals, [
        call_unifiers/2,
        expand_subgoals/3
]).

:- use_module(library(lists), [maplist/3,maplist/4]).
:- use_module(library(loader), [expand_goal/3]).
:- use_module(library(lambda)).

:- meta_predicate(call_unifiers(0, ?)).

%% call_unifiers(?G_0, -Us).
%
% `Us` is a list of unifiers that are equivalent to calling G_0.
call_unifiers(G_0, Us) :-
    term_variables(G_0, GVs),
    copy_term(G_0/GVs, H_0/HVs),
    H_0,
    maplist(_+\A^B^(A=B)^true, GVs, HVs, Us).


%% expand_sub_goals(?M, ?A, -X).
%
% Similar to expand_goal/3, but recursively tries to expand every sub-term.
% TODO: Try to make it more generic, don't rely on (#)/2.
expand_subgoals(M, A, X) :-
    nonvar(A) ->
        (   functor(A, (#), 2) ->
            expand_goal(A, M, X)
        ;   A =.. [F|Args],
            maplist(expand_subgoals(M), Args, XArgs),
            X =.. [F|XArgs]
        )
    ;   A = X.
