/**
Provides the predicate `when/2`.
*/

:- module(when, [when/2]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(lambda)).

:- attribute when_list/1.

:- meta_predicate(when(+, 0)).

%% when(Condition, Goal).
%
% Executes Goal when Condition becomes true.
when(Condition, Goal) :-
    (   when_condition(Condition) ->
        (   Condition ->
            Goal
        ;   term_variables(Condition, Vars),
            maplist(
                [Goal, Condition]+\Var^(
                    get_atts(Var, when_list(Whens0)) ->
                    Whens = [when(Condition, Goal) | Whens0],
                    put_atts(Var, when_list(Whens))
                ;   put_atts(Var, when_list([when(Condition, Goal)]))
                ),
                Vars
            )
        )
    ;   throw(error(domain_error(when_condition, Condition),_))
    ).

when_condition(Cond) :-
    % Should this be delayed?
    var(Cond), !, throw(error(instantiation_error,when_condition/1)).
when_condition(ground(_)).
when_condition(nonvar(_)).
when_condition((A, B)) :-
    when_condition(A),
    when_condition(B).
when_condition((A ; B)) :-
    when_condition(A),
    when_condition(B).

remove_goal([], _, []).
remove_goal([G0|G0s], Goal, Goals) :-
    (   G0 == Goal ->
        remove_goal(G0s, Goal, Goals)
    ;   Goals = [G0|Goals1],
        remove_goal(G0, Goal, Goals1)
    ).

vars_remove_goal(Vars, Goal) :-
    maplist(
        Goal+\Var^(
            get_atts(Var, when_list(Whens0)) ->
            remove_goal(Whens0, Goal, Whens),
            (   Whens = [] ->
                put_atts(Var, -when_list(_))
            ;   put_atts(Var, when_list(Whens))
            )
        ;   true
        ),
        Vars
    ).

reinforce_goal(Goal0, Goal) :-
    Goal = (
        term_variables(Goal0, Vars),
        when:vars_remove_goal(Vars, Goal0),
        Goal0
    ).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, when_list(Whens)) ->
        (   var(Value) ->
            (   get_atts(Value, when_list(WhensValue)) ->
                append(Whens, WhensValue, WhensNew),
                put_atts(Value, when_list(WhensNew))
            ;   put_atts(Value, when_list(Whens))
            ),
            Goals = []
        ;   maplist(reinforce_goal, Whens, Goals)
        )
    ;   Goals = []
    ).

gather_when_goals([], _) --> [].
gather_when_goals([When|Whens], Var) -->
    ( { term_variables(When, [V0|_]), Var == V0 } ->
        [when:When]
    ;   []
    ),
    gather_when_goals(Whens, Var).

attribute_goals(Var) -->
    { get_atts(Var, when_list(Whens)) },
    gather_when_goals(Whens, Var),
    { put_atts(Var, -when_list(_)) }.
