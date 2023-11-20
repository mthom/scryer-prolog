/**
Provides predicate `dif/2`. `dif/2` is a constraint that is true only if both of its
arguments are different terms.
*/

:- module(dif, [dif/2]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(lists), [append/3, maplist/3]).

:- attribute dif/1.

put_dif_att(Var, X, Y) :-
    (   get_atts(Var, +dif(Z)) ->
	    sort([X \== Y | Z], NewZ),
	    put_atts(Var, +dif(NewZ))
    ;   put_atts(Var, +dif([X \== Y]))
    ).

dif_set_variables([], _, _).
dif_set_variables([Var|Vars], X, Y) :-
    put_dif_att(Var, X, Y),
    dif_set_variables(Vars, X, Y).

remove_goal([], _, []).
remove_goal([G0|G0s], Goal0, Goals) :-
    (   G0 == Goal0 ->
        remove_goal(G0s, Goal0, Goals)
    ;   Goals = [G0|Goals1],
        remove_goal(G0s, Goal0, Goals1)
    ).

vars_remove_goal([], _).
vars_remove_goal([Var|Vars], Goal0) :-
    (  get_atts(Var, +dif(Goals0)) ->
       remove_goal(Goals0, Goal0, Goals),
       (   Goals = [] ->
           put_atts(Var, -dif(_))
       ;   put_atts(Var, +dif(Goals))
       )
    ;  true
    ),
    vars_remove_goal(Vars, Goal0).

reinforce_goal(Goal0, Goal) :-
    Goal = (
        term_variables(Goal0, Vars),
        dif:vars_remove_goal(Vars, Goal0),
        Goal0 = (L \== R),
        dif:dif(L, R)
    ).

append_goals([], _).
append_goals([Var|Vars], Goals) :-
    (   get_atts(Var, +dif(VarGoals)) ->
	    append(Goals, VarGoals, NewGoals0),
	    sort(NewGoals0, NewGoals)
    ;   NewGoals = Goals
    ),
    put_atts(Var, +dif(NewGoals)),
    append_goals(Vars, Goals).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, +dif(Goals0)) ->
	    term_variables(Value, ValueVars),
	    append_goals(ValueVars, Goals0),
        maplist(reinforce_goal, Goals0, Goals)
    ;   Goals = []
    ).

%% dif(?X, ?Y).
%
% True iff X and Y are different terms. Unlike `\=/2`, `dif/2` is more declarative because if X and Y can
% unify but they're not yet equal, the decision is delayed, and prevents X and Y to become equal later.
% Examples:
%
% ```
% ?- dif(a, a).
%    false.
% ?- dif(a, b).
%    true.
% ?- dif(X, b).
%    dif:dif(X,b).
% ?- dif(X, b), X = b.
%    false.
% ```
dif(X, Y) :-
    X \== Y,
    (   X \= Y -> true
    ;   term_variables(dif(X,Y), Vars),
        dif_set_variables(Vars, X, Y)
    ).

gather_dif_goals(_, []) --> [].
gather_dif_goals(V, [(X \== Y) | Goals]) -->
    (  { term_variables(X-Y, [V0 | _]),
         V == V0 } ->
       [dif:dif(X, Y)]
    ;  []
    ),
    gather_dif_goals(V, Goals).

attribute_goals(X) -->
    { get_atts(X, +dif(Goals)) },
    gather_dif_goals(X, Goals),
    { put_atts(X, -dif(_)) }.
