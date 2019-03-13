:- module(dif, [dif/2]).

:- use_module(library(atts)).

:- attribute dif/1.

non_unif_member([X \== Y | Z], V, W) :-
    (   X == V, Y == W -> true
    ;   non_unif_member(Z, V, W)
    ).

put_dif_att(Var, X, Y) :-
    (   get_atts(Var, +dif(Z)) ->
	(   non_unif_member(Z, X, Y) -> true
	;   put_atts(Var, +dif([X \== Y | Z]))
	)
    ;   put_atts(Var, +dif([X \== Y]))
    ).

dif_set_variables([], _, _).
dif_set_variables([Var|Vars], X, Y) :-
    put_dif_att(Var, X, Y),
    dif_set_variables(Vars, X, Y).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, +dif(Goals)) -> true
    ;   Goals = []
    ).

% Probably the world's worst dif/2 implementation. I'm open to
% suggestions for improvement.

dif(X, Y) :- X \== Y,
             (   term_variables(X, XVars), term_variables(Y, YVars),
	         dif_set_variables(XVars, X, Y),
		 dif_set_variables(YVars, X, Y)
	     ).

gather_dif_goals([], _).
gather_dif_goals([(X \== Y) | Goals0], [dif(X, Y) | Goals]) :-
    gather_dif_goals(Goals0, Goals).

attribute_goals(X, Goals) :-
    get_atts(X, +dif(Goals0)),
    gather_dif_goals(Goals0, Goals).
