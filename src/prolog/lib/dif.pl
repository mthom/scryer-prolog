:- module(dif, [dif/2]).

:- use_module(library(atts)).
:- use_module(library(ordsets)).

:- attribute dif/1.

put_dif_att(Var, X, Y) :-
    (   get_atts(Var, +dif(Z)) ->
	ord_add_element(Z, X \== Y, NewZ),
	(   Z == NewZ -> true
	;   put_atts(Var, +dif(NewZ))
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
