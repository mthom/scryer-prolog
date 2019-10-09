driver(QueryVars, AttrVars) :-
    gather_modules(AttrVars, Modules0, _),
    sort(Modules0, Modules),
    call_project_attributes(Modules, QueryVars, AttrVars),
    call_attribute_goals(Modules, QueryVars),
    call_attribute_goals(Modules, AttrVars),
    '$return_from_attribute_goals'.

enqueue_goals(Goals0) :-
    nonvar(Goals0),
    Goals0 = [Goal | Goals],
    nonvar(Goal),
    !,
    '$enqueue_attribute_goal'(Goal),
    enqueue_goals(Goals).
enqueue_goals(_).

'$print_project_attributes_exception'(Module, E) :-
    (  E = error(evaluation_error((Module:project_attributes)/2), project_attributes/2) ->
       true
    ;  write_term('caught: ', [quoted(false)]),
       writeq(E),
       nl
    ).

call_project_attributes([], _, _).
call_project_attributes([Module|Modules], QueryVars, AttrVars) :-
    (   catch(Module:project_attributes(QueryVars, AttrVars),
	      E,
	      '$print_project_attributes_exception'(Module, E))
    ->  true
    ;   true
    ),
    call_project_attributes(Modules, QueryVars, AttrVars).

call_attribute_goals([], _).
call_attribute_goals([Module | Modules], AttrVars) :-
    call_goals(AttrVars, Module, Goals),
    enqueue_goals(Goals),
    call_attribute_goals(Modules, AttrVars).

'$print_attribute_goals_exception'(Module, E) :-
    (  E = error(evaluation_error((Module:attribute_goals)/3), attribute_goals/3)
    -> true
    ;  write_term('caught: ', [quoted(false)]),
       writeq(E),
       nl
    ).

call_goals([], _, []).
call_goals([AttrVar|AttrVars], Module, Goals) :-
    (  catch((  Module:attribute_goals(AttrVar, Goals, RGoals0),
	        atts:'$default_attr_list'(Module, AttrVar, RGoals0, RGoals)
	     ),
	     E,
	     (  '$print_attribute_goals_exception'(Module, E),
		atts:'$default_attr_list'(Module, AttrVar, Goals, RGoals)
	     ))
    -> true
    ;  atts:'$default_attr_list'(Module, AttrVar, Goals, RGoals)
    ),
    call_goals(AttrVars, Module, RGoals).

gather_modules([], [], _).
gather_modules([AttrVar|AttrVars], Modules, Modules0) :-
    '$get_attr_list'(AttrVar, Attrs),
    gather_modules_for_attrs(Attrs, Modules, Modules0),
    gather_modules(AttrVars, Modules0, _).

gather_modules_for_attrs(Attrs, Modules, Modules) :-
    var(Attrs), !.
gather_modules_for_attrs([Attr|Attrs], [Module|Modules], Modules0) :-
    '$module_of'(Module, Attr),
    gather_modules_for_attrs(Attrs, Modules, Modules0).
