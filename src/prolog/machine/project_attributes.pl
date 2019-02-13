:- use_module(library(dcgs)).

driver(QueryVars, AttrVars) :-
    phrase(gather_modules(AttrVars), Modules0),
    sort(Modules0, Modules),
    call_project_attributes(Modules, QueryVars, AttrVars),
    call_attribute_goals(QueryVars),
    call_attribute_goals(AttrVars).

call_project_attributes([], _, _).
call_project_attributes([Module|Modules], QueryVars, AttrVars) :-
    (   catch(Module:project_attributes(QueryVars, AttrVars),
	      error(evaluation_error((Module:project_attributes/2), project_attributes/2)),
	      true) -> true
    ;   true
    ),
    call_project_attributes(Modules, QueryVars, AttrVars).

call_attribute_goals([]).
call_attribute_goals([AttrVar | AttrVars]) :-
    (   '$get_attr_list'(AttrVar, Ls) -> call_goals(Ls, AttrVar)
    ;   true
    ),
    call_attribute_goals(AttrVars).

call_goals(Ls, _) :- var(Ls), !.
call_goals([Attr|Attrs], X) :-
    '$module_of'(Module, Attr),
    (   catch(Module:attribute_goals(X, Goal),
	      error(evaluation_error((Module:attribute_goals/2), attribute_goals/2)),
	      writeq(Goal)) -> true
    ;   true
    ),
    call_goals(Attrs, X).

gather_modules([]) --> [].
gather_modules([AttrVar|AttrVars]) -->
    { '$get_attr_list'(AttrVar, Attrs) },
    gather_modules_for_attrs(Attrs),
    gather_modules(AttrVars).

gather_modules_for_attrs(Attrs) --> { var(Attrs), ! }.
gather_modules_for_attrs([Attr|Attrs]) -->
    { '$module_of'(Module, Attr) },
    [Module],
    gather_modules_for_attrs(Attrs).
