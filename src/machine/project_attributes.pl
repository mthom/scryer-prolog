:- module('$project_atts', [copy_term/3]).

:- use_module(library(dcgs)).
:- use_module(library(error), [can_be/2]).
:- use_module(library(lambda)).
:- use_module(library(lists), [foldl/4, maplist/2]).

project_attributes(QueryVars, AttrVars) :-
    phrase(gather_attr_modules(AttrVars), Modules0),
    sort(Modules0, Modules),
    call_project_attributes(Modules, QueryVars, AttrVars).

'$print_project_attributes_exception'(Module, E) :-
    (  (  E = error(existence_error(procedure, project_attributes/2), _)
       ;  E = error(evaluation_error((Module:project_attributes)/2), _)
       )  ->
       true
    ;  loader:write_error(E),
       nl
    ).

call_project_attributes([], _, _).
call_project_attributes([Module|Modules], QueryVars, AttrVars) :-
    (   catch(Module:project_attributes(QueryVars, AttrVars),
	          E,
	          '$project_atts':'$print_project_attributes_exception'(Module, E)
	         )
    ->  true
    ;   true
    ),
    call_project_attributes(Modules, QueryVars, AttrVars).

'$print_attribute_goals_exception'(Module, E) :-
    (  E = error(evaluation_error((Module:attribute_goals)/3), attribute_goals/3)
    ;  E = error(existence_error(procedure, attribute_goals/3), attribute_goals/3)
    -> true
    ;  loader:write_error(E),
       nl
    ).

call_query_var_goals([], _, []).
call_query_var_goals([AttrVar|AttrVars], Module, Goals) :-
    (  catch((  Module:attribute_goals(AttrVar, Goals, RGoals0),
	            atts:'$default_attr_list'(Module, AttrVar, RGoals0, RGoals)
	         ),
	         E,
	         (  '$project_atts':'$print_attribute_goals_exception'(Module, E),
		        atts:'$default_attr_list'(Module, AttrVar, Goals, RGoals)
	         ))
    -> true
    ;  atts:'$default_attr_list'(Module, AttrVar, Goals, RGoals)
    ),
    call_query_var_goals(AttrVars, Module, RGoals).

call_attr_var_goals([], _, []).
call_attr_var_goals([AttrVar|AttrVars], Module, Goals) :-
    (  catch(Module:attribute_goals(AttrVar, Goals, RGoals),
	         E,
	         '$project_atts':'$print_attribute_goals_exception'(Module, E)
	        )
    -> true
    ;  true
    ),
    call_attr_var_goals(AttrVars, Module, RGoals).


module_prefixed_goals([], _, Gs, Gs).
module_prefixed_goals([G|Gs], Module, [MG|MGs], TailGs) :-
    (  G = _:_ -> MG = G
    ;  MG = Module:G
    ),
    module_prefixed_goals(Gs, Module, MGs, TailGs).

call_attribute_goals_with_module_prefix([], _, _, []).
call_attribute_goals_with_module_prefix([Module | Modules], GoalCaller, AttrVars, Goals) :-
    call(GoalCaller, AttrVars, Module, Goals0),
    module_prefixed_goals(Goals0, Module, Goals, Gs),
    call_attribute_goals_with_module_prefix(Modules, GoalCaller, AttrVars, Gs).

gather_attr_modules([]) --> [].
gather_attr_modules([AttrVar|AttrVars]) -->
    { '$get_attr_list'(AttrVar, Attrs) },
    copy_attribute_modules(Attrs),
    gather_attr_modules(AttrVars).

copy_attribute_modules(Attrs) -->
    { var(Attrs) },
    !.
copy_attribute_modules([Module:_|Attrs]) -->
    [Module],
    copy_attribute_modules(Attrs).

attribute_goals_or_fail(M, V, V0, V1) :-
    (  catch(M:attribute_goals(V, V0, V1),
             E,
             '$project_atts':'$print_attribute_goals_exception'(M, E)
            ) ->
       true
    ;  V0 = V1
    ).

gather_residual_goals([]) --> [].
gather_residual_goals([V|Vs]) -->
    { '$get_attr_list'(V, Attrs),
      phrase(copy_attribute_modules(Attrs), Modules0),
      sort(Modules0, Modules) },
    foldl(V+\M^attribute_goals_or_fail(M, V), Modules),
    gather_residual_goals(Vs).

delete_all_attributes_from_var(V) :- '$delete_all_attributes_from_var'(V).

copy_term(Term, Copy, Gs) :-
   can_be(list, Gs),
   findall(Term-Rs, term_residual_goals(Term,Rs), [Copy-Gs]),
   (  var(Gs) ->
      Gs = []
   ;  true
   ).

term_residual_goals(Term,Rs) :-
    '$term_attributed_variables'(Term, Vs),
    phrase(gather_residual_goals(Vs), Rs),
    maplist(delete_all_attributes_from_var, Vs).
