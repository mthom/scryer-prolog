:- module('$atts', []).


driver(Vars, Values) :-
    iterate(Vars, Values, ListOfListsOfGoalLists),
    !,
    call_goals(ListOfListsOfGoalLists),
    '$return_from_verify_attr'.

iterate([Var|VarBindings], [Value|ValueBindings], [ListOfGoalLists | ListsCubed]) :-
    '$get_attr_list'(Var, Ls),
    call_verify_attributes(Ls, Var, Value, ListOfGoalLists),
    '$redo_attr_var_binding'(Var, Value),
    iterate(VarBindings, ValueBindings, ListsCubed).
iterate([], [], []).


gather_modules(Attrs, []) :- var(Attrs), !.
gather_modules([Module:_|Attrs], [Module|Modules]) :-
    gather_modules(Attrs, Modules).

call_verify_attributes(Attrs, _, _, []) :-
    var(Attrs), !.
call_verify_attributes([], _, _, []).
call_verify_attributes([Attr|Attrs], Var, Value, ListOfGoalLists) :-
    gather_modules([Attr|Attrs], Modules0),
    sort(Modules0, Modules),
    verify_attrs(Modules, Var, Value, ListOfGoalLists).


verify_attrs([Module|Modules], Var, Value, [Module-Goals|ListOfGoalLists]) :-
    catch(Module:verify_attributes(Var, Value, Goals),
          error(evaluation_error((Module:verify_attributes)/3), verify_attributes/3),
          Goals = []),
    verify_attrs(Modules, Var, Value, ListOfGoalLists).
verify_attrs([], _, _, []).


call_goals([ListOfGoalLists | ListsCubed]) :-
    call_goals_0(ListOfGoalLists),
    call_goals(ListsCubed).
call_goals([]).

call_goals_0([Module-GoalList | GoalLists]) :-
    (  var(GoalList),
       throw(error(instantiation_error, call_goals_0/1))
    ;  true
    ),
    call_goals_1(GoalList, Module),
    call_goals_0(GoalLists).
call_goals_0([]).

call_goals_1([Goal | Goals], Module) :-
    expand_goal(Goal, Module, Goal1), % TODO: remove this when goal expansions are added to call/N.
    call(Module:Goal1),
    call_goals_1(Goals, Module).
call_goals_1([], _).
