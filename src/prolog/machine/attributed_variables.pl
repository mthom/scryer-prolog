driver(Vars, Values) :-
    iterate(Vars, Values, ListOfListsOfGoalLists),
    '$redo_attr_var_bindings', %% the bindings list is emptied here.
    call_goals(ListOfListsOfGoalLists),
    '$restore_p_from_sfcp'.

iterate([Var|VarBindings], [Value|ValueBindings], [ListOfGoalLists | ListsCubed]) :-
    '$get_attr_list'(Var, Ls),
    call_verify_attributes(Ls, Var, Value, ListOfGoalLists),
    iterate(VarBindings, ValueBindings, ListsCubed).
iterate([], [], []).

call_verify_attributes(Attrs, _, _, []) :-
    var(Attrs), !.
call_verify_attributes([Attr|Attrs], Var, Value, [Goals|ListOfGoalLists]) :-
    '$module_of'(M, Attr), % write the owning module Attr to M.
    catch(M:verify_attributes(Var, Value, Goals),
          error(evaluation_error((M:verify_attributes)/3), verify_attributes/3),
          Goals = []),
    call_verify_attributes(Attrs, Var, Value, ListOfGoalLists).

call_goals([ListOfGoalLists | ListsCubed]) :-
    call_goals_0(ListOfGoalLists),
    call_goals(ListsCubed).
call_goals([]).

call_goals_0([GoalList | GoalLists]) :-
    (  var(GoalList), throw(error(instantiation_error, call_goals_0/1))
    ;  true
    ),
    call_goals_1(GoalList),
    call_goals_0(GoalLists).
call_goals_0([]).

call_goals_1([Goal | Goals]) :-
    call(Goal),
    call_goals_1(Goals).
call_goals_1([]).
