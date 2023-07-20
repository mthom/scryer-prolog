:- module('$toplevel', [argv/1,
                        copy_term/3]).

:- use_module(library(atts), [call_residue_vars/2]).
:- use_module(library(charsio)).
:- use_module(library(error)).
:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lambda)).
:- use_module(library(lists)).
:- use_module(library(si)).

:- use_module(library('$project_atts')).
:- use_module(library('$atts')).

:- dynamic(disabled_init_file/0).

:- dynamic(argv/1).


arg_type(g).
arg_type(t).
arg_type(g(_)).
arg_type(t(_)).

trailing_period_is_ambiguous(Value) :-
    atom(Value),
    atom_chars(Value, ValueChars),
    list_last_item(ValueChars, Char),
    ValueChars \== ['.'],
    graphic_token_char(Char).

graphic_token_char(C) :-
    memberchk(C, ['#', '$', '&', '*', '+', '-', '.', ('/'), ':',
                  '<', '=', '>', '?', '@', '^', '~', ('\\')]).

needs_bracketing(Value, Op) :-
    catch((functor(Value, F, _),
           current_op(EqPrec, EqSpec, Op),
           current_op(FPrec, _, F)),
          _,
          false),
    (  EqPrec < FPrec ->
       true
    ;  FPrec > 0, F == Value, graphic_token_char(F) ->
       true
    ;  F \== '.', '$quoted_token'(F) ->
       true
    ;  EqPrec == FPrec,
       memberchk(EqSpec, [fx,xfx,yfx])
    ).

write_goal(G, VarList, MaxDepth) :-
    (  G = (Var = Value) ->
       (  var(Value) ->
          select((Var = _), VarList, NewVarList)
       ;  VarList = NewVarList
       ),
       write(Var),
       write(' = '),
       (  needs_bracketing(Value, (=)) ->
          write('('),
          write_term(Value, [quoted(true), variable_names(NewVarList), max_depth(MaxDepth)]),
          write(')')
       ;  write_term(Value, [quoted(true), variable_names(NewVarList), max_depth(MaxDepth)])
       )
    ;  G == [] ->
       write('true')
    ;  write_term(G, [quoted(true), variable_names(VarList), max_depth(MaxDepth)])
    ).


write_last_goal(G, VarList, MaxDepth) :-
    (  G = (Var = Value) ->
       (  var(Value) ->
          select((Var = _), VarList, NewVarList)
       ;  VarList = NewVarList
       ),
       write(Var),
       write(' = '),
       (  needs_bracketing(Value, (=)) ->
          write('('),
          write_term(Value, [quoted(true), variable_names(NewVarList), max_depth(MaxDepth)]),
          write(')')
       ;  write_term(Value, [quoted(true), variable_names(NewVarList), max_depth(MaxDepth)]),
          (  trailing_period_is_ambiguous(Value) ->
             write(' ')
          ;  true
          )
       )
    ;  G == [] ->
       write('true')
    ;  write_term(G, [quoted(true), variable_names(VarList), max_depth(MaxDepth)])
    ).

write_eq((G1, G2), VarList, MaxDepth) :-
    !,
    write_goal(G1, VarList, MaxDepth),
    write(', '),
    write_eq(G2, VarList, MaxDepth).
write_eq(G, VarList, MaxDepth) :-
    write_last_goal(G, VarList, MaxDepth).

term_variables_under_max_depth(Term, MaxDepth, Vars) :-
    '$term_variables_under_max_depth'(Term, MaxDepth, Vars).

write_eqs_and_read_input(B, VarList) :-
    gather_query_vars(VarList, OrigVars),
    % one layer of depth added for (=/2) functor
    '$term_variables_under_max_depth'(OrigVars, 22, Vars0),
    '$term_attributed_variables'(VarList, AttrVars),
    '$project_atts':project_attributes(Vars0, AttrVars),
    copy_term(AttrVars, AttrVars, AttrGoals),
    term_variables(AttrGoals, AttrGoalVars),
    append([Vars0, AttrGoalVars, AttrVars], Vars),
    charsio:extend_var_list(Vars, VarList, NewVarList, fabricated),
    '$get_b_value'(B0),
    gather_equations(NewVarList, OrigVars, Equations),
    append(Equations, AttrGoals, Goals),
    % one layer of depth added for (=/2) functor
    maplist(\Term^Vs^term_variables_under_max_depth(Term, 22, Vs), Equations, EquationVars),
    % maplist(term_variables_under_max_depth(22), Equations, EquationVars),
    append([AttrGoalVars | EquationVars], Vars1),
    term_variables(Vars1, Vars2), % deduplicate vars of Vars1 but preserve their order.
    charsio:extend_var_list(Vars2, VarList, NewVarList0, fabricated),
    bb_get('$answer_count', Count),
    (   Count =:= 0 ->
        write('   ')
    ;   true
    ),
    Count1 is Count + 1,
    bb_put('$answer_count', Count1),
    (  B0 == B ->
       (  Goals == [] ->
          write('true.'), nl
       ;  loader:thread_goals(Goals, ThreadedGoals, (',')),
          write_eq(ThreadedGoals, NewVarList0, 20),
          write('.'),
          nl
       )
    ;  loader:thread_goals(Goals, ThreadedGoals, (',')),
       write_eq(ThreadedGoals, NewVarList0, 20),
       read_input(ThreadedGoals, NewVarList0)
    ).

read_input(ThreadedGoals, NewVarList) :-
    (  bb_get('$report_all', true) ->
       C = n
    ;  bb_get('$report_n_more', N), N > 1 ->
       N1 is N - 1,
       bb_put('$report_n_more', N1),
       C = n
    ;  get_single_char(C)
    ),
    (  C = w ->
       nl,
       write('   '),
       write_eq(ThreadedGoals, NewVarList, 0),
       read_input(ThreadedGoals, NewVarList)
    ;  C = p ->
       nl,
       write('   '),
       write_eq(ThreadedGoals, NewVarList, 20),
       read_input(ThreadedGoals, NewVarList)
    ;  member(C, [';', ' ', n]) ->
       nl, write(';  '), false
    ;  C = h ->
       help_message,
       read_input(ThreadedGoals, NewVarList)
    ;  member(C, ['\n', .]) ->
       nl, write(';  ... .'), nl
    ;  C = a ->
       bb_put('$report_all', true),
       nl, write(';  '), false
    ;  C = f ->
       bb_get('$answer_count', Count),
       More is 5 - Count mod 5,
       bb_put('$report_n_more', More),
       nl, write(';  '), false
    ;  read_input(ThreadedGoals, NewVarList)
    ).

gather_query_vars([_ = Var | Vars], QueryVars) :-
    (  var(Var) ->
       QueryVars = [Var | QueryVars0],
       gather_query_vars(Vars, QueryVars0)
    ;
    gather_query_vars(Vars, QueryVars)
    ).
gather_query_vars([], []).

gather_equations([], _, []).
gather_equations([Var = Value | Pairs], OrigVarList, Goals) :-
    (  var(Value) ->
       (  eq_member(Value, OrigVarList),
          select_all(Pairs, Var, Value, [_ | VarEqs], NewPairs) ->
          append([Var = Value | VarEqs], Goals0, Goals),
          gather_equations(NewPairs, OrigVarList, Goals0)
       ;
       gather_equations(Pairs, OrigVarList, Goals)
       )
    ;
    Goals = [Var = Value | Goals0],
    gather_equations(Pairs, OrigVarList, Goals0)
    ).

print_exception(E) :-
    (  E == error('$interrupt_thrown', repl) -> nl % print the
                                                   % exception on a
                                                   % newline to evade
                                                   % "^C".
    ;  true
    ),
    loader:write_error(E),
    nl.


run_input_once :-
    bb_put('$report_all', true),
    catch(read_and_match_all_results, E, print_exception(E)).

read_and_match_all_results :-
    '$read_query_term'(_, Term, _, _, VarList),
    bb_put('$answer_count', 0),
    submit_query_and_print_all_results(Term, VarList).

submit_query_and_print_all_results(Term, VarList) :-
    '$get_b_value'(B),
    bb_put('$report_all', true),
    bb_put('$report_n_more', 0),
    call(user:Term),
    write_eqs_and_read_input(B, VarList),
    !.
submit_query_and_print_all_results(_, _) :-
    (   bb_get('$answer_count', 0) ->
        write('   ')
    ;   true
    ),
    write('false.'),
    nl.
