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

load_scryerrc :-
    (  '$home_directory'(HomeDir) ->
       append(HomeDir, "/.scryerrc", ScryerrcFile),
       (  file_exists(ScryerrcFile) ->
          atom_chars(ScryerrcFileAtom, ScryerrcFile),
          catch(use_module(ScryerrcFileAtom), E, print_exception(E))
       ;  true
       )
    ;  true
    ).

:- dynamic(argv/1).

'$repl'([_|Args0]) :-
    \+ argv(_),
    (   append(Args1, ["--"|Args2], Args0) ->
        asserta('$toplevel':argv(Args2)),
        Args = Args1
    ;   asserta('$toplevel':argv([])),
        Args = Args0
    ),
    delegate_task(Args, []),
    (\+ disabled_init_file -> load_scryerrc ; true),
    repl.
'$repl'(_) :-
    (   \+ argv(_) -> asserta('$toplevel':argv([]))
    ;   true
    ),
    load_scryerrc,
    repl.

delegate_task([], []).
delegate_task([], Goals0) :-
    reverse(Goals0, Goals),
    (\+ disabled_init_file -> load_scryerrc ; true),
    run_goals(Goals),
    repl.

delegate_task([Arg0|Args], Goals0) :-
    (   member(Arg0, ["-h", "--help"]) -> print_help
    ;   member(Arg0, ["-v", "--version"]) -> print_version
    ;   member(Arg0, ["-g", "--goal"]) -> gather_goal(g, Args, Goals0)
    ;   member(Arg0, ["-f"]) -> disable_init_file
    ;   member(Arg0, ["--no-add-history"]) -> ignore_machine_arg
    ;   atom_chars(Mod, Arg0),
        catch(consult(Mod), E, print_exception(E))
    ),
    delegate_task(Args, Goals0).

print_help :-
    write('Usage: scryer-prolog [OPTIONS] [FILES] [-- ARGUMENTS]'),
    nl, nl,
    write('Options:'), nl,
    write('   -h, --help             '),
    write('Display this message'), nl,
    write('   -v, --version          '),
    write('Print version information and exit'), nl,
    write('   -g, --goal GOAL        '),
    write('Run the query GOAL'), nl,
    write('   -f                     '),
    write('Fast startup. Do not load initialization file (~/.scryerrc)'), nl,
    write('   --no-add-history       '),
    write('Prevent adding input to history file (~/.scryer_history)'), nl,
    % write('                        '),
    halt.

print_version :-
    '$scryer_prolog_version'(Version),
    write(Version), nl,
    halt.

gather_goal(Type, Args0, Goals) :-
    length(Args0, N),
    (   N < 1 -> print_help, halt
    ;   true
    ),
    [Gs1|Args] = Args0,
    Gs =.. [Type, Gs1],
    delegate_task(Args, [Gs|Goals]).

disable_init_file :-
    asserta('disabled_init_file').

ignore_machine_arg.

arg_type(g).
arg_type(t).
arg_type(g(_)).
arg_type(t(_)).

ends_with_dot(Ls0) :-
    reverse(Ls0, Ls),
    layout_and_dot(Ls).

layout_and_dot(['.'|_]).
layout_and_dot([C|Cs]) :-
    char_type(C, layout),
    layout_and_dot(Cs).

run_goals([]).
run_goals([g(Gs0)|Goals]) :-
    (   ends_with_dot(Gs0) -> Gs1 = Gs0
    ;   append(Gs0, ".", Gs1)
    ),
    read_from_chars(Gs1, Goal),
    (   catch(
            user:Goal,
            Exception,
            (write(Goal), write(' causes: '), write(Exception), nl) % halt?
        )
    ;   write('Warning: initialization failed for '),
        write(Gs0), nl
    ),
    run_goals(Goals).
run_goals([Goal|_]) :-
    loader:write_error(error(domain_error(arg_type, Goal), run_goals/1)),
    nl,
    halt.

repl :-
    catch(read_and_match, E, print_exception(E)),
    false. %% this is for GC, until we get actual GC.
repl :-
    repl.

%% Enable op declarations with lists of operands, i.e.,
%% :- op(900, fy, [$,@]).

user:term_expansion((:- op(Pred, Spec, [Op | OtherOps])), OpResults) :-
    expand_op_list([Op | OtherOps], Pred, Spec, OpResults).

expand_op_list([], _, _, []).
expand_op_list([Op | OtherOps], Pred, Spec, [(:- op(Pred, Spec, Op)) | OtherResults]) :-
    expand_op_list(OtherOps, Pred, Spec, OtherResults).


read_and_match :-
    '$read_query_term'(_, Term, _, _, VarList),
    instruction_match(Term, VarList).


instruction_match(Term, VarList) :-
    (  var(Term) ->
       throw(error(instantiation_error, repl/0))
    ;  Term = [Item] ->
       (  atom(Item) ->
          (  Item == user ->
             catch(load(user_input), E, print_exception_with_check(E))
          ;
             submit_query_and_print_results(consult(Item), [])
          )
       ;  catch(type_error(atom, Item, repl/0),
                E,
                print_exception_with_check(E))
       )
    ;  Term = end_of_file ->
       halt
    ;
       submit_query_and_print_results(Term, VarList)
    ).


submit_query_and_print_results_(Term, VarList) :-
    '$get_b_value'(B),
    bb_put('$report_all', false),
    bb_put('$report_n_more', 0),
    expand_goal(Term, user, Term0),
    atts:call_residue_vars(user:Term0, AttrVars),
    write_eqs_and_read_input(B, VarList, AttrVars),
    !.
submit_query_and_print_results_(_, _) :-
    (   bb_get('$answer_count', 0) ->
        write('   ')
    ;   true
    ),
    write('false.'),
    nl.


submit_query_and_print_results(Term, VarList) :-
    % (  functor(Term0, call, _) ->
    %    Term = Term0 % prevent pre-mature expansion of incomplete goal
    %                 % in the first argument, which is done by call/N
    % ;  expand_goal(Term0, user, Term)
    % ),
    bb_put('$answer_count', 0),
    submit_query_and_print_results_(Term, VarList).


needs_bracketing(Value, Op) :-
    nonvar(Value),
    \+ integer(Value),
    functor(Value, F, Arity),
    current_op(FPrec, FSpec, F),
    current_op(EqPrec, EqSpec, Op),
    arity_specifier(Arity, FSpec),
    (  Arity =:= 0
    ;  EqPrec < FPrec
    ;  F \== '.', '$quoted_token'(F)
    ;  EqPrec =:= FPrec,
       member(EqSpec, [fx,xfx,yfx])
    ).

arity_specifier(0, _).
arity_specifier(1, S) :- atom_chars(S, [_,_]).
arity_specifier(2, S) :- atom_chars(S, [_,_,_]).

write_goal(G, VarList, MaxDepth) :-
    (  G = (Var = Value) ->
       (  var(Value) ->
          select((Var = _), VarList, NewVarList)
       ;  VarList = NewVarList
       ),
       write(Var),
       write(' = '),
       (  needs_bracketing(Value, =) ->
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
       (  needs_bracketing(Value, =) ->
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

graphic_token_char(C) :-
    memberchk(C, [#, $, &, *, +, -, ., /, :, <, =, >, ?, @, ^, ~, \\]).

list_last_item([C], C) :- !.
list_last_item([_|Cs], D) :-
    list_last_item(Cs, D).

trailing_period_is_ambiguous(Value) :-
    atom(Value),
    atom_chars(Value, ValueChars),
    list_last_item(ValueChars, Char),
    ValueChars \== ['.'],
    graphic_token_char(Char).

term_variables_under_max_depth(Term, MaxDepth, Vars) :-
    '$term_variables_under_max_depth'(Term, MaxDepth, Vars).

write_eqs_and_read_input(B, VarList, AttrVars) :-
    gather_query_vars(VarList, OrigVars),
    % one layer of depth added for (=/2) functor
    '$term_variables_under_max_depth'(OrigVars, 22, Vars0),
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

help_message :-
    nl, nl,
    write('SPACE, "n" or ";": next solution, if any\n'),
    write('RETURN or ".": stop enumeration\n'),
    write('"a": enumerate all solutions\n'),
    write('"f": enumerate the next 5 solutions\n'),
    write('"h": display this help message\n'),
    write('"w": write terms without depth limit\n'),
    write('"p": print terms with depth limit\n\n').

gather_query_vars([_ = Var | Vars], QueryVars) :-
    (  var(Var) ->
       QueryVars = [Var | QueryVars0],
       gather_query_vars(Vars, QueryVars0)
    ;
    gather_query_vars(Vars, QueryVars)
    ).
gather_query_vars([], []).

is_a_different_variable([_ = Binding | Pairs], Value) :-
    (  Value == Binding, !
    ;  is_a_different_variable(Pairs, Value)
    ).

eq_member(X, [Y|_])  :- X == Y, !.
eq_member(X, [_|Ys]) :- eq_member(X, Ys).

select_all([], _, _, [], []).
select_all([OtherVar = OtherValue | Pairs], Var, Value, Vars, NewPairs) :-
    (  OtherValue == Value ->
       Vars = [OtherVar = OtherValue | Vars0],
       select_all(Pairs, Var, Value, Vars0, NewPairs)
    ;
    NewPairs = [OtherVar = OtherValue | NewPairs0],
    select_all(Pairs, Var, Value, Vars, NewPairs0)
    ).

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

print_exception_with_check(E) :-
    (  E = error(_, _:_) -> true % if the error source contains a line
    % number, a GNU-style error message
    % is expected to be printed instead.
    ;  print_exception(E)
    ).
