:- module('$toplevel', ['$repl'/1, consult/1, use_module/1, use_module/2,
                        argv/1]).

:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(si)).

:- dynamic(argv/1).

'$repl'([_|Args0]) :-
    \+ argv(_),
    (   append(Args1, ["--"|Args2], Args0) ->
        asserta(argv(Args2)),
        Args = Args1
    ;   asserta(argv([])),
        Args = Args0
    ),
    delegate_task(Args, []),
    repl.
'$repl'(_) :-
    (   \+ argv(_) -> asserta(argv([]))
    ;   true
    ),
    repl.

delegate_task([], []).
delegate_task([], Goals0) :-
    reverse(Goals0, Goals),
    run_goals(Goals),
    repl.
delegate_task([Arg0|Args], Goals0) :-
    (   member(Arg0, ["-h", "--help"]) -> print_help
    ;   member(Arg0, ["-v", "--version"]) -> print_version
    ;   member(Arg0, ["-g", "--goal"]) -> gather_goal(g, Args, Goals0)
    ;   atom_chars(Mod, Arg0),
        catch(use_module(Mod), E, print_exception(E))
    ),
    delegate_task(Args, Goals0).

print_help :-
    write('Usage: scryer-prolog [OPTIONS] [FILES] [-- ARGUMENTS]'),
    nl, nl,
    write('Options:'), nl,
    write('   -h, --help           '),
    write('Display this message'), nl,
    write('   -v, --version        '),
    write('Print version information and exit'), nl,
    write('   -g, --goal GOAL      '),
    write('Run the query GOAL'), nl,
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
    read_term_from_chars(Gs1, Goal),
    (   catch(
            Goal,
            Exception,
            (write(Gs0), write(' causes: '), write(Exception), nl) % halt?
        )
    ;   write('Warning: initialization failed for '),
        write(Gs0), nl
    ),
    run_goals(Goals).
run_goals([Goal|_]) :-
    write('caught: '),
    write(error(domain_error(arg_type, Goal), run_goals/1)), nl,
    halt.

repl :-
    catch(read_and_match, E, print_exception(E)),
    false. %% this is for GC, until we get actual GC.
repl :-
    repl.

read_and_match :-
    '$read_query_term'(_, Term, _, _, VarList),
    instruction_match(Term, VarList).

% make compile_batch, a system routine, callable.
compile_batch :- '$compile_batch'.

instruction_match(Term, VarList) :-
    (  var(Term) ->
       throw(error(instantiation_error, repl/0))
    ;
    Term = [Item] -> !,
                     (  atom(Item) ->
	                    (  Item == user ->
	                       catch(compile_batch, E, print_exception_with_check(E))
	                    ;  consult(Item)
	                    )
                     ;
	                 catch(throw(error(type_error(atom, Item), repl/0)),
		                   E,
		                   print_exception_with_check(E))
                     )
    ;
    Term = end_of_file -> halt
    ;
    submit_query_and_print_results(Term, VarList)
    ).

:- use_module(library(iso_ext)).

% auxiliary predicates, so that using them in setup_call_cleanup/3 works
get_b_value(B) :- '$get_b_value'(B).
clear_attribute_goals :- '$clear_attribute_goals'.

submit_query_and_print_results(Term0, VarList) :-
    (  expand_goals(Term0, Term) -> true
    ;  Term0 = Term
    ),
    setup_call_cleanup(bb_put('$first_answer', true),
                       (   get_b_value(B), call(Term), write_eqs_and_read_input(B, VarList),
                           !
                       ;   %  clear attribute goal lists, which may be populated by
                           %  copy_term/3 prior to failure.
                           clear_attribute_goals, write('false.'), nl
                       ),
                       bb_put('$first_answer', false)).

needs_bracketing(Value, Op) :-
    catch((functor(Value, F, _),
	       current_op(EqPrec, EqSpec, Op),
	       current_op(FPrec, _, F)),
	      _,
	      false),
    (  EqPrec < FPrec ->
       true
    ;  '$quoted_token'(F) ->
       true
    ;  FPrec > 0, F == Value, graphic_token_char(F) ->
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

graphic_token_char(C) :-
    memberchk(C, ['#', '$', '&', '*', '+', '-', '.', ('/'), ':',
                  '<', '=', '>', '?', '@', '^', '~', ('\\')]).

list_last_item([C], C) :- !.
list_last_item([_|Cs], D) :-
    list_last_item(Cs, D).

trailing_period_is_ambiguous(Value) :-
    atom(Value),
    atom_chars(Value, ValueChars),
    list_last_item(ValueChars, Char),
    ValueChars \== ['.'],
    graphic_token_char(Char).

write_eqs_and_read_input(B, VarList) :-
    term_variables(VarList, Vars0),
    '$term_attributed_variables'(VarList, AttrVars),
    copy_term(AttrVars, AttrVars, AttrGoals),
    term_variables(AttrGoals, AttrGoalVars),
    append([Vars0, AttrGoalVars, AttrVars], Vars),
    charsio:extend_var_list(Vars, VarList, NewVarList, fabricated),
    '$get_b_value'(B0),
    gather_query_vars(VarList, OrigVars),
    gather_equations(NewVarList, OrigVars, Equations),
    append(Equations, AttrGoals, Goals),
    term_variables(Equations, EquationVars),
    append([AttrGoalVars, EquationVars], Vars1),
    charsio:extend_var_list(Vars1, VarList, NewVarList0, fabricated),
    (   bb_get('$first_answer', true) ->
        write('   '),
        bb_put('$first_answer', false)
    ;   true
    ),
    (  B0 == B ->
       (  Goals == [] ->
	      write('true.'), nl
       ;  thread_goals(Goals, ThreadedGoals, (',')),
	      write_eq(ThreadedGoals, NewVarList0, 20),
	      write('.'),
	      nl
       )
    ;  thread_goals(Goals, ThreadedGoals, (',')),
       write_eq(ThreadedGoals, NewVarList0, 20),
       read_input(ThreadedGoals, NewVarList0)
    ).

read_input(ThreadedGoals, NewVarList) :-
    get_single_char(C),
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
       nl, write(';  ...'), nl
    ;  read_input(ThreadedGoals, NewVarList)
    ).

help_message :-
    nl, nl,
    write('SPACE, "n" or ";": next solution, if any\n'),
    write('RETURN or ".": stop enumeration\n'),
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
    write_term('caught: ', [quoted(false), max_depth(20)]),
    writeq(E),
    nl.

print_exception_with_check(E) :-
    (  E = error(_, _:_) -> true % if the error source contains a line
    % number, a GNU-style error message
    % is expected to be printed instead.
    ;  print_exception(E)
    ).

module_export(Source, PI) :-
    (  nonvar(PI) ->
       (  PI = Name / Arity ->
	      (  var(Name) -> throw(error(instantiation_error, Source))
	      ;  integer(Arity) ->
	         (  \+ atom(Name) -> throw(error(type_error(atom, Name), Source))
	         ;  Arity < 0 -> throw(error(domain_error(not_less_than_zero, Arity), Source))
	         ;  true
	         )
	      ;  throw(error(type_error(integer, Arity), Source))
	      )
       ;  PI = op(Prec, Spec, Name) ->
	      (  integer(Prec) ->
	         (  \+ atom(Name) ->
		        throw(error(type_error(atom, Name), Source))
	         ;  Prec < 0 ->
		        throw(error(domain_error(not_less_than_zero, Prec), Source))
	         ;  Prec > 1200 ->
		        throw(error(domain_error(operator_precision, Prec), Source))
	         ;  memberchk(Spec, [xfy, yfx, xfx, fx, fy, yf, xf])
	         ;  throw(error(domain_error(operator_specification, Spec), Source))
	         )
	      ;  throw(error(type_error(integer, Prec), Source))
	      )
       ;  throw(error(type_error(module_export, PI), Source))
       )
    ;  throw(error(instantiation_error, Source))
    ).

consult(Item) :-
    (  atom(Item) -> use_module(Item)
    ;  throw(error(type_error(atom, Item), consult/1))
    ).

use_module(Module) :-
    (  nonvar(Module) ->
       (  Module = library(Filename) ->
          write_term_to_chars(Filename, [], FilenameString),
          '$use_module'(FilenameString)
       ;  atom(Module) ->
          '$use_module_from_file'(Module)
       ;  throw(error(invalid_module_specifier, use_module/1))
       )
    ;  throw(error(instantiation_error, use_module/1))
    ).

use_module(Module, QualifiedExports) :-
    (  nonvar(Module) ->
       (  list_si(QualifiedExports) ->
	      maplist('$module_export'(use_module/2), QualifiedExports) ->
	          (  Module = library(Filename) ->
                 write_term_to_chars(Filename, [], FilenameString),
	             '$use_qualified_module'(FilenameString, QualifiedExports)
	          ;  atom(Module) ->
	             '$use_qualified_module_from_file'(Module, QualifiedExports)
	          ;  throw(error(invalid_module_specifier, use_module/2))
	          )
       ;  throw(error(type_error(list, QualifiedExports), use_module/2))
       )
    ;  throw(error(instantiation_error, use_module/2))
    ).


% expand goals in initialization directives.
user:term_expansion(Term0, (:- initialization(ExpandedGoals))) :-
    nonvar(Term0),
    Term0 = (:- initialization(Goals)),
    expand_goals(Goals, ExpandedGoals),
    Goals \== ExpandedGoals.

module_expand_goal(UnexpandedGoals, ExpandedGoals) :-
    (  '$module_of'(Module, UnexpandedGoals),
       '$module_exists'(Module),
       Module:goal_expansion(UnexpandedGoals, ExpandedGoals),
       UnexpandedGoals \== ExpandedGoals ->
       true
    ;  user:goal_expansion(UnexpandedGoals, ExpandedGoals)
    ).

expand_goals(UnexpandedGoals, ExpandedGoals) :-
    nonvar(UnexpandedGoals),
    var(ExpandedGoals),
    (  module_expand_goal(UnexpandedGoals, Goals) ->
       true
    ;  Goals = UnexpandedGoals
    ),
    (  Goals = (Goal0, Goals0) ->
       (  expand_goals(Goal0, Goal1) ->
	      expand_goals(Goals0, Goals1),
	      thread_goals(Goal1, ExpandedGoals, Goals1, (','))
       ;  expand_goals(Goals0, Goals1),
	      ExpandedGoals = (Goal0, Goals1)
       )
    ;  Goals = (Goals0 -> Goals1) ->
       expand_goals(Goals0, ExpandedGoals0),
       expand_goals(Goals1, ExpandedGoals1),
       ExpandedGoals = (ExpandedGoals0 -> ExpandedGoals1)
    ;  Goals = (Goals0 ; Goals1) ->
       expand_goals(Goals0, ExpandedGoals0),
       expand_goals(Goals1, ExpandedGoals1),
       ExpandedGoals = (ExpandedGoals0 ; ExpandedGoals1)
    ;  Goals = (\+ Goals0) ->
       expand_goals(Goals0, Goals1),
       ExpandedGoals = (\+ Goals1)
    ;  thread_goals(Goals, ExpandedGoals, (','))
    ;  Goals = ExpandedGoals
    ).

thread_goals(Goals0, Goals1, Hole, Functor) :-
    nonvar(Goals0),
    (  Goals0 = [G | Gs] ->
       (  Gs == [] ->
	      Goals1 =.. [Functor, G, Hole]
       ;  Goals1 =.. [Functor, G, Goals2],
	      thread_goals(Gs, Goals2, Hole, Functor)
       )
    ;  Goals1 =.. [Functor, Goals0, Hole]
    ).

thread_goals(Goals0, Goals1, Functor) :-
    nonvar(Goals0),
    (  Goals0 = [G | Gs] ->
       (  Gs = [] ->
	      Goals1 = G
       ;  Goals1 =.. [Functor, G, Goals2],
	      thread_goals(Gs, Goals2, Functor)
       )
    ;  Goals1 = Goals0
    ).
