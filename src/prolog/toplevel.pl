:- use_module(library(lists)).
:- use_module(library(si)).

:- module('$toplevel', ['$repl'/1, consult/1, use_module/1, use_module/2]).

'$repl'(ListOfModules) :-
    maplist('$use_list_of_modules', ListOfModules),
    false.
'$repl'(_) :- '$repl'.

'$use_list_of_modules'(Module) :-
    catch(use_module(Module), E, '$print_exception'(E)).

'$repl' :-
    catch('$read_and_match', E, '$print_exception'(E)),
    false. %% this is for GC, until we get actual GC.
'$repl' :- '$repl'.

'$read_and_match' :-
    '$read_query_term'(Term, VarList),
    '$instruction_match'(Term, VarList).

% make '$compile_batch', a system routine, callable.
'$$compile_batch' :- '$compile_batch'.

'$instruction_match'([Item], []) :-
    (  atom(Item) -> !,
       (  Item == user ->
	  catch('$$compile_batch', E, '$print_exception_with_check'(E))
       ;  consult(Item)
       )
    ;  !,
       catch(throw(error(type_error(atom, Item), repl/0)),
	     E,
	     '$print_exception_with_check'(E))       
    ).
'$instruction_match'(Term, VarList) :-
    '$submit_query_and_print_results'(Term, VarList),
    !.

'$submit_query_and_print_results'(Term0, VarList) :-
    (  expand_goals(Term0, Term) -> true
    ;  Term = Term0
    ),
    (  '$get_b_value'(B), call(Term), '$write_eqs_and_read_input'(B, VarList), !
    ;  write('false.'), nl
    ).

'$needs_bracketing'(Value, Op) :-
    catch((functor(Value, F, _),
	   current_op(EqPrec, EqSpec, Op),
	   current_op(FPrec, _, F)),
	  _,
	  false),
    (  EqPrec < FPrec -> true
    ;  EqPrec == FPrec,
       memberchk(EqSpec, [fx,xfx,yfx])
    ).

'$write_goal'(G, VarList) :-
    (  G = (Var = Value) ->
       write(Var),
       write(' = '),
       (  '$needs_bracketing'(Value, (=)) ->
	  write('('),
	  write_term(Value, [quoted(true), variable_names(VarList)]),
	  write(')')
       ;  write_term(Value, [quoted(true), variable_names(VarList)])
       )
    ;  G == [] ->
       write('true')
    ;  write_term(G, [quoted(true), variable_names(VarList)])
    ).

'$write_eq'((G1, G2), VarList) :-
    !,
    '$write_goal'(G1, VarList),
    write(', '),
    '$write_eq'(G2, VarList).
'$write_eq'(G, VarList) :-
    '$write_goal'(G, VarList).

'$write_eqs_and_read_input'(B, VarList) :-
    sort(VarList, SortedVarList),
    '$get_b_value'(B0),
    '$gather_goals'(SortedVarList, VarList, Goals),
    (  B0 == B ->
       (  Goals == [] ->
	  write('true.'), nl
       ;  thread_goals(Goals, ThreadedGoals, (',')),
	  '$write_eq'(ThreadedGoals, VarList),
	  write(' .'),
	  nl
       )
    ;  thread_goals(Goals, ThreadedGoals, (',')),
       '$write_eq'(ThreadedGoals, VarList),
       '$raw_input_read_char'(C),
       (  C == (';'), !,
	  write(' ;'), nl, false
       ;  C == ('.'), !,
	  write(' ...'), nl
       )
    ).

'$gather_query_vars'([_ = Var | Vars], QueryVars) :-
    (  var(Var) ->
       QueryVars = [Var | QueryVars1],
       '$gather_query_vars'(Vars, QueryVars1)
    ;  '$gather_query_vars'(Vars, QueryVars)
    ).
'$gather_query_vars'([], []).

'$gather_goals'([], VarList, Goals) :-
    '$get_attr_var_queue_beyond'(0, AttrVars),
    '$gather_query_vars'(VarList, QueryVars),
    '$call_attribute_goals'(QueryVars, AttrVars),
    '$fetch_attribute_goals'(Goals).
'$gather_goals'([Var = Value | Pairs], VarList, Goals) :-
    (  nonvar(Value) ->
       Goals = [Var = Value | Goals0],
       '$gather_goals'(Pairs, VarList, Goals0)
    ;  '$gather_goals'(Pairs, VarList, Goals)
    ).

'$print_exception'(E) :-
    write_term('caught: ', [quoted(false)]),
    writeq(E),
    nl.

'$print_exception_with_check'(E) :-
    (  E = error(_, _:_) -> true % if the error source contains a line
                                 % number, a GNU-style error message
                                 % is expected to be printed instead.
    ;  '$print_exception'(E)
    ).

'$predicate_indicator'(Source, PI) :-
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
       ;  throw(error(type_error(predicate_indicator, PI), Source))
       )
    ;  throw(error(instantiation_error, Source))
    ).

consult(Item) :-
    (  atom(Item) -> use_module(Item)
    ;  throw(error(type_error(atom, Item), consult/1))
    ).

use_module(Module) :-
    (  nonvar(Module) ->
       (  Module = library(Filename) -> '$use_module'(Filename)
       ;  atom(Module) -> '$use_module_from_file'(Module)
       ;  throw(error(invalid_module_specifier, use_module/1))
       )
    ;  throw(error(instantiation_error, use_module/1))
    ).

use_module(Module, QualifiedExports) :-
    (  nonvar(Module) ->
       (  list_si(QualifiedExports) ->
	  maplist('$predicate_indicator'(use_module/2), QualifiedExports), !,
	  (  Module = library(Filename) -> '$use_qualified_module'(Filename, QualifiedExports)
	  ;  atom(Module) -> '$use_qualified_module_from_file'(Module, QualifiedExports)
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

expand_goals(UnexpandedGoals, ExpandedGoals) :-
    nonvar(UnexpandedGoals),
    var(ExpandedGoals),
    (  expand_goal(UnexpandedGoals, Goals) -> true
    ;  Goals = UnexpandedGoals
    ),
    (  Goals = (Goal0, Goals0) ->
       (  expand_goal(Goal0, Goal1) ->
	  Expanded = true,
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
