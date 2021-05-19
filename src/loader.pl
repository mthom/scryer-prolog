
:- module(loader, [consult/1,
                   expand_goal/3,
                   expand_term/2,
                   file_load/2,
                   load/1,
                   predicate_property/2,
                   prolog_load_context/2,
                   strip_module/3,
                   use_module/1,
                   use_module/2
                  ]).


:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(pairs)).


'$print_message_and_fail'(Error) :-
    (  (  Error = error(existence_error(procedure, Expansion), Expansion)
       ;  Error = error(evaluation_error((_:_)/_),Expansion)
       )  ->
       (  (  Expansion = goal_expansion/2
          ;  Expansion = term_expansion/2
          )  ->
          true
       ;  write('caught: '),
          writeq(Error),
          nl
       )
    ;  write('caught: '),
       writeq(Error),
       nl
    ),
    '$fail'.

expand_term(Term, ExpandedTerm) :-
    (  catch('$call'(user:term_expansion(Term, ExpandedTerm0)),
             E,
             '$call'(loader:'$print_message_and_fail'(E))) ->
       (  var(ExpandedTerm0) ->
          error:instantiation_error(term_expansion/2)
       ;  ExpandedTerm0 = [_|_] ->
          term_expansion_list(ExpandedTerm0, ExpandedTerm, [])
       ;  expand_term(ExpandedTerm0, ExpandedTerm)
       )
    ;  Term = ExpandedTerm
    ).

term_expansion_list([], ExpandedTerms, ExpandedTerms).
term_expansion_list([Term|Terms], ExpandedTermsHead, ExpandedTermsTail) :-
    expand_term(Term, ExpandedTerm0),
    (  var(ExpandedTerm0) ->
       error:instantiation_error(term_expansion/2)
    ;  ExpandedTerm0 = [_|_] ->
       term_expansion_list(ExpandedTerm0, ExpandedTermsHead, ExpandedTerms0Tail),
       term_expansion_list(Terms, ExpandedTerms0Tail, ExpandedTermsTail)
    ;  ExpandedTermsHead = [ExpandedTerm0 | ExpandedTerms0Tail],
       term_expansion_list(Terms, ExpandedTerms0Tail, ExpandedTermsTail)
    ).


goal_expansion(Goal, Module, ExpandedGoal) :-
    (  atom(Module),
       catch('$call'(Module:goal_expansion(Goal, ExpandedGoal0)),
             E,
             '$call'(loader:'$print_message_and_fail'(E))) ->
       (  var(ExpandedGoal0) ->
          error:instantiation_error(goal_expansion/2)
       ;  goal_expansion(ExpandedGoal0, Module, ExpandedGoal)
       )
    ;  Goal = ExpandedGoal
    ).



create_file_load_context(Stream, Path, Evacuable) :-
    '$push_load_context'(Stream, Path),
    '$push_load_state_payload'(Evacuable).

create_load_context(Stream, Evacuable) :-
    '$push_load_context'(Stream, ''),
    '$push_load_state_payload'(Evacuable).

unload_evacuable(Evacuable) :-
    '$pop_load_state_payload'(Evacuable),
    '$pop_load_context'.

run_initialization_goals :-
    prolog_load_context(module, Module),
    (  predicate_property(Module:'$initialization_goals'(_), dynamic) ->
       findall(Module:Goal, '$call'(builtins:retract(Module:'$initialization_goals'(Goal))), Goals),
       abolish(Module:'$initialization_goals'/1),
       (  maplist(Module:call, Goals) ->
          true
       ;  true %% initialization goals can fail without thwarting the load.
       )
    ;  true
    ).

file_load(Stream, Path) :-
    file_load(Stream, Path, _),
    false.        %% Clear the heap.
file_load(_, _).

file_load(Stream, Path, Evacuable) :-
    create_file_load_context(Stream, Path, Evacuable),
    % '$add_in_situ_filename_module' removes user level predicates,
    % local predicate clauses, etc. from a previous load of the file
    % at Path.
    '$add_in_situ_filename_module'(Evacuable),
    catch((loader:load_loop(Stream, Evacuable),
           loader:run_initialization_goals),
          E,
          builtins:(loader:unload_evacuable(Evacuable),
                    loader:'$print_message_and_fail'(E),
		            builtins:throw(E))),
    '$pop_load_context'.


load(Stream) :-
    create_load_context(Stream, Evacuable),
    catch((loader:load_loop(Stream, Evacuable),
           loader:run_initialization_goals),
          E,
          builtins:(loader:unload_evacuable(Evacuable),
                    loader:'$print_message_and_fail'(E),
		            builtins:throw(E))),
    '$pop_load_context',
    false.        %% Clear the heap.
load(_).


print_comma_separated_list([VN=_]) :-
    write(VN),
    !.
print_comma_separated_list([VN=_, VNEq | VNEqs]) :-
    write(VN),
    write(', '),
    print_comma_separated_list([VNEq | VNEqs]).


filter_anonymous_vars([], []).
filter_anonymous_vars([VN=V | VNEqs0], VNEqs) :-
    (  atom_concat('_', _, VN) ->
       filter_anonymous_vars(VNEqs0, VNEqs)
    ;  VNEqs = [VN=V | VNEqs1],
       filter_anonymous_vars(VNEqs0, VNEqs1)
    ).

warn_about_singletons([], _).
warn_about_singletons([Singleton|Singletons], LinesRead) :-
    (  filter_anonymous_vars([Singleton|Singletons], VarEqs),
       VarEqs \== [] ->
       write('Warning: singleton variables '),
       print_comma_separated_list(VarEqs),
       write(' at line '),
       write(LinesRead),
       write(' of '),
       prolog_load_context(file, File),
       write(File),
       nl
    ;  true
    ).


load_loop(Stream, Evacuable) :-
    (  '$devour_whitespace'(Stream) ->
       stream_property(Stream, position(position_and_lines_read(_, LinesRead))),
       read_term(Stream, Term, [singletons(Singletons)])
    ;  Term = end_of_file
    ),
    (  Term == end_of_file ->
       close(Stream),
       '$conclude_load'(Evacuable)
    ;  var(Term) ->
       instantiation_error(load/1)
    ;  warn_about_singletons(Singletons, LinesRead),
       compile_term(Term, Evacuable),
       load_loop(Stream, Evacuable)
    ).


compile_term(Term, Evacuable) :-
    expand_terms_and_goals(Term, Terms),
    !,
    (  var(Terms) ->
       instantiation_error(load/1)
    ;  Terms = [_|_] ->
       compile_dispatch_or_clause_on_list(Terms, Evacuable)
    ;  compile_dispatch_or_clause(Terms, Evacuable)
    ).


inner_meta_specs(0, HeadArg, InnerHeadArgs, InnerMetaSpecs) :-
    !,
    predicate_property(HeadArg, meta_predicate(InnerMetaSpecs)),
    HeadArg =.. [_ | InnerHeadArgs].

inner_meta_specs(N, HeadArg, InnerHeadArgs, InnerMetaSpecs) :-
    integer(N),
    N >= 0,
    HeadArg =.. [Functor | InnerHeadArgs],
    length(InnerHeadArgs1, N),
    append(InnerHeadArgs, InnerHeadArgs1, InnerHeadArgs0),
    CompleteHeadArg =.. [Functor | InnerHeadArgs0],
    predicate_property(CompleteHeadArg, meta_predicate(InnerMetaSpecs)).


module_expanded_head_variables_([], _, HeadVars, HeadVars).
module_expanded_head_variables_([HeadArg | HeadArgs], [MetaSpec | MetaSpecs], HeadVars, HeadVars0) :-
    (  (  MetaSpec == (:)
       ;  integer(MetaSpec),
          MetaSpec >= 0
       )  ->
       (  var(HeadArg) ->
          HeadVars = [HeadArg-HeadArg | HeadVars1],
          module_expanded_head_variables_(HeadArgs, MetaSpecs, HeadVars1, HeadVars0)
       ;  inner_meta_specs(MetaSpec, HeadArg, InnerHeadArgs, InnerMetaSpecs) ->
          module_expanded_head_variables_(InnerHeadArgs, InnerMetaSpecs, HeadVars, HeadVars1),
          module_expanded_head_variables_(HeadArgs, MetaSpecs, HeadVars1, HeadVars0)
       ;  module_expanded_head_variables_(HeadArgs, MetaSpecs, HeadVars, HeadVars0)
       )
    ;  module_expanded_head_variables_(HeadArgs, MetaSpecs, HeadVars, HeadVars0)
    ).

module_expanded_head_variables(Head, HeadVars) :-
    (  var(Head) ->
       instantiation_error(load/1)
    ;  predicate_property(Head, meta_predicate(MetaSpecs)),
       Head =.. [_ | HeadArgs] ->
       module_expanded_head_variables_(HeadArgs, MetaSpecs, HeadVars, [])
    ;  HeadVars = []
    ).


expand_term_goals(Terms0, Terms) :-
    (  Terms0 = (Head1 :- Body0) ->
       (  var(Head1) ->
          instantiation_error(load/1)
       ;  Head1 = Module:Head2 ->
          (  atom(Module) ->
             prolog_load_context(module, Target),
             module_expanded_head_variables(Head2, HeadVars),
             expand_goal(Body0, Target, Body1, HeadVars),
             Terms = (Module:Head2 :- Body1)
          ;  type_error(atom, Module, load/1)
          )
       ;  prolog_load_context(module, Target),
          module_expanded_head_variables(Head1, HeadVars),
          expand_goal(Body0, Target, Body1, HeadVars),
          Terms = (Head1 :- Body1)
       )
    ;  Terms = Terms0
    ).


expand_terms_and_goals(Term, Terms) :-
    expand_term(Term, Terms0),
    (  var(Terms0) ->
       instantiation_error(load/1)
    ;  Terms0 = [_|_] ->
       maplist(loader:expand_term_goals, Terms0, Terms)
    ;  expand_term_goals(Terms0, Terms)
    ).


compile_dispatch_or_clause_on_list([], Evacuable).
compile_dispatch_or_clause_on_list([Term | Terms], Evacuable) :-
    compile_dispatch_or_clause(Term, Evacuable),
    compile_dispatch_or_clause_on_list(Terms, Evacuable).


compile_dispatch_or_clause(Term, Evacuable) :-
    (  var(Term) ->
       instantiation_error(load/1)
    ;  compile_dispatch(Term, Evacuable) ->
       '$flush_term_queue'(Evacuable)
    ;  compile_clause(Term, Evacuable)
    ).


compile_dispatch((:- Declaration), Evacuable) :-
    (  var(Declaration) ->
       instantiation_error(load/1)
    ;  compile_declaration(Declaration, Evacuable)
    ).
compile_dispatch(term_expansion(Term, Terms), Evacuable) :-
    '$add_term_expansion_clause'(term_expansion(Term, Terms), Evacuable).
compile_dispatch((term_expansion(Term, Terms) :- Body), Evacuable) :-
    '$add_term_expansion_clause'((term_expansion(Term, Terms) :- Body), Evacuable).
compile_dispatch(user:term_expansion(Term, Terms), Evacuable) :-
    '$add_term_expansion_clause'(term_expansion(Term, Terms), Evacuable).
compile_dispatch((user:term_expansion(Term, Terms) :- Body), Evacuable) :-
    '$add_term_expansion_clause'((term_expansion(Term, Terms) :- Body), Evacuable).
compile_dispatch(goal_expansion(Term, Terms), Evacuable) :-
    prolog_load_context(module, user),
    '$add_goal_expansion_clause'(user, goal_expansion(Term, Terms), Evacuable).
compile_dispatch((goal_expansion(Term, Terms) :- Body), Evacuable) :-
    prolog_load_context(module, user),
    '$add_goal_expansion_clause'(user, (goal_expansion(Term, Terms) :- Body), Evacuable).
compile_dispatch(user:goal_expansion(Term, Terms), Evacuable) :-
    '$add_goal_expansion_clause'(user, goal_expansion(Term, Terms), Evacuable).
compile_dispatch((user:goal_expansion(Term, Terms) :- Body), Evacuable) :-
    '$add_goal_expansion_clause'(user, (goal_expansion(Term, Terms) :- Body), Evacuable).

remove_module(Module, Evacuable) :-
    (  nonvar(Module),
       Module = library(ModuleName),
       atom(ModuleName),
       atom \== [] ->
       '$remove_module_exports'(ModuleName, Evacuable)
    ;  atom(Module),
       atom \== [] ->
       '$remove_module_exports'(Module, Evacuable)
    ;  domain_error(module_specifier, Module, use_module/2)
    ).


compile_declaration(use_module(Module), Evacuable) :-
    use_module(Module, [], Evacuable).
compile_declaration(use_module(Module, Exports), Evacuable) :-
    (  Exports == [] ->
       remove_module(Module, Evacuable)
    ;  use_module(Module, Exports, Evacuable)
    ).
compile_declaration(module(Module, Exports), Evacuable) :-
    (  atom(Module) ->
       '$declare_module'(Module, Exports, Evacuable)
    ;  type_error(atom, Module, load/1)
    ).
compile_declaration(dynamic(Module:Name/Arity), Evacuable) :-
    !,
    must_be(atom, Module),
    must_be(atom, Name),
    must_be(integer, Arity),
    '$add_dynamic_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(dynamic(Name/Arity), Evacuable) :-
    must_be(atom, Name),
    must_be(integer, Arity),
    prolog_load_context(module, Module),
    '$add_dynamic_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(multifile(Module:Name/Arity), Evacuable) :-
    !,
    must_be(atom, Module),
    must_be(atom, Name),
    must_be(integer, Arity),
    '$add_multifile_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(multifile(Name/Arity), Evacuable) :-
    must_be(atom, Name),
    must_be(integer, Arity),
    prolog_load_context(module, Module),
    '$add_multifile_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(discontiguous(Module:Name/Arity), Evacuable) :-
    !,
    must_be(atom, Module),
    must_be(atom, Name),
    must_be(integer, Arity),
    '$add_discontiguous_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(discontiguous(Name/Arity), Evacuable) :-
    must_be(atom, Name),
    must_be(integer, Arity),
    prolog_load_context(module, Module),
    '$add_discontiguous_predicate'(Module, Name, Arity, Evacuable).
compile_declaration(initialization(Goal), Evacuable) :-
    prolog_load_context(module, Module),
    assertz(Module:'$initialization_goals'(Goal)).
compile_declaration(set_prolog_flag(Flag, Value), _) :-
    set_prolog_flag(Flag, Value).
compile_declaration(non_counted_backtracking(Name/Arity), Evacuable) :-
    must_be(atom, Name),
    must_be(integer, Arity),
    (  Arity >= 0 ->
       '$add_non_counted_backtracking'(Name, Arity, Evacuable)
    ;  domain_error(not_less_than_zero, Arity, load/1)
    ).


compile_clause((Target:Head :- Body), Evacuable) :-
    !,
    functor(Head, Name, Arity),
    (  '$is_consistent_with_term_queue'(Target, Name, Arity, Evacuable) ->
       '$scoped_clause_to_evacuable'(Target, (Head :- Body), Evacuable)
    ;  '$flush_term_queue'(Evacuable),
       compile_term((Target:Head :- Body), Evacuable)
    ).
compile_clause(Target:Head, Evacuable) :-
    !,
    functor(Head, Name, Arity),
    (  '$is_consistent_with_term_queue'(Target, Name, Arity, Evacuable) ->
       '$scoped_clause_to_evacuable'(Target, Head, Evacuable)
    ;  '$flush_term_queue'(Evacuable),
       compile_term(Target:Head, Evacuable)
    ).
compile_clause((Head :- Body), Evacuable) :-
    !,
    prolog_load_context(module, Target),
    functor(Head, Name, Arity),
    (  '$is_consistent_with_term_queue'(Target, Name, Arity, Evacuable) ->
       '$clause_to_evacuable'((Head :- Body), Evacuable)
    ;  '$flush_term_queue'(Evacuable),
       compile_term((Head :- Body), Evacuable)
    ).
compile_clause(Head, Evacuable) :-
    prolog_load_context(module, Target),
    functor(Head, Name, Arity),
    (  '$is_consistent_with_term_queue'(Target, Name, Arity, Evacuable) ->
       '$clause_to_evacuable'(Head, Evacuable)
    ;  '$flush_term_queue'(Evacuable),
       compile_term(Head, Evacuable)
    ).


prolog_load_context(source, Source) :-
    %% The absolute path name of the file being compiled. During
    %% loading of a PO file, the corresponding source file name is
    %% returned.
    '$prolog_lc_source'(Source).
prolog_load_context(file, File) :-
    %% Outside included files (see Include Declarations) this is the
    %% same as the source key. In included files this is the absolute
    %% path name of the file being included.
    '$prolog_lc_file'(File).
prolog_load_context(directory, Dir) :-
    %% The absolute path name of the directory of the file being
    %% compiled/loaded. In included files this is the directory of the
    %% file being included.
    '$prolog_lc_dir'(Dir).
prolog_load_context(module, Module) :-
    %% The source module (see ref-mod-mne). This is useful for example
    %% if you are defining clauses for user:term_expansion/6 and need
    %% to access the source module at compile time.
    '$prolog_lc_module'(Module).
prolog_load_context(stream, Stream) :-
    %% The stream being compiled or loaded from.
    '$prolog_lc_stream'(Stream).
prolog_load_context(term_position, TermPosition) :-
    %% TermPosition represents the stream position of the last term read.
    '$prolog_lc_stream'(Stream),
    stream_property(Stream, position(TermPosition)).


consult(Item) :-
    (  atom(Item) -> use_module(Item)
    ;  type_error(atom, Item, consult/1)
    ).


use_module(Module) :-
    '$push_load_state_payload'(Evacuable),
    use_module(Module, [], Evacuable).

use_module(Module, Exports) :-
    '$push_load_state_payload'(Evacuable),
    (  Exports == [] ->
       remove_module(Module, Evacuable)
    ;  use_module(Module, Exports, Evacuable)
    ).


%% If use_module is invoked in an existing load context, use its
%% directory. Otherwise, use the relative path of Path.

load_context_path(Module, Path) :-
    (  sub_atom(Module, 0, 1, _, '/') ->
       Path = Module
    ;  prolog_load_context(directory, CurrentDir) ->
       % Rust's Path module never ends a directory path with '/', so
       % add one here.
       atom_concat(CurrentDir, '/', CurrentDirSlashed),
       atom_concat(CurrentDirSlashed, Module, Path)
    ;  Module = Path
    ).

path_atom(Dir/File, Path) :-
    must_be(atom, File),
    !,
    path_atom(Dir, DirPath),
    foldl(builtins:atom_concat, ['/', DirPath], File, Path).
path_atom(Path, Path) :-
    must_be(atom, Path).

% Try to open the file with the Path name as given; if that fails,
% append '.pl' and try again.
open_file(Path, Stream) :-
    (  atom_concat(_, '.pl', Path) ->
       open(Path, read, Stream)
    ;  catch(open(Path, read, Stream),
             error(existence_error(source_sink, Path), _),
             ( atom_concat(Path, '.pl', ExtendedPath),
               open(ExtendedPath, read, Stream) )
            )
    ).

use_module(Module, Exports, Evacuable) :-
    (  var(Module) ->
       instantiation_error(load/1)
    ;  Module = library(Library) ->
       (  path_atom(Library, LibraryPath) ->
          (  '$load_compiled_library'(LibraryPath, Exports, Evacuable) ->
             true
          ;  '$load_library_as_stream'(LibraryPath, Stream, Path),
             file_load(Stream, Path, Subevacuable),
             '$use_module'(Evacuable, Subevacuable, Exports)
          )
       ;  var(Library) ->
          instantiation_error(load/1)
       ;  type_error(atom, Library, load/1)
       )
    ;  (  path_atom(Module, ModulePath) ->
          load_context_path(ModulePath, Path),
          open_file(Path, Stream),
          stream_property(Stream, file_name(PathFileName)),
          file_load(Stream, PathFileName, Subevacuable),
          '$use_module'(Evacuable, Subevacuable, Exports)
       ;  type_error(atom, Library, load/1)
       )
    ).



check_predicate_property(meta_predicate, Module, Name, Arity, MetaPredicateTerm) :-
    '$cpp_meta_predicate_property'(Module, Name, Arity, MetaPredicateTerm).
check_predicate_property(built_in, _, Name, Arity, built_in) :-
    '$cpp_built_in_property'(Name, Arity).
check_predicate_property(dynamic, Module, Name, Arity, dynamic) :-
    '$cpp_dynamic_property'(Module, Name, Arity).
check_predicate_property(multifile, Module, Name, Arity, multifile) :-
    '$cpp_multifile_property'(Module, Name, Arity).
check_predicate_property(discontiguous, Module, Name, Arity, discontiguous) :-
    '$cpp_discontiguous_property'(Module, Name, Arity).



extract_predicate_property(Property, PropertyType) :-
    (  var(Property) ->
       true
    ;  functor(Property, PropertyType, _)
    ).

load_context(Module) :-
    (  prolog_load_context(module, Module) ->
       true
    ;  Module = user
    ).

predicate_property(Callable, Property) :-
    (  var(Callable) ->
       instantiation_error(predicate_property/2)
    ;  functor(Callable, (:), 2),
       arg(1, Callable, Module),
       arg(2, Callable, Callable0),
       atom(Module),
       nonvar(Callable0) ->
       functor(Callable0, Name, Arity),
       (  atom(Name),
          Name \== [] ->
          extract_predicate_property(Property, PropertyType),
          check_predicate_property(PropertyType, Module, Name, Arity, Property)
       ;  type_error(callable, Callable0, predicate_property/2)
       )
    ;  functor(Callable, Name, Arity),
       (  atom(Name),
          Name \== [] ->
          extract_predicate_property(Property, PropertyType),
          load_context(Module),
          check_predicate_property(PropertyType, Module, Name, Arity, Property)
       ;  type_error(callable, Callable, predicate_property/2)
       )
    ).


strip_module(M0, G0, M1, G1) :-
    (  nonvar(G0),
       G0 = (MG1:G2) ->
       strip_module(MG1, G2, M1, G1)
    ;  M0 = M1,
       G0 = G1
    ).

strip_module(Goal, M, G) :-
    strip_module(_, Goal, M, G).


expand_subgoal(UnexpandedGoals, MS, Module, ExpandedGoals, HeadVars) :-
    (  var(UnexpandedGoals) ->
       UnexpandedGoals = ExpandedGoals
    ;  (  MS == 0 ->
          % only expand complete goals. call/N will take care of incomplete goals
          % by calling goal expansion after it is supplied the remaining arguments.
          (  goal_expansion(UnexpandedGoals, Module, UnexpandedGoals1),
             (  Module \== user ->
                goal_expansion(UnexpandedGoals1, user, Goals)
             ;  Goals = UnexpandedGoals1
             )
          )
       ;  Goals = UnexpandedGoals
       ),
       (  inner_meta_specs(MS, Goals, _, MetaSpecs) ->
          expand_module_names(Goals, MetaSpecs, Module, ExpandedGoals, HeadVars)
       ;  Goals = ExpandedGoals
       )
    ;  UnexpandedGoals = ExpandedGoals
    ).


expand_module_name(ESG0, M, ESG) :-
    (  var(ESG0) ->
       ESG = M:ESG0
    ;  ESG0 = _:_ ->
       ESG = ESG0
    ;  ESG = M:ESG0
    ).


expand_meta_predicate_subgoals([SG | SGs], [MS | MSs], M, [ESG | ESGs], HeadVars) :-
    (  (  integer(MS),
          MS >= 0
       )  ->
       (  var(SG),
          pairs:same_key(SG, HeadVars, [_|_], _) ->
          expand_subgoal(SG, MS, M, ESG, HeadVars)
       ;  expand_subgoal(SG, MS, M, ESG0, HeadVars),
          expand_module_name(ESG0, M, ESG)
       ),
       expand_meta_predicate_subgoals(SGs, MSs, M, ESGs, HeadVars)
    ;  ESG = SG,
       expand_meta_predicate_subgoals(SGs, MSs, M, ESGs, HeadVars)
    ).

expand_meta_predicate_subgoals([], _, _, [], _).


expand_module_names(Goals, MetaSpecs, Module, ExpandedGoals, HeadVars) :-
    Goals =.. [GoalFunctor | SubGoals],
    (  GoalFunctor == (:),
       SubGoals = [M, SubGoal] ->
       expand_module_names(SubGoal, MetaSpecs, M, ExpandedSubGoal, HeadVars),
       ExpandedGoals = M:ExpandedSubGoal
    ;  expand_meta_predicate_subgoals(SubGoals, MetaSpecs, Module, ExpandedGoalList, HeadVars),
       ExpandedGoals =.. [GoalFunctor | ExpandedGoalList]
    ).


expand_goal(UnexpandedGoals, Module, ExpandedGoals) :-
    expand_goal(UnexpandedGoals, Module, ExpandedGoals, []),
    !.

expand_goal_cases((Goal0, Goals0), Module, ExpandedGoals, HeadVars) :-
    (  expand_goal(Goal0, Module, Goal1, HeadVars) ->
       expand_goal(Goals0, Module, Goals1, HeadVars),
       thread_goals(Goal1, ExpandedGoals, Goals1, (','))
    ;  expand_goal(Goals0, Module, Goals1, HeadVars),
       ExpandedGoals = (Goal0, Goals1)
    ).
expand_goal_cases((Goals0 -> Goals1), Module, ExpandedGoals, HeadVars) :-
    expand_goal(Goals0, Module, ExpandedGoals0, HeadVars),
    expand_goal(Goals1, Module, ExpandedGoals1, HeadVars),
    ExpandedGoals = (ExpandedGoals0 -> ExpandedGoals1).
expand_goal_cases((Goals0 ; Goals1), Module, ExpandedGoals, HeadVars) :-
    expand_goal(Goals0, Module, ExpandedGoals0, HeadVars),
    expand_goal(Goals1, Module, ExpandedGoals1, HeadVars),
    ExpandedGoals = (ExpandedGoals0 ; ExpandedGoals1).
expand_goal_cases((\+ Goals0), Module, ExpandedGoals, HeadVars) :-
    expand_goal(Goals0, Module, Goals1, HeadVars),
    ExpandedGoals = (\+ Goals1).
expand_goal_cases((Module:Goals0), _, ExpandedGoals, HeadVars) :-
    expand_goal(Goals0, Module, Goals1, HeadVars),
    ExpandedGoals = (Module:Goals1).

expand_goal(UnexpandedGoals, Module, ExpandedGoals, HeadVars) :-
    (  var(UnexpandedGoals) ->
       expand_module_names(call(UnexpandedGoals), [0], Module, ExpandedGoals, HeadVars)
    ;  goal_expansion(UnexpandedGoals, Module, UnexpandedGoals1),
       (  Module \== user ->
          goal_expansion(UnexpandedGoals1, user, Goals)
       ;  Goals = UnexpandedGoals1
       ),
       (  expand_goal_cases(Goals, Module, ExpandedGoals, HeadVars) ->
          true
       ;  predicate_property(Module:Goals, meta_predicate(MetaSpecs)) ->
          expand_module_names(Goals, MetaSpecs, Module, ExpandedGoals, HeadVars)
       ;  thread_goals(Goals, ExpandedGoals, (','))
       ;  Goals = ExpandedGoals
       )
    ).

thread_goals(Goals0, Goals1, Functor) :-
    (  var(Goals0) ->
       Goals0 = Goals1
    ;  (  Goals0 = [G | Gs] ->
          (  Gs = [] ->
             Goals1 = G
          ;  Goals1 =.. [Functor, G, Goals2],
             thread_goals(Gs, Goals2, Functor)
          )
       ;  Goals1 = Goals0
       )
    ).

thread_goals(Goals0, Goals1, Hole, Functor) :-
    (  var(Goals0) ->
       Goals1 =.. [Functor, Goals0, Hole]
    ;  (  Goals0 = [G | Gs] ->
          (  Gs == [] ->
             Goals1 =.. [Functor, G, Hole]
          ;  Goals1 =.. [Functor, G, Goals2],
             thread_goals(Gs, Goals2, Hole, Functor)
          )
       ;  Goals1 =.. [Functor, Goals0, Hole]
       )
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% call/{1-64} with dynamic goal expansion.
%
% The program used to generate the call/N predicates:
%
%
% :- use_module(library(between)).
% :- use_module(library(error)).
% :- use_module(library(lists)).
% :- use_module(library(format)).
%
% n_call_clause(N, Clause) :-
%     length(Args, N),
%     Head =.. [call, G | Args],
%     N1 is N + 1,
%     Clause = (Head :- (  var(G) ->
%                           instantiation_error(call/N1)
%                       ;   call_clause(G, Args, N1, G0) ->
%                           '$call'(G0)
%                       ;   type_error(callable, G, call/N1)
%                       )).
%
% generate_call_forms :-
%     between(1, 64, N),
%     n_call_clause(N, Clause),
%     portray_clause(Clause),
%     nl,
%     false.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% The '$call' functor is an escape hatch from goal expansion. So far,
% it is used only to avoid infinite recursion into expand_goal/3.

call_clause('$call'(G), G0) :-
    (  var(G),
       instantiation_error(call/1)
    ;  G = M:G1,
       !,
       functor(G1, F, _),
       atom(F),
       atom(M),
       F \== [],
       G0 = M:G1
    ;  !,
       functor(G, F, _),
       atom(F),
       F \== [],
       load_context(M),
       G0 = M:G
    ).

call_clause(G, G0) :-
    strip_module(G, M, G1),
    functor(G1, F, _),
    atom(F),
    F \== [],
    (  var(M) ->
       load_context(M)
    ;  true
    ),
    expand_goal(M:G1, M, G0).


call(G) :-
    (  var(G) ->
       instantiation_error(call/1)
    ;  call_clause(G, G0) ->
       '$call'(G0)
    ;  type_error(callable, G, call/1)
    ).


call_clause('$call'(G1), Args, N, G0) :-
    (  var(G1),
       instantiation_error(call/N)
    ;  G1 = M:G2,
       !,
       atom(M),
       G2 =.. [F | As],
       atom(F),
       F \== [],
       append(As, Args, As1),
       G3 =.. [F | As1],
       G0 = M:G3
    ;  !,
       G1 =.. [F | As],
       atom(F),
       F \== [],
       load_context(M),
       append(As, Args, As1),
       G2 =.. [F | As1],
       G0 = M:G2
    ).

call_clause(G, Args, _, G0) :-
    strip_module(G, M, G1),
    G1 =.. [F | As],
    atom(F),
    F \== [],
    (  var(M) ->
       load_context(M)
    ;  true
    ),
    append(As, Args, As1),
    G2 =.. [F | As1],
    expand_goal(M:G2, M, G0).


call(A,B) :-
    (  var(A) ->
       instantiation_error(call/2)
    ;  call_clause(A,[B],2,C) ->
       '$call'(C)
    ;  type_error(callable,A,call/2)
    ).

call(A,B,C) :-
    (  var(A) ->
       instantiation_error(call/3)
    ;  call_clause(A,[B,C],3,D) ->
       '$call'(D)
    ;  type_error(callable,A,call/3)
    ).

call(A,B,C,D) :-
    (  var(A) ->
       instantiation_error(call/4)
    ;  call_clause(A,[B,C,D],4,E) ->
       '$call'(E)
    ;  type_error(callable,A,call/4)
    ).

call(A,B,C,D,E) :-
    (  var(A) ->
       instantiation_error(call/5)
    ;  call_clause(A,[B,C,D,E],5,F) ->
       '$call'(F)
    ;  type_error(callable,A,call/5)
    ).

call(A,B,C,D,E,F) :-
    (  var(A) ->
       instantiation_error(call/6)
    ;  call_clause(A,[B,C,D,E,F],6,G) ->
       '$call'(G)
    ;  type_error(callable,A,call/6)
    ).

call(A,B,C,D,E,F,G) :-
    (  var(A) ->
       instantiation_error(call/7)
    ;  call_clause(A,[B,C,D,E,F,G],7,H) ->
       '$call'(H)
    ;  type_error(callable,A,call/7)
    ).

call(A,B,C,D,E,F,G,H) :-
    (  var(A) ->
       instantiation_error(call/8)
    ;  call_clause(A,[B,C,D,E,F,G,H],8,I) ->
       '$call'(I)
    ;  type_error(callable,A,call/8)
    ).

call(A,B,C,D,E,F,G,H,I) :-
    (  var(A) ->
       instantiation_error(call/9)
    ;  call_clause(A,[B,C,D,E,F,G,H,I],9,J) ->
       '$call'(J)
    ;  type_error(callable,A,call/9)
    ).

call(A,B,C,D,E,F,G,H,I,J) :-
    (  var(A) ->
       instantiation_error(call/10)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J],10,K) ->
       '$call'(K)
    ;  type_error(callable,A,call/10)
    ).

call(A,B,C,D,E,F,G,H,I,J,K) :-
    (  var(A) ->
       instantiation_error(call/11)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K],11,L) ->
       '$call'(L)
    ;  type_error(callable,A,call/11)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L) :-
    (  var(A) ->
       instantiation_error(call/12)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L],12,M) ->
       '$call'(M)
    ;  type_error(callable,A,call/12)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M) :-
    (  var(A) ->
       instantiation_error(call/13)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M],13,N) ->
       '$call'(N)
    ;  type_error(callable,A,call/13)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N) :-
    (  var(A) ->
       instantiation_error(call/14)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N],14,O) ->
       '$call'(O)
    ;  type_error(callable,A,call/14)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O) :-
    (  var(A) ->
       instantiation_error(call/15)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O],15,P) ->
       '$call'(P)
    ;  type_error(callable,A,call/15)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P) :-
    (  var(A) ->
       instantiation_error(call/16)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P],16,Q) ->
       '$call'(Q)
    ;  type_error(callable,A,call/16)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q) :-
    (  var(A) ->
       instantiation_error(call/17)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q],17,R) ->
       '$call'(R)
    ;  type_error(callable,A,call/17)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R) :-
    (  var(A) ->
       instantiation_error(call/18)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R],18,S) ->
       '$call'(S)
    ;  type_error(callable,A,call/18)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S) :-
    (  var(A) ->
       instantiation_error(call/19)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S],19,T) ->
       '$call'(T)
    ;  type_error(callable,A,call/19)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T) :-
    (  var(A) ->
       instantiation_error(call/20)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T],20,U) ->
       '$call'(U)
    ;  type_error(callable,A,call/20)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U) :-
    (  var(A) ->
       instantiation_error(call/21)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U],21,V) ->
       '$call'(V)
    ;  type_error(callable,A,call/21)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V) :-
    (  var(A) ->
       instantiation_error(call/22)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V],22,W) ->
       '$call'(W)
    ;  type_error(callable,A,call/22)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W) :-
    (  var(A) ->
       instantiation_error(call/23)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W],23,X) ->
       '$call'(X)
    ;  type_error(callable,A,call/23)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X) :-
    (  var(A) ->
       instantiation_error(call/24)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X],24,Y) ->
       '$call'(Y)
    ;  type_error(callable,A,call/24)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y) :-
    (  var(A) ->
       instantiation_error(call/25)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y],25,Z) ->
       '$call'(Z)
    ;  type_error(callable,A,call/25)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z) :-
    (  var(A) ->
       instantiation_error(call/26)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z],26,A1) ->
       '$call'(A1)
    ;  type_error(callable,A,call/26)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1) :-
    (  var(A) ->
       instantiation_error(call/27)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1],27,B1) ->
       '$call'(B1)
    ;  type_error(callable,A,call/27)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1) :-
    (  var(A) ->
       instantiation_error(call/28)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1],28,C1) ->
       '$call'(C1)
    ;  type_error(callable,A,call/28)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1) :-
    (  var(A) ->
       instantiation_error(call/29)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1],29,D1) ->
       '$call'(D1)
    ;  type_error(callable,A,call/29)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1) :-
    (  var(A) ->
       instantiation_error(call/30)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1],30,E1) ->
       '$call'(E1)
    ;  type_error(callable,A,call/30)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1) :-
    (  var(A) ->
       instantiation_error(call/31)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1],31,F1) ->
       '$call'(F1)
    ;  type_error(callable,A,call/31)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1) :-
    (  var(A) ->
       instantiation_error(call/32)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1],32,G1) ->
       '$call'(G1)
    ;  type_error(callable,A,call/32)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1) :-
    (  var(A) ->
       instantiation_error(call/33)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1],33,H1) ->
       '$call'(H1)
    ;  type_error(callable,A,call/33)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1) :-
    (  var(A) ->
       instantiation_error(call/34)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1],34,I1) ->
       '$call'(I1)
    ;  type_error(callable,A,call/34)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1) :-
    (  var(A) ->
       instantiation_error(call/35)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1],35,J1) ->
       '$call'(J1)
    ;  type_error(callable,A,call/35)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1) :-
    (  var(A) ->
       instantiation_error(call/36)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1],36,K1) ->
       '$call'(K1)
    ;  type_error(callable,A,call/36)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1) :-
    (  var(A) ->
       instantiation_error(call/37)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1],37,L1) ->
       '$call'(L1)
    ;  type_error(callable,A,call/37)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1) :-
    (  var(A) ->
       instantiation_error(call/38)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1],38,M1) ->
       '$call'(M1)
    ;  type_error(callable,A,call/38)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1) :-
    (  var(A) ->
       instantiation_error(call/39)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1],39,N1) ->
       '$call'(N1)
    ;  type_error(callable,A,call/39)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1) :-
    (  var(A) ->
       instantiation_error(call/40)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1],40,O1) ->
       '$call'(O1)
    ;  type_error(callable,A,call/40)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1) :-
    (  var(A) ->
       instantiation_error(call/41)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1],41,P1) ->
       '$call'(P1)
    ;  type_error(callable,A,call/41)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1) :-
    (  var(A) ->
       instantiation_error(call/42)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1],42,Q1) ->
       '$call'(Q1)
    ;  type_error(callable,A,call/42)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1) :-
    (  var(A) ->
       instantiation_error(call/43)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1],43,R1) ->
       '$call'(R1)
    ;  type_error(callable,A,call/43)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1) :-
    (  var(A) ->
       instantiation_error(call/44)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1],44,S1) ->
       '$call'(S1)
    ;  type_error(callable,A,call/44)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1) :-
    (  var(A) ->
       instantiation_error(call/45)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1],45,T1) ->
       '$call'(T1)
    ;  type_error(callable,A,call/45)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1) :-
    (  var(A) ->
       instantiation_error(call/46)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1],46,U1) ->
       '$call'(U1)
    ;  type_error(callable,A,call/46)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1) :-
    (  var(A) ->
       instantiation_error(call/47)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1],47,V1) ->
       '$call'(V1)
    ;  type_error(callable,A,call/47)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1) :-
    (  var(A) ->
       instantiation_error(call/48)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1],48,W1) ->
       '$call'(W1)
    ;  type_error(callable,A,call/48)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1) :-
    (  var(A) ->
       instantiation_error(call/49)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1],49,X1) ->
       '$call'(X1)
    ;  type_error(callable,A,call/49)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1) :-
    (  var(A) ->
       instantiation_error(call/50)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1],50,Y1) ->
       '$call'(Y1)
    ;  type_error(callable,A,call/50)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1) :-
    (  var(A) ->
       instantiation_error(call/51)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1],51,Z1) ->
       '$call'(Z1)
    ;  type_error(callable,A,call/51)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1) :-
    (  var(A) ->
       instantiation_error(call/52)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1],52,A2) ->
       '$call'(A2)
    ;  type_error(callable,A,call/52)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2) :-
    (  var(A) ->
       instantiation_error(call/53)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2],53,B2) ->
       '$call'(B2)
    ;  type_error(callable,A,call/53)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2) :-
    (  var(A) ->
       instantiation_error(call/54)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2],54,C2) ->
       '$call'(C2)
    ;  type_error(callable,A,call/54)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2) :-
    (  var(A) ->
       instantiation_error(call/55)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2],55,D2) ->
       '$call'(D2)
    ;  type_error(callable,A,call/55)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2) :-
    (  var(A) ->
       instantiation_error(call/56)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2],56,E2) ->
       '$call'(E2)
    ;  type_error(callable,A,call/56)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2) :-
    (  var(A) ->
       instantiation_error(call/57)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2],57,F2) ->
       '$call'(F2)
    ;  type_error(callable,A,call/57)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2) :-
    (  var(A) ->
       instantiation_error(call/58)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2],58,G2) ->
       '$call'(G2)
    ;  type_error(callable,A,call/58)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2) :-
    (  var(A) ->
       instantiation_error(call/59)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2],59,H2) ->
       '$call'(H2)
    ;  type_error(callable,A,call/59)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2) :-
    (  var(A) ->
       instantiation_error(call/60)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2],60,I2) ->
       '$call'(I2)
    ;  type_error(callable,A,call/60)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2) :-
    (  var(A) ->
       instantiation_error(call/61)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2],61,J2) ->
       '$call'(J2)
    ;  type_error(callable,A,call/61)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2) :-
    (  var(A) ->
       instantiation_error(call/62)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2],62,K2) ->
       '$call'(K2)
    ;  type_error(callable,A,call/62)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2) :-
    (  var(A) ->
       instantiation_error(call/63)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2],63,L2) ->
       '$call'(L2)
    ;  type_error(callable,A,call/63)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2) :-
    (  var(A) ->
       instantiation_error(call/64)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2],64,M2) ->
       '$call'(M2)
    ;  type_error(callable,A,call/64)
    ).

call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2) :-
    (  var(A) ->
       instantiation_error(call/65)
    ;  call_clause(A,[B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2],65,N2) ->
       '$call'(N2)
    ;  type_error(callable,A,call/65)
    ).
