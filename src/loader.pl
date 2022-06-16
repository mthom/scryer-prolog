:- module(loader, [consult/1,
                   expand_goal/3,
                   expand_term/2,
                   file_load/2,
                   load/1,
                   predicate_property/2,
                   prolog_load_context/2,
                   strip_module/3,
                   use_module/1,
                   use_module/2,
                   current_module/1
                  ]).


:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(pairs)).


write_error(Error) :-
    % '$fetch_global_var' is the core system call of bb_get/2, but
    % bb_get may not exist when write_error is first called, so fall
    % back on '$fetch_global_var'.
    (  '$fetch_global_var'('$first_answer', false) ->
       true
    ;  write('   ') % if '$first_answer' isn't defined yet or true,
                    % print indentation.
    ),
    (  nonvar(Error),
       functor(Error, error, 2) ->
       writeq(Error)
    ;  writeq(throw(Error))
    ),
    write('.').

'$print_message_and_fail'(Error) :-
    write_error(Error),
    nl,
    '$fail'.

expand_term(Term, ExpandedTerm) :-
    (  '$predicate_defined'(user, term_expansion, 2),
       catch('$call'(user:term_expansion(Term, ExpandedTerm0)),
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
       '$predicate_defined'(Module, goal_expansion, 2),
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

run_initialization_goals(Module) :-
    (  predicate_property(Module:'$initialization_goals'(_), dynamic) ->
       % FIXME: failing here. also, see add_module.
       findall(Module:Goal, '$call'(builtins:retract(Module:'$initialization_goals'(Goal))), Goals),
       abolish(Module:'$initialization_goals'/1),
       maplist(loader:success_or_warning, Goals)
    ;  true
    ).

success_or_warning(Goal) :-
    (   call(Goal) ->
        true
    ;   %% initialization goals can fail without thwarting the load.
        write('Warning: initialization/1 failed for: '),
        writeq(Goal),
        nl
    ).

run_initialization_goals :-
    prolog_load_context(module, Module),
    run_initialization_goals(user),
    (  Module \== user ->
       run_initialization_goals(Module)
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
    predicate_property(HeadArg, meta_predicate(InnerMetaSpecs0)),
    InnerMetaSpecs0 =.. [_ | InnerMetaSpecs],
    HeadArg =.. [_ | InnerHeadArgs].

inner_meta_specs((:), _, [], []) :-
    !.

inner_meta_specs(N, HeadArg, InnerHeadArgs, InnerMetaSpecs) :-
    integer(N),
    N >= 0,
    HeadArg =.. [Functor | InnerHeadArgs],
    length(InnerHeadArgs1, N),
    append(InnerHeadArgs, InnerHeadArgs1, InnerHeadArgs0),
    CompleteHeadArg =.. [Functor | InnerHeadArgs0],
    predicate_property(CompleteHeadArg, meta_predicate(InnerMetaSpecs0)),
    InnerMetaSpecs0 =.. [_ | InnerMetaSpecs].


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
    ;  predicate_property(Head, meta_predicate(MetaSpecs0)),
       MetaSpecs0 =.. [_ | MetaSpecs],
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
       ;  module_expanded_head_variables(Head1, HeadVars),
          prolog_load_context(module, Target),
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

current_module(Module) :-
    (  var(Module) ->
       instantiation_error(current_module/1)
    ;  \+ atom(Module) ->
       type_error(atom, Module, current_module/1)
    ;  '$module_exists'(Module)
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
             error(existence_error(source_sink, _), _),
             ( atom_concat(Path, '.pl', ExtendedPath),
               open(ExtendedPath, read, Stream)
             )
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
    '$meta_predicate_property'(Module, Name, Arity, MetaPredicateTerm).
check_predicate_property(built_in, _, Name, Arity, built_in) :-
    '$built_in_property'(Name, Arity).
check_predicate_property(dynamic, Module, Name, Arity, dynamic) :-
    '$dynamic_property'(Module, Name, Arity).
check_predicate_property(multifile, Module, Name, Arity, multifile) :-
    '$multifile_property'(Module, Name, Arity).
check_predicate_property(discontiguous, Module, Name, Arity, discontiguous) :-
    '$discontiguous_property'(Module, Name, Arity).



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
       (  atom(Name) ->
          extract_predicate_property(Property, PropertyType),
          check_predicate_property(PropertyType, Module, Name, Arity, Property)
       ;  type_error(callable, Callable0, predicate_property/2)
       )
    ;  functor(Callable, Name, Arity),
       (  atom(Name) ->
          extract_predicate_property(Property, PropertyType),
          load_context(Module),
          check_predicate_property(PropertyType, Module, Name, Arity, Property)
       ;  type_error(callable, Callable, predicate_property/2)
       )
    ).

strip_module(Goal, M, G) :-
    '$strip_module'(Goal, M, G).

:- non_counted_backtracking expand_subgoal/5.

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


:- non_counted_backtracking expand_module_name/4.

expand_module_name(ESG0, MS, M, ESG) :-
    (  var(ESG0) ->
       ESG = M:ESG0
    ;  ESG0 = _:_ ->
       ESG = ESG0
    ;  functor(ESG0, F, A0),
       integer(MS),
       A is A0 + MS,
       functor(EESG0, F, A),
       predicate_property(EESG0, built_in) ->
       ESG = ESG0
    ;  ESG = M:ESG0
    ).


:- non_counted_backtracking expand_meta_predicate_subgoals/5.

expand_meta_predicate_subgoals([SG | SGs], [MS | MSs], M, [ESG | ESGs], HeadVars) :-
    (  (  integer(MS),
          MS >= 0
       ;  MS == (:)
       )  ->
       (  var(SG),
          pairs:same_key(SG, HeadVars, [_|_], _) ->
          expand_subgoal(SG, MS, M, ESG, HeadVars)
       ;  expand_subgoal(SG, MS, M, ESG0, HeadVars),
          expand_module_name(ESG0, MS, M, ESG)
       ),
       expand_meta_predicate_subgoals(SGs, MSs, M, ESGs, HeadVars)
    ;  ESG = SG,
       expand_meta_predicate_subgoals(SGs, MSs, M, ESGs, HeadVars)
    ).

expand_meta_predicate_subgoals([], _, _, [], _).


:- non_counted_backtracking expand_module_names/5.

expand_module_names(Goals, MetaSpecs, Module, ExpandedGoals, HeadVars) :-
    Goals =.. [GoalFunctor | SubGoals],
    (  GoalFunctor == (:),
       SubGoals = [M, SubGoal] ->
       expand_module_names(SubGoal, MetaSpecs, M, ExpandedSubGoal, HeadVars),
       expand_module_name(ExpandedSubGoal, 0, M, ExpandedGoals)
    ;  expand_meta_predicate_subgoals(SubGoals, MetaSpecs, Module, ExpandedGoalList, HeadVars),
       ExpandedGoals =.. [GoalFunctor | ExpandedGoalList]
    ).


:- non_counted_backtracking expand_goal/3.

expand_goal(UnexpandedGoals, Module, ExpandedGoals) :-
    % if a goal isn't callable, defer to call/N to report the error.
    catch('$call'(loader:expand_goal(UnexpandedGoals, Module, ExpandedGoals, [])),
          error(type_error(callable, _), _),
          '$call'(UnexpandedGoals = ExpandedGoals)),
    !.

:- non_counted_backtracking expand_goal/4.

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
       ;  predicate_property(Module:Goals, meta_predicate(MetaSpecs0)),
          MetaSpecs0 =.. [_ | MetaSpecs] ->
          expand_module_names(Goals, MetaSpecs, Module, ExpandedGoals, HeadVars)
       ;  thread_goals(Goals, ExpandedGoals, (','))
       ;  Goals = ExpandedGoals
       )
    ).

:- non_counted_backtracking expand_goal_cases/4.

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


:- non_counted_backtracking thread_goals/3.

thread_goals(Goals0, Goals1, Functor) :-
    (  var(Goals0) ->
       Goals0 = Goals1
    ;  Goals0 = [G | Gs] ->
       (  Gs = [] ->
          Goals1 = G
       ;  Goals1 =.. [Functor, G, Goals2],
          thread_goals(Gs, Goals2, Functor)
       )
    ;  Goals1 = Goals0
    ).

:- non_counted_backtracking thread_goals/4.

thread_goals(Goals0, Goals1, Hole, Functor) :-
    (  var(Goals0) ->
       Goals1 =.. [Functor, Goals0, Hole]
    ;  Goals0 = [G | Gs] ->
       (  Gs == [] ->
          Goals1 =.. [Functor, G, Hole]
       ;  Goals1 =.. [Functor, G, Goals2],
          thread_goals(Gs, Goals2, Hole, Functor)
       )
    ;  Goals1 =.. [Functor, Goals0, Hole]
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% call/{1-64} with dynamic goal expansion.
%
% The program used to generate the call/N predicates:
%
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
%     CallClause0 =.. ['$prepare_call_clause', G1, M, G0 | Args],
%     CallClause =.. ['$prepare_call_clause', G1, M, G | Args],
%     Clause = (Head :- (  var(G) ->
%                          instantiation_error(call/N1)
%                       ;  G = '$call'(G0) ->
%                          CallClause0,
%                          '$call_with_inference_counting'('$call'(M:G1))
%                       ;  CallClause,
%                          expand_goal(call(M:G1), M, call(G2)),
%                          '$call_with_inference_counting'('$call'(G2))
%                       )
%              ).
%
% generate_call_forms :-
%     between(1, 64, N),
%     n_call_clause(N, Clause),
%     N1 is N+1,
%     portray_clause((:- non_counted_backtracking call/N1)),
%     portray_clause(Clause),
%     nl,
%     false.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The '$call' functor is an escape hatch from goal expansion. So far,
% it is used only to avoid infinite recursion into expand_goal/3.

:- non_counted_backtracking call/1.
call(G) :-
   (  var(G) ->
      instantiation_error(call/1)
   ;  G = '$call'(G0) ->
      '$prepare_call_clause'(G1, M, G0),
      '$call_with_inference_counting'('$call'(M:G1))
   ;  '$prepare_call_clause'(G1, M, G),
      expand_goal(call(M:G1), M, call(G2)),
      '$call_with_inference_counting'('$call'(G2))
   ).

:-non_counted_backtracking call/2.
call(A,B) :-
   (  var(A) ->
      instantiation_error(call/2)
   ;  A= '$call'(C) ->
      '$prepare_call_clause'(D,E,C,B),
      '$call_with_inference_counting'('$call'(E:D))
   ;  '$prepare_call_clause'(D,E,A,B),
      expand_goal(call(E:D),E,call(F)),
      '$call_with_inference_counting'('$call'(F))
   ).

:-non_counted_backtracking call/3.
call(A,B,C) :-
   (  var(A) ->
      instantiation_error(call/3)
   ;  A= '$call'(D) ->
      '$prepare_call_clause'(E,F,D,B,C),
      '$call_with_inference_counting'('$call'(F:E))
   ;  '$prepare_call_clause'(E,F,A,B,C),
      expand_goal(call(F:E),F,call(G)),
      '$call_with_inference_counting'('$call'(G))
   ).

:-non_counted_backtracking call/4.
call(A,B,C,D) :-
   (  var(A) ->
      instantiation_error(call/4)
   ;  A= '$call'(E) ->
      '$prepare_call_clause'(F,G,E,B,C,D),
      '$call_with_inference_counting'('$call'(G:F))
   ;  '$prepare_call_clause'(F,G,A,B,C,D),
      expand_goal(call(G:F),G,call(H)),
      '$call_with_inference_counting'('$call'(H))
   ).

:-non_counted_backtracking call/5.
call(A,B,C,D,E) :-
   (  var(A) ->
      instantiation_error(call/5)
   ;  A= '$call'(F) ->
      '$prepare_call_clause'(G,H,F,B,C,D,E),
      '$call_with_inference_counting'('$call'(H:G))
   ;  '$prepare_call_clause'(G,H,A,B,C,D,E),
      expand_goal(call(H:G),H,call(I)),
      '$call_with_inference_counting'('$call'(I))
   ).

:-non_counted_backtracking call/6.
call(A,B,C,D,E,F) :-
   (  var(A) ->
      instantiation_error(call/6)
   ;  A= '$call'(G) ->
      '$prepare_call_clause'(H,I,G,B,C,D,E,F),
      '$call_with_inference_counting'('$call'(I:H))
   ;  '$prepare_call_clause'(H,I,A,B,C,D,E,F),
      expand_goal(call(I:H),I,call(J)),
      '$call_with_inference_counting'('$call'(J))
   ).

:-non_counted_backtracking call/7.
call(A,B,C,D,E,F,G) :-
   (  var(A) ->
      instantiation_error(call/7)
   ;  A= '$call'(H) ->
      '$prepare_call_clause'(I,J,H,B,C,D,E,F,G),
      '$call_with_inference_counting'('$call'(J:I))
   ;  '$prepare_call_clause'(I,J,A,B,C,D,E,F,G),
      expand_goal(call(J:I),J,call(K)),
      '$call_with_inference_counting'('$call'(K))
   ).

:-non_counted_backtracking call/8.
call(A,B,C,D,E,F,G,H) :-
   (  var(A) ->
      instantiation_error(call/8)
   ;  A= '$call'(I) ->
      '$prepare_call_clause'(J,K,I,B,C,D,E,F,G,H),
      '$call_with_inference_counting'('$call'(K:J))
   ;  '$prepare_call_clause'(J,K,A,B,C,D,E,F,G,H),
      expand_goal(call(K:J),K,call(L)),
      '$call_with_inference_counting'('$call'(L))
   ).

:-non_counted_backtracking call/9.
call(A,B,C,D,E,F,G,H,I) :-
   (  var(A) ->
      instantiation_error(call/9)
   ;  A= '$call'(J) ->
      '$prepare_call_clause'(K,L,J,B,C,D,E,F,G,H,I),
      '$call_with_inference_counting'('$call'(L:K))
   ;  '$prepare_call_clause'(K,L,A,B,C,D,E,F,G,H,I),
      expand_goal(call(L:K),L,call(M)),
      '$call_with_inference_counting'('$call'(M))
   ).

:-non_counted_backtracking call/10.
call(A,B,C,D,E,F,G,H,I,J) :-
   (  var(A) ->
      instantiation_error(call/10)
   ;  A= '$call'(K) ->
      '$prepare_call_clause'(L,M,K,B,C,D,E,F,G,H,I,J),
      '$call_with_inference_counting'('$call'(M:L))
   ;  '$prepare_call_clause'(L,M,A,B,C,D,E,F,G,H,I,J),
      expand_goal(call(M:L),M,call(N)),
      '$call_with_inference_counting'('$call'(N))
   ).

:-non_counted_backtracking call/11.
call(A,B,C,D,E,F,G,H,I,J,K) :-
   (  var(A) ->
      instantiation_error(call/11)
   ;  A= '$call'(L) ->
      '$prepare_call_clause'(M,N,L,B,C,D,E,F,G,H,I,J,K),
      '$call_with_inference_counting'('$call'(N:M))
   ;  '$prepare_call_clause'(M,N,A,B,C,D,E,F,G,H,I,J,K),
      expand_goal(call(N:M),N,call(O)),
      '$call_with_inference_counting'('$call'(O))
   ).

:-non_counted_backtracking call/12.
call(A,B,C,D,E,F,G,H,I,J,K,L) :-
   (  var(A) ->
      instantiation_error(call/12)
   ;  A= '$call'(M) ->
      '$prepare_call_clause'(N,O,M,B,C,D,E,F,G,H,I,J,K,L),
      '$call_with_inference_counting'('$call'(O:N))
   ;  '$prepare_call_clause'(N,O,A,B,C,D,E,F,G,H,I,J,K,L),
      expand_goal(call(O:N),O,call(P)),
      '$call_with_inference_counting'('$call'(P))
   ).

:-non_counted_backtracking call/13.
call(A,B,C,D,E,F,G,H,I,J,K,L,M) :-
   (  var(A) ->
      instantiation_error(call/13)
   ;  A= '$call'(N) ->
      '$prepare_call_clause'(O,P,N,B,C,D,E,F,G,H,I,J,K,L,M),
      '$call_with_inference_counting'('$call'(P:O))
   ;  '$prepare_call_clause'(O,P,A,B,C,D,E,F,G,H,I,J,K,L,M),
      expand_goal(call(P:O),P,call(Q)),
      '$call_with_inference_counting'('$call'(Q))
   ).

:-non_counted_backtracking call/14.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N) :-
   (  var(A) ->
      instantiation_error(call/14)
   ;  A= '$call'(O) ->
      '$prepare_call_clause'(P,Q,O,B,C,D,E,F,G,H,I,J,K,L,M,N),
      '$call_with_inference_counting'('$call'(Q:P))
   ;  '$prepare_call_clause'(P,Q,A,B,C,D,E,F,G,H,I,J,K,L,M,N),
      expand_goal(call(Q:P),Q,call(R)),
      '$call_with_inference_counting'('$call'(R))
   ).

:-non_counted_backtracking call/15.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O) :-
   (  var(A) ->
      instantiation_error(call/15)
   ;  A= '$call'(P) ->
      '$prepare_call_clause'(Q,R,P,B,C,D,E,F,G,H,I,J,K,L,M,N,O),
      '$call_with_inference_counting'('$call'(R:Q))
   ;  '$prepare_call_clause'(Q,R,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O),
      expand_goal(call(R:Q),R,call(S)),
      '$call_with_inference_counting'('$call'(S))
   ).

:-non_counted_backtracking call/16.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P) :-
   (  var(A) ->
      instantiation_error(call/16)
   ;  A= '$call'(Q) ->
      '$prepare_call_clause'(R,S,Q,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P),
      '$call_with_inference_counting'('$call'(S:R))
   ;  '$prepare_call_clause'(R,S,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P),
      expand_goal(call(S:R),S,call(T)),
      '$call_with_inference_counting'('$call'(T))
   ).

:-non_counted_backtracking call/17.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q) :-
   (  var(A) ->
      instantiation_error(call/17)
   ;  A= '$call'(R) ->
      '$prepare_call_clause'(S,T,R,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q),
      '$call_with_inference_counting'('$call'(T:S))
   ;  '$prepare_call_clause'(S,T,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q),
      expand_goal(call(T:S),T,call(U)),
      '$call_with_inference_counting'('$call'(U))
   ).

:-non_counted_backtracking call/18.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R) :-
   (  var(A) ->
      instantiation_error(call/18)
   ;  A= '$call'(S) ->
      '$prepare_call_clause'(T,U,S,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R),
      '$call_with_inference_counting'('$call'(U:T))
   ;  '$prepare_call_clause'(T,U,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R),
      expand_goal(call(U:T),U,call(V)),
      '$call_with_inference_counting'('$call'(V))
   ).

:-non_counted_backtracking call/19.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S) :-
   (  var(A) ->
      instantiation_error(call/19)
   ;  A= '$call'(T) ->
      '$prepare_call_clause'(U,V,T,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S),
      '$call_with_inference_counting'('$call'(V:U))
   ;  '$prepare_call_clause'(U,V,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S),
      expand_goal(call(V:U),V,call(W)),
      '$call_with_inference_counting'('$call'(W))
   ).

:-non_counted_backtracking call/20.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T) :-
   (  var(A) ->
      instantiation_error(call/20)
   ;  A= '$call'(U) ->
      '$prepare_call_clause'(V,W,U,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T),
      '$call_with_inference_counting'('$call'(W:V))
   ;  '$prepare_call_clause'(V,W,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T),
      expand_goal(call(W:V),W,call(X)),
      '$call_with_inference_counting'('$call'(X))
   ).

:-non_counted_backtracking call/21.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U) :-
   (  var(A) ->
      instantiation_error(call/21)
   ;  A= '$call'(V) ->
      '$prepare_call_clause'(W,X,V,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U),
      '$call_with_inference_counting'('$call'(X:W))
   ;  '$prepare_call_clause'(W,X,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U),
      expand_goal(call(X:W),X,call(Y)),
      '$call_with_inference_counting'('$call'(Y))
   ).

:-non_counted_backtracking call/22.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V) :-
   (  var(A) ->
      instantiation_error(call/22)
   ;  A= '$call'(W) ->
      '$prepare_call_clause'(X,Y,W,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V),
      '$call_with_inference_counting'('$call'(Y:X))
   ;  '$prepare_call_clause'(X,Y,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V),
      expand_goal(call(Y:X),Y,call(Z)),
      '$call_with_inference_counting'('$call'(Z))
   ).

:-non_counted_backtracking call/23.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W) :-
   (  var(A) ->
      instantiation_error(call/23)
   ;  A= '$call'(X) ->
      '$prepare_call_clause'(Y,Z,X,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W),
      '$call_with_inference_counting'('$call'(Z:Y))
   ;  '$prepare_call_clause'(Y,Z,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W),
      expand_goal(call(Z:Y),Z,call(A1)),
      '$call_with_inference_counting'('$call'(A1))
   ).

:-non_counted_backtracking call/24.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X) :-
   (  var(A) ->
      instantiation_error(call/24)
   ;  A= '$call'(Y) ->
      '$prepare_call_clause'(Z,A1,Y,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X),
      '$call_with_inference_counting'('$call'(A1:Z))
   ;  '$prepare_call_clause'(Z,A1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X),
      expand_goal(call(A1:Z),A1,call(B1)),
      '$call_with_inference_counting'('$call'(B1))
   ).

:-non_counted_backtracking call/25.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y) :-
   (  var(A) ->
      instantiation_error(call/25)
   ;  A= '$call'(Z) ->
      '$prepare_call_clause'(A1,B1,Z,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y),
      '$call_with_inference_counting'('$call'(B1:A1))
   ;  '$prepare_call_clause'(A1,B1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y),
      expand_goal(call(B1:A1),B1,call(C1)),
      '$call_with_inference_counting'('$call'(C1))
   ).

:-non_counted_backtracking call/26.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z) :-
   (  var(A) ->
      instantiation_error(call/26)
   ;  A= '$call'(A1) ->
      '$prepare_call_clause'(B1,C1,A1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z),
      '$call_with_inference_counting'('$call'(C1:B1))
   ;  '$prepare_call_clause'(B1,C1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z),
      expand_goal(call(C1:B1),C1,call(D1)),
      '$call_with_inference_counting'('$call'(D1))
   ).

:-non_counted_backtracking call/27.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1) :-
   (  var(A) ->
      instantiation_error(call/27)
   ;  A= '$call'(B1) ->
      '$prepare_call_clause'(C1,D1,B1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1),
      '$call_with_inference_counting'('$call'(D1:C1))
   ;  '$prepare_call_clause'(C1,D1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1),
      expand_goal(call(D1:C1),D1,call(E1)),
      '$call_with_inference_counting'('$call'(E1))
   ).

:-non_counted_backtracking call/28.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1) :-
   (  var(A) ->
      instantiation_error(call/28)
   ;  A= '$call'(C1) ->
      '$prepare_call_clause'(D1,E1,C1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1),
      '$call_with_inference_counting'('$call'(E1:D1))
   ;  '$prepare_call_clause'(D1,E1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1),
      expand_goal(call(E1:D1),E1,call(F1)),
      '$call_with_inference_counting'('$call'(F1))
   ).

:-non_counted_backtracking call/29.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1) :-
   (  var(A) ->
      instantiation_error(call/29)
   ;  A= '$call'(D1) ->
      '$prepare_call_clause'(E1,F1,D1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1),
      '$call_with_inference_counting'('$call'(F1:E1))
   ;  '$prepare_call_clause'(E1,F1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1),
      expand_goal(call(F1:E1),F1,call(G1)),
      '$call_with_inference_counting'('$call'(G1))
   ).

:-non_counted_backtracking call/30.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1) :-
   (  var(A) ->
      instantiation_error(call/30)
   ;  A= '$call'(E1) ->
      '$prepare_call_clause'(F1,G1,E1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1),
      '$call_with_inference_counting'('$call'(G1:F1))
   ;  '$prepare_call_clause'(F1,G1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1),
      expand_goal(call(G1:F1),G1,call(H1)),
      '$call_with_inference_counting'('$call'(H1))
   ).

:-non_counted_backtracking call/31.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1) :-
   (  var(A) ->
      instantiation_error(call/31)
   ;  A= '$call'(F1) ->
      '$prepare_call_clause'(G1,H1,F1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1),
      '$call_with_inference_counting'('$call'(H1:G1))
   ;  '$prepare_call_clause'(G1,H1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1),
      expand_goal(call(H1:G1),H1,call(I1)),
      '$call_with_inference_counting'('$call'(I1))
   ).

:-non_counted_backtracking call/32.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1) :-
   (  var(A) ->
      instantiation_error(call/32)
   ;  A= '$call'(G1) ->
      '$prepare_call_clause'(H1,I1,G1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1),
      '$call_with_inference_counting'('$call'(I1:H1))
   ;  '$prepare_call_clause'(H1,I1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1),
      expand_goal(call(I1:H1),I1,call(J1)),
      '$call_with_inference_counting'('$call'(J1))
   ).

:-non_counted_backtracking call/33.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1) :-
   (  var(A) ->
      instantiation_error(call/33)
   ;  A= '$call'(H1) ->
      '$prepare_call_clause'(I1,J1,H1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1),
      '$call_with_inference_counting'('$call'(J1:I1))
   ;  '$prepare_call_clause'(I1,J1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1),
      expand_goal(call(J1:I1),J1,call(K1)),
      '$call_with_inference_counting'('$call'(K1))
   ).

:-non_counted_backtracking call/34.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1) :-
   (  var(A) ->
      instantiation_error(call/34)
   ;  A= '$call'(I1) ->
      '$prepare_call_clause'(J1,K1,I1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1),
      '$call_with_inference_counting'('$call'(K1:J1))
   ;  '$prepare_call_clause'(J1,K1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1),
      expand_goal(call(K1:J1),K1,call(L1)),
      '$call_with_inference_counting'('$call'(L1))
   ).

:-non_counted_backtracking call/35.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1) :-
   (  var(A) ->
      instantiation_error(call/35)
   ;  A= '$call'(J1) ->
      '$prepare_call_clause'(K1,L1,J1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1),
      '$call_with_inference_counting'('$call'(L1:K1))
   ;  '$prepare_call_clause'(K1,L1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1),
      expand_goal(call(L1:K1),L1,call(M1)),
      '$call_with_inference_counting'('$call'(M1))
   ).

:-non_counted_backtracking call/36.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1) :-
   (  var(A) ->
      instantiation_error(call/36)
   ;  A= '$call'(K1) ->
      '$prepare_call_clause'(L1,M1,K1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1),
      '$call_with_inference_counting'('$call'(M1:L1))
   ;  '$prepare_call_clause'(L1,M1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1),
      expand_goal(call(M1:L1),M1,call(N1)),
      '$call_with_inference_counting'('$call'(N1))
   ).

:-non_counted_backtracking call/37.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1) :-
   (  var(A) ->
      instantiation_error(call/37)
   ;  A= '$call'(L1) ->
      '$prepare_call_clause'(M1,N1,L1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1),
      '$call_with_inference_counting'('$call'(N1:M1))
   ;  '$prepare_call_clause'(M1,N1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1),
      expand_goal(call(N1:M1),N1,call(O1)),
      '$call_with_inference_counting'('$call'(O1))
   ).

:-non_counted_backtracking call/38.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1) :-
   (  var(A) ->
      instantiation_error(call/38)
   ;  A= '$call'(M1) ->
      '$prepare_call_clause'(N1,O1,M1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1),
      '$call_with_inference_counting'('$call'(O1:N1))
   ;  '$prepare_call_clause'(N1,O1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1),
      expand_goal(call(O1:N1),O1,call(P1)),
      '$call_with_inference_counting'('$call'(P1))
   ).

:-non_counted_backtracking call/39.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1) :-
   (  var(A) ->
      instantiation_error(call/39)
   ;  A= '$call'(N1) ->
      '$prepare_call_clause'(O1,P1,N1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1),
      '$call_with_inference_counting'('$call'(P1:O1))
   ;  '$prepare_call_clause'(O1,P1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1),
      expand_goal(call(P1:O1),P1,call(Q1)),
      '$call_with_inference_counting'('$call'(Q1))
   ).

:-non_counted_backtracking call/40.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1) :-
   (  var(A) ->
      instantiation_error(call/40)
   ;  A= '$call'(O1) ->
      '$prepare_call_clause'(P1,Q1,O1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1),
      '$call_with_inference_counting'('$call'(Q1:P1))
   ;  '$prepare_call_clause'(P1,Q1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1),
      expand_goal(call(Q1:P1),Q1,call(R1)),
      '$call_with_inference_counting'('$call'(R1))
   ).

:-non_counted_backtracking call/41.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1) :-
   (  var(A) ->
      instantiation_error(call/41)
   ;  A= '$call'(P1) ->
      '$prepare_call_clause'(Q1,R1,P1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1),
      '$call_with_inference_counting'('$call'(R1:Q1))
   ;  '$prepare_call_clause'(Q1,R1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1),
      expand_goal(call(R1:Q1),R1,call(S1)),
      '$call_with_inference_counting'('$call'(S1))
   ).

:-non_counted_backtracking call/42.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1) :-
   (  var(A) ->
      instantiation_error(call/42)
   ;  A= '$call'(Q1) ->
      '$prepare_call_clause'(R1,S1,Q1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1),
      '$call_with_inference_counting'('$call'(S1:R1))
   ;  '$prepare_call_clause'(R1,S1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1),
      expand_goal(call(S1:R1),S1,call(T1)),
      '$call_with_inference_counting'('$call'(T1))
   ).

:-non_counted_backtracking call/43.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1) :-
   (  var(A) ->
      instantiation_error(call/43)
   ;  A= '$call'(R1) ->
      '$prepare_call_clause'(S1,T1,R1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1),
      '$call_with_inference_counting'('$call'(T1:S1))
   ;  '$prepare_call_clause'(S1,T1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1),
      expand_goal(call(T1:S1),T1,call(U1)),
      '$call_with_inference_counting'('$call'(U1))
   ).

:-non_counted_backtracking call/44.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1) :-
   (  var(A) ->
      instantiation_error(call/44)
   ;  A= '$call'(S1) ->
      '$prepare_call_clause'(T1,U1,S1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1),
      '$call_with_inference_counting'('$call'(U1:T1))
   ;  '$prepare_call_clause'(T1,U1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1),
      expand_goal(call(U1:T1),U1,call(V1)),
      '$call_with_inference_counting'('$call'(V1))
   ).

:-non_counted_backtracking call/45.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1) :-
   (  var(A) ->
      instantiation_error(call/45)
   ;  A= '$call'(T1) ->
      '$prepare_call_clause'(U1,V1,T1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1),
      '$call_with_inference_counting'('$call'(V1:U1))
   ;  '$prepare_call_clause'(U1,V1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1),
      expand_goal(call(V1:U1),V1,call(W1)),
      '$call_with_inference_counting'('$call'(W1))
   ).

:-non_counted_backtracking call/46.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1) :-
   (  var(A) ->
      instantiation_error(call/46)
   ;  A= '$call'(U1) ->
      '$prepare_call_clause'(V1,W1,U1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1),
      '$call_with_inference_counting'('$call'(W1:V1))
   ;  '$prepare_call_clause'(V1,W1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1),
      expand_goal(call(W1:V1),W1,call(X1)),
      '$call_with_inference_counting'('$call'(X1))
   ).

:-non_counted_backtracking call/47.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1) :-
   (  var(A) ->
      instantiation_error(call/47)
   ;  A= '$call'(V1) ->
      '$prepare_call_clause'(W1,X1,V1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1),
      '$call_with_inference_counting'('$call'(X1:W1))
   ;  '$prepare_call_clause'(W1,X1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1),
      expand_goal(call(X1:W1),X1,call(Y1)),
      '$call_with_inference_counting'('$call'(Y1))
   ).

:-non_counted_backtracking call/48.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1) :-
   (  var(A) ->
      instantiation_error(call/48)
   ;  A= '$call'(W1) ->
      '$prepare_call_clause'(X1,Y1,W1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1),
      '$call_with_inference_counting'('$call'(Y1:X1))
   ;  '$prepare_call_clause'(X1,Y1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1),
      expand_goal(call(Y1:X1),Y1,call(Z1)),
      '$call_with_inference_counting'('$call'(Z1))
   ).

:-non_counted_backtracking call/49.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1) :-
   (  var(A) ->
      instantiation_error(call/49)
   ;  A= '$call'(X1) ->
      '$prepare_call_clause'(Y1,Z1,X1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1),
      '$call_with_inference_counting'('$call'(Z1:Y1))
   ;  '$prepare_call_clause'(Y1,Z1,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1),
      expand_goal(call(Z1:Y1),Z1,call(A2)),
      '$call_with_inference_counting'('$call'(A2))
   ).

:-non_counted_backtracking call/50.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1) :-
   (  var(A) ->
      instantiation_error(call/50)
   ;  A= '$call'(Y1) ->
      '$prepare_call_clause'(Z1,A2,Y1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1),
      '$call_with_inference_counting'('$call'(A2:Z1))
   ;  '$prepare_call_clause'(Z1,A2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1),
      expand_goal(call(A2:Z1),A2,call(B2)),
      '$call_with_inference_counting'('$call'(B2))
   ).

:-non_counted_backtracking call/51.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1) :-
   (  var(A) ->
      instantiation_error(call/51)
   ;  A= '$call'(Z1) ->
      '$prepare_call_clause'(A2,B2,Z1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1),
      '$call_with_inference_counting'('$call'(B2:A2))
   ;  '$prepare_call_clause'(A2,B2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1),
      expand_goal(call(B2:A2),B2,call(C2)),
      '$call_with_inference_counting'('$call'(C2))
   ).

:-non_counted_backtracking call/52.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1) :-
   (  var(A) ->
      instantiation_error(call/52)
   ;  A= '$call'(A2) ->
      '$prepare_call_clause'(B2,C2,A2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1),
      '$call_with_inference_counting'('$call'(C2:B2))
   ;  '$prepare_call_clause'(B2,C2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1),
      expand_goal(call(C2:B2),C2,call(D2)),
      '$call_with_inference_counting'('$call'(D2))
   ).

:-non_counted_backtracking call/53.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2) :-
   (  var(A) ->
      instantiation_error(call/53)
   ;  A= '$call'(B2) ->
      '$prepare_call_clause'(C2,D2,B2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2),
      '$call_with_inference_counting'('$call'(D2:C2))
   ;  '$prepare_call_clause'(C2,D2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2),
      expand_goal(call(D2:C2),D2,call(E2)),
      '$call_with_inference_counting'('$call'(E2))
   ).

:-non_counted_backtracking call/54.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2) :-
   (  var(A) ->
      instantiation_error(call/54)
   ;  A= '$call'(C2) ->
      '$prepare_call_clause'(D2,E2,C2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2),
      '$call_with_inference_counting'('$call'(E2:D2))
   ;  '$prepare_call_clause'(D2,E2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2),
      expand_goal(call(E2:D2),E2,call(F2)),
      '$call_with_inference_counting'('$call'(F2))
   ).

:-non_counted_backtracking call/55.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2) :-
   (  var(A) ->
      instantiation_error(call/55)
   ;  A= '$call'(D2) ->
      '$prepare_call_clause'(E2,F2,D2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2),
      '$call_with_inference_counting'('$call'(F2:E2))
   ;  '$prepare_call_clause'(E2,F2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2),
      expand_goal(call(F2:E2),F2,call(G2)),
      '$call_with_inference_counting'('$call'(G2))
   ).

:-non_counted_backtracking call/56.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2) :-
   (  var(A) ->
      instantiation_error(call/56)
   ;  A= '$call'(E2) ->
      '$prepare_call_clause'(F2,G2,E2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2),
      '$call_with_inference_counting'('$call'(G2:F2))
   ;  '$prepare_call_clause'(F2,G2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2),
      expand_goal(call(G2:F2),G2,call(H2)),
      '$call_with_inference_counting'('$call'(H2))
   ).

:-non_counted_backtracking call/57.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2) :-
   (  var(A) ->
      instantiation_error(call/57)
   ;  A= '$call'(F2) ->
      '$prepare_call_clause'(G2,H2,F2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2),
      '$call_with_inference_counting'('$call'(H2:G2))
   ;  '$prepare_call_clause'(G2,H2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2),
      expand_goal(call(H2:G2),H2,call(I2)),
      '$call_with_inference_counting'('$call'(I2))
   ).

:-non_counted_backtracking call/58.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2) :-
   (  var(A) ->
      instantiation_error(call/58)
   ;  A= '$call'(G2) ->
      '$prepare_call_clause'(H2,I2,G2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2),
      '$call_with_inference_counting'('$call'(I2:H2))
   ;  '$prepare_call_clause'(H2,I2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2),
      expand_goal(call(I2:H2),I2,call(J2)),
      '$call_with_inference_counting'('$call'(J2))
   ).

:-non_counted_backtracking call/59.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2) :-
   (  var(A) ->
      instantiation_error(call/59)
   ;  A= '$call'(H2) ->
      '$prepare_call_clause'(I2,J2,H2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2),
      '$call_with_inference_counting'('$call'(J2:I2))
   ;  '$prepare_call_clause'(I2,J2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2),
      expand_goal(call(J2:I2),J2,call(K2)),
      '$call_with_inference_counting'('$call'(K2))
   ).

:-non_counted_backtracking call/60.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2) :-
   (  var(A) ->
      instantiation_error(call/60)
   ;  A= '$call'(I2) ->
      '$prepare_call_clause'(J2,K2,I2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2),
      '$call_with_inference_counting'('$call'(K2:J2))
   ;  '$prepare_call_clause'(J2,K2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2),
      expand_goal(call(K2:J2),K2,call(L2)),
      '$call_with_inference_counting'('$call'(L2))
   ).

:-non_counted_backtracking call/61.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2) :-
   (  var(A) ->
      instantiation_error(call/61)
   ;  A= '$call'(J2) ->
      '$prepare_call_clause'(K2,L2,J2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2),
      '$call_with_inference_counting'('$call'(L2:K2))
   ;  '$prepare_call_clause'(K2,L2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2),
      expand_goal(call(L2:K2),L2,call(M2)),
      '$call_with_inference_counting'('$call'(M2))
   ).

:-non_counted_backtracking call/62.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2) :-
   (  var(A) ->
      instantiation_error(call/62)
   ;  A= '$call'(K2) ->
      '$prepare_call_clause'(L2,M2,K2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2),
      '$call_with_inference_counting'('$call'(M2:L2))
   ;  '$prepare_call_clause'(L2,M2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2),
      expand_goal(call(M2:L2),M2,call(N2)),
      '$call_with_inference_counting'('$call'(N2))
   ).

:-non_counted_backtracking call/63.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2) :-
   (  var(A) ->
      instantiation_error(call/63)
   ;  A= '$call'(L2) ->
      '$prepare_call_clause'(M2,N2,L2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2),
      '$call_with_inference_counting'('$call'(N2:M2))
   ;  '$prepare_call_clause'(M2,N2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2),
      expand_goal(call(N2:M2),N2,call(O2)),
      '$call_with_inference_counting'('$call'(O2))
   ).

:-non_counted_backtracking call/64.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2) :-
   (  var(A) ->
      instantiation_error(call/64)
   ;  A= '$call'(M2) ->
      '$prepare_call_clause'(N2,O2,M2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2),
      '$call_with_inference_counting'('$call'(O2:N2))
   ;  '$prepare_call_clause'(N2,O2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2),
      expand_goal(call(O2:N2),O2,call(P2)),
      '$call_with_inference_counting'('$call'(P2))
   ).

:-non_counted_backtracking call/65.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2) :-
   (  var(A) ->
      instantiation_error(call/65)
   ;  A= '$call'(N2) ->
      '$prepare_call_clause'(O2,P2,N2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2),
      '$call_with_inference_counting'('$call'(P2:O2))
   ;  '$prepare_call_clause'(O2,P2,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2),
      expand_goal(call(P2:O2),P2,call(Q2)),
      '$call_with_inference_counting'('$call'(Q2))
   ).
