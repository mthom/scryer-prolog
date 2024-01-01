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
    (  current_prolog_flag(double_quotes, chars) ->
       DQ = true
    ;  DQ = false
    ),
    (  nonvar(Error),
       functor(Error, error, 2) ->
       write_term(Error, [ignore_ops(false), numbervars(true), quoted(true), double_quotes(DQ)])
    ;  write_term(throw(Error), [ignore_ops(false), numbervars(true), quoted(true), double_quotes(DQ)])
    ),
    write('.').


:- non_counted_backtracking '$print_message_and_fail'/1.

'$print_message_and_fail'(Error) :-
    write_error(Error),
    nl,
    '$fail'.

expand_term(Term, ExpandedTerm) :-
    (  '$predicate_defined'(user, term_expansion, 2),
       catch(user:term_expansion(Term, ExpandedTerm0),
             E,
             loader:'$print_message_and_fail'(E)) ->
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


:- non_counted_backtracking goal_expansion/3.

goal_expansion(Goal, Module, ExpandedGoal) :-
    (  atom(Module),
       '$predicate_defined'(Module, goal_expansion, 2),
       catch('$call'(Module:goal_expansion(Goal, ExpandedGoal0)),
             E,
             loader:'$print_message_and_fail'(E)) ->
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
       findall(Module:Goal, builtins:retract(Module:'$initialization_goals'(Goal)), Goals),
       abolish(Module:'$initialization_goals'/1),
       maplist(loader:success_or_warning, Goals)
    ;  true
    ).

:- meta_predicate success_or_warning(0).

success_or_warning(Goal) :-
    (   call(Goal) ->
        true
    ;   %% initialization goals can fail without thwarting the load.
        write('% Warning: initialization/1 failed for: '),
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

file_load_init(Stream, Evacuable) :-
    load_loop(Stream, Evacuable),
    run_initialization_goals.

file_load_cleanup(Evacuable, Error) :-
    load_context(Module),
    abolish(Module:'$initialization_goals'/1),
    unload_evacuable(Evacuable),
    (  clause('$toplevel':argv(_), _) ->
       % let the toplevel call loader:write_error/1
       throw(Error)
    ;  '$print_message_and_fail'(Error)
    ;  throw(file_load_error)
    ).

file_load(Stream, Path, Evacuable) :-
    create_file_load_context(Stream, Path, Evacuable),
    % '$add_in_situ_filename_module' removes user level predicates,
    % local predicate clauses, etc. from a previous load of the file
    % at Path.
    '$add_in_situ_filename_module'(Evacuable),
    catch(loader:file_load_init(Stream, Evacuable),
          E,
          loader:file_load_cleanup(Evacuable, E)),
    '$pop_load_context'.


load(Stream) :-
    create_load_context(Stream, Evacuable),
    catch(loader:file_load_init(Stream, Evacuable),
          E,
          loader:file_load_cleanup(Evacuable, E)),
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
       write('% Warning: singleton variables '),
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

complete_partial_goal(N, HeadArg, InnerHeadArgs, SuppArgs, CompleteHeadArg) :-
    integer(N),
    N >= 0,
    HeadArg =.. [Functor | InnerHeadArgs],
    (  callable(Functor) ->
       % the next two lines are equivalent to length(SuppArgs, N) but
       % avoid length/2 so that copy_term/3 (which is invoked by
       % length/2) can be bootstrapped without self-reference.
       functor(SuppArgsFunctor, '.', N),
       SuppArgsFunctor =.. [_ | SuppArgs],
       % length(SuppArgs, N),
       append(InnerHeadArgs, SuppArgs, InnerHeadArgs0),
       CompleteHeadArg =.. [Functor | InnerHeadArgs0]
    ;  type_error(callable, Functor, _)
    ).

inner_meta_specs(0, HeadArg, InnerHeadArgs, InnerMetaSpecs) :-
    !,
    predicate_property(HeadArg, meta_predicate(InnerMetaSpecs0)),
    InnerMetaSpecs0 =.. [_ | InnerMetaSpecs],
    HeadArg =.. [_ | InnerHeadArgs].
inner_meta_specs((:), _, [], []) :-
    !.
inner_meta_specs(N, HeadArg, InnerHeadArgs, InnerMetaSpecs) :-
    complete_partial_goal(N, HeadArg, InnerHeadArgs, _, CompleteHeadArg),
    predicate_property(CompleteHeadArg, meta_predicate(InnerMetaSpecs0)),
    InnerMetaSpecs0 =.. [_ | InnerMetaSpecs].


module_expanded_head_variables_([], _, HeadVars, HeadVars).
module_expanded_head_variables_([HeadArg | HeadArgs], [MetaSpec | MetaSpecs], HeadVars, HeadVars0) :-
    (  (  MetaSpec == (:)
       ;  integer(MetaSpec),
          MetaSpec >= 0
       )  ->
       (  var(HeadArg) ->
          HeadVars = [HeadArg-MetaSpec | HeadVars1],
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


print_goal_expansion_warning(Pred) :-
    nl,
    write('% Warning: clause body goal expansion failed because '),
    writeq(Pred),
    write(' is not callable.'),
    nl.

expand_term_goals(Terms0, Terms) :-
    (  Terms0 = (Head1 :- Body0) ->
       (  var(Head1) ->
          instantiation_error(load/1)
       ;  Head1 = Module:Head2 ->
          (  atom(Module) ->
             prolog_load_context(module, Target),
             module_expanded_head_variables(Head2, HeadVars),
             catch(expand_goal(Body0, Target, Body1, HeadVars),
                   error(type_error(callable, Pred), _),
                   (  loader:print_goal_expansion_warning(Pred),
                      builtins:(Body1 = Body0)
                   )),
             Terms = (Module:Head2 :- Body1)
          ;  type_error(atom, Module, load/1)
          )
       ;  module_expanded_head_variables(Head1, HeadVars),
          prolog_load_context(module, Target),
          catch(expand_goal(Body0, Target, Body1, HeadVars),
                error(type_error(callable, Pred), _),
                (  loader:print_goal_expansion_warning(Pred),
                   builtins:(Body1 = Body0)
                )),
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


predicate_indicator(PI) :-
    (  var(PI) ->
       throw(error(instantiation_error, _))
    ;  PI = Name/Arity,
       must_be(atom, Name),
       must_be(integer, Arity),
       Arity >= 0
    ).

predicate_indicator_sequence(PI_Seq) :-
    (  var(PI_Seq) ->
       throw(error(instantiation_error, load/1))
    ;  PI_Seq = (PI, PIs),
       predicate_indicator(PI),
       (  predicate_indicator(PIs) ->
          true
       ;  predicate_indicator_sequence(PIs)
       )
    ).

:- meta_predicate add_predicate_declaration(3, ?).

add_predicate_declaration(Handler, Name/Arity) :-
    predicate_indicator(Name/Arity),
    prolog_load_context(module, Module),
    call(Handler, Module, Name, Arity).
add_predicate_declaration(Handler, Module:Name/Arity) :-
    must_be(atom, Module),
    predicate_indicator(Name/Arity),
    call(Handler, Module, Name, Arity).
add_predicate_declaration(Handler, [PI|PIs]) :-
    '$skip_max_list'(_, _, PIs, Tail),
    (  Tail == [],
       maplist(loader:predicate_indicator, PIs) ->
       maplist(loader:add_predicate_declaration(Handler), [PI|PIs])
    ;  throw(error(type_error(predicate_indicator_list, [PI|PIs]), load/1))
    ).
add_predicate_declaration(Handler, (PI, PIs)) :-
    (  predicate_indicator_sequence((PI, PIs)) ->
       add_predicate_declaration(Handler, PI),
       add_predicate_declaration(Handler, PIs)
    ;  throw(error(type_error(predicate_indicator_sequence, (PI, PIs)), load/1))
    ).

add_dynamic_predicate(Evacuable, Module, Name, Arity) :-
    '$add_dynamic_predicate'(Module, Name, Arity, Evacuable).

add_multifile_predicate(Evacuable, Module, Name, Arity) :-
    '$add_multifile_predicate'(Module, Name, Arity, Evacuable).

add_discontiguous_predicate(Evacuable, Module, Name, Arity) :-
    '$add_discontiguous_predicate'(Module, Name, Arity, Evacuable).

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
compile_declaration(dynamic(PIs), Evacuable) :-
    add_predicate_declaration(loader:add_dynamic_predicate(Evacuable), PIs).
compile_declaration(multifile(PIs), Evacuable) :-
    add_predicate_declaration(loader:add_multifile_predicate(Evacuable), PIs).
compile_declaration(discontiguous(PIs), Evacuable) :-
    add_predicate_declaration(loader:add_discontiguous_predicate(Evacuable), PIs).
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
    catch('$call'(loader:use_module(Module, [], Evacuable)),
          file_load_error,
          '$call'(builtins:false)).

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


open_file_cleanup(Path, Stream) :-
    atom_concat(Path, '.pl', ExtendedPath),
    open(ExtendedPath, read, Stream).

% Try to open the file with the Path name as given; if that fails,
% append '.pl' and try again.
open_file(Path, Stream) :-
    (  atom_concat(_, '.pl', Path) ->
       open(Path, read, Stream)
    ;  catch(open(Path, read, Stream),
             error(existence_error(source_sink, _), _),
             loader:open_file_cleanup(Path, Stream)
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
       ;  type_error(atom, Module, load/1)
       )
    ).

consult_stream(Stream, PathFileName) :-
   '$push_load_state_payload'(Evacuable),
    file_load(Stream, PathFileName, Subevacuable),
    '$use_module'(Evacuable, Subevacuable, _).

:- non_counted_backtracking check_predicate_property/5.

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


:- non_counted_backtracking extract_predicate_property/2.

extract_predicate_property(Property, PropertyType) :-
    (  var(Property) ->
       true
    ;  functor(Property, PropertyType, _)
    ).

:- non_counted_backtracking load_context/1.

load_context(Module) :-
    (  prolog_load_context(module, Module) ->
       true
    ;  Module = user
    ).

:- non_counted_backtracking predicate_property/2.

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


:- non_counted_backtracking strip_subst_module/4.

strip_subst_module(Goal, M1, M2, G) :-
    '$strip_module'(Goal, M2, G),
    (  var(M2), \+ functor(Goal, (:), 2) ->
       M2 = M1
    ;  true
    ).

/*
 * subgoal_expansion differs from goal_expansion only in that it fails
 * unconditionally after catching an(y) exception, aborting the
 * inlining process. It is expected that goal expansion will succeed
 * when expand_goal is later invoked at runtime.
 */

:- non_counted_backtracking subgoal_expansion_fail/1.

subgoal_expansion_fail(B) :-
    builtins:set_cp(B),
    fail.

:- non_counted_backtracking subgoal_expansion/3.

subgoal_expansion(Goal, Module, ExpandedGoal) :-
    '$get_cp'(B),
    (  atom(Module),
       '$predicate_defined'(Module, goal_expansion, 2),
       catch('$call'(Module:goal_expansion(Goal, ExpandedGoal0)),
             _E,
             '$call'(loader:subgoal_expansion_fail(B))
            ),
       (  var(ExpandedGoal0) ->
          error:instantiation_error(goal_expansion/2)
       ;  '$set_cp'(B),
          subgoal_expansion(ExpandedGoal0, Module, ExpandedGoal)
       )
    ;  Goal = ExpandedGoal
    ).


:- non_counted_backtracking expand_subgoal/5.

expand_subgoal(UnexpandedGoals, MS, M, ExpandedGoals, HeadVars) :-
    strip_subst_module(UnexpandedGoals, M, Module, UnexpandedGoals0),
    nonvar(UnexpandedGoals0),
    complete_partial_goal(MS, UnexpandedGoals0, _, SuppArgs, UnexpandedGoals1),
    (  subgoal_expansion(UnexpandedGoals1, Module, UnexpandedGoals2),
       (  Module \== user ->
          subgoal_expansion(UnexpandedGoals2, user, UnexpandedGoals3)
       ;  UnexpandedGoals3 = UnexpandedGoals2
       )
    ),
    strip_subst_module(UnexpandedGoals3, Module, Module1, UnexpandedGoals4),
    (  inner_meta_specs(0, UnexpandedGoals4, _, MetaSpecs) ->
       expand_module_names(UnexpandedGoals4, MetaSpecs, Module1, ExpandedGoals0, HeadVars)
    ;  ExpandedGoals0 = UnexpandedGoals4
    ),
    '$compile_inline_or_expanded_goal'(ExpandedGoals0, SuppArgs, ExpandedGoals1, Module1, UnexpandedGoals0),
    expand_module_name(ExpandedGoals1, MS, Module1, ExpandedGoals).


:- non_counted_backtracking expand_module_name/4.

expand_module_name(ESG0, MS, M, ESG) :-
    (  var(ESG0) ->
       (  M == user ->
          ESG = ESG0
       ;  ESG = M:ESG0
       )
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


:- non_counted_backtracking eq_member/2.

eq_member(V, [L-_|Ls]) :-
    V == L.
eq_member(V, [_|Ls]) :-
    eq_member(V, Ls).

:- non_counted_backtracking qualified_spec/1.

qualified_spec((:)).
qualified_spec(MS) :- integer(MS), MS >= 0.


:- non_counted_backtracking expand_meta_predicate_subgoals/5.

expand_meta_predicate_subgoals([SG | SGs], [MS | MSs], M, [ESG | ESGs], HeadVars) :-
    (  var(SG) ->
       (  qualified_spec(MS) ->
          (  eq_member(SG, HeadVars) ->
             ESG = SG
          ;  expand_module_name(SG, MS, M, ESG)
          )
       ;  ESG = SG
       )
    ;  MS == (:) ->
       expand_module_name(SG, MS, M, ESG)
    ;  '$is_expanded_or_inlined'(SG) ->
       ESG = SG
    ;  expand_subgoal(SG, MS, M, ESG, HeadVars) ->
       true
    ;  integer(MS),
       MS >= 0 ->
       expand_module_name(SG, MS, M, ESG)
    ;  SG = ESG
    ),
    expand_meta_predicate_subgoals(SGs, MSs, M, ESGs, HeadVars).

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
    catch(loader:expand_goal(UnexpandedGoals, Module, ExpandedGoals, []),
          error(type_error(callable, _), _),
          UnexpandedGoals = ExpandedGoals),
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

/*
 * private predicate for use in call/N. it doesn't specially consider
 * control predicates as expand_goal does with expand_goal_cases.
 * HeadVars is always [].
 */

:- non_counted_backtracking expand_call_goal/3.

expand_call_goal(UnexpandedGoals, Module, ExpandedGoals) :-
    % if a goal isn't callable, defer to call/N to report the error.
    catch('$call'(loader:expand_call_goal_(UnexpandedGoals, Module, ExpandedGoals)),
          error(type_error(callable, _), _),
          '$call'(UnexpandedGoals = ExpandedGoals)),
    !.

:- non_counted_backtracking expand_call_goal_/3.

expand_call_goal_(UnexpandedGoals, Module, ExpandedGoals) :-
    (  var(UnexpandedGoals) ->
       UnexpandedGoals = ExpandedGoals
    ;  goal_expansion(UnexpandedGoals, Module, UnexpandedGoals1),
       (  Module \== user ->
          goal_expansion(UnexpandedGoals1, user, ExpandedGoals)
       ;  ExpandedGoals = UnexpandedGoals1
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
% :- use_module(library(between)).
% :- use_module(library(error)).
% :- use_module(library(lists)).
% :- use_module(library(format)).
%
% n_call_clause(N, Clauses) :-
%     length(Args, N),
%     Head =.. [call, G | Args],
%     N1 is N + 1,
%     StripModule =.. ['$strip_module', G, M1, G1],
%     FastCall =.. ['$fast_call', G | Args],
%     PrepareCallClause =.. [ '$prepare_call_clause', G2, G1 | Args],
%     ModuleCall =.. ['$module_call', M2, G4],
%     Clauses = [(Head :- var(G),
%                         instantiation_error(call/N1)),
%                (Head :- FastCall),
%                (Head :- StripModule,
%                         PrepareCallClause,
%                         expand_call_goal(G2, M1, G3),
%                         strip_subst_module(G3, M1, M2, G4),
%                         ModuleCall)].
%
% generate_call_forms :-
%     between(1, 64, N),
%     n_call_clause(N, Clauses),
%     N1 is N+1,
%     portray_clause((:- non_counted_backtracking call/N1)),
%     maplist(portray_clause, Clauses),
%     nl,
%     false.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The '$call' functor is an escape hatch from goal expansion. So far,
% it is used only to avoid infinite recursion into expand_call_goal/3.

:- non_counted_backtracking call/1.

call(G) :-
    var(G),
    instantiation_error(call/1).
call(G) :-
    '$fast_call'(G).
call(G0) :-
    '$strip_module'(G0, M0, G1),
    expand_call_goal(G1, M0, G2),
    strip_subst_module(G2, M0, M1, G3),
    '$module_call'(M1, G3).

:-non_counted_backtracking call/2.
call(A,B) :-
   var(A),
   instantiation_error(call/2).
call(A,B) :-
   '$fast_call'(A,B).
call(A,B) :-
   '$strip_module'(A,C,D),
   '$prepare_call_clause'(E,D,B),
   expand_call_goal(E,C,F),
   strip_subst_module(F,C,G,H),
   '$module_call'(G,H).

:-non_counted_backtracking call/3.
call(A,B,C) :-
   var(A),
   instantiation_error(call/3).
call(A,B,C) :-
   '$fast_call'(A,B,C).
call(A,B,C) :-
   '$strip_module'(A,D,E),
   '$prepare_call_clause'(F,E,B,C),
   expand_call_goal(F,D,G),
   strip_subst_module(G,D,H,I),
   '$module_call'(H,I).

:-non_counted_backtracking call/4.
call(A,B,C,D) :-
   var(A),
   instantiation_error(call/4).
call(A,B,C,D) :-
   '$fast_call'(A,B,C,D).
call(A,B,C,D) :-
   '$strip_module'(A,E,F),
   '$prepare_call_clause'(G,F,B,C,D),
   expand_call_goal(G,E,H),
   strip_subst_module(H,E,I,J),
   '$module_call'(I,J).

:-non_counted_backtracking call/5.
call(A,B,C,D,E) :-
   var(A),
   instantiation_error(call/5).
call(A,B,C,D,E) :-
   '$fast_call'(A,B,C,D,E).
call(A,B,C,D,E) :-
   '$strip_module'(A,F,G),
   '$prepare_call_clause'(H,G,B,C,D,E),
   expand_call_goal(H,F,I),
   strip_subst_module(I,F,J,K),
   '$module_call'(J,K).

:-non_counted_backtracking call/6.
call(A,B,C,D,E,F) :-
   var(A),
   instantiation_error(call/6).
call(A,B,C,D,E,F) :-
   '$fast_call'(A,B,C,D,E,F).
call(A,B,C,D,E,F) :-
   '$strip_module'(A,G,H),
   '$prepare_call_clause'(I,H,B,C,D,E,F),
   expand_call_goal(I,G,J),
   strip_subst_module(J,G,K,L),
   '$module_call'(K,L).

:-non_counted_backtracking call/7.
call(A,B,C,D,E,F,G) :-
   var(A),
   instantiation_error(call/7).
call(A,B,C,D,E,F,G) :-
   '$fast_call'(A,B,C,D,E,F,G).
call(A,B,C,D,E,F,G) :-
   '$strip_module'(A,H,I),
   '$prepare_call_clause'(J,I,B,C,D,E,F,G),
   expand_call_goal(J,H,K),
   strip_subst_module(K,H,L,M),
   '$module_call'(L,M).

:-non_counted_backtracking call/8.
call(A,B,C,D,E,F,G,H) :-
   var(A),
   instantiation_error(call/8).
call(A,B,C,D,E,F,G,H) :-
   '$fast_call'(A,B,C,D,E,F,G,H).
call(A,B,C,D,E,F,G,H) :-
   '$strip_module'(A,I,J),
   '$prepare_call_clause'(K,J,B,C,D,E,F,G,H),
   expand_call_goal(K,I,L),
   strip_subst_module(L,I,M,N),
   '$module_call'(M,N).

:-non_counted_backtracking call/9.
call(A,B,C,D,E,F,G,H,I) :-
   var(A),
   instantiation_error(call/9).
call(A,B,C,D,E,F,G,H,I) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I).
call(A,B,C,D,E,F,G,H,I) :-
   '$strip_module'(A,J,K),
   '$prepare_call_clause'(L,K,B,C,D,E,F,G,H,I),
   expand_call_goal(L,J,M),
   strip_subst_module(M,J,N,O),
   '$module_call'(N,O).

:-non_counted_backtracking call/10.
call(A,B,C,D,E,F,G,H,I,J) :-
   var(A),
   instantiation_error(call/10).
call(A,B,C,D,E,F,G,H,I,J) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J).
call(A,B,C,D,E,F,G,H,I,J) :-
   '$strip_module'(A,K,L),
   '$prepare_call_clause'(M,L,B,C,D,E,F,G,H,I,J),
   expand_call_goal(M,K,N),
   strip_subst_module(N,K,O,P),
   '$module_call'(O,P).

:-non_counted_backtracking call/11.
call(A,B,C,D,E,F,G,H,I,J,K) :-
   var(A),
   instantiation_error(call/11).
call(A,B,C,D,E,F,G,H,I,J,K) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K).
call(A,B,C,D,E,F,G,H,I,J,K) :-
   '$strip_module'(A,L,M),
   '$prepare_call_clause'(N,M,B,C,D,E,F,G,H,I,J,K),
   expand_call_goal(N,L,O),
   strip_subst_module(O,L,P,Q),
   '$module_call'(P,Q).

:-non_counted_backtracking call/12.
call(A,B,C,D,E,F,G,H,I,J,K,L) :-
   var(A),
   instantiation_error(call/12).
call(A,B,C,D,E,F,G,H,I,J,K,L) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L).
call(A,B,C,D,E,F,G,H,I,J,K,L) :-
   '$strip_module'(A,M,N),
   '$prepare_call_clause'(O,N,B,C,D,E,F,G,H,I,J,K,L),
   expand_call_goal(O,M,P),
   strip_subst_module(P,M,Q,R),
   '$module_call'(Q,R).

:-non_counted_backtracking call/13.
call(A,B,C,D,E,F,G,H,I,J,K,L,M) :-
   var(A),
   instantiation_error(call/13).
call(A,B,C,D,E,F,G,H,I,J,K,L,M) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M).
call(A,B,C,D,E,F,G,H,I,J,K,L,M) :-
   '$strip_module'(A,N,O),
   '$prepare_call_clause'(P,O,B,C,D,E,F,G,H,I,J,K,L,M),
   expand_call_goal(P,N,Q),
   strip_subst_module(Q,N,R,S),
   '$module_call'(R,S).

:-non_counted_backtracking call/14.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N) :-
   var(A),
   instantiation_error(call/14).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N) :-
   '$strip_module'(A,O,P),
   '$prepare_call_clause'(Q,P,B,C,D,E,F,G,H,I,J,K,L,M,N),
   expand_call_goal(Q,O,R),
   strip_subst_module(R,O,S,T),
   '$module_call'(S,T).

:-non_counted_backtracking call/15.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O) :-
   var(A),
   instantiation_error(call/15).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O) :-
   '$strip_module'(A,P,Q),
   '$prepare_call_clause'(R,Q,B,C,D,E,F,G,H,I,J,K,L,M,N,O),
   expand_call_goal(R,P,S),
   strip_subst_module(S,P,T,U),
   '$module_call'(T,U).

:-non_counted_backtracking call/16.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P) :-
   var(A),
   instantiation_error(call/16).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P) :-
   '$strip_module'(A,Q,R),
   '$prepare_call_clause'(S,R,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P),
   expand_call_goal(S,Q,T),
   strip_subst_module(T,Q,U,V),
   '$module_call'(U,V).

:-non_counted_backtracking call/17.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q) :-
   var(A),
   instantiation_error(call/17).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q) :-
   '$strip_module'(A,R,S),
   '$prepare_call_clause'(T,S,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q),
   expand_call_goal(T,R,U),
   strip_subst_module(U,R,V,W),
   '$module_call'(V,W).

:-non_counted_backtracking call/18.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R) :-
   var(A),
   instantiation_error(call/18).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R) :-
   '$strip_module'(A,S,T),
   '$prepare_call_clause'(U,T,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R),
   expand_call_goal(U,S,V),
   strip_subst_module(V,S,W,X),
   '$module_call'(W,X).

:-non_counted_backtracking call/19.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S) :-
   var(A),
   instantiation_error(call/19).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S) :-
   '$strip_module'(A,T,U),
   '$prepare_call_clause'(V,U,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S),
   expand_call_goal(V,T,W),
   strip_subst_module(W,T,X,Y),
   '$module_call'(X,Y).

:-non_counted_backtracking call/20.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T) :-
   var(A),
   instantiation_error(call/20).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T) :-
   '$strip_module'(A,U,V),
   '$prepare_call_clause'(W,V,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T),
   expand_call_goal(W,U,X),
   strip_subst_module(X,U,Y,Z),
   '$module_call'(Y,Z).

:-non_counted_backtracking call/21.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U) :-
   var(A),
   instantiation_error(call/21).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U) :-
   '$strip_module'(A,V,W),
   '$prepare_call_clause'(X,W,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U),
   expand_call_goal(X,V,Y),
   strip_subst_module(Y,V,Z,A1),
   '$module_call'(Z,A1).

:-non_counted_backtracking call/22.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V) :-
   var(A),
   instantiation_error(call/22).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V) :-
   '$strip_module'(A,W,X),
   '$prepare_call_clause'(Y,X,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V),
   expand_call_goal(Y,W,Z),
   strip_subst_module(Z,W,A1,B1),
   '$module_call'(A1,B1).

:-non_counted_backtracking call/23.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W) :-
   var(A),
   instantiation_error(call/23).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W) :-
   '$strip_module'(A,X,Y),
   '$prepare_call_clause'(Z,Y,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W),
   expand_call_goal(Z,X,A1),
   strip_subst_module(A1,X,B1,C1),
   '$module_call'(B1,C1).

:-non_counted_backtracking call/24.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X) :-
   var(A),
   instantiation_error(call/24).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X) :-
   '$strip_module'(A,Y,Z),
   '$prepare_call_clause'(A1,Z,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X),
   expand_call_goal(A1,Y,B1),
   strip_subst_module(B1,Y,C1,D1),
   '$module_call'(C1,D1).

:-non_counted_backtracking call/25.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y) :-
   var(A),
   instantiation_error(call/25).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y) :-
   '$strip_module'(A,Z,A1),
   '$prepare_call_clause'(B1,A1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y),
   expand_call_goal(B1,Z,C1),
   strip_subst_module(C1,Z,D1,E1),
   '$module_call'(D1,E1).

:-non_counted_backtracking call/26.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z) :-
   var(A),
   instantiation_error(call/26).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z) :-
   '$strip_module'(A,A1,B1),
   '$prepare_call_clause'(C1,B1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z),
   expand_call_goal(C1,A1,D1),
   strip_subst_module(D1,A1,E1,F1),
   '$module_call'(E1,F1).

:-non_counted_backtracking call/27.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1) :-
   var(A),
   instantiation_error(call/27).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1) :-
   '$strip_module'(A,B1,C1),
   '$prepare_call_clause'(D1,C1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1),
   expand_call_goal(D1,B1,E1),
   strip_subst_module(E1,B1,F1,G1),
   '$module_call'(F1,G1).

:-non_counted_backtracking call/28.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1) :-
   var(A),
   instantiation_error(call/28).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1) :-
   '$strip_module'(A,C1,D1),
   '$prepare_call_clause'(E1,D1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1),
   expand_call_goal(E1,C1,F1),
   strip_subst_module(F1,C1,G1,H1),
   '$module_call'(G1,H1).

:-non_counted_backtracking call/29.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1) :-
   var(A),
   instantiation_error(call/29).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1) :-
   '$strip_module'(A,D1,E1),
   '$prepare_call_clause'(F1,E1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1),
   expand_call_goal(F1,D1,G1),
   strip_subst_module(G1,D1,H1,I1),
   '$module_call'(H1,I1).

:-non_counted_backtracking call/30.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1) :-
   var(A),
   instantiation_error(call/30).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1) :-
   '$strip_module'(A,E1,F1),
   '$prepare_call_clause'(G1,F1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1),
   expand_call_goal(G1,E1,H1),
   strip_subst_module(H1,E1,I1,J1),
   '$module_call'(I1,J1).

:-non_counted_backtracking call/31.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1) :-
   var(A),
   instantiation_error(call/31).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1) :-
   '$strip_module'(A,F1,G1),
   '$prepare_call_clause'(H1,G1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1),
   expand_call_goal(H1,F1,I1),
   strip_subst_module(I1,F1,J1,K1),
   '$module_call'(J1,K1).

:-non_counted_backtracking call/32.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1) :-
   var(A),
   instantiation_error(call/32).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1) :-
   '$strip_module'(A,G1,H1),
   '$prepare_call_clause'(I1,H1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1),
   expand_call_goal(I1,G1,J1),
   strip_subst_module(J1,G1,K1,L1),
   '$module_call'(K1,L1).

:-non_counted_backtracking call/33.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1) :-
   var(A),
   instantiation_error(call/33).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1) :-
   '$strip_module'(A,H1,I1),
   '$prepare_call_clause'(J1,I1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1),
   expand_call_goal(J1,H1,K1),
   strip_subst_module(K1,H1,L1,M1),
   '$module_call'(L1,M1).

:-non_counted_backtracking call/34.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1) :-
   var(A),
   instantiation_error(call/34).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1) :-
   '$strip_module'(A,I1,J1),
   '$prepare_call_clause'(K1,J1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1),
   expand_call_goal(K1,I1,L1),
   strip_subst_module(L1,I1,M1,N1),
   '$module_call'(M1,N1).

:-non_counted_backtracking call/35.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1) :-
   var(A),
   instantiation_error(call/35).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1) :-
   '$strip_module'(A,J1,K1),
   '$prepare_call_clause'(L1,K1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1),
   expand_call_goal(L1,J1,M1),
   strip_subst_module(M1,J1,N1,O1),
   '$module_call'(N1,O1).

:-non_counted_backtracking call/36.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1) :-
   var(A),
   instantiation_error(call/36).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1) :-
   '$strip_module'(A,K1,L1),
   '$prepare_call_clause'(M1,L1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1),
   expand_call_goal(M1,K1,N1),
   strip_subst_module(N1,K1,O1,P1),
   '$module_call'(O1,P1).

:-non_counted_backtracking call/37.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1) :-
   var(A),
   instantiation_error(call/37).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1) :-
   '$strip_module'(A,L1,M1),
   '$prepare_call_clause'(N1,M1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1),
   expand_call_goal(N1,L1,O1),
   strip_subst_module(O1,L1,P1,Q1),
   '$module_call'(P1,Q1).

:-non_counted_backtracking call/38.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1) :-
   var(A),
   instantiation_error(call/38).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1) :-
   '$strip_module'(A,M1,N1),
   '$prepare_call_clause'(O1,N1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1),
   expand_call_goal(O1,M1,P1),
   strip_subst_module(P1,M1,Q1,R1),
   '$module_call'(Q1,R1).

:-non_counted_backtracking call/39.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1) :-
   var(A),
   instantiation_error(call/39).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1) :-
   '$strip_module'(A,N1,O1),
   '$prepare_call_clause'(P1,O1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1),
   expand_call_goal(P1,N1,Q1),
   strip_subst_module(Q1,N1,R1,S1),
   '$module_call'(R1,S1).

:-non_counted_backtracking call/40.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1) :-
   var(A),
   instantiation_error(call/40).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1) :-
   '$strip_module'(A,O1,P1),
   '$prepare_call_clause'(Q1,P1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1),
   expand_call_goal(Q1,O1,R1),
   strip_subst_module(R1,O1,S1,T1),
   '$module_call'(S1,T1).

:-non_counted_backtracking call/41.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1) :-
   var(A),
   instantiation_error(call/41).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1) :-
   '$strip_module'(A,P1,Q1),
   '$prepare_call_clause'(R1,Q1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1),
   expand_call_goal(R1,P1,S1),
   strip_subst_module(S1,P1,T1,U1),
   '$module_call'(T1,U1).

:-non_counted_backtracking call/42.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1) :-
   var(A),
   instantiation_error(call/42).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1) :-
   '$strip_module'(A,Q1,R1),
   '$prepare_call_clause'(S1,R1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1),
   expand_call_goal(S1,Q1,T1),
   strip_subst_module(T1,Q1,U1,V1),
   '$module_call'(U1,V1).

:-non_counted_backtracking call/43.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1) :-
   var(A),
   instantiation_error(call/43).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1) :-
   '$strip_module'(A,R1,S1),
   '$prepare_call_clause'(T1,S1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1),
   expand_call_goal(T1,R1,U1),
   strip_subst_module(U1,R1,V1,W1),
   '$module_call'(V1,W1).

:-non_counted_backtracking call/44.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1) :-
   var(A),
   instantiation_error(call/44).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1) :-
   '$strip_module'(A,S1,T1),
   '$prepare_call_clause'(U1,T1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1),
   expand_call_goal(U1,S1,V1),
   strip_subst_module(V1,S1,W1,X1),
   '$module_call'(W1,X1).

:-non_counted_backtracking call/45.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1) :-
   var(A),
   instantiation_error(call/45).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1) :-
   '$strip_module'(A,T1,U1),
   '$prepare_call_clause'(V1,U1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1),
   expand_call_goal(V1,T1,W1),
   strip_subst_module(W1,T1,X1,Y1),
   '$module_call'(X1,Y1).

:-non_counted_backtracking call/46.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1) :-
   var(A),
   instantiation_error(call/46).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1) :-
   '$strip_module'(A,U1,V1),
   '$prepare_call_clause'(W1,V1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1),
   expand_call_goal(W1,U1,X1),
   strip_subst_module(X1,U1,Y1,Z1),
   '$module_call'(Y1,Z1).

:-non_counted_backtracking call/47.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1) :-
   var(A),
   instantiation_error(call/47).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1) :-
   '$strip_module'(A,V1,W1),
   '$prepare_call_clause'(X1,W1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1),
   expand_call_goal(X1,V1,Y1),
   strip_subst_module(Y1,V1,Z1,A2),
   '$module_call'(Z1,A2).

:-non_counted_backtracking call/48.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1) :-
   var(A),
   instantiation_error(call/48).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1) :-
   '$strip_module'(A,W1,X1),
   '$prepare_call_clause'(Y1,X1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1),
   expand_call_goal(Y1,W1,Z1),
   strip_subst_module(Z1,W1,A2,B2),
   '$module_call'(A2,B2).

:-non_counted_backtracking call/49.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1) :-
   var(A),
   instantiation_error(call/49).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1) :-
   '$strip_module'(A,X1,Y1),
   '$prepare_call_clause'(Z1,Y1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1),
   expand_call_goal(Z1,X1,A2),
   strip_subst_module(A2,X1,B2,C2),
   '$module_call'(B2,C2).

:-non_counted_backtracking call/50.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1) :-
   var(A),
   instantiation_error(call/50).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1) :-
   '$strip_module'(A,Y1,Z1),
   '$prepare_call_clause'(A2,Z1,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1),
   expand_call_goal(A2,Y1,B2),
   strip_subst_module(B2,Y1,C2,D2),
   '$module_call'(C2,D2).

:-non_counted_backtracking call/51.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1) :-
   var(A),
   instantiation_error(call/51).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1) :-
   '$strip_module'(A,Z1,A2),
   '$prepare_call_clause'(B2,A2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1),
   expand_call_goal(B2,Z1,C2),
   strip_subst_module(C2,Z1,D2,E2),
   '$module_call'(D2,E2).

:-non_counted_backtracking call/52.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1) :-
   var(A),
   instantiation_error(call/52).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1) :-
   '$strip_module'(A,A2,B2),
   '$prepare_call_clause'(C2,B2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1),
   expand_call_goal(C2,A2,D2),
   strip_subst_module(D2,A2,E2,F2),
   '$module_call'(E2,F2).

:-non_counted_backtracking call/53.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2) :-
   var(A),
   instantiation_error(call/53).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2) :-
   '$strip_module'(A,B2,C2),
   '$prepare_call_clause'(D2,C2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2),
   expand_call_goal(D2,B2,E2),
   strip_subst_module(E2,B2,F2,G2),
   '$module_call'(F2,G2).

:-non_counted_backtracking call/54.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2) :-
   var(A),
   instantiation_error(call/54).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2) :-
   '$strip_module'(A,C2,D2),
   '$prepare_call_clause'(E2,D2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2),
   expand_call_goal(E2,C2,F2),
   strip_subst_module(F2,C2,G2,H2),
   '$module_call'(G2,H2).

:-non_counted_backtracking call/55.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2) :-
   var(A),
   instantiation_error(call/55).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2) :-
   '$strip_module'(A,D2,E2),
   '$prepare_call_clause'(F2,E2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2),
   expand_call_goal(F2,D2,G2),
   strip_subst_module(G2,D2,H2,I2),
   '$module_call'(H2,I2).

:-non_counted_backtracking call/56.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2) :-
   var(A),
   instantiation_error(call/56).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2) :-
   '$strip_module'(A,E2,F2),
   '$prepare_call_clause'(G2,F2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2),
   expand_call_goal(G2,E2,H2),
   strip_subst_module(H2,E2,I2,J2),
   '$module_call'(I2,J2).

:-non_counted_backtracking call/57.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2) :-
   var(A),
   instantiation_error(call/57).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2) :-
   '$strip_module'(A,F2,G2),
   '$prepare_call_clause'(H2,G2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2),
   expand_call_goal(H2,F2,I2),
   strip_subst_module(I2,F2,J2,K2),
   '$module_call'(J2,K2).

:-non_counted_backtracking call/58.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2) :-
   var(A),
   instantiation_error(call/58).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2) :-
   '$strip_module'(A,G2,H2),
   '$prepare_call_clause'(I2,H2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2),
   expand_call_goal(I2,G2,J2),
   strip_subst_module(J2,G2,K2,L2),
   '$module_call'(K2,L2).

:-non_counted_backtracking call/59.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2) :-
   var(A),
   instantiation_error(call/59).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2) :-
   '$strip_module'(A,H2,I2),
   '$prepare_call_clause'(J2,I2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2),
   expand_call_goal(J2,H2,K2),
   strip_subst_module(K2,H2,L2,M2),
   '$module_call'(L2,M2).

:-non_counted_backtracking call/60.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2) :-
   var(A),
   instantiation_error(call/60).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2) :-
   '$strip_module'(A,I2,J2),
   '$prepare_call_clause'(K2,J2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2),
   expand_call_goal(K2,I2,L2),
   strip_subst_module(L2,I2,M2,N2),
   '$module_call'(M2,N2).

:-non_counted_backtracking call/61.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2) :-
   var(A),
   instantiation_error(call/61).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2) :-
   '$strip_module'(A,J2,K2),
   '$prepare_call_clause'(L2,K2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2),
   expand_call_goal(L2,J2,M2),
   strip_subst_module(M2,J2,N2,O2),
   '$module_call'(N2,O2).

:-non_counted_backtracking call/62.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2) :-
   var(A),
   instantiation_error(call/62).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2) :-
   '$strip_module'(A,K2,L2),
   '$prepare_call_clause'(M2,L2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2),
   expand_call_goal(M2,K2,N2),
   strip_subst_module(N2,K2,O2,P2),
   '$module_call'(O2,P2).

:-non_counted_backtracking call/63.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2) :-
   var(A),
   instantiation_error(call/63).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2) :-
   '$strip_module'(A,L2,M2),
   '$prepare_call_clause'(N2,M2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2),
   expand_call_goal(N2,L2,O2),
   strip_subst_module(O2,L2,P2,Q2),
   '$module_call'(P2,Q2).

:-non_counted_backtracking call/64.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2) :-
   var(A),
   instantiation_error(call/64).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2) :-
   '$strip_module'(A,M2,N2),
   '$prepare_call_clause'(O2,N2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2),
   expand_call_goal(O2,M2,P2),
   strip_subst_module(P2,M2,Q2,R2),
   '$module_call'(Q2,R2).

:-non_counted_backtracking call/65.
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2) :-
   var(A),
   instantiation_error(call/65).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2) :-
   '$fast_call'(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2).
call(A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2) :-
   '$strip_module'(A,N2,O2),
   '$prepare_call_clause'(P2,O2,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,A1,B1,C1,D1,E1,F1,G1,H1,I1,J1,K1,L1,M1,N1,O1,P1,Q1,R1,S1,T1,U1,V1,W1,X1,Y1,Z1,A2,B2,C2,D2,E2,F2,G2,H2,I2,J2,K2,L2,M2),
   expand_call_goal(P2,N2,Q2),
   strip_subst_module(Q2,N2,R2,S2),
   '$module_call'(R2,S2).
