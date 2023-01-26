/** Tabling, also called SLG resolution.

    SLG resolution is an alternative execution strategy that sometimes
    helps to improve termination and performance characters of Prolog
    predicates.

    To enable this execution strategy for a Prolog predicate, add a
    `(table)/1` directive, using the prefix operator `table` that this
    module defines. For example, to enable tabling for the predicate
    `p/2`, use:

```
:- use_module(library(tabling)).

:- table p/2.

...
```

    The possibility to apply different execution strategies is one of
    the greatest attractions of pure Prolog code, and one of the
    strongest arguments for keeping to the pure core of Prolog as far
    as possible.

    Scryer Prolog implements tabling as described by Desouter et al. in [*Tabling as a Library with Delimited Control*](https://www.ijcai.org/Proceedings/16/Papers/619.pdf).
*/

:- module(tabling,
	  [ start_tabling/2,		% +Wrapper, :Worker.

	    abolish_all_tables/0,

%	    (table)/1,			% +PI ...
	    op(1150, fx, table)
	  ]).

:- use_module(library(tabling/double_linked_list)).
:- use_module(library(tabling/table_data_structure)).
:- use_module(library(tabling/batched_worklist)).
:- use_module(library(tabling/global_worklist)).
:- use_module(library(tabling/table_link_manager)).
:- use_module(library(tabling/wrapper)).

:- use_module(library(cont)).
:- use_module(library(lists)).
%:- use_module(library(debug)).
:- use_module(library(iso_ext)).

%% :- meta_predicate
%% 	start_tabling(+, 0).

%%	user:exception(+Exception, +Var, -Action)
%
%	Realises lazy initialization of table variables.

%% user:exception(undefined_global_variable, Var, retry) :-
%%   (   table_gvar(Var)
%%   ->  true
%%   ;   format('Creating global var ~q~n', [Var]),
%%       nb_setval(Var, [])
%%   ).
/*
table_gvar(trie_table_link) :-
  table_datastructure_initialize.
table_gvar(newly_created_table_identifiers) :-
  table_datastructure_initialize.
table_gvar(table_global_worklist) :-
  bb_put(table_global_worklist, []).
table_gvar(table_leader) :-
  bb_put(table_leader, []).
*/

%%	abolish_all_tables
%
%	Remove all tables.  Should not be called when tabling is in
%	progress.
%
%	@bug	Check whether tabling is in progress


abolish_all_tables :-
  bb_put(trie_table_link, []),
  bb_put(newly_created_table_identifiers, []),
  bb_put(table_global_worklist,[]),
  bb_put(table_leader, []).


% Find table and status for the given call variant.
%
table_and_status_for_variant(V,T,S) :-
  % Order of the two calls really important: first create, then get status
  table_for_variant(V,T),
  tbd_table_status(T,S).


:- meta_predicate start_tabling(?, :).

start_tabling(Wrapper,Worker) :-
  put_new_trie_table_link,
  put_new_global_worklist,
  put_new_table_identifiers,
  table_and_status_for_variant(Wrapper,T,S),
  ( S == complete ->
    get_answer(T,Wrapper)
  ;
    ( exists_scheduling_component ->
      run_leader(Wrapper,Worker,T),
      % Now answer the original query!
      get_answer(T,Wrapper)
    ;
      run_follower(S,Wrapper,Worker,T)
    )
  ).

run_follower(fresh,Wrapper,Worker,T) :-
  activate(Wrapper,Worker,T),
  shift(call_info(Wrapper,T)).

run_follower(active,Wrapper,_Worker,T) :-
  shift(call_info(Wrapper,T)).

run_leader(Wrapper,Worker,T) :-
  create_scheduling_component,
  activate(Wrapper,Worker,T),
  completion,
  unset_scheduling_component.

exists_scheduling_component :-
  bb_get(table_leader, Leader),
  Leader == [].

create_scheduling_component :-
  bb_b_put(table_leader, leaderCreated).

unset_scheduling_component :-
  bb_put(table_leader, []).

set_all_complete :-
  get_newly_created_table_identifiers(Ts, _),
  set_all_complete_(Ts).

set_all_complete_([]).
set_all_complete_([T|Ts]) :-
  set_complete_status(T),
  set_all_complete_(Ts).

cleanup_all_complete :-
  get_newly_created_table_identifiers(Ts,_),
  cleanup_all_complete_(Ts).

cleanup_all_complete_([]).
cleanup_all_complete_([T|Ts]) :-
  cleanup_after_complete(T),
  cleanup_all_complete_(Ts).

activate(Wrapper,Worker,T) :-
    set_active_status(T),
  (
    delim(Wrapper,Worker,T),
    fail
  ;
    true
  ).

delim(Wrapper,Worker,Table) :-
%   debug(tabling, 'ACT: ~p on ~p', [Wrapper, Table]),
    reset(Worker,SourceCall,Continuation),
   ( Continuation = none ->
     (	 add_answer(Table,Wrapper)
     ->	 true %debug(tabling, 'ADD: ~p', [Wrapper])
     ;	 %debug(tabling, 'DUP: ~p', [Wrapper]),
	 fail
     )
   ;
     Continuation = cont(Cont),
     SourceCall = call_info(_,SourceTable),
     TargetCall = call_info(Wrapper,Table),
     Dependency = dependency(SourceCall,Cont,TargetCall),
     %debug(tabling, 'DEP: ~p: ~p', [SourceTable,Dependency]),
     store_dependency(SourceTable,Dependency)
   ).

completion :-
  ( worklist_empty ->
    set_all_complete,
    cleanup_all_complete,
    % The place of the call to reset is really important: it must happen after the completion. If you do it before, you will wrongly remove yourself from the list of newly created table identifiers. On starting hProlog there are no newly created table identifiers, and nb_getval gives [] which is the perfect value.
    reset_newly_created_table_identifiers
  ;
    pop_worklist(Table),
    completion_step(Table),
    completion
  ).

completion_step(SourceTableID) :-
  bb_get(SourceTableID, Table),
  get_nb_identifiers(Table, NBWorklistID, _),
  (
    table_get_work(NBWorklistID,Answer,dependency(Source,Continuation,Target)),
    Source = call_info(Answer,_),
    Target = call_info(Wrapper,TargetTable),
    delim(Wrapper,Continuation,TargetTable),
    fail
  ;
    true
  ).

table_get_work(NBWorklistID,Answer,Dependency) :-
  % get_worklist(Table, Worklist),
  % NOT IN PAPER (could be part of the definition of pop_worklist):
  bb_get(NBWorklistID, table_nb_worklist(Worklist)),
  unset_global_worklist_presence_flag(Worklist),
  set_flag_executing_all_work(Worklist),
  bb_put(NBWorklistID, table_nb_worklist(Worklist)),
  table_get_work_(NBWorklistID,Answer,Dependency).

table_get_work_(NBWorklistID,Answer,Dependency) :-
  worklist_do_all_work(NBWorklistID,Answer,Dependency0), % This will eventually fail
  copy_term(Dependency0,Dependency).

table_get_work_(NBWorklistID,_Answer,_Dependency) :-
  bb_get(NBWorklistID, table_nb_worklist(Worklist)),
  unset_flag_executing_all_work(Worklist),
  bb_put(NBWorklistID, table_nb_worklist(Worklist)),
  fail.

worklist_do_all_work(NBWorklistID,Answer,Dependency) :-
  ( bb_get(NBWorklistID, table_nb_worklist(Worklist)),
    wkl_worklist_work_done(Worklist) ->
    fail
  ;
    worklist_do_step(NBWorklistID,Answer,Dependency)
  ;
    worklist_do_all_work(NBWorklistID,Answer,Dependency)
  ).

worklist_do_step(NBWorklistID,Answer,Dependency) :-
  bb_get(NBWorklistID, table_nb_worklist(Worklist)),
  wkl_p_get_rightmost_inner_answer_cluster_pointer(Worklist,ACP),
  wkl_p_swap_answer_continuation(Worklist,ACP,SCP),
  dll_get_data(ACP,wkl_answer_cluster(AListFlag)),
  dll_get_data(SCP,wkl_suspension_cluster(SListFlag)),
  get_atts(AListFlag, batched_worklist, wkl_answer_cluster(AList)),
  get_atts(SListFlag, batched_worklist, wkl_suspension_cluster(SList)),
  bb_put(NBWorklistID, table_nb_worklist(Worklist)),
  member(Answer,AList),
  member(Dependency,SList).

:- initialization(bb_put(table_leader, [])).
