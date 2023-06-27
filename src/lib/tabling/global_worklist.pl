/*    Ported to Scryer Prolog by Mark Thom (2019/2020).
 */

:- module(global_worklist,
	  [ put_new_global_worklist/0,
	    add_to_global_worklist/1,
	    worklist_empty/0,
	    pop_worklist/1
	  ]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).

:- attribute table_global_worklist/1.

verify_attributes(_, _, []).

attribute_goals(X) --> { put_atts(X, -table_global_worklist(_)) }.

put_new_global_worklist :-
  (  bb_get(table_global_worklist_initialized, _) ->
     true
  ;  put_atts(Worklist, table_global_worklist([])),
     bb_put(table_global_worklist, Worklist),
     bb_b_put(table_global_worklist_initialized, [])
  ).

add_to_global_worklist(TableIdentifier) :-
  bb_get(table_global_worklist, TableGlobalWorklistFlag),
  get_atts(TableGlobalWorklistFlag, table_global_worklist(L1)),
  put_atts(TableGlobalWorklistFlag, table_global_worklist([TableIdentifier|L1])),
  bb_put(table_global_worklist, TableGlobalWorklistFlag).

worklist_empty :-
  bb_get(table_global_worklist,TableGlobalWorklistFlag),
  get_atts(TableGlobalWorklistFlag, table_global_worklist(L)),
  L == [].

pop_worklist(TableIdentifier) :-
  bb_get(table_global_worklist,TableGlobalWorklistFlag),
  get_atts(TableGlobalWorklistFlag, table_global_worklist(L1)),
  L1 = [TableIdentifier|L2],
  put_atts(TableGlobalWorklistFlag, table_global_worklist(L2)),
  bb_put(table_global_worklist, TableGlobalWorklistFlag).
