:- module(table_datastructure,
	  [ get_answer/2,			% +TableID, -Answer
	    add_answer/2,			% +TableID, +Answer
	    get_call_variant/2,			% +TableID, -CallVariant
	    set_complete_status/1,		% +TableID
	    set_active_status/1,		% +TableID
	    tbd_table_status/2,			% +TableID, -Status
	    table_for_variant/2,		% +Variant, -TableID
	    store_dependency/2,			% +TableID, +Suspension
	    cleanup_after_complete/1,		% +TableID
	    get_newly_created_table_identifiers/2, % NewlyCreatedTableIDs, NumIDs
	    reset_newly_created_table_identifiers/0,
	    answers_for_variant/2,	        % +Variant, -Answers
	    put_new_table_identifiers/0,
	    get_nb_identifiers/3                % +Table, -NbWorklistID, -NbAnswerTreeID
	  ]).

:- use_module(library(tabling/table_link_manager)).
:- use_module(library(tabling/trie)).

/*  Part of SWI-Prolog

    Author:        Benoit Desouter <Benoit.Desouter@UGent.be>
		   Jan Wielemaker (SWI-Prolog port)
    Copyright (c)  2016, Benoit Desouter
    All rights reserved.

    Ported to Scryer Prolog by Mark Thom (2019/2020).

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- use_module(library(tabling/batched_worklist)).

:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(gensym)).
:- use_module(library(iso_ext)).

:- attribute table_status/1, newly_created_table_identifiers/1.

verify_attributes(_, _, []).

attribute_goals(X) -->
    { put_atts(X, -table_status(_)),
      put_atts(X, -newly_created_table_identifiers(_)) }.

% This file defines the table datastructure.
%
% The table datastructure contains the following sub-structures:
% - the answer trie
% - the worklist
%
% Structure for tables:
% table(CallVariant,Status,AnswerTrie,Worklist) or complete_table(CallVariant,AnswerTrie).
% where AnswerTrie contains a trie of unique answers
%
% Remember that a table may also be nonexistent!
% nb_getval(nonexistent,X) then gives [].

put_new_table_identifiers :-
  (  bb_get(newly_created_table_identifiers_initialized, _) ->
     true
  ;  put_atts(NewlyCreatedFlag, newly_created_table_identifiers([]-0)),
     bb_b_put(newly_created_table_identifiers, NewlyCreatedFlag),
     bb_b_put(newly_created_table_identifiers_initialized, [])
  ).

% Returns a list of newly created table identifiers since the last call to reset_newly_created_table_identifiers/0, as well as the length of the list.
get_newly_created_table_identifiers(NewlyCreatedTableIdentifiers,NumIdentifiers) :-
  bb_get(newly_created_table_identifiers, NewlyCreatedFlag),
  get_atts(NewlyCreatedFlag, newly_created_table_identifiers(NewlyCreatedTableIdentifiers-NumIdentifiers)).

reset_newly_created_table_identifiers :-
  bb_get(newly_created_table_identifiers, NewlyCreatedFlag),
  put_atts(NewlyCreatedFlag, newly_created_table_identifiers([]-0)).

add_to_newly_created_table_identifiers(TableIdentifier) :-
  bb_get(newly_created_table_identifiers, NewlyCreatedFlag),
  get_atts(NewlyCreatedFlag, newly_created_table_identifiers(L1-Num1)),
  Num2 is Num1 + 1,
  put_atts(NewlyCreatedFlag, newly_created_table_identifiers([TableIdentifier|L1]-Num2)).

% PRIVATE
% Mode: + -
%
% Created in the fresh status.
p_create_table(CallVariant,TableIdentifier) :-
  % We use a copy_term here so that we can be sure not to corrupt our table if CallVariant is "changed" afterwards.
  copy_term(CallVariant,CallVariant2),
  % Generate a table identifier, create the table and do bookkeeping.
  gensym(table,TableIdentifier),
  % Create a trie and a worklist.
  trie_new(EmptyTrie),
  wkl_new_worklist(TableIdentifier,NewWorklist),
  put_atts(StatusFlag, table_status(fresh)),
  %% this is important! we don't want to copy the incomplete table every time we refer to it,
  %% which would occur if we used bb_put here.
  %% note that the complete_table variant is written to the blackboard using bb_get.
  atom_concat(TableIdentifier, nb_worklist, NbWorklistID),
  atom_concat(TableIdentifier, nb_answer_trie, NbAnswerTrieID),
  bb_put(TableIdentifier, table(CallVariant2,StatusFlag,NbWorklistID,NbAnswerTrieID)),
  bb_put(NbWorklistID, table_nb_worklist(NewWorklist)),
  bb_put(NbAnswerTrieID, table_nb_answer_trie(EmptyTrie)),
  p_link_variant_identifier(CallVariant2,TableIdentifier),
  add_to_newly_created_table_identifiers(TableIdentifier).

% Get the Status for table TableIdentifier
% Throws exception if this table does not exist.
tbd_table_status(TableIdentifier,Status) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  tbd_table_status_(Table,Status).

% Is also used in other predicates than tbd_table_status.
tbd_table_status_(table(_CallVariant,StatusFlag,_NbWorklistID, _NbAnswerTrieID),Status) :-
  get_atts(StatusFlag, table_status(Status)).
tbd_table_status_(complete_table(_,_,_),complete).

% PRIVATE
% Table must already exist.
p_get_table_for_identifier(TableIdentifier,Table) :-
  bb_get(TableIdentifier,Table).

% Get the table identifier (!!) for call variant V, creating a new one if necessary.
%
% More costly than directly passing the table identifier for already existing tables.
%
% Since this creates a new table, this predicate is NOT meant for users who should get access to existing tables - f.e. benchmark shortest_path.P
%
table_for_variant(V,TableIdentifier) :-
  ( p_existing_table(V,TableIdentifier) ->
    true
  ;
    p_create_table(V,TableIdentifier)
  ).

% Get call variant for this table
get_call_variant(TableIdentifier,CallVariant) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  get_call_variant_(Table,CallVariant).

get_call_variant_(table(CallVariant,_Status,_NbWorklistID,_NbAnswerTrieID),CallVariant).
get_call_variant_(complete_table(CallVariant,_NbWorklistID,_NbAnswerTrieID),CallVariant).

add_answer(TableIdentifier,A) :-
  p_get_table_for_identifier(TableIdentifier,Table),
% arg(1,Table,CallVariant),
  arg(3,Table,NbWorklistID),
  arg(4,Table,NbAnswerTrieID),
  bb_get(NbWorklistID,table_nb_worklist(Worklist)),
  bb_get(NbAnswerTrieID,table_nb_answer_trie(AnswerTrie)),
  copy_term(A,A2),
  % This predicate succeeds if the answer was new, otherwise it fails.
  trie_insert(AnswerTrie,A2,A2), % Use answer both as key and as value. Having it as value uses memory, but greatly simplifies getting all the answers.
  % We got here, so trie_insert added a new answer.
  % We must also insert this answer in the worklist
  wkl_add_answer(Worklist,A2),
  bb_put(NbWorklistID, table_nb_worklist(Worklist)),
  bb_put(NbAnswerTrieID, table_nb_answer_trie(AnswerTrie)).

get_answer(TableIdentifier,A) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  get_answer_trie_(Table,AnswerTrie),
  % The trick is that we have stored the answers as values of the trie and that there is a method to get all the values.
  trie_get_all_values(AnswerTrie,A).

% get_answer_trie_(TableOrCompleteTable,AnswerTrie).
% First argument is not a TableIdentifier.
get_answer_trie_(table(_CallVariant,_Status,_NbWorklistID, NbAnswerTrieID),AnswerTrie) :-
  bb_get(NbAnswerTrieID, table_nb_answer_trie(AnswerTrie)).
get_answer_trie_(complete_table(_CallVariant,_NbWorklistID, NbAnswerTrieID),AnswerTrie) :-
  bb_get(NbAnswerTrieID, table_nb_answer_trie(AnswerTrie)).

get_nb_identifiers(table(_CallVariant, _Status, NbWorklistID, NbAnswerTrieID), NbWorklistID, NbAnswerTrieID).
get_nb_identifiers(complete_table(_CallVariant, NbWorklistID, NbAnswerTrieID), NbWorklistID, NbAnswerTrieID).

% Get a list of answers for the given call variant.
% Used in compare_expected_for_variant/3 in testlib.pl
% IMPORTANT: table must be filled already, this is not done in this predicate! Therefore can be called during execution.
% V = variant
% LA = list of answers.
%
% More costly operation than directly giving the table identifier.
answers_for_variant(V,LA) :-
  table_for_variant(V,TableIdentifier),
  p_get_table_for_identifier(TableIdentifier,Table),
  get_answer_trie_(Table,AnswerTrie),
  findall(Value,trie_get_all_values(AnswerTrie,Value),LA).

% Set status of table TableIdentifier to active
set_active_status(TableIdentifier) :-
  tbd_status_transition(TableIdentifier,active,fresh,'set_active_status').

cleanup_after_complete(TableIdentifier) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  cleanup_after_complete_(Table,TableIdentifier).

% Clause for a (noncomplete) table.
cleanup_after_complete_(
    table(CallVariant,_ActualOldStatus, NbWorklistID, NbAnswerTrieID),
    TableIdentifier
  ) :-
  bb_put(TableIdentifier,complete_table(CallVariant, NbWorklistID, NbAnswerTrieID)).
% If necessary for debugging add second clause for complete_table.

% Set status of table TableIdentifier to complete.
set_complete_status(TableIdentifier) :-
  % The transition must be active to complete, otherwise we have an invalid status transition.
  % Preexisting tables should have been cleaned-up, thus not have the form table/5 anymore, thus complete -> complete is not possible there.
  p_get_table_for_identifier(TableIdentifier,Table),
  set_complete_status_(Table,TableIdentifier).

% set_complete_status_(Table,TableIdentifier).
set_complete_status_(table(_CallVariant,_OldStatus,_NbWorklistID, _NbAnswerTrieID),TableIdentifier) :-
  tbd_status_transition(TableIdentifier,complete,active,'set_complete_status').

tbd_status_transition_no_check(TableIdentifier,NewStatus) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  tbd_status_transition_no_check_(TableIdentifier,Table,NewStatus).

tbd_status_transition_no_check_(TableIdentifier,Table,NewStatus) :-
    Table = table(_,StatusFlag,_,_),
    put_atts(StatusFlag, table_status(NewStatus)),
    bb_put(TableIdentifier, Table).

% Set Table's status to NewStatus if current status is RequiredOldStatus, otherwise throw an exception mentioning CallerAsString: attempt to set NewStatus for table TableIdentifier, but current status was ActualOldStatus instead of RequiredOldStatus
tbd_status_transition(TableIdentifier,NewStatus,_RequiredOldStatus,_CallerAsString) :-
  p_get_table_for_identifier(TableIdentifier,Table),
  tbd_status_transition_no_check_(TableIdentifier,Table,NewStatus).

store_dependency(TableIdentifier,Suspension) :-
  p_get_table_for_identifier(TableIdentifier, Table),
  get_nb_identifiers(Table, NbWorklistID, _NbAnswerTrieID),
  copy_term(Suspension, SuspensionCopy),
  bb_get(NbWorklistID, table_nb_worklist(Worklist)),
  wkl_add_suspension(Worklist, SuspensionCopy),
  bb_put(NbWorklistID, table_nb_worklist(Worklist)).
