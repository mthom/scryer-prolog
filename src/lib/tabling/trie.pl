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

:- module(trie,
	  [ trie_new/1,				% -Trie
	    trie_insert/3,			% !Trie, +Key, +Value
	    trie_insert_succeed/3,
	    trie_lookup/3,			% +Trie, +Key, -Value
	    trie_get_all_values/2		% +Trie, -Value
	  ]).

:- use_module(library(format)).

:- use_module(library(assoc)).
:- use_module(library(atts)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).

:- attribute maybe_just/1, children/1.

verify_attributes(_, _, []).

attribute_goals(X) -->
    { put_atts(X, -maybe_just(_)),
      put_atts(X, -children(_)) }.

% Implementation of a prefix tree, a.k.a. trie %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Desired complexity for lookup and insert: linear in the length of the key.

% ATTENTION: do not use the term functor_data/2; this is used internally here.

% Inspiration from http://en.wikipedia.org/wiki/Trie

% Structure of tries:
% trie_inner_node(MaybeValue,Children).
% where Children is an association list of nonvars to tries.
% and where MaybeValue is maybe_none/0 or maybe_just(Value).

% PRIVATE
% For a term of the form p(a,q(b)), "returns" functor_data(p,2) and [a,q(b)].
% p_trie_arity_univ(+Term,-FunctorData,-ArgumentsList).
p_trie_arity_univ(Term,functor_data(Name,Arity),Arguments) :-
  (  var(Term) ->
     Name = Term,
     Arity = 0,
     Arguments = []
  ;  Term =.. [Name|Arguments],
     functor(Term,_,Arity)
  ).

% Returns a new empty trie.
trie_new(Trie) :-
  empty_assoc(Assoc),
  put_atts(A, children(Assoc)),
  Trie = trie_inner_node(_,A).

% Succeeds if given trie does not contain any key-value pair.
% trie_is_empty(+Trie)
trie_is_empty(trie_inner_node(X,A)) :-
  get_atts(X, -maybe_just(_)),
  get_atts(A, children(Assoc)),
  empty_assoc(Assoc).

% For internal use.
% For now, Children is an association list that can be manipulated using the assoc_ predicates.
trie_get_children(trie_inner_node(_,ChildNode),Children) :-
  get_atts(ChildNode, children(Children)).

% For internal use.
trie_get_maybe_value(trie_inner_node(MaybeNode,_),MaybeValue) :-
  get_atts(MaybeNode, maybe_just(MaybeValue)).

% Destructive update of the association list Children.
% For internal use.
trie_set_children(trie_inner_node(_,ChildNode),Children) :-
  put_atts(ChildNode, children(Children)).

trie_set_maybe_value(trie_inner_node(MaybeNode, _),MaybeValue) :-
  put_atts(MaybeNode, MaybeValue).

trie_insert_succeed(Trie,Key,Value) :-
  ( trie_insert(Trie,Key,Value) ->
    true
  ;
    true
  ).

% Succeeds if the term was not present, fails if the term was present.
% The term will be present now, whatever the outcome.
% We don't use an extra argument to indicate earlier presence, as this increases the trail size.
trie_insert(Trie,Key,Value) :-
  p_trie_arity_univ(Key,FunctorData,KeyList),
  trie_insert_1(KeyList,FunctorData,Trie,Value).

trie_insert_1([],FunctorData,Trie,Value) :-
  trie_get_children(Trie,Assoc),
  % You need Assoc twice: once to traverse through it, once keeping it as a whole for insertion using put_assoc/4.
  trie_insert_a(Assoc,Assoc,FunctorData,Trie,Value).

% Inline the failure and success continuation to avoid a growing trail stack.
trie_insert_1([First|Rest],FunctorData,Trie,Value) :-
  trie_get_children(Trie,Assoc),
  % You need Assoc twice: once to traverse through it, once keeping it as a whole for insertion using put_assoc/4.
  trie_insert_1_1(Assoc,Assoc,FunctorData,Trie,First,Rest,Value).

% Else part, base case: empty assoc list.
trie_insert_a(t,Assoc,FunctorData,Trie,Value) :-
  trie_new(Subtrie),
  trie_set_maybe_value(Subtrie,maybe_just(Value)),
  put_assoc(FunctorData,Assoc,Subtrie,NewAssoc),
  trie_set_children(Trie,NewAssoc).

% Then part, nonempty assoc tree.
trie_insert_a(t(K,V,_,L,R),Assoc,FunctorData,Trie,Value) :-
  compare(Rel,FunctorData,K),
  trie_insert_b(Rel,V,L,R,Assoc,FunctorData,Trie,Value).

% Recursively look in the left part of the assoc tree.
trie_insert_b(<,_V,L,_R,Assoc,FunctorData,Trie,Value) :-
  trie_insert_a(L,Assoc,FunctorData,Trie,Value).

% Recursively look in the right part of the assoc tree.
trie_insert_b(>,_V,_L,R,Assoc,FunctorData,Trie,Value) :-
  trie_insert_a(R,Assoc,FunctorData,Trie,Value).

trie_insert_b(=,V,_L,_R,_Assoc,_FunctorData,_Trie,Value) :-
  trie_get_maybe_value(V,MaybeValue), % V is the Subtrie
  ( MaybeValue == maybe_none ->
    trie_set_maybe_value(V,maybe_just(Value))
    % Use true to indicate that the answer was new.
  ;
    MaybeValue = maybe_just(JustValue),
    ( JustValue == Value ->
  	% Fail to indicate earlier presence
  	fail
    ;
      throw('trie: attempt to update the value for a key')
    )
  ).

% Else part, base case: empty assoc list
trie_insert_1_1(t,Assoc,FunctorData,Trie,First,Rest,Value) :-
  % Assoc = t, % t is the empty assoc tree
  trie_new(Subtrie),
  put_assoc(FunctorData,Assoc,Subtrie,NewAssoc),
  trie_set_children(Trie,NewAssoc),
  trie_insert_2(First,Rest,Subtrie,Value).

% Then part, lookup in assoc list.
trie_insert_1_1(t(K,V,_,L,R),Assoc,FunctorData,Trie,First,Rest,Value) :-
  compare(Rel,FunctorData,K),
  trie_insert_1_1_1(Rel,V,L,R,Assoc,FunctorData,Trie,First,Rest,Value).

trie_insert_1_1_1(=,V,_L,_R,_Assoc,_FunctorData,_Trie,First,Rest,Value) :-
  trie_insert_2(First,Rest,V,Value). % V is the Subtrie

trie_insert_1_1_1(<,_V,L,_R,Assoc,FunctorData,Trie,First,Rest,Value) :-
  % Look in the left part of the assoc tree.
  trie_insert_1_1(L,Assoc,FunctorData,Trie,First,Rest,Value).

trie_insert_1_1_1(>,_V,_L,R,Assoc,FunctorData,Trie,First,Rest,Value) :-
  % Look in the right part of the assoc tree.
  trie_insert_1_1(R,Assoc,FunctorData,Trie,First,Rest,Value).

trie_insert_2(RegularTerm,Rest,Trie,Value) :-
  p_trie_arity_univ(RegularTerm,FunctorData,KList),
  append(KList,Rest,KList2),
  trie_insert_1(KList2,FunctorData,Trie,Value).

trie_lookup(Trie,Key,Value) :-
  p_trie_arity_univ(Key,FunctorData,KeyList),
  trie_lookup_1(FunctorData,KeyList,Trie,Value).

trie_lookup_1(FunctorData,Rest,Trie,Value) :-
  % Select right subtree, fail if it isn't there, and do recursive call.
  trie_get_children(Trie,Assoc),
  get_assoc(FunctorData,Assoc,Subtrie), % Fails if not present
  trie_lookup_2(Rest,Subtrie,Value).

trie_lookup_2([],Trie,Value) :-
  % If the value at this trie is maybe_just(X), then X is our Value.
  % Otherwise, there is no value for this key, so we fail...
  trie_get_maybe_value(Trie,Value).
% Regular term at the head, like p or p(a). Not functor_data/2.
trie_lookup_2([RegularTerm|Rest],Trie,Value) :-
  % split RegularTerm
  p_trie_arity_univ(RegularTerm,FunctorData,KList),
  % Make a recursive call on KList ++ Rest.
  % Since we cannot implement p_trie_arity_univ so that "its result", KList, has a free variable at the end, without resorting to techniques that require linear time, we need a call to append/3. However, since KList will in general be rather short, I don't expect this to be a large problem in practice.
  append(KList,Rest,KList2),
  trie_lookup_1(FunctorData,KList2,Trie,Value).


% Returns all values in the trie by backtracking - we don't provide any information about the associated key.
trie_get_all_values(Trie,Value) :-
  trie_get_maybe_value(Trie,Value).
trie_get_all_values(Trie,Value) :-
  trie_get_children(Trie,Children),
  gen_assoc(_Key, Children, ChildTrie),
  trie_get_all_values(ChildTrie,Value).
