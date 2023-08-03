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

:- module(double_linked_list,
	  [ dll_new_double_linked_list/1,	% -List
	    dll_append_right/2,			% !List, +Element
	    dll_append_left/2,			% !List, +Element
	    dll_append_right/3,			% !List, +Element, -Pointer
	    dll_append_left/3,			% !List, +Element, -Pointer
	    dll_get_data/2,			% +List, -Head
	    dll_get_pointer_to_next/2,		% +List, -Pointer
	    dll_get_pointer_to_previous/2,	% +List, -Pointer
	    dll_is_dummy_pointer/2,		% +List, +Pointer
	    dll_p_swap_adjacent_elements_/2,	% +Pointer1, +Pointer2
	    dll_get_contents/2,
	    dll_get_reverse_contents/2
	  ]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).

:- attribute dll_element/1, dll_next/1, dll_prev/1.

attribute_goals(X) -->
     { put_atts(X, -dll_element(_)),
       put_atts(X, -dll_next(_)),
       put_atts(X, -dll_prev(_)) }.

% A circular double linked list
% =============================

% Always have a unused-cell at the beginning.

% I do not always inline unifications because the head is then more readable for users who don't need to know the details.

% Due to lack of modules in hProlog, the following predicate names should not be used elsewhere:
% - the heads of all following rules (starting with dll_, I reserve "the namespace"!)

% dll_cell(Element,Next,Previous)

% The following is perhaps odd:
%
%   Next link = more to the front (the left)
%   Previous link = more to the back (the right)
%
%   List structure
%   --------------
%   front-of-the-list | ... | back-of-the-list

dll_new_double_linked_list(List) :-
    % Nonused cell dll_start at the beginning, points to itself (this is easy when adding elements).
    List = dll_cell(Start),
    put_atts(Start, [dll_next(List), dll_prev(List), dll_element(dll_start)]).

dll_append_right(List, Element) :-
  dll_append_right(List, Element, _).

dll_append_left(List, Element) :-
  dll_append_left(List, Element, _).

% Append at the back of the list
% Mode: + + -
dll_append_right(List, Element, Pointer) :-
  % Get pointer to cell currently at the back. Done by taking the previous element from the unused element representing the list.
  dll_get_pointer_to_previous(List, OldBack),
  % Make the new cell point to OldBack as predecessor
  % Make the new cell point to the unused cell as successor.
  Pointer = dll_cell(NewCell),
  put_atts(NewCell, [dll_element(Element), dll_next(List), dll_prev(OldBack)]),
  % Make OldBack point to the new cell as successor
  dll_p_set_next_pointer(OldBack, Pointer),
  % Make the unused cell point to the new cell as predecessor
  dll_p_set_previous_pointer(List, Pointer).

% Add to the front of the list
% Mode: + + -
dll_append_left(List, Element, Pointer) :-
    % Get pointer to cell currently at the front. Done by taking the next element from the unused element representing the list.
    dll_get_pointer_to_next(List, OldFront),
    % Make the new cell point to OldFront as successor
    % Make the new cell point to the unused cell as predecessor
    Pointer = dll_cell(NewCell),
    put_atts(NewCell, [dll_element(Element), dll_prev(List), dll_next(OldFront)]),
    % Make OldFront point to the new cell as predecessor
    dll_p_set_previous_pointer(OldFront, Pointer),
    % Make the unused cell point to the new cell as successor
    dll_p_set_next_pointer(List, Pointer).

% get_next_cell?
dll_get_pointer_to_next(dll_cell(Cell), PointerNext) :-
    get_atts(Cell, dll_next(PointerNext)).

% get_previous_cell?
dll_get_pointer_to_previous(dll_cell(Cell), PointerPrevious) :-
    get_atts(Cell, dll_prev(PointerPrevious)).

% Will happily give you the "data" from the unused cell at the beginning. (We use this odd behaviour below, f.e. in dll_p_foreach_element_/2.)
dll_get_data(dll_cell(Cell), Element) :-
    get_atts(Cell, dll_element(Element)).

dll_is_dummy_pointer(List, Pointer) :-
    dll_get_contents(List, ListContents),
    dll_get_contents(Pointer, PointerContents),
    \+ PointerContents \= ListContents.

% Special case of swapping - used in dll_swap/2.
% This is also the case used for swapping a freshly created list with itself.
%
% Sketch: APrevious <-> PointerA <-> PointerB <-> BNext etc.
dll_p_swap_adjacent_elements(PointerA, PointerB) :-
    % Order B A?
    ( dll_get_pointer_to_next(PointerB, PointerA) ->
      dll_p_swap_adjacent_elements_(PointerB, PointerA)
    ;
      % Order A B!
      dll_p_swap_adjacent_elements_(PointerA, PointerB)
    ).

% Assumes the order A B.
dll_p_swap_adjacent_elements_(PointerA, PointerB) :-
    % Get A's previous and B's next
    dll_get_pointer_to_previous(PointerA, PointerAPrevious),
    dll_get_pointer_to_next(PointerB, PointerBNext),
    % Set A's previous to B
    dll_p_set_previous_pointer(PointerA, PointerB),
    % Set B's next to A
    dll_p_set_next_pointer(PointerB, PointerA),
    % Set A's next to BNext
    dll_p_set_next_pointer(PointerA, PointerBNext),
    % Set B's previous to APrevious
    dll_p_set_previous_pointer(PointerB, PointerAPrevious),
    % Set APrevious' next to B !!
    dll_p_set_next_pointer(PointerAPrevious, PointerB),
    % Set BNext's previous to A !!
    dll_p_set_previous_pointer(PointerBNext, PointerA).

% Private
% Careful: make sure this is called on the actual cell, and not some copy.
% Mode: + +
dll_p_set_previous_pointer(dll_cell(Cell), PointerToNewPrevious) :-
    put_atts(Cell, dll_prev(PointerToNewPrevious)).

% Private
% Careful: make sure this is called on the actual cell, and not some copy.
% Mode: + +
dll_p_set_next_pointer(dll_cell(Cell), PointerToNewNext) :-
    put_atts(Cell, dll_next(PointerToNewNext)).

dll_extract_element(ElementFlag, Element) :-
    (  ElementFlag = wkl_suspension_cluster(SuspensionClusterFlag) ->
       get_atts(SuspensionClusterFlag, batched_worklist, wkl_suspension_cluster(SuspensionCluster)),
       Element = wkl_suspension_cluster(SuspensionCluster)
    ;  ElementFlag = wkl_answer_cluster(AnswerClusterFlag) ->
       get_atts(AnswerClusterFlag, batched_worklist, wkl_answer_cluster(AnswerCluster)),
       Element = wkl_answer_cluster(AnswerCluster)
    ).

dll_get_contents(List, Contents) :-
    dll_get_pointer_to_next(List, Next),
    dll_get_contents_(Next, Contents).

dll_get_contents_(List, Contents) :-
    dll_get_data(List, ElementFlag),
    (  ElementFlag == dll_start ->
       Contents = []
    ;  dll_extract_element(ElementFlag, Element),
       Contents = [Element | Rest],
       dll_get_pointer_to_next(List, Next),
       dll_get_contents_(Next, Rest)
    ).

dll_get_reverse_contents(List, Contents) :-
    dll_get_pointer_to_previous(List, Prev),
    dll_get_reverse_contents_(Prev, Contents).

dll_get_reverse_contents_(List, Contents) :-
    dll_get_data(List, ElementFlag),
    (  ElementFlag == dll_start ->
       Contents = []
    ;  dll_extract_element(ElementFlag, Element),
       Contents = [Element | Rest],
       dll_get_pointer_to_previous(List, Prev),
       dll_get_reverse_contents_(Prev, Rest)
    ).
