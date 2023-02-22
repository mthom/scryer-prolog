:- module(ffi, [use_foreign_module/2, foreign_struct/2]).

:- use_module(library(lists)).
:- use_module(library(error)).
    
foreign_struct(Name, Elements) :-
    '$define_foreign_struct'(Name, Elements).

use_foreign_module(LibName, Predicates) :-
    '$load_foreign_lib'(LibName, Predicates),
    maplist(assert_predicate, Predicates).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, void],
    length(Inputs, NumInputs),
    functor(Head, Name, NumInputs),
    term_variables(Head, TermList),
    Body = (
	lists:maplist(ffi:check_input, Inputs, TermList),
	'$foreign_call'(Name, TermList, _),!
    ),
    Predicate =.. [:-, Head, Body],
    assertz(ffi:Predicate).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, bool],
    length(Inputs, NumInputs),
    functor(Head, Name, NumInputs),
    term_variables(Head, TermList),
    Body = (
	lists:maplist(ffi:check_input, Inputs, TermList),
	'$foreign_call'(Name, TermList, 1),!
    ),
    Predicate =.. [:-, Head, Body],
    assertz(ffi:Predicate).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, Return],
    \+ member(Return, [void, bool]),
    length(Inputs, NumInputs),
    NumArgs is NumInputs + 1,
    functor(Head, Name, NumArgs),
    term_variables(Head, TermList),
    Body = (
	lists:append(TermListInputs, [TermListReturn], TermList),
	lists:maplist(ffi:check_input, Inputs, TermListInputs),
	'$foreign_call'(Name, TermListInputs, TermListReturn),!
    ),
    Predicate =.. [:-, Head, Body],
    assertz(ffi:Predicate).

check_input(sint8, Var) :-
    must_be(integer, Var),
    (
	(Var > -129, Var < 128) ->
	true
    ;   domain_error(integer_does_not_fit, Var, foreign_call/3)
    ).
check_input(sint16, Var) :-
    must_be(integer, Var),
    (
	(Var > -32769, Var < 32768) ->
	true
    ;   domain_error(integer_does_not_fit, Var, foreign_call/3)
    ).
check_input(sint32, Var) :-
    must_be(integer, Var),
    (
	(Var > -2147483649, Var < 2147483648) ->
	true
    ;   domain_error(integer_does_not_fit, Var, foreign_call/3)
    ).
check_input(sint64, Var) :-
    must_be(integer, Var).
check_input(f32, _Var).
check_input(f64, _Var).
check_input(cstr, Var) :-
    must_be(chars, Var).
check_input(_, Var).
%    must_be(list, Var).
    
% TODO: assert native predicates.
% They MUST validate types
