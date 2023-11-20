/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    Copyright (c)  2016, VU University Amsterdam
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

:- module(table_wrapper,
	  [ %(table)/1,			% +Predicates
	    op(1150, fx, table)
	  ]).

:- use_module(library(dcgs)).
:- use_module(library(error)).

:- multifile(tabled/2).

%%:- multifile
%%	system:term_expansion/2,
%%	tabled/2.
%%:- dynamic
%%	system:term_expansion/2.

%%	table(+PredicateIndicators)
%
%	Prepare the given PredicateIndicators for tabling.  Can only
%	be used as a directive.

%% table(PIList) :-
%% 	throw(error(context_error(nodirective, table(PIList)), _)).

%% instantiation_error(Var) :-
%%         throw(error(instantiation_error(Var), _)).

wrappers(Var) -->
	{ var(Var), !,
	  instantiation_error(Var)
	}.
wrappers((A,B)) --> !,
	wrappers(A),
	wrappers(B).
wrappers(Name//Arity) -->
	{ atom(Name), integer(Arity), Arity >= 0, !,
	  Arity1 is Arity+2
	},
	wrappers(Name/Arity1).
wrappers(Name/Arity) -->
	{ atom(Name), integer(Arity), Arity >= 0, !,
	  functor(Head, Name, Arity),
	  atom_concat(Name, ' tabled', WrapName),
	  Head =.. [Name|Args],
	  WrappedHead =.. [WrapName|Args],
	  prolog_load_context(module, Module)
	},
	[ (   Head :-
		 start_tabling(Module:Head, WrappedHead)
	  ),
	  (:- multifile(table_wrapper:tabled/2)),
	  table_wrapper:tabled(Head, Module)
	].

rename(M:Term0, M:Term, _) :-
	atom(M), !,
	rename(Term0, Term, M).
rename((Head :- Body), (NewHead :- Body), Module) :- !,
	rename(Head, NewHead, Module).
rename((Head --> Body), (NewHead --> Body), Module) :- !,
	functor(Head, Name, Arity),
	PlainArity is Arity+1,
	functor(PlainHead, Name, PlainArity),
	catch(table_wrapper:tabled(PlainHead, Module),
          error(existence_error(procedure, tabled/2), _),
          false),
	rename_term(Head, NewHead).
rename(Head, NewHead, Module) :-
	catch(table_wrapper:tabled(Head, Module),
          error(existence_error(procedure, tabled/2), _),
          false),
    !,
	rename_term(Head, NewHead).

rename_term(Compound0, Compound) :-
	compound(Compound0), !,
	Compound0 =.. [Name|Args],
	atom_concat(Name, ' tabled', WrapName),
	Compound =.. [WrapName|Args].
rename_term(Name, WrapName) :-
	atom_concat(Name, ' tabled', WrapName).


user:term_expansion(Term0, Clauses) :-
    nonvar(Term0),
	Term0 = (:- table Preds),
	phrase(wrappers(Preds), Clauses).
user:term_expansion(Clause, NewClause) :-
    nonvar(Clause),
    prolog_load_context(module, Module),
	rename(Clause, NewClause, Module).
