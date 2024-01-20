/** Support for Definite Clause Grammars.

A Prolog definite clause grammar (DCG) describes a sequence. Operationally, DCGs
can be used to parse, generate, complete and check sequences manifested as lists.

Check [The Power of Prolog chapter on DCGs](https://www.metalevel.at/prolog/dcg)
to learn more about them.
*/


:- module(dcgs,
          [op(1105, xfy, '|'),
           phrase/2,
           phrase/3,
           phrase/4,
           phrase/5,
           seq//1,
           seqq//1,
           ... //0,
           (-->)/2
          ]).

:- use_module(library(error)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(loader), [strip_module/3]).

:- meta_predicate phrase(2, ?).

:- meta_predicate phrase(2, ?, ?).

:- meta_predicate phrase(2, ?, ?, ?).

:- meta_predicate phrase(2, ?, ?, ?, ?).

%% phrase(+Body, ?Ls).
%
% True iff Body describes the list Ls. Body must be a DCG body.
% It is equivalent to `phrase(Body, Ls, [])`.
%
% Examples:
%
% ```
% as --> [].
% as --> [a], as.
%
% ?- phrase(as, Ls).
%    Ls = []
% ;  Ls = "a"
% ;  Ls = "aa"
% ;  Ls = "aaa"
% ;  ... .
%
% ?- phrase(as, "aaa").
%    true.
% ```

phrase(GRBody, S0) :-
    phrase(GRBody, S0, []).

%% phrase(+Body, ?Ls, ?Ls0).
%
% True iff Body describes part of the list Ls and the rest of Ls is Ls0.
%
% Example:
%
% ```
% ?- phrase(seq(X), "aaa", Y).
%    X = [], Y = "aaa"
% ;  X = "a", Y = "aa"
% ;  X = "aa", Y = "a"
% ;  X = "aaa", Y = [].
% ```
phrase(GRBody, S0, S) :-
    strip_module(GRBody, M, GRBody1),
    (  var(GRBody) ->
       instantiation_error(phrase/3)
    ;  nonvar(GRBody1),
       dcg_constr(GRBody1),
       dcg_body(GRBody1, S0, S, GRBody2) ->
       call(M:GRBody2)
    ;  call(M:GRBody1, S0, S)
    ).

phrase(GRBody, Arg, S0, S) :-
    strip_module(GRBody, M, GRBody1),
    (  var(GRBody) ->
       instantiation_error(phrase/4)
    ;  nonvar(GRBody1),
       GRBody1 =.. GRBodys1,
       append(GRBodys1, [Arg], GRBodys2),
       GRBody2 =.. GRBodys2,
       dcg_constr(GRBody2),
       dcg_body(GRBody2, S0, S, GRBody3) ->
       call(M:GRBody3)
    ;  call(M:GRBody1, Arg, S0, S)
    ).

phrase(GRBody, Arg1, Arg2, S0, S) :-
    strip_module(GRBody, M, GRBody1),
    (  var(GRBody) ->
       instantiation_error(phrase/5)
    ;  nonvar(GRBody1),
       GRBody1 =.. GRBodys1,
       append(GRBodys1, [Arg1,Arg2], GRBodys2),
       GRBody2 =.. GRBodys2,
       dcg_constr(GRBody2),
       dcg_body(GRBody2, S0, S, GRBody3) ->
       call(M:GRBody3)
    ;  call(M:GRBody1, Arg1, Arg2, S0, S)
    ).

% The same version of the below two dcg_rule clauses, but with module scoping.
dcg_rule(( M:NonTerminal, Terminals --> GRBody ), ( M:Head :- Body )) :-
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S1, Goal1),
    dcg_terminals(Terminals, S, S1, Goal2),
    Body = ( Goal1, Goal2 ).
dcg_rule(( M:NonTerminal --> GRBody ), ( M:Head :- Body )) :-
    NonTerminal \= ( _, _ ),
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S, Body).

% This program uses append/3 as defined in the Prolog prologue.
% Expands a DCG rule into a Prolog rule, when no error condition applies.
dcg_rule(( NonTerminal, Terminals --> GRBody ), ( Head :- Body )) :-
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S1, Goal1),
    dcg_terminals(Terminals, S, S1, Goal2),
    Body = ( Goal1, Goal2 ).
dcg_rule(( NonTerminal --> GRBody ), ( Head :- Body )) :-
    NonTerminal \= ( _, _ ),
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S, Body).

dcg_non_terminal(NonTerminal, S0, S, Goal) :-
    NonTerminal =.. NonTerminalUniv,
    append(NonTerminalUniv, [S0, S], GoalUniv),
    (  callable(NonTerminal) ->
       Goal =.. GoalUniv
    ;  Goal = NonTerminal % let call/N throw an error instead of throwing one here.
    ).

dcg_terminals(Terminals, S0, S, S0 = List) :-
    append(Terminals, S, List).

dcg_body(Var, S0, S, Body) :-
    var(Var),
    Body = phrase(Var, S0, S).
dcg_body(GRBody, S0, S, Body) :-
    nonvar(GRBody),
    dcg_constr(GRBody),
    dcg_cbody(GRBody, S0, S, Body).
dcg_body(NonTerminal, S0, S, Goal1) :-
    nonvar(NonTerminal),
    \+ dcg_constr(NonTerminal),
    NonTerminal \= ( _ -> _ ),
    NonTerminal \= ( \+ _ ),
    loader:strip_module(NonTerminal, M, NonTerminal0),
    dcg_non_terminal(NonTerminal0, S0, S, Goal0),
    (  functor(NonTerminal, (:), 2) ->
       Goal1 = M:Goal0
    ;  Goal1 = Goal0
    ).

% The following constructs in a grammar rule body
% are defined in the corresponding subclauses.
dcg_constr([]). % 7.14.1
dcg_constr([_|_]). % 7.14.2 - terminal sequence
dcg_constr(( _, _ )). % 7.14.3 - concatenation
dcg_constr(( _ ; _ )). % 7.14.4 - alternative
dcg_constr(( _'|'_ )). % 7.14.6 - alternative
dcg_constr({_}). % 7.14.7
dcg_constr(call(_)). % 7.14.8
dcg_constr(phrase(_)). % 7.14.9
dcg_constr(phrase(_,_)). % extension of 7.14.9
dcg_constr(phrase(_,_,_)). % extension of 7.14.9
dcg_constr(!). % 7.14.10
dcg_constr(\+ _) :- % 7.14.11 - not (existence implementation dep.)
    throw(error(representation_error(dcg_body), phrase/3)).
dcg_constr((_->_)) :- % 7.14.12 - if-then (existence implementation dep.)
    throw(error(representation_error(dcg_body), phrase/3)).

% The principal functor of the first argument indicates
% the construct to be expanded.
dcg_cbody([], S0, S, S0 = S).
dcg_cbody([T|Ts], S0, S, Goal) :-
    must_be(list, [T|Ts]),
    dcg_terminals([T|Ts], S0, S, Goal).
dcg_cbody(( GRFirst, GRSecond ), S0, S, ( First, Second )) :-
    dcg_body(GRFirst, S0, S1, First),
    dcg_body(GRSecond, S1, S, Second).
dcg_cbody(( GREither ; GROr ), S0, S, ( Either ; Or )) :-
    \+ subsumes_term(( _ -> _ ), GREither),
    dcg_body(GREither, S0, S, Either),
    dcg_body(GROr, S0, S, Or).
dcg_cbody(( GRCond ; GRElse ), S0, S, ( Cond ; Else )) :-
    subsumes_term(( _GRIf -> _GRThen ), GRCond),
    dcg_cbody(GRCond, S0, S, Cond),
    dcg_body(GRElse, S0, S, Else).
dcg_cbody(( GREither '|' GROr ), S0, S, ( Either ; Or )) :-
    dcg_body(GREither, S0, S, Either),
    dcg_body(GROr, S0, S, Or).
dcg_cbody({Goal}, S0, S, ( Goal, S0 = S )).
dcg_cbody(call(Cont), S0, S, call(Cont, S0, S)).
dcg_cbody(phrase(Body), S0, S, phrase(Body, S0, S)).
dcg_cbody(phrase(Body, Arg), S0, S, phrase(Body, Arg, S0, S)).
dcg_cbody(phrase(Body, Arg1, Arg2), S0, S, phrase(Body, Arg1, Arg2, S0, S)).
dcg_cbody(!, S0, S, ( !, S0 = S )).
% dcg_cbody(\+ GRBody, S0, S, ( \+ phrase(GRBody,S0,_), S0 = S )).
dcg_cbody(( GRIf -> GRThen ), S0, S, ( If -> Then )) :-
    dcg_body(GRIf, S0, S1, If),
    dcg_body(GRThen, S1, S, Then).

user:term_expansion(Term0, Term) :-
    nonvar(Term0),
    dcg_rule(Term0, Term).


%% seq(Seq)//
% 
% Describes a sequence
seq(Xs, Cs0,Cs) :-
   var(Xs),
   Cs0 == [],
   !,
   Xs = [],
   Cs0 = Cs.
seq([]) --> [].
seq([E|Es]) --> [E], seq(Es).

%% seqq(SeqOfSeqs)//
%
% Describes a sequence of sequences
seqq([]) --> [].
seqq([Es|Ess]) --> seq(Es), seqq(Ess).

%% ...//
%
% Describes an arbitrary number of elements
...(Cs0,Cs) :-
   Cs0 == [],
   !,
   Cs0 = Cs.
... --> [] | [_], ... .

error_goal(error(E, must_be/2), error(E, must_be/2)).
error_goal(error(E, (=..)/2), error(E, (=..)/2)).
error_goal(error(representation_error(dcg_body), Context),
           error(representation_error(dcg_body), Context)).
error_goal(E, _) :- throw(E).

user:goal_expansion(phrase(GRBody, S, S0), GRBody2) :-
    loader:strip_module(GRBody, M, GRBody0),
    nonvar(GRBody0),
    catch(dcgs:dcg_body(GRBody0, S, S0, GRBody1),
          E,
          dcgs:error_goal(E, GRBody1)
         ),
    (  GRBody = (_:_) ->
       GRBody2 = M:GRBody1
    ;  GRBody2 = GRBody1
    ).

user:goal_expansion(phrase(GRBody, S), phrase(GRBody, S, [])).


% (-->)/2 behaves as if it didn't exist. We export (and define) it
% only so that clauses for (-->)/2 cannot be asserted when
% library(dcgs) is loaded.

(_-->_) :- throw(error(existence_error(procedure,(-->)/2),(-->)/2)).
