:- module(dcgs,
          [op(1105, xfy, '|'),
           phrase/2,
           phrase/3,
           seq//1,
           seqq//1,
           ... //0
          ]).

:- use_module(library(error)).
:- use_module(library(iso_ext)).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(loader), [strip_module/3]).

load_context(GRBody, Module, GRBody0) :-
    strip_module(GRBody, Module, GRBody0),
    (  nonvar(Module) ->
       true
    ;  prolog_load_context(module, Module) ->
       true
    ;  Module = user
    ).


:- meta_predicate phrase(2, ?).

:- meta_predicate phrase(2, ?, ?).

phrase(GRBody, S0) :-
    phrase(GRBody, S0, []).

phrase(GRBody, S0, S) :-
    load_context(GRBody, Module, GRBody0),
    (  var(GRBody0) ->
       instantiation_error(phrase/3)
    ;  dcg_body(GRBody0, S0, S, GRBody1, Module) ->
       call(Module:GRBody1)
    ;  type_error(callable, GRBody0, phrase/3)
    ).


module_call_qualified(M, Call, Call1) :-
    (  nonvar(M) -> Call1 = M:Call
    ;  Call = Call1
    ).


% The same version of the below two dcg_rule clauses, but with module scoping.
dcg_rule(( M:NonTerminal, Terminals --> GRBody ), ( M:Head :- Body )) :-
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S1, Goal1, _),
    dcg_terminals(Terminals, S, S1, Goal2),
    Body = ( Goal1, Goal2 ).
dcg_rule(( M:NonTerminal --> GRBody ), ( M:Head :- Body )) :-
    NonTerminal \= ( _, _ ),
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S, Body, _).

% This program uses append/3 as defined in the Prolog prologue.
% Expands a DCG rule into a Prolog rule, when no error condition applies.
dcg_rule(( NonTerminal, Terminals --> GRBody ), ( Head :- Body )) :-
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S1, Goal1, _),
    dcg_terminals(Terminals, S, S1, Goal2),
    Body = ( Goal1, Goal2 ).
dcg_rule(( NonTerminal --> GRBody ), ( Head :- Body )) :-
    NonTerminal \= ( _, _ ),
    dcg_non_terminal(NonTerminal, S0, S, Head),
    dcg_body(GRBody, S0, S, Body, _).

dcg_non_terminal(NonTerminal, S0, S, Goal) :-
    NonTerminal =.. NonTerminalUniv,
    append(NonTerminalUniv, [S0, S], GoalUniv),
    Goal =.. GoalUniv.

dcg_terminals(Terminals, S0, S, S0 = List) :-
    append(Terminals, S, List).

dcg_body(Var, S0, S, Body, M) :-
    var(Var),
    module_call_qualified(M, Var, Var1),
    Body = phrase(Var1, S0, S).
dcg_body(GRBody, S0, S, Body, M) :-
    nonvar(GRBody),
    dcg_constr(GRBody),
    dcg_cbody(GRBody, S0, S, Body, M).
dcg_body(NonTerminal, S0, S, Goal1, M) :-
    nonvar(NonTerminal),
    \+ dcg_constr(NonTerminal),
    NonTerminal \= ( _ -> _ ),
    NonTerminal \= ( \+ _ ),
    module_call_qualified(M, Goal, Goal1),
    dcg_non_terminal(NonTerminal, S0, S, Goal).

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
dcg_constr(!). % 7.14.10
%% dcg_constr(\+ _). % 7.14.11 - not (existence implementation dep.)
dcg_constr((_->_)). % 7.14.12 - if-then (existence implementation dep.)

% The principal functor of the first argument indicates
% the construct to be expanded.
dcg_cbody([], S0, S, S0 = S, _M).
dcg_cbody([T|Ts], S0, S, Goal, _M) :-
    must_be(list, [T|Ts]),
    dcg_terminals([T|Ts], S0, S, Goal).
dcg_cbody(( GRFirst, GRSecond ), S0, S, ( First, Second ), M) :-
    dcg_body(GRFirst, S0, S1, First, M),
    dcg_body(GRSecond, S1, S, Second, M).
dcg_cbody(( GREither ; GROr ), S0, S, ( Either ; Or ), M) :-
    \+ subsumes_term(( _ -> _ ), GREither),
    dcg_body(GREither, S0, S, Either, M),
    dcg_body(GROr, S0, S, Or, M).
dcg_cbody(( GRCond ; GRElse ), S0, S, ( Cond ; Else ), M) :-
    subsumes_term(( _GRIf -> _GRThen ), GRCond),
    dcg_cbody(GRCond, S0, S, Cond, M),
    dcg_body(GRElse, S0, S, Else, M).
dcg_cbody(( GREither '|' GROr ), S0, S, ( Either ; Or ), M) :-
    dcg_body(GREither, S0, S, Either, M),
    dcg_body(GROr, S0, S, Or, M).
dcg_cbody({Goal}, S0, S, ( Goal1, S0 = S ), M) :-
    module_call_qualified(M, Goal, Goal1).
dcg_cbody(call(Cont), S0, S, call(Cont1, S0, S), M) :-
    module_call_qualified(M, Cont, Cont1).
dcg_cbody(phrase(Body), S0, S, phrase(Body1, S0, S), M) :-
    module_call_qualified(M, Body, Body1).
dcg_cbody(!, S0, S, ( !, S0 = S ), _M).
dcg_cbody(\+ GRBody, S0, S, ( \+ phrase(GRBody1,S0,_), S0 = S ), M) :-
    module_call_qualified(M, GRBody, GRBody1).
dcg_cbody(( GRIf -> GRThen ), S0, S, ( If -> Then ), M) :-
    dcg_body(GRIf, S0, S1, If, M),
    dcg_body(GRThen, S1, S, Then, M).

user:term_expansion(Term0, Term) :-
    nonvar(Term0),
    dcg_rule(Term0, Term).

% Describes a sequence
seq([]) --> [].
seq([E|Es]) --> [E], seq(Es).

% Describes a sequence of sequences
seqq([]) --> [].
seqq([Es|Ess]) --> seq(Es), seqq(Ess).

% Describes an arbitrary number of elements
... --> [] | [_], ... .


error_goal(error(E, must_be/2), error(E, must_be/2)).
error_goal(error(E, (=..)/2), error(E, (=..)/2)).
error_goal(E, _) :- throw(E).

user:goal_expansion(phrase(GRBody, S, S0), GRBody1) :-
    load_context(GRBody, M, GRBody0),
    nonvar(GRBody0),
    catch(dcgs:dcg_body(GRBody0, S, S0, GRBody1, M),
          E,
          dcgs:error_goal(E, GRBody1)
         ).

user:goal_expansion(phrase(GRBody, S), phrase(GRBody, S, [])).
