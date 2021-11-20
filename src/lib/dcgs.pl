:- module(dcgs,
          [op(1105, xfy, '|'),
           phrase/2,
           phrase/3,
           seq//1,
           seqq//1,
           ... //0
          ]).

:- use_module(library(error)).
:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(loader), [strip_module/3]).

load_context(GRBody, Module, GRBody0) :-
    strip_module(GRBody, Module, GRBody0),
    (  nonvar(Module) ->
       true
    ;  prolog_load_context(module, Module) ->
       true
    ;  true
    ).

:- meta_predicate phrase(2, ?).

:- meta_predicate phrase(2, ?, ?).

phrase(GRBody, S0) :-
    phrase(GRBody, S0, []).

phrase(GRBody, S0, S) :-
    (  var(GRBody) ->
       throw(error(instantiation_error, phrase/3))
    ;  load_context(GRBody, Module, GRBody0),
       dcg_constr(GRBody0) ->
       (  var(Module) ->
          phrase_(GRBody0, S0, S)
       ;  phrase_(GRBody0, S0, S, Module)
       )
    ;  functor(GRBody, _, _) ->
       call(GRBody, S0, S)
    ;  throw(error(type_error(callable, GRBody), phrase/3))
    ).

phrase_([], S, S, _).
phrase_(!, S, S, _).
phrase_((A, B), S0, S, M) :-
    phrase(M:A, S0, S1),
    phrase(M:B, S1, S).
phrase_((A -> B ; C), S0, S, M) :-
    (  phrase(M:A, S0, S1) ->
       phrase(M:B, S1, S)
    ;  phrase(M:C, S0, S)
    ).
phrase_((A ; B), S0, S, M) :-
    (  phrase(M:A, S0, S)
    ;  phrase(M:B, S0, S)
    ).
phrase_((A | B), S0, S, M) :-
    (  phrase(M:A, S0, S)
    ;  phrase(M:B, S0, S)
    ).
phrase_({G}, S, S, M) :-
    call(M:G).
phrase_(call(G), S0, S, M) :-
    call(M:G, S0, S).
phrase_((A -> B), S0, S, M) :-
    (  phrase(M:A, S0, S1) ->
       phrase(M:B, S1, S)
    ;  fail
    ).
phrase_(phrase(NonTerminal), S0, S, M) :-
    phrase(NonTerminal, S0, S, M).
phrase_([T|Ts], S0, S, _) :-
    append([T|Ts], S, S0).

phrase_([], S, S).
phrase_(!, S, S).
phrase_(M:G, S0, S) :-
    phrase_(G, S0, S, M).
phrase_((A, B), S0, S) :-
    phrase(A, S0, S1),
    phrase(B, S1, S).
phrase_((A -> B ; C), S0, S) :-
    (  phrase(A, S0, S1) ->
       phrase(B, S1, S)
    ;  phrase(C, S0, S)
    ).
phrase_((A ; B), S0, S) :-
    (  phrase(A, S0, S) ; phrase(B, S0, S)  ).
phrase_((A | B), S0, S) :-
    (  phrase(A, S0, S) ; phrase(B, S0, S)  ).
phrase_({G}, S0, S) :-
    (  call(G), S0 = S  ).
phrase_(call(G), S0, S) :-
    call(G, S0, S).
phrase_((A -> B), S0, S) :-
    phrase((A -> B ; fail), S0, S).
phrase_(phrase(NonTerminal), S0, S) :-
    phrase(NonTerminal, S0, S).
phrase_([T|Ts], S0, S) :-
    append([T|Ts], S, S0).

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
    Goal =.. GoalUniv.

dcg_terminals(Terminals, S0, S, S0 = List) :-
    append(Terminals, S, List).

dcg_body(Var, S0, S, Body) :-
    var(Var),
    Body = phrase(Var, S0, S).
dcg_body(GRBody, S0, S, Body) :-
    nonvar(GRBody),
    dcg_constr(GRBody),
    dcg_cbody(GRBody, S0, S, Body).
dcg_body(NonTerminal, S0, S, Goal) :-
    nonvar(NonTerminal),
    \+ dcg_constr(NonTerminal),
    NonTerminal \= ( _ -> _ ),
    NonTerminal \= ( \+ _ ),
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
dcg_cbody(!, S0, S, ( !, S0 = S )).
dcg_cbody(\+ GRBody, S0, S, ( \+ phrase(GRBody,S0,_), S0 = S )).
dcg_cbody(( GRIf -> GRThen ), S0, S, ( If -> Then )) :-
    dcg_body(GRIf, S0, S1, If),
    dcg_body(GRThen, S1, S, Then).

user:term_expansion(Term0, Term) :-
    nonvar(Term0),
    dcg_rule(Term0, (Head :- Body)),
    Term = (Head :- Body).

% Describes a sequence
seq([]) --> [].
seq([E|Es]) --> [E], seq(Es).

% Describes a sequence of sequences
seqq([]) --> [].
seqq([Es|Ess]) --> seq(Es), seqq(Ess).

% Describes an arbitrary number of elements
... --> [] | [_], ... .

user:goal_expansion(phrase(GRBody, S, S0), phrase(GRBody1, S, S0)) :-
    strip_module(GRBody, M, GRBody0),
    var(M),
    prolog_load_context(module, M),
    (  nonvar(GRBody0) ->
       GRBody0 \== [],
       dcg_constr(GRBody0),
       predicate_property(GRBody0, meta_predicate(_))
    ),
    GRBody1 = M:GRBody0.

user:goal_expansion(phrase(GRBody, S), phrase(GRBody1, S, [])) :-
    strip_module(GRBody, M, GRBody0),
    var(M),
    prolog_load_context(module, M),
    (  nonvar(GRBody0) ->
       GRBody0 \== [],
       dcg_constr(GRBody0),
       predicate_property(GRBody0, meta_predicate(_))
    ),
    GRBody1 = M:GRBody0.
