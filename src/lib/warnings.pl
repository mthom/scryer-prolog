:- module(warnings, []).

:- use_module(library(format)).
:- use_module(library(pio)).

warn_fail(Format, Vars) :-
    warn_fail(user_error, Format, Vars).
warn_fail(Stream, Format, Vars) :-
    prolog_load_context(file, File),
    prolog_load_context(term_position, position_and_lines_read(_,Line)),
    phrase_to_stream(
        (
            "% Warning: ", format_(Format,Vars), format_(" at line ~d of ~a~n",[Line,File])
        ),
        Stream
    ),
    false.

% FIXME: Replace with predicate_property(_, built_in) when #2600 will be ready
builtin((_;_)).
builtin((_,_)).
builtin((_->_)).

unsound_type_test(atom(_)).
unsound_type_test(atomic(_)).
unsound_type_test(integer(_)).

% Warn about builtin predicates re-definition. It can happen by mistake for
% example:
%     x :- a. b, c.
%
user:term_expansion(G, _) :-
    nonvar(G),
    builtin(G),
    functor(G, F, 2),
    warn_fail("(~q) attempts to re-define ~w", [G, F/2]).

% Warn about unsound type test predicates and suggest using library(si).
% Observe that following queries yield different results:
%
%     ?- X=1, integer(X).
%        true.
%     ?- integer(X), X=1.
%        false.
%
user:goal_expansion(G, _) :-
    nonvar(G),
    unsound_type_test(G),
    functor(G, F, 1),
    warn_fail("~q is a constant source of bugs, use ~a_si/1 from library(si)", [F/1,F]).

% Warn when more than 2 negations are nested. Double negation has legit
% use-case, but I don't think that more nested negations are ever useful.
%
user:goal_expansion(G, _) :-
    nonvar(G),
    G = (\+ \+ \+ _),
    warn_fail("Nested negations can be reduced", []).
