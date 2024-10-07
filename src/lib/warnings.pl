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

% Warn about builtin predicates re-definition. It can happen by mistake for
% example:
%     x :- a. b, c.
%
user:term_expansion(G, _) :-
    nonvar(G),
    builtin(G),
    functor(G, O, 2),
    warn_fail("(~q) attempts to re-define ~w", [G, O/2]).
