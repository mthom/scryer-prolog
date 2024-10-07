:- module(warnings, []).

:- use_module(library(format)).
:- use_module(library(pio)).

warn(Format, Vars) :-
    warn(user_error, Format, Vars).
warn(Stream, Format, Vars) :-
    prolog_load_context(file, File),
    prolog_load_context(term_position, position_and_lines_read(_,Line)),
    phrase_to_stream(
        (
            "% Warning: ", format_(Format,Vars), format_(" at line ~d of ~a~n",[Line,File])
        ),
        Stream
    ).

% FIXME: Replace with predicate_property(_, built_in) when #2600 will be ready
builtin((_;_)).
builtin((_,_)).
builtin((_->_)).
builtin(\+_).

unsound_type_test(atom(_)).
unsound_type_test(atomic(_)).
unsound_type_test(integer(_)).

% Warn about builtin predicates re-definition. It can happen by mistake for
% example:
%     x :- a. b, c.
%
term_warning(term, Term, "(~q) attempts to re-define ~w", [Term,F/A]) :-
    builtin(Term),
    functor(Term, F, A).

% Warn about unsound type test predicates and suggest using library(si).
% Observe that following queries yield different results:
%
%     ?- X=1, integer(X).
%        true.
%     ?- integer(X), X=1.
%        false.
%
term_warning(goal, Term, "~q is a constant source of wrong results, use ~a_si/1 from library(si)", [F/1,F]) :-
    unsound_type_test(Term),
    functor(Term, F, 1).

% Warn when more than 2 negations are nested. Double negation has legit
% use-case, but I don't think that more nested negations are ever useful.
%
term_warning(goal, \+ \+ \+_, "Nested negations can be reduced", []).

expansion_warning(ExpansionKind, Term) :-
    nonvar(Term),
    term_warning(ExpansionKind, Term, Msg, Vars),
    warn(Msg, Vars),
    false.

user:term_expansion(Term, _) :-
    expansion_warning(term, Term).

user:goal_expansion(Term, _) :-
    expansion_warning(goal, Term).
