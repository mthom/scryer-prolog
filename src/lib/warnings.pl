:- module(warnings, []).

:- use_module(library(lists)).
:- use_module(library(format)).

%% warnings:output(+OutputStream).
%
% If defined – use `OutputStream` (eg. user_output) instead of standard error
% for message output.
%
:- dynamic(output_stream/1).

output(OutputStream) :- output_stream(OutputStream), !.
output(user_error).

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
    warn("(~q) attempts to re-define ~w", [G, O/2]).

warn(Format, Vars) :-
    output(S),
    prolog_load_context(file, F),
    prolog_load_context(term_position, position_and_lines_read(_,L)),
    append(["% Warning: ", Format, " at line ~d of ~a~n"], FullFormat),
    append(Vars, [L,F], AllVars),
    format(S, FullFormat, AllVars),
    false.
