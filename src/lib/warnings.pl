:- module(warnings, [
    warn/2,
    warn/3
]).

:- use_module(library(format)).
:- use_module(library(pio)).

%% warn(+Format, ?Vars).
%
% Same as warn/3 using default user_error stream.
warn(Format, Vars) :-
    warn(user_error, Format, Vars).


%% warn(+Stream, +Format, ?Vars).
%
% Print a warning message to Stream. Predicate is provided for uniformity of
% warning messages throughout the codebase.
warn(Stream, Format, Vars) :-
    prolog_load_context(file, File),
    prolog_load_context(term_position, position_and_lines_read(_,Line)),
    phrase_to_stream(
        (
            "% Warning: ", format_(Format,Vars), format_(" at line ~d of ~a~n",[Line,File])
        ),
        Stream
    ).
