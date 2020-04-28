:- module(pio, [phrase_from_file/2]).

:- use_module(library(dcgs)).
:- use_module(library(error)).

phrase_from_file(NT, File) :-
    (   var(File) -> instantiation_error(phrase_from_file/2)
    ;   (\+ atom(File) ; File = []) ->
            domain_error(source_sink, File, phrase_from_file/2)
    ;   '$file_to_chars'(File, Chars),
        phrase(NT, Chars)
    ).
