:- module(pio, [phrase_from_file/2]).

:- use_module(library(dcgs)).

phrase_from_file(NT, File) :-
    (   var(File) -> throw(error(instantiation_error, phrase_from_file/2))
    ;   (\+ atom(File) ; File = []) ->
            throw(error(domain_error(source_sink, File), phrase_from_file/2))
    ;   '$file_to_chars'(File, Chars),
        phrase(NT, Chars)
    ).
