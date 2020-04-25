:- module(pio, [phrase_from_file/2]).

:- use_module(library(dcgs)).

phrase_from_file(NT, File) :-
    '$file_to_chars'(File, Chars),
    phrase(NT, Chars).
