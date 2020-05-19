:- module(pio, [phrase_from_file/2,
                phrase_from_file/3]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(lists), [member/2]).

phrase_from_file(NT, File) :-
    phrase_from_file(NT, File, []).

phrase_from_file(NT, File, Options) :-
    (   var(File) -> instantiation_error(phrase_from_file/3)
    ;   (\+ atom(File) ; File = []) ->
            domain_error(source_sink, File, phrase_from_file/3)
    ;   must_be(list, Options),
        (   member(Var, Options), var(Var) -> instantiation_error(phrase_from_file/3)
        ;   member(type(Type), Options) ->
            must_be(atom, Type),
            member(Type, [text,binary])
        ;   Type = text
        ),
        '$file_to_chars'(File, Chars, Type),
        phrase(NT, Chars)
    ).
