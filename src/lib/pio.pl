:- module(pio, [phrase_from_file/2,
                phrase_from_file/3]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(freeze)).
:- use_module(library(iso_ext), [setup_call_cleanup/3, partial_string/3]).
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
        setup_call_cleanup(open(File, read, Stream, [reposition(true)|Options]),
                           (   stream_to_lazy_list(Stream, Xs),
                               phrase(NT, Xs) ),
                           close(Stream))
   ).


stream_to_lazy_list(Stream, Xs) :-
        stream_property(Stream, position(Pos)),
        freeze(Xs, reader_step(Stream, Pos, Xs)).

reader_step(Stream, Pos, Xs0) :-
        set_stream_position(Stream, Pos),
        (   at_end_of_stream(Stream)
        ->  Xs0 = []
        ;   '$get_n_chars'(Stream, 4096, Cs),
            partial_string(Cs, Xs0, Xs),
            stream_to_lazy_list(Stream, Xs)
        ).
