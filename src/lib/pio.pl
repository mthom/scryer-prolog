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
                           (   stream_to_lazy_list(pio:Type, Stream, Xs),
                               phrase(NT, Xs) ),
                           close(Stream))
   ).


stream_to_lazy_list(Type_3, Stream, Xs) :-
        stream_property(Stream, position(Pos)),
        freeze(Xs, reader_step(Type_3, Stream, Pos, Xs)).

reader_step(Type_3, Stream, Pos, Xs0) :-
        set_stream_position(Stream, Pos),
        (   at_end_of_stream(Stream)
        ->  Xs0 = []
        ;   % phrase(call(call(Type_3,Stream)), Xs0,Xs), % conforming call
            call(Type_3, Stream, Cs,[]), % effective call
            partial_string(Cs, Xs0, Xs),
            stream_to_lazy_list(Type_3, Stream, Xs)
        ).

binary(Stream, Xs0, Xs) :- get_pending_bytes(Stream, Xs0, Xs).
text(Stream, Xs0, Xs)   :- get_pending_chars(Stream, Xs0, Xs).


get_pending_chars(Stream, Chs0,Chs) :-
        n_get_chars(4096, Stream, Chs, Chs0,Chs).

% EOF means: If EOF == [], then EOF has definitely been reached, otherwise
% it is unknown and the argument remains uninstantiated.

% To improve performance, the following predicates should be replaced
% by a fast Rust implementation that reads a number of characters (or
% bytes) at once.

% Files that do not contain 0-bytes can even be mmapped to memory.

n_get_chars(N0, Stream, EOF, Chs0,Chs) :-
        N0 > 0,
        N1 is N0-1,
        get_char(Stream, Ch),
        (   Ch == end_of_file
        ->  Chs0 = Chs,
            EOF = []
        ;   Chs0 = [Ch|Chs1],
            n_get_chars(N1, Stream, EOF, Chs1,Chs)
        ).
n_get_chars(0, _, _, Chs,Chs).


get_pending_bytes(Stream, Chs0,Chs) :-
        n_get_bytes(4096, Stream, Chs, Chs0,Chs).

n_get_bytes(N0, Stream, EOF, Chs0,Chs) :-
        N0 > 0,
        N1 is N0-1,
        get_byte(Stream, Byte),
        (   Byte == -1
        ->  Chs0 = Chs,
            EOF = []
        ;   char_code(Ch, Byte),
            Chs0 = [Ch|Chs1],
            n_get_bytes(N1, Stream, EOF, Chs1,Chs)
        ).
n_get_bytes(0, _, _, Chs,Chs).
