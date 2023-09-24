/** Pure I/O.

   Our goal is to encourage the use of definite clause grammars (DCGs)
   for describing strings. The predicates `phrase_from_file/[2,3]`,
   `phrase_to_file/[2,3]` and `phrase_to_stream/2` let us apply DCGs
   transparently to files and streams, and therefore decouple side-effects
   from declarative descriptions.
*/

:- module(pio, [phrase_from_file/2,
                phrase_from_file/3,
                phrase_from_stream/2,
                phrase_to_file/2,
                phrase_to_file/3,
                phrase_to_stream/2
               ]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(freeze)).
:- use_module(library(gensym)).
:- use_module(library(iso_ext), [
    bb_get/2, bb_put/2, setup_call_cleanup/3, partial_string/3, partial_string_tail/2
]).
:- use_module(library(lists), [length/2, member/2, maplist/2]).
:- use_module(library(charsio), [get_n_chars/3]).

:- meta_predicate(phrase_from_file(2, ?)).
:- meta_predicate(phrase_from_file(2, ?, ?)).
:- meta_predicate(phrase_from_stream(2, ?)).
:- meta_predicate(phrase_to_file(2, ?)).
:- meta_predicate(phrase_to_file(2, ?, ?)).
:- meta_predicate(phrase_to_stream(2, ?)).


%% phrase_from_stream(+GRBody, +Stream)
%
%  True if grammar rule body GRBody covers the contents of the stream,
%  represented as a list of characters.

phrase_from_stream(GRBody, Stream) :-
    stream_to_lazy_list(Stream, Ls),
    phrase(GRBody, Ls).

%% phrase_from_file(+GRBody, +File)
%
%  True if grammar rule body GRBody covers the contents of File,
%  represented as a list of characters.

phrase_from_file(NT, File) :-
    phrase_from_file(NT, File, []).

%% phrase_from_file(+GRBody, +File, +Options)
%
%  Like `phrase_from_file/2`, using Options to open the file.

phrase_from_file(NT, File, Options) :-
    (   var(File) -> instantiation_error(phrase_from_file/3)
    ;   must_be(list, Options),
        (   member(Var, Options), var(Var) -> instantiation_error(phrase_from_file/3)
        ;   member(type(Type), Options) ->
            must_be(atom, Type),
            member(Type, [text,binary])
        ;   Type = text
        ),
        setup_call_cleanup(open(File, read, Stream, [reposition(true)|Options]),
                           phrase_from_stream(NT, Stream),
                           close(Stream))
    ).

% How many chars to read from stream and buffer in each step
chars_to_read(4096).

stream_to_lazy_list(Stream, Xs) :-
    stream_property(Stream, reposition(Rep)),
    (   Rep = true ->
        stream_to_lazy_list_repositionable(Stream, Xs)
    ;   stream_to_lazy_list_buffer(Stream, Xs)
    ).

stream_to_lazy_list_repositionable(Stream, Xs) :-
    stream_property(Stream, position(Pos)),
    freeze(Xs, reader_step_repositionable(Stream, Pos, Xs)).

reader_step_repositionable(Stream, Pos, Xs0) :-
    set_stream_position(Stream, Pos),
    (   at_end_of_stream(Stream)
    ->  Xs0 = []
    ;   chars_to_read(CharsToRead),
        get_n_chars(Stream, CharsToRead, Cs),
        partial_string(Cs, Xs0, Xs),
        stream_to_lazy_list_repositionable(Stream, Xs)
    ).

stream_to_lazy_list_buffer(Stream, Ls) :-
    get_stream_buffer_position(Stream, Pos),
    freeze(Ls, render_step_buffer(Stream, Pos, Ls)).

render_step_buffer(Stream, Pos, Ls) :-
    set_stream_buffer_position(Stream, Pos),
    (   buffer_at_end_of_stream(Stream) ->
        Ls = []
    ;   chars_to_read(CharsToRead),
        buffer_get_n_chars(Stream, CharsToRead, Chars),
        partial_string(Chars, Ls, Ls0),
        stream_to_lazy_list_buffer(Stream, Ls0)
    ).

buffer_at_end_of_stream(Stream) :-
    stream_bufferids(Stream, _, BufferPosId, _),
    bb_get(BufferPosId, Pos),
    Pos = eof.

get_stream_buffer_position(Stream, Pos) :-
    stream_bufferids(Stream, _, BufferPosId, _),
    bb_get(BufferPosId, Pos).

set_stream_buffer_position(Stream, Pos) :-
    stream_bufferids(Stream, _, BufferPosId, _),
    bb_put(BufferPosId, Pos).

buffer_get_n_chars(Stream, N, Chars) :-
    stream_bufferids(Stream, BufferId, BufferPosId, BufferLenId),
    buffer_prepare_for_n(Stream, BufferId, BufferPosId, BufferLenId, N),
    bb_get(BufferId, Buffer),
    bb_get(BufferPosId, BufferPos),
    (   BufferPos = eof ->
        Chars = []
    ;   string_get_n_chars(Buffer, BufferPos, N, Chars),
        length(Chars, NChars),
        (   NChars = 0 ->
            BufferPos1 = eof
        ;   BufferPos1 is BufferPos + NChars
        ),
        bb_put(BufferPosId, BufferPos1)
    ).

buffer_prepare_for_n(Stream, BufferId, BufferPosId, BufferLenId, N) :-
    bb_get(BufferPosId, BufferPos),
    bb_get(BufferLenId, BufferLen),
    (   BufferLen < BufferPos + N ->
        bb_get(BufferId, Buffer),
        (
            (   var(Buffer) ->
                BufferTail = Buffer
            ;   partial_string_last_tail(Buffer, BufferTail)
            ) ->
            (   at_end_of_stream(Stream) ->
                BufferTail = [],
                bb_put(BufferId, Buffer)
            ;   chars_to_read(CharsToRead),
                get_n_chars(Stream, CharsToRead, Chars),
                length(Chars, NChars),
                partial_string(Chars, BufferTail, _),
                bb_put(BufferId, Buffer),
                BufferLen1 is BufferLen + NChars,
                bb_put(BufferLenId, BufferLen1),
                buffer_prepare_for_n(Stream, BufferId, BufferPosId, BufferLenId, N)
            )
        ;   true
        )
    ;   true
    ).

partial_string_last_tail(PartialString, PartialStringTail) :-
    partial_string_tail(PartialString, PartialStringTail0),
    (   var(PartialStringTail0) ->
        PartialStringTail = PartialStringTail0
    ;   partial_string_last_tail(PartialStringTail0, PartialStringTail)
    ).

string_get_n_chars(String, Pos, N, Chars) :-
    '$skip_max_list'(_, Pos, String, String1),
    string_get_n_chars_(String1, N, Chars).

string_get_n_chars_([], _, []).
string_get_n_chars_([S|Ss], N, Chars) :-
    (   N = 0 ->
        Chars = []
    ;   N = 1 ->
        % This case is needed to not break the tail of the partial string
        Chars = [S]
    ;   Chars = [S|Cs],
        N1 is N - 1,
        string_get_n_chars_(Ss, N1, Cs)
    ).

stream_bufferids(Stream, BufferId, BufferPosId, BufferLenId) :-
    (   bb_get(streams_buffers, _) ->
        true
    ;   bb_put(streams_buffers, [])
    ),
    bb_get(streams_buffers, StreamsBuffers),
    (   member(
            stream_buffer(Stream, BufferId, BufferPosId, BufferLenId),
            StreamsBuffers
        ) ->
        true
    ;   gensym(buffer, BufferId),
        gensym(buffer_pos, BufferPosId),
        gensym(buffer_len, BufferLenId),
        bb_put(
            streams_buffers,
            [stream_buffer(Stream, BufferId, BufferPosId, BufferLenId)|StreamsBuffers]
        ),
        bb_put(BufferId, _),
        bb_put(BufferPosId, 0),
        bb_put(BufferLenId, 0)
    ).

%% phrase_to_stream(+GRBody, +Stream)
%
%  Emit the list of characters described by the grammar rule body
%  GRBody to Stream.
%
%  An ideal implementation of `phrase_to_stream/2` writes each
%  character as soon as it becomes known and no choice-points remain,
%  and thus avoids the manifestation of the entire string in memory.
%  See [#691](https://github.com/mthom/scryer-prolog/issues/691) for
%  more information.
%
%  The current preliminary implementation is provided so that Prolog
%  programmers can already get used to describing output with DCGs,
%  and then writing it to a file when necessary. This simple
%  implementation suffices as long as the entire contents can be
%  represented in memory, and thus covers a large number of use cases.

phrase_to_stream(GRBody, Stream) :-
        phrase(GRBody, Cs),
        must_be(chars, Cs),
        (   stream_property(Stream, type(binary)) ->
            (   '$first_non_octet'(Cs, N) ->
                domain_error(octet_character, N, phrase_to_stream/2)
            ;   true
            )
        ;   true
        ),
        % we use a specialised internal predicate that uses only a
        % single "write" operation for efficiency. It is equivalent to
        % maplist(put_char(Stream), Cs). It also works for binary streams.
        '$put_chars'(Stream, Cs).

%% phrase_to_file(+GRBody, +File)
%
%  Write the string described by GRBody to File.

phrase_to_file(GRBody, File) :-
        phrase_to_file(GRBody, File, []).


%% phrase_to_file(+GRBody, +File, +Options)
%
%  Like `phrase_to_file/2`, using Options to open the file.

phrase_to_file(GRBody, File, Options) :-
        setup_call_cleanup(open(File, write, Stream, Options),
                           phrase_to_stream(GRBody, Stream),
                           close(Stream)).
