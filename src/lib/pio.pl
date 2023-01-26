/** Pure I/O.

   Our goal is to encourage the use of definite clause grammars (DCGs)
   for describing strings. The predicates `phrase_from_file/[2,3]`,
   `phrase_to_file/[2,3]` and `phrase_to_stream/2` let us apply DCGs
   transparently to files and streams, and therefore decouple side-effects
   from declarative descriptions.
*/

:- module(pio, [phrase_from_file/2,
                phrase_from_file/3,
                phrase_to_file/2,
                phrase_to_file/3,
                phrase_to_stream/2
               ]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(freeze)).
:- use_module(library(iso_ext), [setup_call_cleanup/3, partial_string/3]).
:- use_module(library(lists), [member/2, maplist/2]).
:- use_module(library(charsio), [get_n_chars/3]).

:- meta_predicate(phrase_from_file(2, ?)).
:- meta_predicate(phrase_from_file(2, ?, ?)).
:- meta_predicate(phrase_to_file(2, ?)).
:- meta_predicate(phrase_to_file(2, ?, ?)).
:- meta_predicate(phrase_to_stream(2, ?)).

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
        ;   get_n_chars(Stream, 4096, Cs),
            partial_string(Cs, Xs0, Xs),
            stream_to_lazy_list(Stream, Xs)
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
