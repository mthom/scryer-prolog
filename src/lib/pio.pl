:- module(pio, [phrase_from_file/2,
                phrase_from_file/3,
                phrase_to_file/2]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(freeze)).
:- use_module(library(iso_ext), [setup_call_cleanup/3, partial_string/3]).
:- use_module(library(lists), [member/2, maplist/2]).
:- use_module(library(format), [format/3]).

:- meta_predicate(phrase_from_file(2, ?)).
:- meta_predicate(phrase_from_file(2, ?, ?)).
:- meta_predicate(phrase_to_file(2, ?)).

phrase_from_file(NT, File) :-
    phrase_from_file(NT, File, []).

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
        ;   '$get_n_chars'(Stream, 4096, Cs),
            partial_string(Cs, Xs0, Xs),
            stream_to_lazy_list(Stream, Xs)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   phrase_to_file(+GRBody, +File)

   Emit the list of characters described by the grammar rule body
   GRBody to File. File is a string, which is also the representation
   used by library(files) to test for existence etc. of files.

   An ideal implementation of phrase_to_file/2 writes each character
   as soon as it becomes known and no choice-points remain, and thus
   avoids the manifestation of the entire string in memory. See #691
   for more information.

   The current preliminary implementation is provided so that Prolog
   programmers can already get used to describing output with DCGs,
   and then writing it to a file when necessary. This simple
   implementation suffices as long as the entire contents can be
   represented in memory, and thus covers a large number of use cases.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

phrase_to_file(GRBody, File) :-
        atom_chars(Atom, File),
        phrase(GRBody, Chars),
        setup_call_cleanup(open(Atom, write, Stream),
                           format(Stream, "~s", [Chars]),
                           close(Stream)).
