/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predicates for parsing markup documents.
   Written June 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Currently, only a single predicate is provided:

   load_html(+In, -Es, +Options)
   =============================

   In must be a stream, specified as stream(S), and Es is unified with
   a list of elements of the form:

   * a list of characters, representing text

   * element(Name, Attrs, Children)
     - Name is the name of the tag
     - Attrs is a list of Key=Value pairs:
       Key is an atom, and Value is a list of characters
     - Children is a list of elements as specified here.

   Currently, Options are ignored. In the future, more options may be
   provided to control parsing.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(sgml, [load_html/3]).

:- use_module(library(iso_ext)).
:- use_module(library(error)).

load_html(stream(Stream), [E], Options) :-
        must_be(list, Options),
        read_to_end(Stream, Cs),
        '$load_html'(Cs, E, []).

read_to_end(Stream, Cs) :-
        '$get_n_chars'(Stream, 4096, Cs0),
        (   Cs0 = [] -> Cs = []
        ;   partial_string(Cs0, Cs, Rest),
            read_to_end(Stream, Rest)
        ).
