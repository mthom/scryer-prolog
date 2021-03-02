/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predicates for parsing HTML and XML documents.
   Written June 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Currently, two predicates are provided:

   -  load_html(+Source, -Es, +Options)
   -  load_xml(+Source, -Es, +Options)

   These predicates parse HTML and XML documents, respectively.

   Source must be a stream, specified as stream(S), or a file,
   specified as file(Name), where Name is a list of characters, or a
   list of characters with the document contents.

   Es is unified with the abstract syntax tree of the parsed document,
   represented as a list of elements where each is of the form:

   * a list of characters, representing text
   * element(Name, Attrs, Children)
     - Name is the name of the tag
     - Attrs is a list of Key=Value pairs:
       Key is an atom, and Value is a list of characters
     - Children is a list of elements as specified here.

   Currently, Options are ignored. In the future, more options may be
   provided to control parsing.

   Example:

      ?- load_html("<html><head><title>Hello!</title></head></html>", Es, []).

   Yielding:

         Es = [element(html,[],
                [element(head,[],
                  [element(title,[],
                    ["Hello!"])]),
                 element(body,[],[])])].

   library(xpath) provides convenient reasoning about parsed documents.
   For example, to fetch the title of the document above, we can use:

      ?- load_html("<html><head><title>Hello!</title></head></html>", Es, []),
         xpath(Es, //title(text), T).

   Yielding T = "Hello!".

   Use http_open/3 from library(http/http_open) to read answers from
   web servers via streams.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(sgml, [load_html/3,
                 load_xml/3]).

:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).

load_html(Source, Es, Options) :-
        load_structure_(Source, Es, Options, html).
load_xml(Source, Es, Options) :-
        load_structure_(Source, Es, Options, xml).

list([]) --> [].
list([L|Ls]) --> [L], list(Ls).

load_structure_([], [], _, _).
load_structure_([C|Cs], [E], Options, What) :-
        load_(What, [C|Cs], E, Options).
load_structure_(file(Fs), [E], Options, What) :-
        must_be(list, Options),
        must_be(list, Fs),
        atom_chars(File, Fs),
        once(phrase_from_file(list(Cs), File)),
        load_(What, Cs, E, Options).
load_structure_(stream(Stream), [E], Options, What) :-
        must_be(list, Options),
        read_to_end(Stream, Cs),
        load_(What, Cs, E, Options).

load_(html, Cs, E, Options) :- '$load_html'(Cs, E, Options).
load_(xml, Cs, E, Options) :- '$load_xml'(Cs, E, Options).

read_to_end(Stream, Cs) :-
        '$get_n_chars'(Stream, 4096, Cs0),
        (   Cs0 = [] -> Cs = []
        ;   partial_string(Cs0, Cs, Rest),
            read_to_end(Stream, Rest)
        ).
