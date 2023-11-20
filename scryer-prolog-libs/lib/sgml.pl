/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predicates for parsing HTML and XML documents.
   Written 2020-2022 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/** Predicates for parsing HTML and XML documents.

Currently, two predicates are provided:

  -  `load_html(+Source, -Es, +Options)`
  -  `load_xml(+Source, -Es, +Options)`

These predicates parse HTML and XML documents, respectively.

Source must be one of:

  - a list of characters with the document contents
  - `stream(S)`, specifying a stream S from which to read the content
  - `file(Name)`, where Name is a list of characters specifying a file name.

Es is unified with the abstract syntax tree of the parsed document,
represented as a list of elements where each is of the form:

  * a list of characters, representing text

  * `element(Name, Attrs, Children)`

    - `Name`, an atom, is the name of the tag

    - `Attrs` is a list of `Key=Value` pairs:
      `Key` is an atom, and `Value` is a list of characters

    - `Children` is a list of elements as specified here.

Currently, Options are ignored. In the future, more options may be
provided to control parsing.

Example:

```
   ?- load_html("<html><head><title>Hello!</title></head></html>", Es, []).
```

Yielding:

```
      Es = [element(html,[],
             [element(head,[],
               [element(title,[],
                 ["Hello!"])]),
              element(body,[],[])])].
```

`library(xpath)` provides convenient reasoning about parsed documents.
For example, to fetch the title of the document above, we can use:

```
   ?- load_html("<html><head><title>Hello!</title></head></html>", Es, []),
      xpath(Es, //title(text), T).
```

Yielding `T = "Hello!"`.

Use `http_open/3` from `library(http/http_open)` to read answers from
web servers via streams.
*/

:- module(sgml, [load_html/3,
                 load_xml/3]).

:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(charsio)).

load_html(Source, Es, Options) :-
        must_be_source(Source, load_html/3),
        must_be(list, Options),
        load_structure_(Source, Es, Options, html).
load_xml(Source, Es, Options) :-
        must_be_source(Source, load_xml/3),
        must_be(list, Options),
        load_structure_(Source, Es, Options, xml).

must_be_source(Source, Context) :-
        (   var(Source) -> instantiation_error(Context)
        ;   is_sgml_source(Source) -> true
        ;   domain_error(sgml_source, Source, Context)
        ).

is_sgml_source(file(Fs)) :- must_be(chars, Fs).
is_sgml_source(stream(_)).
is_sgml_source([]).
is_sgml_source([C|Cs]) :- must_be(chars, [C|Cs]).

load_structure_([], [], _, _).
load_structure_([C|Cs], [E], Options, What) :-
        load_(What, [C|Cs], E, Options).
load_structure_(file(Fs), [E], Options, What) :-
        once(phrase_from_file(seq(Cs), Fs)),
        load_(What, Cs, E, Options).
load_structure_(stream(Stream), [E], Options, What) :-
        get_n_chars(Stream, _, Cs),
        load_(What, Cs, E, Options).

load_(html, Cs, E, Options) :- '$load_html'(Cs, E, Options).
load_(xml, Cs, E, Options) :- '$load_xml'(Cs, E, Options).
