:- module(charsio_tests, []).
:- use_module(library(debug)).
:- use_module(library(lists)).
:- use_module(library(charsio)).

:- use_module(test_framework).



test("can create string char stream",
        (   char_stream(Stream),
            put_char(Stream, a),
            get_char(Stream, C),
            C=a
        )).


test("can spell simple word with char stream",
     (
      char_stream(Stream),
      put_char(Stream, c),
      put_char(Stream, a),
      put_char(Stream, t),
      get_n_chars(Stream, 3, Chars),
      Chars=[c,a,t]
     )).

test("can read from and write to char stream",
     (
      char_stream(Stream),
      put_char(Stream, c),
      put_char(Stream, a),
      get_char(Stream, _C),
      put_char(Stream, b),
      get_n_chars(Stream, 2, Chars),
      Chars=[a,b]
     )
    ).


test("can convert string to char stream",
     (
      Phrase="can convert string to char stream",
      length(Phrase, N),
      char_stream(Phrase, Stream),
      get_n_chars(Stream, N, Chars),
      Phrase=Chars
     )
    ).

test("can convert string to char stream with options",
     (
      Phrase="can convert string to char stream",
      length(Phrase, N),
      char_stream(Phrase, Stream, []),
      get_n_chars(Stream, N, Chars),
      Phrase=Chars
     )).
