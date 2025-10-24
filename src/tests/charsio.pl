:- module(charsio_tests, []).
:- use_module(library(lists)).
:- use_module(library(charsio)).

:- use_module(test_framework).



test("can create string char stream",
        (   chars_stream(Stream),
            put_char(Stream, a),
            get_char(Stream, C),
            C=a
        )).


test("can spell simple word with char stream",
     (
      chars_stream(Stream),
      put_char(Stream, c),
      put_char(Stream, a),
      put_char(Stream, t),
      get_n_chars(Stream, 3, Chars),
      Chars=[c,a,t]
     )).

test("can read from and write to char stream",
     (
      chars_stream(Stream),
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
      chars_to_stream(Phrase, Stream),
      get_n_chars(Stream, N, Chars),
      Phrase=Chars
     )
    ).

test("can convert string to char stream with options",
     (
      Phrase="can convert string to char stream",
      length(Phrase, N),
      chars_to_stream(Phrase, Stream, []),
      get_n_chars(Stream, N, Chars),
      Phrase=Chars
     )).


test("can read/write bytes",
     (
      A=97,
      B=98,
      C=99,
      chars_to_stream([A,B,C], Stream, [type(binary)]),
      get_byte(Stream, A),
      get_byte(Stream, B),
      get_byte(Stream, C),
      put_byte(Stream, A),
      put_byte(Stream, B),
      put_byte(Stream, C),
      get_byte(Stream, A),
      get_byte(Stream, B),
      get_byte(Stream, C)
      )).

test("can convert Unicode chars to UTF-8 bytes",
     (
      chars_to_stream("💜", Stream, [type(binary)]),
      get_byte(Stream, B1),
      get_byte(Stream, B2),
      get_byte(Stream, B3),
      get_byte(Stream, B4),
      B1 = 240,
      B2 = 159,
      B3 = 146,
      B4 = 156
      )).

test("can convert mixed ASCII and Unicode to UTF-8 bytes",
     (
      chars_to_stream("a💜b", Stream, [type(binary)]),
      get_byte(Stream, 97),
      get_byte(Stream, 240),
      get_byte(Stream, 159),
      get_byte(Stream, 146),
      get_byte(Stream, 156),
      get_byte(Stream, 98)
      )).


% ?- test_framework:main(charsio_tests). 

