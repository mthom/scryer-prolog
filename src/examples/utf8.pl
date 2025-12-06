:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).

:- initialization(unit_test).

unit_test :-
  chars_utf8bytes("a£\x2124\", Bs),
  Bs = [97, 194, 163, 226, 132, 164],
  chars_utf8bytes(Cs, Bs),
  Cs = "a£\x2124\".

write_f :-
  chars_utf8bytes("£\x2124\\x2764\\x1F496\\n", Bs),
  maplist(char_code, Cs, Bs),
  phrase_to_file(Cs, "x.txt", [type(binary)]).

read_f :-
  phrase_from_file(seq(Cs), "x.txt", [type(binary)]),
  maplist(char_code, Cs, Bs),
  chars_utf8bytes(Chars, Bs),
  write(Chars).
