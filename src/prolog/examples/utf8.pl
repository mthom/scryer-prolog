:- use_module(library(charsio)).
:- use_module(library(lists)).

:- initialization(unit_test).

unit_test :-
  string_utf8bytes("a£\x2124\", Bs),
  Bs = [97, 194, 163, 226, 132, 164].

write_f :-
  open('x.txt', write, Stream, [type(binary)]),
  F = put_byte(Stream),
  string_utf8bytes("£\x2124\\x2764\\x1F496\\n", Bs),
  maplist(F, Bs),
  close(Stream).
