:- use_module(library(charsio)).
:- use_module(library(lists)).

:- initialization(unit_test).

unit_test :-
  char_utf8bytes('a', Ls),
  write(Ls),
  char_utf8bytes('£', L2),
  write(L2),
  char_utf8bytes('\x2124\', Bs),
  write(Bs),
  Bs = [226,132,164].

write_f :-
  open('x.txt', write, Stream, [type(binary)]),
  F = put_byte(Stream),
  char_utf8bytes('£', B1),
  maplist(F, B1),
  char_utf8bytes('\x2124\', B2),
  maplist(F, B2),
  char_utf8bytes('\x2764\', B3),
  maplist(F, B3),
  char_utf8bytes('\x1F496\', Bs),
  maplist(F, Bs),
  char_utf8bytes('\n', Bsn),
  maplist(F, Bsn),
  close(Stream).
