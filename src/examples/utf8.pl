:- use_module(library(charsio)).
:- use_module(library(lists)).

:- initialization(unit_test).

unit_test :-
  chars_utf8bytes("a£\x2124\", Bs),
  Bs = [97, 194, 163, 226, 132, 164],
  chars_utf8bytes(Cs, Bs),
  Cs = "a£\x2124\".

write_f :-
  open('x.txt', write, Stream, [type(binary)]),
  F = put_byte(Stream),
  chars_utf8bytes("£\x2124\\x2764\\x1F496\\n", Bs),
  maplist(F, Bs),
  close(Stream).

get_bytes(Stream, Res) :- get_bytes(Stream, [], Res).
get_bytes(Stream, Acc, Res) :-
  get_byte(Stream, B),
  (B =:= -1 ->
    reverse(Acc, Res)
  ; get_bytes(Stream, [B|Acc], Res)).

read_f :-
  open('x.txt', read, Stream, [type(binary)]),
  get_bytes(Stream, Bs),
  chars_utf8bytes(Cs, Bs),
  write(Cs),
  close(Stream).
