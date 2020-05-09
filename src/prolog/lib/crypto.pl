/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written May 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Predicates for cryptographic applications.

   This library assumes that the Prolog flag double_quotes is set to chars.
   In Scryer Prolog, lists of characters are very efficiently represented,
   and strings have the advantage that the atom table remains unmodified.

   Especially for cryptographic applications, it as an advantage that
   using strings leaves little trace of what was processed in the system,
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(crypto, [hex_bytes/2]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(dcgs)).

%   hex_bytes(?Hex, ?Bytes) is det.
%
%   Relation between a hexadecimal sequence and a list of bytes. Hex
%   is a string of hexadecimal numbers. Bytes is a list of *integers*
%   between 0 and 255 that represent the sequence as a list of bytes.
%   At least one of the arguments must be instantiated.
%
%   Example:
%
%   ==
%   ?- hex_bytes("501ACE", Bs).
%      Bs = [80,26,206]
%   ;  false.
%   ==

hex_bytes(Hs, Bytes) :-
        (   ground(Hs) ->
            must_be(list, Hs),
            maplist(must_be(atom), Hs),
            (   phrase(hex_bytes(Hs), Bytes) ->
                true
            ;   domain_error(hex_encoding, Hs, hex_bytes/2)
            )
        ;   must_be(list, Bytes),
            maplist(must_be(integer), Bytes),
            (   member(B, Bytes), \+ between(0, 255, B) ->
                type_error(byte, B, hex_bytes/2)
            ;   true
            ),
            phrase(bytes_hex(Bytes), Hs)
        ).

hex_bytes([]) --> [].
hex_bytes([H1,H2|Hs]) --> [Byte],
        { char_hexval(H1, High),
          char_hexval(H2, Low),
          Byte is High*16 + Low },
        hex_bytes(Hs).

bytes_hex([]) --> [].
bytes_hex([B|Bs]) --> [C0,C1],
        { High is B>>4,
          Low is B /\ 0xf,
          char_hexval(C0, High),
          char_hexval(C1, Low)
        },
        bytes_hex(Bs).

char_hexval(C, H) :- nth0(H, "0123456789abcdef", C), !.
char_hexval(C, H) :- nth0(H, "0123456789ABCDEF", C), !.

