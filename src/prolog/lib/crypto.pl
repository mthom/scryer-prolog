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

:- module(crypto, [hex_bytes/2,
                   crypto_n_random_bytes/2,
                   crypto_data_hash/3
                   ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(dcgs)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   hex_bytes(?Hex, ?Bytes) is det.

   Relation between a hexadecimal sequence and a list of bytes. Hex
   is a string of hexadecimal numbers. Bytes is a list of *integers*
   between 0 and 255 that represent the sequence as a list of bytes.
   At least one of the arguments must be instantiated.

   Example:

   ?- hex_bytes("501ACE", Bs).
      Bs = [80,26,206]
   ;  false.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


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
            must_be_bytes(Bytes, hex_bytes/2),
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


must_be_bytes(Bytes, Context) :-
        (   member(B, Bytes), \+ between(0, 255, B) ->
            type_error(byte, B, Context)
        ;   true
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_n_random_bytes(+N, -Bytes) is det

   Bytes is unified with a list of N cryptographically secure
   pseudo-random bytes. Each byte is an integer between 0 and 255. If
   the internal pseudo-random number generator (PRNG) has not been
   seeded with enough entropy to ensure an unpredictable byte
   sequence, an exception is thrown.

   One way to relate such a list of bytes to an _integer_ is to use
   CLP(ℤ) constraints as follows:

   :- use_module(library(clpz)).
   :- use_module(library(lists)).

   bytes_integer(Bs, N) :-
           foldl(pow, Bs, 0-0, N-_).

   pow(B, N0-I0, N-I) :-
           B in 0..255,
           N #= N0 + B*256^I0,
           I #= I0 + 1.

   With this definition, we can generate a random 256-bit integer
   _from_ a list of 32 random _bytes_:

   ?- crypto_n_random_bytes(32, Bs),
      bytes_integer(Bs, I).
      Bs = [146,166,162,210,242,7,25,132,64,94|...],
      I = 337420085690608915485...(56 digits omitted)

   The above relation also works in the other direction, letting you
   translate an integer _to_ a list of bytes. In addition, you can
   use hex_bytes/2 to convert bytes to _tokens_ that can be easily
   exchanged in your applications.

   ?- crypto_n_random_bytes(12, Bs),
      hex_bytes(Hex, Bs).
      Bs = [34,25,50,72,58,63,50,172,32,46|...], Hex = "221932483a3f32ac202 ..."
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


crypto_n_random_bytes(N, Bs) :-
        must_be(integer, N),
        length(Bs, N),
        maplist(crypto_random_byte, Bs).

crypto_random_byte(B) :- '$crypto_random_byte'(B).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_data_hash(+Data, -Hash, +Options)

   Where Data is a list of bytes (integers between 0 and 255),
   and Hash is the computed hash as a list of hexadecimal characters.

   The single supported option is:

      algorithm(A)

   where A is one of ripemd160, sha256, sha384, sha512, sha512_256,
   or a variable.

   If A is a variable, then it is unified with the default algorithm,
   which is an algorithm that is considered cryptographically secure
   at the time of this writing.

   Example:

   ?- crypto_data_hash([0'a,0'b,0'c], Hs, [algorithm(sha256)]).
      Hs = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
   ;  false.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_hash(Data, Hash, Options) :-
        must_be(list, Data),
        must_be_bytes(Data, crypto_data_hash/3),
        must_be(list, Options),
        (   Options = [algorithm(A)] -> true
        ;   true
        ),
        (   var(A) -> A = sha256
        ;   true
        ),
        (   hash_algorithm(A) -> true
        ;   domain_error(hash_algorithm, A, crypto_data_hash/3)
        ),
        '$crypto_data_hash'(Data, HashBytes, A),
        hex_bytes(Hash, HashBytes).

hash_algorithm(ripemd160).
hash_algorithm(sha256).
hash_algorithm(sha512).
hash_algorithm(sha384).
hash_algorithm(sha512_256).
