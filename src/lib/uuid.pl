/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written in February 2021 by Adrián Arroyo (adrian.arroyocalle@gmail.com)
   Part of Scryer-Prolog
   I place this code in the public domain. Use it in any way you want.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/**
This library provides reasoning and working with [UUID](https://en.wikipedia.org/wiki/Universally_unique_identifier)
(only version 4 right now).

There are three predicates:

 * `uuidv4/1`, to generate a new UUIDv4
 * `uuidv4_string/1`, to generate a new UUIDv4 in string hex representation
 * `uuid_string/2`, to converte between UUID list of bytes and UUID hex representation

Examples:

```
?- uuidv4(X).
   X = [42,147,248,242,117,196,79,2,129,159|...].
?- uuidv4_string(X).
   X = "428499fc-76e3-4240- ...".
?- uuidv4(X), uuid_string(X, S).
   X = [173,12,244,152,139,118,64,139,137,4|...], S = "ad0cf498-8b76-408b- ...".
?- uuid_string(X, "61ae692e-eaf6-4199-8dd3-9f01db70a20b").
   X = [97,174,105,46,234,246,65,153,141,211|...].
*/

:- module(uuid, [
    uuidv4/1,
    uuidv4_string/1,
    uuid_string/2
]).

:- use_module(library(crypto)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).

/*
An UUID is made of 16 bytes, composed of 5 sections:
time_low - 4
time_mid - 2
time_hi_and_version - 2
clock_seq_hi_and_res_clock_seq_low - 2
node - 6
UUID v4 can be generated from a set of 16 random bytes: https://www.rfc-archive.org/getrfc.php?rfc=4122#gsc.tab=0 (section 4.4)
*/

%% uuidv4(-Uuid).
%
% Generates a new UUID v4 (random). It unifies with a list of bytes.
uuidv4(Uuid) :-
    crypto_n_random_bytes(16, Bytes),
    Bytes = [B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16],
    byte_bits(B9, BitsClockSeqHi0),
    BitsClockSeqHi0 = [_X7, _X6, X5, X4, X3, X2, X1, X0],
    NewBitsClockSeqHi0 = [1, 0, X5, X4, X3, X2, X1, X0],
    byte_bits(NewClockSeqHi0, NewBitsClockSeqHi0),
    byte_bits(B7, BitsTimeHi),
    BitsTimeHi = [_Y7, _Y6, _Y5, _Y4, Y3, Y2, Y1, Y0],
    NewBitsTimeHi = [0, 1, 0, 0, Y3, Y2, Y1, Y0],
    byte_bits(NewTimeHi, NewBitsTimeHi),
    Uuid = [B1, B2, B3, B4, B5, B6, NewTimeHi, B8, NewClockSeqHi0, B10, B11, B12, B13, B14, B15, B16].

%% uuidv4_string(-UuidString).
%
% Generates a new UUID v4 (random). It unifies with a string representation of the UUID.
% It is equivalent of calling `uuidv4/1` followed by `uuid_string/2`.
uuidv4_string(String) :- uuidv4(Uuid), uuid_string(Uuid, String).

%% uuid_string(?UuidBytes, ?UuidString).
%
% Translates between the bytes representation and the string representation of the same UUID.
uuid_string(Uuid, String) :-
    Uuid = [B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16],
    phrase(uuid_([S1, S2, S3, S4, S5]), String),
    hex_bytes(S1, [B1, B2, B3, B4]),
    hex_bytes(S2, [B5, B6]),
    hex_bytes(S3, [B7, B8]),
    hex_bytes(S4, [B9, B10]),
    hex_bytes(S5, [B11, B12, B13, B14, B15, B16]).

uuid_([S1, S2, S3, S4, S5]) -->
    {
        length(S1, 8),
        length(S2, 4),
        length(S3, 4),
        length(S4, 4),
        length(S5, 12)
    },
    S1,
    "-",
    S2,
    "-",
    S3,
    "-",
    S4,
    "-",
    S5.

byte_bits(Byte, Bits) :-
    \+ var(Byte),
    byte_bits_(Byte, Bits),
    length(Bits, 8),!.

byte_bits(Byte, Bits) :-
    \+ var(Bits),
    length(Bits, 8),
    byte_bits__(Byte, Bits),!.

byte_bits_(0, [0]).
byte_bits_(1, [1]).
byte_bits_(Byte, Bits) :-
    R is Byte // 2,
    M is Byte mod 2,
    byte_bits_(R, Bits0),
    append(Bits0, [M], Bits).

byte_bits__(0, []).
byte_bits__(Byte, Bits) :-
    length(Bits, N),
    Bits = [Bit|Bits0],
    byte_bits__(Byte0, Bits0),
    Byte is Byte0 + Bit*(2 ^ (N-1)).
