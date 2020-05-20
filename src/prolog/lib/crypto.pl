/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written May 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Predicates for cryptographic applications.

   This library assumes that the Prolog flag double_quotes is set to chars.
   In Scryer Prolog, lists of characters are very efficiently represented,
   and strings have the advantage that the atom table remains unmodified.

   Especially for cryptographic applications, it as an advantage that
   using strings leaves little trace of what was processed in the system.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(crypto,
          [hex_bytes/2,                % ?Hex, ?Bytes
           crypto_n_random_bytes/2,    % +N, -Bytes
           crypto_data_hash/3,         % +Data, -Hash, +Options
           crypto_data_hkdf/4,         % +Data, +Length, -Bytes, +Options
           crypto_password_hash/2,     % +Password, ?Hash
           crypto_password_hash/3,     % +Password, -Hash, +Options
           crypto_data_encrypt/6,      % +PlainText, +Algorithm, +Key, +IV, -CipherText, +Options
           crypto_data_decrypt/6,      % +CipherText, +Algorithm, +Key, +IV, -PlainText, +Options
           crypto_ed25519_sign/4,      % +Key, +Data, -Signature, +Options
           crypto_name_curve/2,        % +Name, -Curve
           crypto_curve_order/2,       % +Curve, -Order
           crypto_curve_generator/2,   % +Curve, -Generator
           crypto_curve_scalar_mult/4  % +Curve, +Scalar, +Point, -Result
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(dcgs)).
:- use_module(library(clpz)).
:- use_module(library(arithmetic)).
:- use_module(library(format)).
:- use_module(library(charsio)).

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
        ;   must_be_bytes(Bytes, hex_bytes/2),
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
        must_be(list, Bytes),
        maplist(must_be(integer), Bytes),
        (   member(B, Bytes), \+ between(0, 255, B) ->
            type_error(byte, B, Context)
        ;   true
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Cryptographically secure random numbers
   =======================================

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
   Hashing
   =======

   crypto_data_hash(+Data, -Hash, +Options)

   Where Data is a list of bytes (integers between 0 and 255) or
   characters, and Hash is the computed hash as a list of hexadecimal
   characters.

   Options is a list of:

     - algorithm(+A)
       where A is one of ripemd160, sha256, sha384, sha512, sha512_256,
       sha3_224, sha3_256, sha3_384, sha3_512, blake2s256, blake2b512,
       or a variable. If A is a variable, then it is unified with the
       default algorithm, which is an algorithm that is considered
       cryptographically secure at the time of this writing.
     - encoding(+Encoding)
       The default encoding is utf8. The alternative is octet,
       to treat the input as a list of raw bytes.

   Example:

   ?- crypto_data_hash("abc", Hs, [algorithm(sha256)]).
      Hs = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
   ;  false.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   SHA256 is the current default for several hash-related predicates.
   It is deemed sufficiently secure for the foreseeable future.  Yet,
   application programmers must be aware that the default may change in
   future versions. The hash predicates all yield the algorithm they
   used if a Prolog variable is used for the pertaining option.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_hash(Data0, Hash, Options0) :-
        must_be(list, Options0),
        options_data_bytes(Options0, Data0, Data),
        functor_hash_options(algorithm, A, Options0, _),
        (   hash_algorithm(A) -> true
        ;   domain_error(hash_algorithm, A, crypto_data_hash/3)
        ),
        '$crypto_data_hash'(Data, HashBytes, A),
        hex_bytes(Hash, HashBytes).

options_data_bytes(Options, Data, Bytes) :-
        option(encoding(Encoding), Options, utf8),
        must_be(atom, Encoding),
        encoding_bytes(Encoding, Data, Bytes).

default_hash(sha256).

functor_hash_options(F, Hash, Options0, [Option|Options]) :-
        Option =.. [F,Hash],
        (   select(Option, Options0, Options) ->
            (   var(Hash) ->
                default_hash(Hash)
            ;   must_be(atom, Hash)
            )
        ;   Options = Options0,
            default_hash(Hash)
        ).

hash_algorithm(ripemd160).
hash_algorithm(sha256).
hash_algorithm(sha512).
hash_algorithm(sha384).
hash_algorithm(sha512_256).
hash_algorithm(sha3_224).
hash_algorithm(sha3_256).
hash_algorithm(sha3_384).
hash_algorithm(sha3_512).
hash_algorithm(blake2s256).
hash_algorithm(blake2b512).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_data_hkdf(+Data, +Length, -Bytes, +Options) is det.

   Concentrate possibly dispersed entropy of Data and then expand it
   to the desired length. Data is a list of bytes or characters.

   Bytes is unified with a list of bytes of length Length, and is
   suitable as input keying material and initialization vectors to
   symmetric encryption algorithms.

   Admissible options are:

     - algorithm(+Algorithm)
       One of sha256, sha384 or sha512. If you specify a variable,
       then it is unified with the algorithm that was used, which is a
       cryptographically secure algorithm by default.
     - info(+Info)
       Optional context and application specific information,
       specified as a list of bytes or characters. The default is [].
     - salt(+List)
       Optionally, a list of bytes that are used as salt. The
       default is all zeroes.
     - encoding(+Encoding)
       The default encoding is utf8. The alternative is octet,
       to treat the input as a list of raw bytes.

   The `info/1`  option can be  used to  generate multiple keys  from a
   single  master key,  using for  example values  such as  "key" and
   "iv", or the name of a file that is to be encrypted.

   See crypto_n_random_bytes/2 to obtain a suitable salt.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_hkdf(Data0, L, Bytes, Options0) :-
        functor_hash_options(algorithm, Algorithm, Options0, Options),
        (   hkdf_algorithm(Algorithm) -> true
        ;   domain_error(hkdf_algorithm, Algorithm, crypto_data_hkdf/4)
        ),
        must_be(integer, L),
        L >= 0,
        options_data_bytes(Options, Data0, Data),
        option(salt(SaltBytes), Options, []),
        must_be_bytes(SaltBytes, crypto_data_hkdf/4),
        option(info(Info0), Options, []),
        chars_bytes_(Info0, Info, crypto_data_hkdf/4),
        '$crypto_data_hkdf'(Data, SaltBytes, Info, Algorithm, L, Bytes).

hkdf_algorithm(sha256).
hkdf_algorithm(sha384).
hkdf_algorithm(sha512).

option(What, Options, Default) :-
        (   member(V, Options), var(V) ->
            instantiation_error(option/3)
        ;   true
        ),
        (   member(What, Options) -> true
        ;   What =.. [_,Default]
        ).

chars_bytes_(Cs, Bytes, Context) :-
        must_be(list, Cs),
        (   maplist(integer, Cs) -> Bytes = Cs
        ;   chars_utf8bytes(Cs, Bytes)
        ),
        must_be_bytes(Bytes, Context).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   The so-called modular crypt format (MCF) is a standard for encoding
   password hash strings. However, there's no official specification
   document describing it. Nor is there a central registry of
   identifiers or rules. This page describes what is known about it:

   https://pythonhosted.org/passlib/modular_crypt_format.html

   As of 2016, the MCF is deprecated in favor of the PHC String Format:

   https://github.com/P-H-C/phc-string-format/blob/master/phc-sf-spec.md

   This is what we are using below. For the time being, it is best to
   treat these hashes as opaque terms in applications. Please let me
   know if you need to rely on any specifics of this format.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_password_hash(+Password, ?Hash) is semidet.

   If Hash is instantiated, the predicate succeeds _iff_ the hash
   matches the given password. Otherwise, the call is equivalent to
   crypto_password_hash(Password, Hash, []) and computes a
   password-based hash using the default options.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_password_hash(Password0, Hash) :-
        (   nonvar(Hash) ->
            chars_bytes_(Password0, Password, crypto_password_hash/2),
            must_be(list, Hash),
            dollar_segments(Hash, [[],"pbkdf2-sha512",[t,=|CsIterations],SaltB64,HashB64]),
            number_chars(Iterations, CsIterations),
            bytes_base64(SaltBytes, SaltB64),
            bytes_base64(HashBytes, HashB64),
            '$crypto_password_hash'(Password, SaltBytes, Iterations, HashBytes)
        ;   crypto_password_hash(Password0, Hash, [])
        ).


dollar_segments(Ls, Segments) :-
        (   append(Front, [$|Ds], Ls) ->
            Segments = [Front|Rest],
            dollar_segments(Ds, Rest)
        ;   Segments = [Ls]
        ).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_password_hash(+Password, -Hash, +Options) is det.

   Derive Hash based on Password. This predicate is similar to
   crypto_data_hash/3 in that it derives a hash from given data.
   However, it is tailored for the specific use case of _passwords_.
   One essential distinction is that for this use case, the derivation
   of a hash should be _as slow as possible_ to counteract brute-force
   attacks over possible passwords.

   Another important distinction is that equal passwords must yield,
   with very high probability, _different_ hashes. For this reason,
   cryptographically strong random numbers are automatically added to
   the password before a hash is derived.

   Hash is unified with a string that contains the computed hash and
   all parameters that were used, except for the password. Instead of
   storing passwords, store these hashes. Later, you can verify the
   validity of a password with crypto_password_hash/2, comparing the
   then entered password to the stored hash. If you need to export this
   atom, you should treat it as opaque ASCII data with up to 255 bytes
   of length. The maximal length may increase in the future.

   Admissible options are:

     - algorithm(+Algorithm)
       The algorithm to use. Currently, the only available algorithm
       is 'pbkdf2-sha512', which is therefore also the default.
     - cost(+C)
       C is an integer, denoting the binary logarithm of the number
       of _iterations_ used for the derivation of the hash. This
       means that the number of iterations is set to 2^C. Currently,
       the default is 17, and thus more than one hundred _thousand_
       iterations. You should set this option as high as your server
       and users can tolerate. The default is subject to change and
       will likely increase in the future or adapt to new algorithms.
     - salt(+Salt)
       Use the given list of bytes as salt. By default,
       cryptographically secure random numbers are generated for this
       purpose. The default is intended to be secure, and constitutes
       the typical use case of this predicate.

   Currently, PBKDF2 with SHA-512 is used as the hash derivation
   function, using 128 bits of salt. All default parameters, including
   the algorithm, are subject to change, and other algorithms will also
   become available in the future. Since computed hashes store all
   parameters that were used during their derivation, such changes will
   not affect the operation of existing deployments. Note though that
   new hashes will then be computed with the new default parameters.

   See crypto_data_hkdf/4 for generating keys from Hash.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_password_hash(Password0, Hash, Options) :-
        chars_bytes_(Password0, Password, crypto_password_hash/3),
        must_be(list, Options),
        option(cost(C), Options, 17),
        Iterations is 2^C,
        Algorithm = 'pbkdf2-sha512', % current default and only option
        option(algorithm(Algorithm), Options, Algorithm),
        (   member(salt(SaltBytes), Options) ->
            must_be_bytes(SaltBytes, crypto_password_hash/2)
        ;   crypto_n_random_bytes(16, SaltBytes)
        ),
        '$crypto_password_hash'(Password, SaltBytes, Iterations, HashBytes),
        bytes_base64(HashBytes, HashB64),
        bytes_base64(SaltBytes, SaltB64),
        phrase(format_("$pbkdf2-sha512$t=~d$~s$~s", [Iterations,SaltB64,HashB64]), Hash).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Bidirectional Bytes <-> Base64 conversion
   =========================================

   This implements Base64 conversion *without padding*.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

n_base64(0 , 'A'). n_base64(1 , 'B'). n_base64(2 , 'C'). n_base64(3 , 'D').
n_base64(4 , 'E'). n_base64(5 , 'F'). n_base64(6 , 'G'). n_base64(7 , 'H').
n_base64(8 , 'I'). n_base64(9 , 'J'). n_base64(10, 'K'). n_base64(11, 'L').
n_base64(12, 'M'). n_base64(13, 'N'). n_base64(14, 'O'). n_base64(15, 'P').
n_base64(16, 'Q'). n_base64(17, 'R'). n_base64(18, 'S'). n_base64(19, 'T').
n_base64(20, 'U'). n_base64(21, 'V'). n_base64(22, 'W'). n_base64(23, 'X').
n_base64(24, 'Y'). n_base64(25, 'Z'). n_base64(26, 'a'). n_base64(27, 'b').
n_base64(28, 'c'). n_base64(29, 'd'). n_base64(30, 'e'). n_base64(31, 'f').
n_base64(32, 'g'). n_base64(33, 'h'). n_base64(34, 'i'). n_base64(35, 'j').
n_base64(36, 'k'). n_base64(37, 'l'). n_base64(38, 'm'). n_base64(39, 'n').
n_base64(40, 'o'). n_base64(41, 'p'). n_base64(42, 'q'). n_base64(43, 'r').
n_base64(44, 's'). n_base64(45, 't'). n_base64(46, 'u'). n_base64(47, 'v').
n_base64(48, 'w'). n_base64(49, 'x'). n_base64(50, 'y'). n_base64(51, 'z').
n_base64(52, '0'). n_base64(53, '1'). n_base64(54, '2'). n_base64(55, '3').
n_base64(56, '4'). n_base64(57, '5'). n_base64(58, '6'). n_base64(59, '7').
n_base64(60, '8'). n_base64(61, '9'). n_base64(62, '+'). n_base64(63, '/').

bytes_base64(Ls, Bs) :-
        (   list(Bs), maplist(atom, Bs) ->
            maplist(n_base64, Is, Bs),
            phrase(bytes_base64_(Ls), Is),
            Ls ins 0..255
        ;   phrase(bytes_base64_(Ls), Is),
            Is ins 0..63,
            maplist(n_base64, Is, Bs)
        ).

list(Ls) :-
        nonvar(Ls),
        (   Ls = [] -> true
        ;   Ls = [_|Rest],
            list(Rest)
        ).

bytes_base64_([])         --> [].
bytes_base64_([A])        --> [W,X],
        { A #= W*4 + X//16,
          X #= 16*_ }.
bytes_base64_([A,B])      --> [W,X,Y],
        { A #= W*4 + X//16,
          B #= (X mod 16)*16 + Y//4,
          Y #= 4*_ }.
bytes_base64_([A,B,C|Ls]) --> [W,X,Y,Z],
        { A #= W*4 + X//16,
          B #= (X mod 16)*16 + Y//4,
          C #= (Y mod 4)*64 + Z },
        bytes_base64_(Ls).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   crypto_data_encrypt(+PlainText,
                       +Algorithm,
                       +Key,
                       +IV,
                       -CipherText,
                       +Options).

   Encrypt the given PlainText, using the symmetric algorithm
   Algorithm, key Key, and initialization vector (or nonce) IV, to
   give CipherText.

   PlainText must be a list of bytes or characters, Key and IV must be
   lists of bytes, and CipherText is created as a list of characters.

   Keys and IVs can be chosen at random (using for example
   crypto_n_random_bytes/2) or derived from input keying material (IKM)
   using for example crypto_data_hkdf/4. This input is often a shared
   secret, such as a negotiated point on an elliptic curve, or the hash
   that was computed from a password via crypto_password_hash/3 with a
   freshly generated and specified _salt_.

   Reusing the same combination of Key and IV typically leaks at least
   _some_ information about the plaintext. For example, identical
   plaintexts will then correspond to identical ciphertexts. For some
   algorithms, reusing an IV with the same Key has disastrous results
   and can cause the loss of all properties that are otherwise
   guaranteed. Especially in such cases, an IV is also called a
   _nonce_ (number used once).

   It is safe to store and  transfer the used initialization vector (or
   nonce) in plain text, but the key _must be kept secret_.

   Currently, the only supported algorithm is 'chacha20-poly1305', a
   powerful and efficient _authenticated_ encryption scheme, providing
   secrecy and at the same time reliable protection against undetected
   _modifications_ of the encrypted data. This is a very good choice
   for virtually all use cases. It is a stream cipher and can encrypt
   data of any length up to 256 GB. Further, the encrypted data has
   exactly the same length as the original, and no padding is used.

   Options:

      - encoding(+Encoding)
      Encoding to use for PlainText. Default is utf8. The alternative
      is octet to treat PlainText as raw bytes.

      - tag(-List)
      For authenticated encryption schemes, List is unified with a
      list of _bytes_ holding the tag. This tag must be provided for
      decryption.

   Here is an example encryption and decryption, using the ChaCha20
   stream cipher with the Poly1305 authenticator. This cipher uses a
   256-bit key and a 96-bit nonce, i.e., 32 and 12 _bytes_,
   respectively:

    ?- Algorithm = 'chacha20-poly1305',
       crypto_n_random_bytes(32, Key),
       crypto_n_random_bytes(12, IV),
       crypto_data_encrypt("this text is to be encrypted", Algorithm,
                   Key, IV, CipherText, [tag(Tag)]),
       crypto_data_decrypt(CipherText, Algorithm,
                   Key, IV, RecoveredText, [tag(Tag)]).

   Yielding:

       Algorithm = 'chacha20-poly1305',
       Key = [113,247,153,134,177,220,13,193,50,150|...],
       IV = [135,20,149,153,63,35,68,114,247,171|...],
       CipherText = "\x94\0Ej\x94\®Â\x95\óÑÆXÃn¾ð©b\x1c\ ...",
       RecoveredText = "this text is to be  ...",
       Tag = [152,117,152,17,162,75,150,206,144,40|...]

   In this example, we use crypto_n_random_bytes/2 to generate a key
   and nonce from cryptographically secure random numbers. For
   repeated applications, you must ensure that a nonce is only used
   _once_ together with the same key. Note that for _authenticated_
   encryption schemes, the _tag_ that was computed during encryption
   is necessary for decryption. It is safe to store and transfer the
   tag in plain text.

   See also crypto_data_decrypt/6, and hex_bytes/2 for conversion
   between bytes and hex encoding.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_encrypt(PlainText0, Algorithm, Key, IV, CipherText, Options) :-
        options_data_bytes(Options, PlainText0, PlainText),
        option(tag(Tag), Options, _),
        (   nonvar(Tag) ->
            must_be_bytes(Tag, crypto_data_encrypt/6)
        ;   true
        ),
        must_be_bytes(Key, crypto_data_encrypt/6),
        must_be_bytes(IV, crypto_data_encrypt/6),
        must_be(atom, Algorithm),
        (   Algorithm = 'chacha20-poly1305' -> true
        ;   domain_error('chacha20-poly1305', Algorithm, crypto_data_encrypt/6)
        ),
        '$crypto_data_encrypt'(PlainText, Key, IV, Tag, CipherText).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  crypto_data_decrypt(+CipherText,
                      +Algorithm,
                      +Key,
                      +IV,
                      -PlainText,
                      +Options).

   Decrypt the given CipherText, using the symmetric algorithm
   Algorithm, key Key, and initialization vector IV, to give
   PlainText. CipherText must be a list of bytes or characters, and
   Key and IV must be lists of bytes. PlainText is created as a list
   of characters.

   Currently, the only supported algorithm is 'chacha20-poly1305',
   a very secure, fast and versatile authenticated encryption method.

   Options is a list of:

    - encoding(+Encoding)
    Encoding to use for PlainText. The default is utf8. The
    alternative is octet, which is used if the data are raw bytes.

    - tag(+Tag)
    For authenticated encryption schemes, the tag must be specified as
    a list of bytes exactly as they were generated upon encryption.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_decrypt(CipherText0, Algorithm, Key, IV, PlainText, Options) :-
        option(tag(Tag), Options, []),
        must_be_bytes(Tag, crypto_data_decrypt/6),
        must_be_bytes(Key, crypto_data_decrypt/6),
        must_be_bytes(IV, crypto_data_decrypt/6),
        must_be(atom, Algorithm),
        option(encoding(Encoding), Options, utf8),
        must_be(atom, Encoding),
        member(Encoding, [utf8,octet]),
        must_be(list, CipherText0),
        encoding_bytes(octet, CipherText0, CipherText1),
        append(CipherText1, Tag, CipherText),
        (   Algorithm = 'chacha20-poly1305' -> true
        ;   domain_error('chacha20-poly1305', Algorithm, crypto_data_decrypt/6)
        ),
        '$crypto_data_decrypt'(CipherText, Key, IV, Encoding, PlainText).

encoding_bytes(octet, Bs0, Bs) :-
        must_be(list, Bs0),
        (   maplist(integer, Bs0) ->
            Bs0 = Bs
        ;   maplist(char_code, Bs0, Bs)
        ),
        must_be_bytes(Bs, crypto_encoding).
encoding_bytes(utf8, Cs, Bs) :-
        must_be(list, Cs),
        (   maplist(atom, Cs) ->
            chars_bytes_(Cs, Bs, crypto_encoding)
        ;   domain_error(encryption_encoding, Cs, crypto)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Digital signatures with Ed25519
   ===============================

   crypto_ed25519_sign(+Key, +Data, -Signature, +Options)

   Key and Data must be lists of characters. Key is a private key in
   PKCS#8 (v1 or v2) DER format. Sign Data with Key, yielding
   Signature as a list of hexadecimal characters.


   crypto_ed25519_verify(+Key, +Data, +Signature, +Options)

   Key and Data must be lists of characters. Key is a public key in
   PKCS#8 DER format. Succeeds if Data was signed with the private key
   corresponding to Key, where Signature is a list of hexadecimal
   characters as generated by crypto_ed25519_sign/4. Fails otherwise.


   Currently, the only option for both predicates is:

     - encoding(+Encoding)
       The default encoding of Data is utf8. The alternative is octet,
       which treats Data as a list of raw bytes.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_ed25519_sign(Key0, Data0, Signature, Options) :-
        options_data_bytes(Options, Data0, Data),
        encoding_bytes(octet, Key0, Key),
        '$crypto_ed25519_sign'(Key, Data, Signature0),
        hex_bytes(Signature, Signature0).

crypto_ed25519_verify(Key0, Data0, Signature0, Options) :-
        options_data_bytes(Options, Data0, Data),
        encoding_bytes(octet, Key0, Key),
        hex_bytes(Signature0, Signature),
        '$crypto_ed25519_verify'(Key, Data, Signature).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Modular multiplicative inverse.

   Compute Y = X^(-1) mod p, using the extended Euclidean algorithm.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

multiplicative_inverse_modulo_p(X, P, Y) :-
        eea(X, P, _, _, Y),
        R #= X*Y mod P,
        zcompare(C, 1, R),
        must_be_one(C, X, P, Y).

must_be_one(=, _, _, _).
must_be_one(>, X, P, Y) :- throw(multiplicative_inverse_modulo_p(X,P,Y)).
must_be_one(<, X, P, Y) :- throw(multiplicative_inverse_modulo_p(X,P,Y)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Extended Euclidean algorithm.

   Computes the GCD and the Bézout coefficients S and T.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

eea(I, J, G, S, T) :-
        State0 = state(1,0,0,1),
        eea_loop(I, J, State0, G, S, T).

eea_loop(I, J, State0, G, S, T) :-
        zcompare(C, 0, J),
        eea_(C, I, J, State0, G, S, T).

eea_(=, I, _, state(_,_,U,V), I, U, V).
eea_(<, I0, J0, state(S0,T0,U0,V0), I, U, V) :-
        Q #= I0 // J0,
        R #= I0 mod J0,
        S1 #= U0 - (Q*S0),
        T1 #= V0 - (Q*T0),
        eea_loop(J0, R, state(S1,T1,S0,T0), I, U, V).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Operations on Elliptic Curves
   =============================

   Sample use: Establishing a shared secret S, using ECDH key exchange.

    ?- crypto_name_curve(Name, C),
       crypto_curve_generator(C, Generator),
       PrivateKey = 10,
       crypto_curve_scalar_mult(C, PrivateKey, Generator, PublicKey),
       Random = 12,
       crypto_curve_scalar_mult(C, Random, Generator, R),
       crypto_curve_scalar_mult(C, Random, PublicKey, S),
       crypto_curve_scalar_mult(C, PrivateKey, R, S).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   An elliptic curve over a prime field F_p is represented as:

   curve(P,A,B,point(X,Y),Order,Cofactor).

   First, we define suitable accessors.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

curve_p(curve(P,_,_,_,_,_), P).
curve_a(curve(_,A,_,_,_,_), A).
curve_b(curve(_,_,B,_,_,_), B).

crypto_curve_order(curve(_,_,_,_,Order,_), Order).
crypto_curve_generator(curve(_,_,_,G,_,_), G).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Scalar point multiplication.

   R = k*Q.

   The Montgomery ladder method is used to mitigate side-channel
   attacks such as timing attacks, since the number of multiplications
   and additions is independent of the private key K. This method does
   not even reveal the key's Hamming weight (number of 1s).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_curve_scalar_mult(Curve, K, Q, R) :-
        msb(K, Upper),
        scalar_multiplication(Curve, K, Upper, ml(null,Q)-R),
        must_be_on_curve(Curve, R).

scalar_multiplication(Curve, K, I, R0-R) :-
        zcompare(C, -1, I),
        scalar_mult_(C, Curve, K, I, R0-R).

scalar_mult_(=, _, _, _, ml(R,_)-R).
scalar_mult_(<, Curve, K, I0, ML0-R) :-
        BitSet #= K /\ (1 << I0),
        zcompare(C, 0, BitSet),
        montgomery_step(C, Curve, ML0, ML1),
        I1 #= I0 - 1,
        scalar_multiplication(Curve, K, I1, ML1-R).

montgomery_step(=, Curve, ml(R0,S0), ml(R,S)) :-
        curve_points_addition(Curve, R0, S0, S),
        curve_point_double(Curve, R0, R).
montgomery_step(<, Curve, ml(R0,S0), ml(R,S)) :-
        curve_points_addition(Curve, R0, S0, R),
        curve_point_double(Curve, S0, S).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Doubling a point: R = A + A.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

curve_point_double(_, null, null).
curve_point_double(Curve, point(AX,AY), R) :-
        curve_p(Curve, P),
        curve_a(Curve, A),
        Numerator #= (3*AX^2 + A) mod P,
        Denom0 #= 2*AY mod P,
        multiplicative_inverse_modulo_p(Denom0, P, Denom),
        S #= (Numerator*Denom) mod P,
        R = point(RX,RY),
        RX #= (S^2 - 2*AX) mod P,
        RY #= (S*(AX - RX) - AY) mod P,
        must_be_on_curve(Curve, R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Adding two points.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

curve_points_addition(Curve, P, Q, R) :-
        curve_points_addition_(P, Curve, Q, R).

curve_points_addition_(null, _, P, P).
curve_points_addition_(P, _, null, P).
curve_points_addition_(point(AX,AY), Curve, point(BX,BY), R) :-
        curve_p(Curve, P),
        Numerator #= (AY - BY) mod P,
        Denom0 #= (AX - BX) mod P,
        multiplicative_inverse_modulo_p(Denom0, P, Denom),
        S #= (Numerator * Denom) mod P,
        R = point(RX,RY),
        RX #= (S^2 - AX - BX) mod P,
        RY #= (S*(AX - RX) - AY) mod P,
        must_be_on_curve(Curve, R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Validation.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

curve_contains_point(Curve, point(QX,QY)) :-
        curve_a(Curve, A),
        curve_b(Curve, B),
        curve_p(Curve, P),
        QY^2 mod P #= (QX^3 + A*QX + B) mod P.

must_be_on_curve(Curve, P) :-
        \+ curve_contains_point(Curve, P),
        throw(not_on_curve(P)).
must_be_on_curve(Curve, P) :- curve_contains_point(Curve, P).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Predefined curves
   =================

   List available curves:

   $ openssl ecparam -list_curves

   Show curve parameters for secp256k1:

   $ openssl ecparam -param_enc explicit -conv_form uncompressed \
                     -text -no_seed -name secp256k1

   You must remove the leading "04:" from the generator.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_name_curve(secp112r1,
                  curve(0x00db7c2abf62e35e668076bead208b,
                        0x00db7c2abf62e35e668076bead2088,
                        0x659ef8ba043916eede8911702b22,
                        point(0x09487239995a5ee76b55f9c2f098,
                              0xa89ce5af8724c0a23e0e0ff77500),
                        0x00db7c2abf62e35e7628dfac6561c5,
                        1)).
crypto_name_curve(secp256k1,
                  curve(0x00fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f,
                        0x0,
                        0x7,
                        point(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
                              0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8),
                        0x00fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141,
                        1)).
