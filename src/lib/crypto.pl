/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2020-2024 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

/** Predicates for cryptographic applications.

   This library assumes that the Prolog flag `double_quotes` is set to `chars`.
   In Scryer Prolog, lists of characters are very efficiently represented,
   and strings have the advantage that the atom table remains unmodified.

   Especially for cryptographic applications, it is an advantage that
   using strings leaves little trace of what was processed in the system.
*/

:- module(crypto,
          [hex_bytes/2,                  % ?Hex, ?Bytes
           crypto_n_random_bytes/2,      % +N, -Bytes
           crypto_data_hash/3,           % +Data, -Hash, +Options
           crypto_data_hkdf/4,           % +Data, +Length, -Bytes, +Options
           crypto_password_hash/2,       % +Password, ?Hash
           crypto_password_hash/3,       % +Password, -Hash, +Options
           crypto_data_encrypt/6,        % +PlainText, +Algorithm, +Key, +IV, -CipherText, +Options
           crypto_data_decrypt/6,        % +CipherText, +Algorithm, +Key, +IV, -PlainText, +Options
           ed25519_seed_keypair/2,       % +Seed, -KeyPair
           ed25519_new_keypair/1,        % -KeyPair
           ed25519_keypair_public_key/2, % +KeyPair, +PublicKey
           ed25519_sign/4,               % +KeyPair, +Data, -Signature, +Options
           ed25519_verify/4,             % +PublicKey, +Data, +Signature, +Options
           curve25519_generator/1,       % -Generator
           curve25519_scalar_mult/3,     % +Scalar, +Point, -Result
           crypto_name_curve/2,          % +Name, -Curve
           crypto_curve_order/2,         % +Curve, -Order
           crypto_curve_generator/2,     % +Curve, -Generator
           crypto_curve_scalar_mult/4    % +Curve, +Scalar, +Point, -Result
          ]).

:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(dcgs)).
:- use_module(library(clpz)).
:- use_module(library(arithmetic)).
:- use_module(library(format)).
:- use_module(library(charsio)).
:- use_module(library(si)).
:- use_module(library(iso_ext), [partial_string/3]).


%% hex_bytes(?Hex, ?Bytes) is det.
%
%  Relation between a hexadecimal sequence and a list of bytes. Hex
%  is a string of hexadecimal numbers. Bytes is a list of _integers_
%  between 0 and 255 that represent the sequence as a list of bytes.
%  At least one of the arguments must be instantiated.
%
%   Example:
%
% ```
%   ?- hex_bytes("501ACE", Bs).
%      Bs = [80,26,206].
% ```

hex_bytes(Hs, Bytes) :-
        (   ground(Hs) ->
            must_be(chars, Hs),
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
          Byte #= High*16 + Low },
        hex_bytes(Hs).

bytes_hex([]) --> [].
bytes_hex([B|Bs]) --> [C0,C1],
        { High #= B>>4,
          Low #= B /\ 0xf,
          char_hexval(C0, High),
          char_hexval(C1, Low)
        },
        bytes_hex(Bs).

char_hexval(C, H) :-
        integer(H),
        !,
        hexval_char(H, C).
char_hexval(C, H) :- nth0(H, "0123456789abcdef", C), !.
char_hexval(C, H) :- nth0(H, "0123456789ABCDEF", C), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  We specialize char_hexval/2 for use if the value is given,
  so that it works in constant time in this case.

  The security of HMAC verification depends on this property.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

hexval_char(0, '0').
hexval_char(1, '1').
hexval_char(2, '2').
hexval_char(3, '3').
hexval_char(4, '4').
hexval_char(5, '5').
hexval_char(6, '6').
hexval_char(7, '7').
hexval_char(8, '8').
hexval_char(9, '9').
hexval_char(0xa, a).
hexval_char(0xb, b).
hexval_char(0xc, c).
hexval_char(0xd, d).
hexval_char(0xe, e).
hexval_char(0xf, f).

must_be_bytes(Bytes, Context) :-
        must_be(list, Bytes),
        maplist(must_be(integer), Bytes),
        (   member(B, Bytes), \+ between(0, 255, B) ->
            type_error(byte, B, Context)
        ;   true
        ).


must_be_octet_chars(Chars, Context) :-
        must_be(chars, Chars),
        (   '$first_non_octet'(Chars, F) ->
            domain_error(octet_character, F, Context)
        ;   true
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Cryptographically secure random numbers
   =======================================
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% crypto_n_random_bytes(+N, -Bytes) is det.
%
%  Bytes is unified with a list of N cryptographically secure
%  pseudo-random bytes. Each byte is an integer between 0 and 255. If
%  the internal pseudo-random number generator (PRNG) has not been
%  seeded with enough entropy to ensure an unpredictable byte
%  sequence, an exception is thrown.
%
%  One way to relate such a list of bytes to an _integer_ is to use
%  CLP(ℤ) constraints as follows:
%
% ```
%  :- use_module(library(clpz)).
%  :- use_module(library(lists)).
%
%  bytes_integer(Bs, N) :-
%          foldl(pow, Bs, 0-0, N-_).
%
%  pow(B, N0-I0, N-I) :-
%          B in 0..255,
%          N #= N0 + B*256^I0,
%          I #= I0 + 1.
% ```
%
%  With this definition, we can generate a random 256-bit integer
%  _from_ a list of 32 random _bytes_:
%
% ```
%  ?- crypto_n_random_bytes(32, Bs),
%     bytes_integer(Bs, I).
%     Bs = [146,166,162,210,242,7,25,132,64,94|...],
%     I = 337420085690608915485...(56 digits omitted).
% ```
%
%  The above relation also works in the other direction, letting you
%  translate an integer _to_ a list of bytes. In addition, you can
%  use `hex_bytes/2` to convert bytes to _tokens_ that can be easily
%  exchanged in your applications.
%
% ```
%  ?- crypto_n_random_bytes(12, Bs),
%     hex_bytes(Hex, Bs).
%     Bs = [34,25,50,72,58,63,50,172,32,46|...], Hex = "221932483a3f32ac202 ...".
% ```

crypto_n_random_bytes(N, Bs) :-
        must_be(integer, N),
        length(Bs, N),
        maplist(crypto_random_byte, Bs).

crypto_random_byte(B) :- '$crypto_random_byte'(B).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Hashing
   =======
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% crypto_data_hash(+Data, -Hash, +Options)
%
%  Where Data is a list of characters, and Hash is the computed hash
%  as a list of hexadecimal characters.
%
%  Options is a list of:
%
%    - `algorithm(+A)`
%      where `A` is one of `ripemd160`, `sha256`, `sha384`, `sha512`,
%      `sha512_256`, `sha3_224`, `sha3_256`, `sha3_384`,
%      `sha3_512`, `blake2s256`, `blake2b512`, or a variable. If `A` is
%      a variable, then it is unified with the default algorithm,
%      which is an algorithm that is considered cryptographically
%      secure at the time of this writing.
%
%    - `encoding(+Encoding)`
%      The default encoding is `utf8`. The alternative is `octet`, to
%      use the character code of each character in Data as a byte
%      value.
%
%    - `hmac(+Key)`
%      Compute a hash-based message authentication code (HMAC) using
%      Key, a list of bytes. This option is currently supported for
%      algorithms `sha256`, `sha384` and `sha512`. If `Hash` is
%      instantiated, then it is compared with the computed HMAC
%      in such a way that no information about the expected HMAC
%      is revealed, using a comparison of strings that always takes
%      the same time independent of whether and where the strings
%      differ. This option can therefore also be used to safely
%      _verify_ a given HMAC.
%
%  Example:
%
% ```
%  ?- crypto_data_hash("abc", Hs, [algorithm(sha256)]).
%     Hs = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad".
% ```

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   SHA256 is the current default for several hash-related predicates.
   It is deemed sufficiently secure for the foreseeable future.  Yet,
   application programmers must be aware that the default may change in
   future versions. The hash predicates all yield the algorithm they
   used if a Prolog variable is used for the pertaining option.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

crypto_data_hash(Data0, Hash, Options0) :-
        must_be(list, Options0),
        options_data_chars(Options0, Data0, Data, Encoding),
        functor_hash_options(algorithm, A, Options0, _),
        (   hash_algorithm(A) -> true
        ;   domain_error(hash_algorithm, A, crypto_data_hash/3)
        ),
        (   member(HMAC, Options0), nonvar(HMAC), HMAC = hmac(Ks) ->
            must_be_bytes(Ks, crypto_data_hash/3),
            hmac_algorithm(A),
            '$crypto_hmac'(Data, Encoding, Ks, HashBytes, A),
            (   var(Hash) ->
                hex_bytes(Hash, HashBytes)
            ;   must_be(chars, Hash),
                hex_bytes(HashMAC, HashBytes),
                chars_equal_constant_time(Hash, HashMAC)
            )
        ;   '$crypto_data_hash'(Data, Encoding, HashBytes, A),
            hex_bytes(Hash, HashBytes)
        ).

chars_equal_constant_time(As, Bs) :-
        maplist(chars_xor, As, Bs, Xs),
        sum_list(Xs, Sum),
        Sum =:= 0.

chars_xor(A, B, Xor) :-
        char_code(A, CA),
        char_code(B, CB),
        Xor is xor(CA,CB).

hmac_algorithm(sha256).
hmac_algorithm(sha384).
hmac_algorithm(sha512).

options_data_chars(Options, Data, Chars, Encoding) :-
        option(encoding(Encoding), Options, utf8),
        must_be(atom, Encoding),
        encoding_chars(Encoding, Data, Chars).

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


%% crypto_data_hkdf(+Data, +Length, -Bytes, +Options) is det.
%
%  Concentrate possibly dispersed entropy of Data and then expand it
%  to the desired length. Data is a list of characters.
%
%  Bytes is unified with a list of bytes of length Length, and is
%  suitable as input keying material and initialization vectors to
%  symmetric encryption algorithms.
%
%  Admissible options are:
%
%    - `algorithm(+Algorithm)`
%      One of `sha256`, `sha384` or `sha512`. If you specify a variable,
%      then it is unified with the algorithm that was used, which is a
%      cryptographically secure algorithm by default.
%    - `info(+Info)`
%      Optional context and application specific information,
%      specified as a list of characters. The default is `[]`.
%    - `salt(+List)`
%      Optionally, a list of bytes that are used as salt. The
%      default is all zeroes.
%    - `encoding(+Encoding)`
%      The default encoding is `utf8`. The alternative is `octet`,
%      to use the character code of each character in Data as a byte
%      value.
%
%  The `info/1`  option can be  used to  generate multiple keys  from a
%  single  master key,  using for  example values  such as  "key" and
%  "iv", or the name of a file that is to be encrypted.
%
%  See `crypto_n_random_bytes/2` to obtain a suitable salt.

crypto_data_hkdf(Data0, L, Bytes, Options0) :-
        functor_hash_options(algorithm, Algorithm, Options0, Options),
        (   hkdf_algorithm(Algorithm) -> true
        ;   domain_error(hkdf_algorithm, Algorithm, crypto_data_hkdf/4)
        ),
        must_be(integer, L),
        L #>= 0,
        options_data_chars(Options, Data0, Data, Encoding),
        option(salt(SaltBytes), Options, []),
        must_be_bytes(SaltBytes, crypto_data_hkdf/4),
        option(info(Info0), Options, []),
        chars_bytes_(Info0, Info, crypto_data_hkdf/4),
        '$crypto_data_hkdf'(Data, Encoding, SaltBytes, Info, Algorithm, L, Bytes).

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

%% crypto_password_hash(+Password, ?Hash) is semidet.
%
%  If Hash is instantiated, the predicate succeeds _iff_ the hash
%  matches the given password. Otherwise, the call is equivalent to
%  `crypto_password_hash(Password, Hash, [])` and computes a
%  password-based hash using the default options.

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


%% crypto_password_hash(+Password, -Hash, +Options) is det.
%
%  Derive Hash based on Password. This predicate is similar to
%  `crypto_data_hash/3` in that it derives a hash from given data.
%  However, it is tailored for the specific use case of _passwords_.
%  One essential distinction is that for this use case, the derivation
%  of a hash should be _as slow as possible_ to counteract brute-force
%  attacks over possible passwords.
%
%  Another important distinction is that equal passwords must yield,
%  with very high probability, _different_ hashes. For this reason,
%  cryptographically strong random numbers are automatically added to
%  the password before a hash is derived.
%
%  Hash is unified with a string that contains the computed hash and
%  all parameters that were used, except for the password. Instead of
%  storing passwords, store these hashes. Later, you can verify the
%  validity of a password with `crypto_password_hash/2`, comparing the
%  then entered password to the stored hash. If you need to export this
%  atom, you should treat it as opaque ASCII data with up to 255 bytes
%  of length. The maximal length may increase in the future.
%
%  Admissible options are:
%
%    - `algorithm(+Algorithm)`
%      The algorithm to use. Currently, the only available algorithm
%      is `'pbkdf2-sha512'`, which is therefore also the default.
%    - `cost(+C)`
%      C is an integer, denoting the binary logarithm of the number
%      of _iterations_ used for the derivation of the hash. This
%      means that the number of iterations is set to 2^C. Currently,
%      the default is 17, and thus more than one hundred _thousand_
%      iterations. You should set this option as high as your server
%      and users can tolerate. The default is subject to change and
%      will likely increase in the future or adapt to new algorithms.
%    - `salt(+Salt)`
%      Use the given list of bytes as salt. By default,
%      cryptographically secure random numbers are generated for this
%      purpose. The default is intended to be secure, and constitutes
%      the typical use case of this predicate.
%
%  Currently, PBKDF2 with SHA-512 is used as the hash derivation
%  function, using 128 bits of salt. All default parameters, including
%  the algorithm, are subject to change, and other algorithms will also
%  become available in the future. Since computed hashes store all
%  parameters that were used during their derivation, such changes will
%  not affect the operation of existing deployments. Note though that
%  new hashes will then be computed with the new default parameters.
%
%  See `crypto_data_hkdf/4` for generating keys from Hash.

crypto_password_hash(Password0, Hash, Options) :-
        chars_bytes_(Password0, Password, crypto_password_hash/3),
        must_be(list, Options),
        option(cost(C), Options, 17),
        Iterations #= 2^C,
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
   Bidirectional Bytes <-> Base64 conversion *without padding*.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

bytes_base64(Bytes, Base64) :-
        (   var(Bytes) ->
            chars_base64(Chars, Base64, [padding(false)]),
            maplist(char_code, Chars, Bytes)
        ;   maplist(char_code, Chars, Bytes),
            chars_base64(Chars, Base64, [padding(false)])
        ).

%% crypto_data_encrypt(+PlainText, +Algorithm, +Key, +IV, -CipherText, +Options).
%
%  Encrypt the given PlainText, using the symmetric algorithm
%  Algorithm, key Key, and initialization vector (or nonce) IV, to
%  give CipherText.
%
%  PlainText must be a list of characters, Key and IV must be lists of
%  bytes, and CipherText is created as a list of characters.
%
%  Keys and IVs can be chosen at random (using for example
%  `crypto_n_random_bytes/2`) or derived from input keying material (IKM)
%  using for example `crypto_data_hkdf/4`. This input is often a shared
%  secret, such as a negotiated point on an elliptic curve, or the hash
%  that was computed from a password via `crypto_password_hash/3` with a
%  freshly generated and specified _salt_.
%
%  Reusing the same combination of Key and IV typically leaks at least
%  _some_ information about the plaintext. For example, identical
%  plaintexts will then correspond to identical ciphertexts. For some
%  algorithms, reusing an IV with the same Key has disastrous results
%  and can cause the loss of all properties that are otherwise
%  guaranteed. Especially in such cases, an IV is also called a
%  _nonce_ (number used once).
%
%  It is safe to store and  transfer the used initialization vector (or
%  nonce) in plain text, but the key _must be kept secret_.
%
%  Currently, the only supported algorithm is 'chacha20-poly1305', a
%  powerful and efficient _authenticated_ encryption scheme, providing
%  secrecy and at the same time reliable protection against undetected
%  _modifications_ of the encrypted data. This is a very good choice
%  for virtually all use cases. It is a stream cipher and can encrypt
%  data of any length up to 256 GB. Further, the encrypted data has
%  exactly the same length as the original, and no padding is used.
%
%  Options:
%
%     - `encoding(+Encoding)`
%     Encoding to use for PlainText. The default is `utf8`. The
%     alternative is `octet`, to use the character code of each
%     character in PlainText as a byte value.
%
%     - `tag(-List)`
%     For authenticated encryption schemes, List is unified with a
%     list of _bytes_ holding the tag. This tag must be provided for
%     decryption.
%
%     - `aad(+Data)`
%     Data is additional authenticated data (AAD), a list of
%     characters. It is authenticated in that it influences the tag,
%     but it is not encrypted. The `encoding/1` option also specifies
%     the encoding of Data.
%
%  Here is an example encryption and decryption, using the ChaCha20
%  stream cipher with the Poly1305 authenticator. This cipher uses a
%  256-bit key and a 96-bit nonce, i.e., 32 and 12 _bytes_,
%  respectively:
%
% ```
%   ?- Algorithm = 'chacha20-poly1305',
%      crypto_n_random_bytes(32, Key),
%      crypto_n_random_bytes(12, IV),
%      crypto_data_encrypt("this text is to be encrypted", Algorithm,
%                  Key, IV, CipherText, [tag(Tag)]),
%      crypto_data_decrypt(CipherText, Algorithm,
%                  Key, IV, RecoveredText, [tag(Tag)]).
% ```
%
%  Yielding:
%
% ```
%      Algorithm = 'chacha20-poly1305',
%      Key = [113,247,153,134,177,220,13,193,50,150|...],
%      IV = [135,20,149,153,63,35,68,114,247,171|...],
%      CipherText = "\x94\0Ej\x94\®Â\x95\óÑÆXÃn¾ð©b\x1c\ ...",
%      RecoveredText = "this text is to be  ...",
%      Tag = [152,117,152,17,162,75,150,206,144,40|...]
% ```
%
%  In this example, we use `crypto_n_random_bytes/2` to generate a key
%  and nonce from cryptographically secure random numbers. For
%  repeated applications, you must ensure that a nonce is only used
%  _once_ together with the same key. Note that for _authenticated_
%  encryption schemes, the _tag_ that was computed during encryption
%  is necessary for decryption. It is safe to store and transfer the
%  tag in plain text.
%
%  See also `crypto_data_decrypt/6`, and `hex_bytes/2` for conversion
%  between bytes and hex encoding.

crypto_data_encrypt(PlainText0, Algorithm, Key, IV, CipherText, Options) :-
        options_data_chars(Options, PlainText0, PlainText, Encoding),
        option(tag(Tag), Options, _),
        (   nonvar(Tag) ->
            must_be_bytes(Tag, crypto_data_encrypt/6)
        ;   true
        ),
        option(aad(AAD0), Options, []),
        encoding_chars(Encoding, AAD0, AAD),
        must_be_bytes(Key, crypto_data_encrypt/6),
        must_be_bytes(IV, crypto_data_encrypt/6),
        must_be(atom, Algorithm),
        (   Algorithm = 'chacha20-poly1305' -> true
        ;   domain_error('chacha20-poly1305', Algorithm, crypto_data_encrypt/6)
        ),
        algorithm_key_iv(Algorithm, Key, IV),
        '$crypto_data_encrypt'(PlainText, AAD, Encoding, Key, IV, Tag, CipherText).

algorithm_key_iv('chacha20-poly1305', Key, IV) :-
        length(Key, 32),
        length(IV, 12).

%% crypto_data_decrypt(+CipherText, +Algorithm, +Key, +IV, -PlainText, +Options).
%
%  Decrypt the given CipherText, using the symmetric algorithm
%  Algorithm, key Key, and initialization vector IV, to give
%  PlainText. CipherText must be a list of characters, and Key and IV
%  must be lists of bytes. PlainText is created as a list of
%  characters.
%
%  Currently, the only supported algorithm is 'chacha20-poly1305',
%  a very secure, fast and versatile authenticated encryption method.
%
%  Options is a list of:
%
%   - `encoding(+Encoding)`
%   Encoding to use for PlainText. The default is `utf8`. The
%   alternative is `octet`, to obtain a list of characters where each
%   character code corresponds to a decrypted octet of CipherText.
%
%   - `tag(+Tag)`
%   For authenticated encryption schemes, the tag must be specified as
%   a list of bytes exactly as they were generated upon encryption.
%
%   - `aad(+Data)`
%   Any additional authenticated data (AAD) must be specified. The
%   `encoding/1` option also specifies the encoding of Data.

crypto_data_decrypt(CipherText0, Algorithm, Key, IV, PlainText, Options) :-
        option(tag(Tag), Options, []),
        must_be_bytes(Tag, crypto_data_decrypt/6),
        must_be_bytes(Key, crypto_data_decrypt/6),
        must_be_bytes(IV, crypto_data_decrypt/6),
        must_be(atom, Algorithm),
        option(encoding(Encoding), Options, utf8),
        option(aad(AAD0), Options, []),
        encoding_chars(Encoding, AAD0, AAD),
        must_be(atom, Encoding),
        member(Encoding, [utf8,octet]),
        encoding_chars(octet, CipherText0, CipherText1),
        maplist(char_code, TagChars, Tag),
        % we append the tag very efficiently, retaining a compact
        % internal string representation of the ciphertext
        partial_string(CipherText1, CipherText, TagChars),
        (   Algorithm = 'chacha20-poly1305' -> true
        ;   domain_error('chacha20-poly1305', Algorithm, crypto_data_decrypt/6)
        ),
        algorithm_key_iv(Algorithm, Key, IV),
        '$crypto_data_decrypt'(CipherText, AAD, Key, IV, Encoding, PlainText).


encoding_chars(octet, Bs, Cs) :-
        must_be(list, Bs),
        (   maplist(integer, Bs) ->
            maplist(char_code, Cs, Bs)
        ;   Bs = Cs
        ),
        must_be_octet_chars(Cs, crypto_encoding).
encoding_chars(utf8, Cs, Cs) :-
        must_be(chars, Cs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Digital signatures with Ed25519
   ===============================
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% ed25519_seed_keypair(+Seed, -Pair)
%
% Use Seed to deterministically generate an Ed25519 key pair Pair, a
% list of characters. Seed must be a list of 32 bytes.  It can be
% chosen at random (using for example `crypto_n_random_bytes/2`) or
% derived from input keying material (IKM) using for example
% `crypto_data_hkdf/4`.  The pair contains the private key and must be
% kept absolutely secret.  Pair can be used for signing. Its public
% key can be obtained with `ed25519_keypair_public_key/2`.

ed25519_seed_keypair(Seed, Pair) :-
        must_be_bytes(Seed, ed25519_keypair_from_seed/2),
        length(Seed, 32),
        '$ed25519_seed_to_public_key'(Seed, Public),
        maplist(char_code, Public, PublicBytes),
        phrase(ed25519_PKCS8v2(Seed,PublicBytes), DERs),
        maplist(char_code, Pair, DERs).

% DER (and hence BER) encoding of an Ed25519 private key and
% corresponding public key in PKCS#8v2 format (RFC 5958) as specified
% in RFC 8410.

ed25519_PKCS8v2(Seed, PublicBytes) -->
        [0x30,81],    % a SEQUENCE of 81 bytes follows

        % the publicKey is present, hence we set version to v2
        [2,1,1],      % the integer 1 denoting version 2 (awesome design!)

        % privateKeyAlgorithm: SEQUENCE
        [0x30,5],     % a SEQUENCE of 5 bytes follows
        [6,3],        % an OBJECT IDENTIFIER of 3 bytes follows
        [43,101,112], % OID of Ed25519

        % privateKey: OCTET STRING
        [4,34],       % an OCTET STRING of 34 bytes follows
        [4,32],       % an OCTET STRING of 32 bytes follows
        seq(Seed),    % the seed is the private key

        % publicKey: [1] IMPLICIT BIT STRING; context-specific, hence bit 7 set
        [0b10000001], % the public key follows
        [33],         % a BIT STRING of length 33 follows
        [0],          % 32 bytes is divisible by 8, hence 0 unused bits
        seq(PublicBytes).

%% ed25519_new_keypair(-Pair)
%
%  Yields a new Ed25519 key pair Pair, a list of characters. The
%  pair contains the private key and must be kept absolutely secret.
%  Pair can be used for signing. Its public key can be obtained
%  with `ed25519_keypair_public_key/2`.

ed25519_new_keypair(Pair) :-
        crypto_n_random_bytes(32, Bytes),
        ed25519_seed_keypair(Bytes, Pair).

%% ed25519_keypair_public_key(+Pair, -PublicKey)
%
%  PublicKey is the public key of the given key pair. The public key
%  can be used for signature verification, and can be shared freely.
%  The public key is represented as a list of characters.

ed25519_keypair_public_key(Pair, PublicKey) :-
        must_be_octet_chars(Pair, ed25519_keypair_public_key/2),
        reverse(Pair, RPs),
        length(RPublicKey, 32),
        phrase((seq(RPublicKey),...), RPs),
        reverse(RPublicKey, PublicKey).

%% ed25519_sign(+Key, +Data, -Signature, +Options)
%
%  Key and Data must be lists of characters. Key is a key pair in
%  PKCS#8 v2 format as generated by `ed25519_new_keypair/1`. Sign Data
%  with Key, yielding Signature as a list of hexadecimal characters.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Side-channel attacks on Ed25519 predicates
   ==========================================

   Ed25519 predicates where the private key occurs as part of the
   arguments are potentially subject to side-channel attacks, since
   key pairs are represented as strings in the context of Ed25519.

   The compact string representation used by Scryer Prolog means that
   different characters may occupy different numbers of bytes: Due
   to UTF-8 encoding, characters with codes 1..127 occupy exactly 1 byte,
   characters with codes 128..2047 occupy exactly 2 bytes, and '0'
   is represented as a list element occupying an entire cell and
   dedicated list constructor in addition to string termination and
   possibly padding.

   This difference is located at the level of the Rust engine. To
   Prolog code, any two characters look conceptually the same (i.e.,
   they are both atoms of length 1), and the internal difference in
   representation cannot be observed at all.

   Very precise timing information or other measurements about
   operations that reason about such strings may yield information
   that is meant to stay secret. For example, if Ks is a secret key
   stored as a list of characters, then the time it takes to run
   phrase(..., Ks) may reveal the number of bytes in Ks that are 0 or
   greater than 127.

   To test whether it is possible to detect such differences, I use
   exp(N) which succeeds exactly 2^N times:

        exp(E) :-
            N is 2^E,
            between(1, N, _).

   Here is an example query that uses partial_string/1 to traverse
   various strings consisting uniformly of characters with the same
   code, such as 0, 32, 255 and others, in the hope to detect
   differences in timing if only in such extreme cases:

        ?- length(Ls, 256),
           member(Code, [12,0,55,0,0,32,255,10,0,127,64]),
           portray_clause(byte=Code),
           maplist(=(Code), Ls),
           atom_codes(A, Ls),
           atom_chars(A, Cs),
           time((exp(21),partial_string(Cs),false)).
        %@ byte=12.
        %@    % CPU time: 1.537s, 14_680_107 inferences
        %@ byte=0.
        %@    % CPU time: 1.526s, 14_680_107 inferences
        %@ byte=55.
        %@    % CPU time: 1.534s, 14_680_107 inferences
        %@ byte=0.
        %@    % CPU time: 1.556s, 14_680_107 inferences
        %@ byte=0.
        %@    % CPU time: 1.520s, 14_680_107 inferences
        %@ byte=32.
        %@    % CPU time: 1.524s, 14_680_107 inferences
        %@ byte=255.
        %@    % CPU time: 1.522s, 14_680_107 inferences
        %@ byte=10.
        %@    % CPU time: 1.526s, 14_680_107 inferences
        %@ byte=0.
        %@    % CPU time: 1.522s, 14_680_107 inferences
        %@ byte=127.
        %@    % CPU time: 1.522s, 14_680_107 inferences
        %@ byte=64.
        %@    % CPU time: 1.517s, 14_680_107 inferences
        %@    false.

   This shows that there is enough variety between runs that
   traversing a list with 256 elements that are all '\x0\' may even,
   and unexpectedly, be faster than traversing a list consisting
   entirely of characters with character code 32, which in turn may be
   slower than processing a list with 256 characters that all have
   code 255 and thus occupy twice as much space. This holds even over
   millions of runs. Reasons for such variety can include CPU power
   saving mechanisms, dynamic optimizations, prefetching heuristics,
   branch prediction algorithms, varying system loads etc.

   This gives rise to the suspicion that any such timing differences
   would be extremely hard to exploit, at least on the architecture I
   tested it on, also since partial_string/1 is a very low-level
   operation and any actual processing (using phrase/2 etc.) would
   introduce additional overheads that in all likelihood far outweigh
   any differences that can be measured with partial_string/1.

   Any resulting differences in timing and resource use, if they are
   measurable at all in any way, can at most reveal one bit per byte.
   Note also that Ed25519 private keys are chosen randomly, and hence
   half of their bytes are expected to be in 128..255. The predicates
   remain completely safe to use in all scenarios where no information
   about the private key can be gathered by unauthorized parties.

   Still, the concern remains: We know that different keys may occupy
   different numbers of bytes in the internal compact representation
   of strings used by Scryer Prolog, and it may be possible to exploit
   these differences to obtain information that is meant to be kept
   secret. We must therefore keep an eye on this issue. For example,
   it may become a concern on very slow devices such as ID-cards where
   Scryer Prolog may be deployed in the future and where such timing
   differences may be detectable, or if Scryer Prolog itself becomes
   so fast that the relative overhead of such low-level operations
   becomes greater and thus more easily measurable.

   Possible mitigations in such situations would be to:

    1. use lists of integers to represent Ed25519 key pairs, resulting
       in a 24-fold space increase. This may be prohibitive in
       applications that manage a great number of keys. The Rust code
       would not be affected by this change, since it already operates
       on bytes. A Prolog application may implement this privately, and
       also encourage an API change of this library.
    2. introduce a compact internal representation for lists of bytes,
       which appear to Prolog programs as lists of characters.

   (2) seems to be the better solution despite the implementation
   overhead: In addition to the improved security properties due to
   the elimination of side-channel attacks when reasoning about keys,
   all applications that reason about binary data would benefit from a
   more compact representation of binary data. Such an additional
   compact representation should only be attempted if the amount of
   Rust code it impacts is kept to the absolute minimum, certainly
   much smaller than what the compact string representation as it is
   currently implemented affects.

   *No* solution would be to:

    - eliminate the compact string representation from the engine and
      use plain lists of characters to represent Ed25519 key pairs,
    - continue to use lists of characters for Ed25519 key pairs,
      and ensure that they are never coalesced into compact strings
      (a future GC compaction step may need to be adapted for this)

   This is because atom names are still represented in UTF-8 encoding,
   and are hence also susceptible to side-channel attacks due to their
   using different numbers of bytes for different codes.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

ed25519_sign(KeyPair, Data0, Signature, Options) :-
        must_be_octet_chars(KeyPair, ed25519_sign/4),
        length(Prefix, 16),
        length(PrivateKeyChars, 32),
        phrase((seq(Prefix),seq(PrivateKeyChars),...), KeyPair),
        maplist(char_code, PrivateKeyChars, PrivateKey),
        options_data_chars(Options, Data0, Data, Encoding),
        '$ed25519_sign_raw'(PrivateKey, Data, Encoding, Signature0),
        hex_bytes(Signature, Signature0).

%% ed25519_verify(+Key, +Data, +Signature, +Options)
%
%  Key and Data must be lists of characters. Key is a public key.
%  Succeeds if Data was signed with the private key corresponding to
%  Key, where Signature is a list of hexadecimal characters as
%  generated by `ed25519_sign/4`. Fails otherwise.
%
%  Currently, the only option for signing and verifying is:
%
%  - `encoding(+Encoding)`
%    The default encoding of Data is `utf8`. The alternative is `octet`,
%    to use the character code of each character in Data as a byte
%    value.

ed25519_verify(Key, Data0, Signature0, Options) :-
        must_be_octet_chars(Key, ed25519_verify/4),
        options_data_chars(Options, Data0, Data, Encoding),
        hex_bytes(Signature0, Signature),
        '$ed25519_verify_raw'(Key, Data, Encoding, Signature).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   X25519: ECDH key exchange over Curve25519
   =========================================
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% curve25519_generator(-Gs)
%
%  Points on Curve25519 are represented as lists of characters that
%  denote the u-coordinate of the Montgomery curve. Gs is the
%  generator point of Curve25519.

curve25519_generator(Gs) :-
        length(Gs0, 32),
        Gs0 = [9|Zs],
        maplist(=(0), Zs),
        maplist(char_code, Gs, Gs0).

%% curve25519_scalar_mult(+Scalar, +Ps, -Rs)
%
%  Scalar must be an integer between 0 and 2^256-1,
%  or a list of 32 bytes, and Ps must be a point on the curve.
%  Computes the point _Rs = Scalar*Ps as_ mandated by X25519.
%
%  Alice and Bob can use this to establish a shared secret as follows,
%  where Gs is the generator point of Curve25519:
%
%    1. Alice creates a random integer _a_ and sends _As = a*Gs_ to Bob.
%
%    2. Bob creates a random integer _b_ and sends _Bs = b*Gs_ to Alice.
%
%    3. Alice computes _Rs = a*Bs_.
%
%    4. Bob computes _Rs = b*As_.
%
%    5. Alice and Bob use `crypto_data_hkdf/4` on Rs with suitable
%       (same) parameters to obtain lists of bytes that can be used as
%       keys and initialization vectors for symmetric encryption.
%
%  If _a_ and _b_ are kept secret, this method is considered very secure.

curve25519_scalar_mult(Scalar, Point, Result) :-
        (   integer_si(Scalar) ->
            length(ScalarBytes, 32),
            bytes_integer(ScalarBytes, Scalar)
        ;   ScalarBytes = Scalar,
            must_be_bytes(ScalarBytes, curve25519_scalar_mult/3),
            length(ScalarBytes, 32)
        ),
        must_be(chars, Point),
        length(Point, 32),
        maplist(char_code, Point, PointBytes),
        '$curve25519_scalar_mult'(ScalarBytes, PointBytes, Result).

bytes_integer(Bs, N) :-
        foldl(pow, Bs, t(0,0,N), t(N,_,_)).

pow(B, t(N0,P0,I0), t(N,P,I)) :-
        (   integer(I0) ->
            B #= I0 mod 256,
            I #= I0 >> 8
        ;   true
        ),
        B in 0..255,
        N #= N0 + B*256^P0,
        P #= P0 + 1.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Operations on Elliptic Curves
   =============================

   Sample use: Establishing a shared secret S, using ECDH key exchange.

    ?- crypto_name_curve(secp256k1, C),
       crypto_curve_generator(C, Generator),
       PrivateKey = 10,
       crypto_curve_scalar_mult(C, PrivateKey, Generator, PublicKey),
       Random = 12,
       crypto_curve_scalar_mult(C, Random, Generator, R),
       crypto_curve_scalar_mult(C, Random, PublicKey, S),
       crypto_curve_scalar_mult(C, PrivateKey, R, S).

   For better security, new code should use Curve25519 instead.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   An elliptic curve over a prime field F_p is represented as:

   curve(Name,P,A,B,point(X,Y),Order,FieldLength,Cofactor).

   First, we define suitable accessors.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

curve_name(curve(Name,_,_,_,_,_,_,_), Name).
curve_p(curve(_,P,_,_,_,_,_,_), P).
curve_a(curve(_,_,A,_,_,_,_,_), A).
curve_b(curve(_,_,_,B,_,_,_,_), B).
curve_field_length(curve(_,_,_,_,_,_,FieldLength,_), FieldLength).

%% crypto_curve_generator(+Curve, -G)
%
%  Yields the generator point G of Curve.

crypto_curve_generator(curve(_,_,_,_,G,_,_,_), G).

%% crypto_curve_order(+Curve, -Order)
%
%  Yields the order of Curve.

crypto_curve_order(curve(_,_,_,_,_,Order,_,_), Order).

%% crypto_curve_scalar_mult(+Curve, +Scalar, +Point, -Result)
%
%  Computes the point _Result = Scalar*Point_. Scalar must be an
%  integer, and Point must be a point on Curve. This operation can be
%  used to negotiate a shared secret over a public channel. Consider
%  using `curve25519_scalar_mult/3` instead for more desirable
%  security properties.

crypto_curve_scalar_mult(Curve, Scalar, point(X,Y), point(RX, RY)) :-
        must_be(integer, Scalar),
        must_be_on_curve(Curve, point(X,Y)),
        curve_name(Curve, Name),
        curve_field_length(Curve, L0),
        L #= 2*L0, % for hex encoding
        phrase(format_("04~|~`0t~16r~*+~`0t~16r~*+", [X,L,Y,L]), PointHex),
        hex_bytes(PointHex, PointBytes),
        once(bytes_integer(ScalarBytes, Scalar)),
        '$crypto_curve_scalar_mult'(Name, ScalarBytes, PointBytes, [_|Us]),
        maplist(char_code, Us, Bs),
        length(XBs, 32),
        append(XBs, YBs, Bs),
        maplist(reverse, [XBs,YBs], RBs),
        maplist(bytes_integer, RBs, [RX,RY]).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- crypto_name_curve(secp256k1, Curve),
   crypto_curve_generator(Curve, G),
   crypto_curve_scalar_mult(Curve, 2, G, R).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

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
        domain_error(point_on_curve, P, crypto_elliptic_curves).
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

   The field length depends on the order of the curve and can be computed
   with order_field_length/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

order_field_length(Order, L) :-
        fitting_exponent(Order, 0, E),
        L #= (E + 7) // 8.

fitting_exponent(N, E0, E) :-
        (   2^E0 #>= N -> E #= E0
        ;   E1 #= E0 + 1,
            fitting_exponent(N, E1, E)
        ).

%% crypto_name_curve(+Name, -Curve)
%
%  Yields a representation of the elliptic curve with name Name.
%  Currently, the only supported name is `secp256k1`, a Koblitz curve
%  regarded as secure.

crypto_name_curve(secp256k1,
                  curve(secp256k1,
                        0x00fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f,
                        0x0,
                        0x7,
                        point(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
                              0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8),
                        0x00fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141,
                        32,
                        1)).
