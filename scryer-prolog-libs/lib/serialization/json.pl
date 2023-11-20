/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written Apr 2021 by Aram Panasenco (panasenco@ucla.edu)
   Part of Scryer Prolog.

   `json_chars//1` can be used with [`phrase_from_file/2`](src/lib/pio.pl)
   or [`phrase/2`](src/lib/dcgs.pl) to parse and generate [JSON](https://www.json.org/json-en.html).

   BSD 3-Clause License

   Copyright (c) 2021, Aram Panasenco
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:

   * Redistributions of source code must retain the above copyright notice, this
     list of conditions and the following disclaimer.

   * Redistributions in binary form must reproduce the above copyright notice,
     this list of conditions and the following disclaimer in the documentation
     and/or other materials provided with the distribution.

   * Neither the name of the copyright holder nor the names of its
     contributors may be used to endorse or promote products derived from
     this software without specific prior written permission.

   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
   FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
   DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
   SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
   CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
   OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(json, [
                 json_chars//1
                ]).

:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(lists)).

/*  The DCGs are written to match the McKeeman form presented on the right side of https://www.json.org/json-en.html
    as closely as possible. Note that the names in the McKeeman form conflict with the pictures on the site. */
json_chars(Internal) --> json_element(Internal).

/*  Because it's impossible to distinguish between an empty array [] and an empty string "", we distinguish between
    different types of values based on their principal functor. The principal functors match the types defined in
    the JSON Schema spec here: https://json-schema.org/draft/2020-12/json-schema-validation.html#rfc.section.6.1.1
    EXCEPT we don't yet support the integer type. There are plans for more JSON Schema support in the near future. */
json_value(pairs(Pairs))    --> json_object(Pairs).
json_value(list(List))      --> json_array(List).
json_value(string(Chars))   --> json_string(Chars).
json_value(number(Number))  --> json_number(Number).
json_value(boolean(Bool))   --> json_boolean(Bool).
json_value(null)            --> "null".

/*  We pull json_boolean out into its own predicate in order to take advantage of first argument indexing and not leave
    choice points. For more details, watch this video on decomposing arguments: https://youtu.be/FZLofckPu4A?t=1648 */
json_boolean(true) --> "true".
json_boolean(false) --> "false".

json_object([])           --> "{", json_ws, "}".
json_object([Pair|Pairs]) -->
        "{",
        json_members(Pairs, Pair),
        "}".

/*  `json_members//2` below is implemented with a lagged argument to take advantage of first argument indexing.
    This is a pure performance-driven decision that doesn't affect the logic. The predicate could equivalently be
    implementes as `json_members//1` below:
    ```
    json_members([Key-Value, Pair2 | Pairs]) --> json_member(Key, Value), ",", json_members([Pair2 | Pairs]).
    ```
    That's a logically equivalent and equally clean representation to the lagged argument. However, it leaves
    choice points, while using the lagged argument doesn't. For more info, watch: https://youtu.be/FZLofckPu4A?t=1737
    */
json_members([], Key-Value)               --> json_member(Key, Value).
json_members([NextPair|Pairs], Key-Value) -->
        json_member(Key, Value),
        ",",
        json_members(Pairs, NextPair).

json_member(string(Key), Value) --> json_ws, json_string(Key), json_ws, ":", json_element(Value).

json_array([])             --> "[", json_ws, "]".
json_array([Value|Values]) --> "[", json_elements(Values, Value), "]".

/* Also using a lagged argument with `json_elements//2` to take advantage of first-argument indexing */
json_elements([], Value)                 --> json_element(Value).
json_elements([NextValue|Values], Value) -->
        json_element(Value),
        ",",
        json_elements(Values, NextValue).

json_element(Value) --> json_ws, json_value(Value), json_ws.

json_string(Chars) --> "\"", json_characters(Chars), "\"".

json_characters("")           --> "".
json_characters([Char|Chars]) --> json_character(Char), json_characters(Chars).

/*  Note on variable instantiation checks (`var/1` and `nonvar/1`) used below and in Prolog in general.
    Instantiation checks should never be used to change the logic of your program. Instead, they are one of
    many tools to adjust the 'control' or 'search strategy' used by Prolog to execute the logic of your program.
    For a general overview of the idea, read Bob Kowalski's "Algorithm = Logic + Control":
    https://www.doc.ic.ac.uk/~rak/papers/algorithm%20=%20logic%20+%20control.pdf
    For an introduction to search strategies in Prolog, read: https://www.metalevel.at/prolog/sorting#searching
    It's tempting to use instantiation checks to be more strict while generating and more relaxed while parsing.
    In fact, the early version of this library aimed to return exactly one result when generating. However, doing that
    is **wrong** and leads to difficult-to-catch bugs. Instead, adjust the search strategy to return the most ideal
    and strictest answer FIRST and then return less ideal answers on backtracking.
    As an example, consider a string containing just the forward slash. The JSON standard recommends the forward slash
    be escaped with a backslash, but allows it to not be escaped. Attempting to force stricter behavior with
    instantiation checks can lead to this confusing mess:
    ```
    phrase(json:json_characters("/"), External).
       External = "\\/".
    ?- phrase(json:json_characters(Internal), "/").
       Internal = "/"
    ;  false.
    ?- phrase(json:json_characters("/"), "/").
    false.
    ```
    To avoid such bugs, never use instantiation checks to reduce the number of right answers, but rather to adjust
    the *path* used to traverse those answers. */

escape_char('"', '"').
escape_char('\\', '\\').
escape_char('/', '/').
escape_char('\b', 'b').
escape_char('\f', 'f').
escape_char('\n', 'n').
escape_char('\r', 'r').
escape_char('\t', 't').

json_character(EscapeChar) -->
        { escape_char(EscapeChar, PrintChar) },
        "\\",
        [PrintChar].
json_character(PrintChar)  -->
    [PrintChar],
    { dif(PrintChar, '\\'),
      dif(PrintChar, '"'),
      char_code(PrintChar, PrintCharCode),
      PrintCharCode >= 32 }.
json_character(EscapeChar) -->
        "\\u",
        json_hex(H1),
        json_hex(H2),
        json_hex(H3),
        json_hex(H4),
        { (   nonvar(H1) ->
              EscapeCharCode is H1 * 16^3 + H2 * 16^2 + H3 * 16 + H4,
              char_code(EscapeChar, EscapeCharCode)
          ;   char_code(EscapeChar, EscapeCharCode),
              H1 is (EscapeCharCode // 16^3) mod 16,
              H2 is (EscapeCharCode // 16^2) mod 16,
              H3 is (EscapeCharCode // 16^1) mod 16,
              H4 is (EscapeCharCode // 16^0) mod 16
          ) }.

json_hex(Digit) --> json_digit(Digit).
json_hex(10)    --> "a".
json_hex(11)    --> "b".
json_hex(12)    --> "c".
json_hex(13)    --> "d".
json_hex(14)    --> "e".
json_hex(15)    --> "f".
json_hex(10)    --> "A".
json_hex(11)    --> "B".
json_hex(12)    --> "C".
json_hex(13)    --> "D".
json_hex(14)    --> "E".
json_hex(15)    --> "F".

/*  I can't think of any alternatives to using `number_chars/2` when generating, though this leads
    to under-reporting of correct solutions. At least matching solutions unify when both are instantiated...
    ```
    ?- phrase(json:json_number(N), "123E2").
       N = 12300
    ;  false.
    ?- phrase(json:json_number(12300), Cs).
       Cs = "12300".
    ?- phrase(json:json_number(12300), "123E2").
       true
    ;  false.
    ```
*/
parsing, [C] --> [C], { nonvar(C) }.

json_number(Number) -->
        (   parsing ->
            json_sign_noplus(Sign),
            json_integer(Integer),
            json_fraction(Fraction),
            json_exponent(Exponent),
            { (   Exponent >= 0 ->
                  Base = 10
              ;   Base = 10.0
              ),
              Number is Sign * (Integer + Fraction) * Base ^ Exponent }
        ;   { number_chars(Number, NumberChars) },
            NumberChars
        ).

json_integer(Digit)      --> json_digit(Digit).
json_integer(TotalValue) -->
        json_onenine(FirstDigit),
        json_digits(RemainingValue, Power),
        { TotalValue is FirstDigit * 10 ^ (Power + 1) + RemainingValue }.

json_digits(Digit, 0)     --> json_digit(Digit).
json_digits(Value, Power) -->
        json_digit(FirstDigit),
        json_digits(RemainingValue, NextPower),
        { Power is NextPower + 1,
          Value is FirstDigit * 10^Power + RemainingValue }.

json_digit(0)     --> "0".
json_digit(Digit) --> json_onenine(Digit).

json_onenine(1) --> "1".
json_onenine(2) --> "2".
json_onenine(3) --> "3".
json_onenine(4) --> "4".
json_onenine(5) --> "5".
json_onenine(6) --> "6".
json_onenine(7) --> "7".
json_onenine(8) --> "8".
json_onenine(9) --> "9".

json_fraction(0)        --> "".
json_fraction(Fraction) -->
        ".",
        json_digits(Value, Power),
        { Fraction is Value / 10.0 ^ (Power + 1) }.

json_exponent(0)        --> "".
json_exponent(Exponent) -->
        json_exponent_signifier,
        json_sign(Sign),
        json_digits(Value, _),
        { Exponent is Sign * Value }.

json_exponent_signifier --> "E".
json_exponent_signifier --> "e".

json_sign_noplus(1)  --> "".
json_sign_noplus(-1) --> "-".

json_sign(Sign) --> json_sign_noplus(Sign).
json_sign(1)    --> "+".

/* Make `json_ws/0` greedy when parsing, lazy when generating */
json_ws_empty --> "".
json_ws_nonempty --> " ".
json_ws_nonempty --> "\n".
json_ws_nonempty --> "\r".
json_ws_nonempty --> "\t".
json_ws_greedy --> json_ws_nonempty, json_ws_greedy.
json_ws_greedy --> json_ws_empty.
json_ws_lazy --> json_ws_empty.
json_ws_lazy --> json_ws_nonempty, json_ws_lazy.
json_ws -->
        (   parsing ->
            json_ws_greedy
        ;   json_ws_lazy
        ).
