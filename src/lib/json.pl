/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written Apr 2021 by Aram Panasenco (panasenco@ucla.edu)
   Part of Scryer Prolog.
   
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

:- use_module(library(assoc)).
:- use_module(library(between)).
:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(reif)).

/*  The DCGs are written to match the McKeeman form presented on the right side of https://www.json.org/json-en.html 
    as closely as possible. Note that the names in the McKeeman form conflict with the pictures on the site. */
json_chars(Internal) --> json_element(Internal).

/*  Because it's impossible to distinguish between an empty array [] and an empty string "", we distinguish between
    different types of values based on their principal functor. The principal functors match the types defined in
    the JSON Schema spec here: https://json-schema.org/draft/2020-12/json-schema-validation.html#rfc.section.6.1.1
    EXCEPT we don't yet support the integer type. There are plans for more JSON Schema support in the near future. */
json_value(object(Assoc))   --> json_object(Assoc).
json_value(array(List))     --> json_array(List).
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
    json_members([Key-Value])                --> json_member(Key, Value).
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

json_member(Key, Value) --> json_ws, json_string(Key), json_ws, ":", json_element(Value).

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

letter_escape('"', '"').
letter_escape('\\', '\\').
letter_escape('/', '/').
letter_escape('\b', 'b').
letter_escape('\f', 'f').
letter_escape('\n', 'n').
letter_escape('\r', 'r').
letter_escape('\t', 't').

/*  Note on variable instantiation checks (`var/1` and `nonvar/1`) used below and in Prolog in general.
    Instantiation checks should ideally never be used to change the logic of your program. Instead, they are one of
    many tools to adjust the 'control' or 'search strategy' used by Prolog to execute the logic of your program.
    For a general overview of the idea, read Bob Kowalski's "Algorithm = Logic + Control":
    https://www.doc.ic.ac.uk/~rak/papers/algorithm%20=%20logic%20+%20control.pdf
    For an introduction to search strategies in Prolog, read: https://www.metalevel.at/prolog/sorting#searching
    However, when dealing with a real-world data format standard, real differences arise in how a string should be
    parsed vs generated. Usually, parsing should allow multiple ways of doing things, while generating should only
    happen in one best way.
    JSON characters are parsed/generated in one of three ways:
    1.  Directly. All characters in the range 20.10FFFF, except '"' and '\\' must be generated and parsed directly,
        escape for the forward slash '/', which must not be generated directly, but can be parsed directly.
    2.  Backslash followed by a single special character defined in the escape map - both parsing and generating.
    3.  Backslash followed by 'u' and 4 hex values defining the character code of the internal character.
        When generating, only allow range 0.20 excepting characters in the escape map.
        When parsing, allow any value.
    In order to take advantage of first argument indexing, we must reify this distinction in a single predicate. */
json_character(InternalChar) -->
        { (   nonvar(InternalChar) ->
              (   letter_escape(InternalChar, _) ->
                  Type = letter_escape
              ;   char_code(InternalChar, InternalCharCode),
                  (   InternalCharCode >= 32 ->
                      Type = direct
                  ;   Type = hex_escape
                  )
              )
          ;   true
          ) },
          json_character(Type, InternalChar).

json_character(direct, PrintChar)  --> [PrintChar].
json_character(letter_escape, EscapeChar) -->
        { letter_escape(EscapeChar, PrintChar) },
        "\\",
        [PrintChar].
json_character(hex_escape, EscapeChar) -->
        "\\u",
        { (   nonvar(EscapeChar) ->
              char_code(EscapeChar, EscapeCharCode),
              H1 = 0,
              H2 = 0,
              H3 is EscapeCharCode // 16,
              H4 is EscapeCharCode mod 16
          ;   true
          ) },
        json_hex(H1),
        json_hex(H2),
        json_hex(H3),
        json_hex(H4),
        { (   var(EscapeChar) ->
              EscapeCharCode is H1 * 16^3 + H2 * 16^2 + H3 * 16 + H4,
              char_code(EscapeChar, EscapeCharCode)
          ;   true
          ) }.

json_hex(Value) -->
    { (   nonvar(Value) ->
          (   between(0, 9, Value) ->
              Code is Value + 48
          ;   (   between(10, 15, Value) ->
                  Code is Value + 87
              ;   false
              )
          ),
          char_code(Char, Code)
      ;   true
      )
    },
    [Char],
    { (   var(Value) ->
          char_code(Char, Code),
          (   between(48, 57, Code) ->
              Value is Code - 48
          ;   (   between(65, 70, Code) ->
                  Value is Code - 55
              ;   (   between(97, 102, Code) ->
                      Value is Code - 87
                  ;   false
                  )
              )
          )
      ;   true
      ) }.

/*  Here we are going to simply rely on `number_chars/2` when generating. */
json_number(Number) -->
        (   { nonvar(Number) } ->
            { number_chars(Number, NumberChars) },
            NumberChars
        ;   json_sign_noplus(Sign),
            json_integer(Integer),
            json_fraction(Fraction),
            json_exponent(Exponent),
            { (   Exponent >= 0 ->
                  Base = 10
              ;   Base = 10.0
              ),
              Number is Sign * (Integer + Fraction) * Base ^ Exponent }
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

json_onenine(1) --> "1".
json_onenine(2) --> "2".
json_onenine(3) --> "3".
json_onenine(4) --> "4".
json_onenine(5) --> "5".
json_onenine(6) --> "6".
json_onenine(7) --> "7".
json_onenine(8) --> "8".
json_onenine(9) --> "9".

json_digit(0) --> "0".
json_digit(1) --> "1".
json_digit(2) --> "2".
json_digit(3) --> "3".
json_digit(4) --> "4".
json_digit(5) --> "5".
json_digit(6) --> "6".
json_digit(7) --> "7".
json_digit(8) --> "8".
json_digit(9) --> "9".

json_fraction(0)        --> "".
json_fraction(Fraction) -->
    ".",
    json_digits(Value, Power),
    { Fraction is Value / 10 ^ (Power + 1) }.

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

/* Make sure json_ws doesn't attempt to generate whitespace and succeeds without choicepoints when generating */
json_ws --> [C], {nonvar(C), member(C, " \n\r\t")}, json_ws.
json_ws --> "".
