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
:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(reif)).

/*  The DCGs are written to match the McKeeman form presented on the right side of https://www.json.org/json-en.html 
    almost perfectly. Note that the McKeeman form conflicts some with the pictures on the left side. */
json_chars(Internal) --> json_element(Internal).

/*  Because it's impossible to distinguish between an empty array [] and an empty string "", we distinguish between
    different types of values based on their principal functor. The principal functors match the types defined in
    the JSON Schema spec here: https://json-schema.org/draft/2020-12/json-schema-validation.html#rfc.section.6.1.1
    Down the line we'll incorporate more JSON Schema support, but this is it for now. */
json_value(object(Assoc))   --> json_object(Assoc).
json_value(array(List))     --> json_array(List).
json_value(string(Chars))   --> json_string(Chars).
json_value(number(Number))  --> json_number(Number).
json_value(boolean(true))   --> "true".
json_value(boolean(false))  --> "false".
json_value(null)            --> "null".

/*  Note on variable instantiation checks (`var/1` and `nonvar/1`) used below and in Prolog in general.
    Instantiation checks should never ever be used to change the logic of your program! Instead, they are one of
    many tools to adjust the 'control' or 'search strategy' used by Prolog to execute the logic of your program.
    Control tweaks are used for the following:
    - Prevent instantiation errors.
    - Prevent nontermination.
    - Improve the time complexity of execution (e.g. from superexponential to linear).
    For a general overview of the idea, read Bob Kowalski's "Algorithm = Logic + Control":
    https://www.doc.ic.ac.uk/~rak/papers/algorithm%20=%20logic%20+%20control.pdf
    For an introduction to search strategies in Prolog, read: https://www.metalevel.at/prolog/sorting#searching
    This DCG definition does two things:
    1.  Logic: Relate an association list to a JSON object serialized in a string.
    2.  Control: Define the exact strategy by which we obtain an association list from a JSON string and vice versa.
        This is done via instantiation checks `var/1` and `nonvar/1`.
    Unfortunately, the logic and control in this DCG aren't separated cleanly like Bob Kowalski proposed.
    Maybe at some point in the future we'll have a library that takes a pure logic character parsing/generating DCG
    and 'injects' control strategy into it. We aren't there yet... */
json_object(EmptyAssoc) --> {empty_assoc(EmptyAssoc)}, "{", json_ws, "}".
json_object(Assoc)      -->
        { (   nonvar(Assoc) ->
              \+ empty_assoc(Assoc),
              assoc_to_list(Assoc, [Pair|Pairs])
          ;   true
          ) },
        "{",
        json_members([Pair|Pairs]),
        "}",
        { (   var(Assoc) ->
              list_to_assoc([Pair|Pairs], Assoc)
          ;   true
          ) }.


/*  Why have both `json_members//1` and `json_members_//2`? Wouldn't it be less confusing to have just
    `json_members//1`?
    In fact in the first version of the code there was just this simple definition of `json_members//1`:
    ```
    json_members([Key-Value])         --> json_member(Key, Value).
    json_members([Key-Value | Pairs]) --> json_member(Key, Value), ",", json_members(Pairs).
    ```
    The problem with this definition was that there's no way for Prolog to distinguish between the two DCG heads,
    because [Key-Value] unifies with [Key-Value|[]], which unifies with [Key-Value|Pairs].
    Therefore, such a representation is defaulty, and is actually misleading because when you look at it you think
    that a list with only one pair would apply to only the first definition, but it actually applies to both!
    For more info on clean vs defaulty representations, read: https://www.metalevel.at/prolog/data#clean
    The below definition, while longer, cleanly distinguishes member lists with just one value from member lists
    with two or more values.
    */
json_members([Pair|Pairs]) --> json_members_(Pairs, Pair).

json_members_([], Key-Value)               --> json_member(Key, Value).
json_members_([NextPair|Pairs], Key-Value) -->
        json_member(Key, Value),
        ",",
        json_members_(Pairs, NextPair).

json_member(Key, Value) --> json_ws, json_string(Key), json_ws, ":", json_element(Value).

json_array([])             --> "[", json_ws, "]".
json_array([Value|Values]) --> "[", json_elements([Value|Values]), "]".

json_elements([Value|Values]) --> json_elements_(Values, Value).

json_elements_([], Value)                 --> json_element(Value).
json_elements_([NextValue|Values], Value) -->
        json_element(Value),
        ",",
        json_elements_(Values, NextValue).

json_element(Value) --> json_ws, json_value(Value), json_ws.

json_string(Chars) --> "\"", json_characters(Chars), "\"".

json_characters("")           --> "".
json_characters([Char|Chars]) --> json_character(Char), json_characters(Chars).

/*  A directly printable character is defined by the JSON spec as a character between 0020 and 10FFFF except the
    escaped characters.
    Note that `char_code/2` throws an instantiation error if both its arguments are undefined, so we delay
    calling it until we've seen both the generating and the parsing sides of the DCG.
    If we moved the block containing `char_code/2` up before `[PrintChar]`, we would still be able to generate JSON,
    but attempting to parse JSON would cause an instantiation error. */
escape_map([
        '"' - '"',
        ('\\') - ('\\'),
        ('/') - ('/'),
        '\b' - 'b',
        '\f' - 'f',
        '\n' - 'n',
        '\r' - 'r',
        '\t' - 't' ]).

json_character(PrintChar)  -->
        [PrintChar],
        { escape_map(EscapeMap),
          \+ member(PrintChar-_, EscapeMap),
          char_code(PrintChar, PrintCharCode),
          PrintCharCode in 32..1114111 /* 20.10FFFF */ }.
json_character(EscapeChar) --> "\\", json_escape(EscapeChar).

json_escape(EscapeChar) -->
        [PrintChar],
        { escape_map(EscapeMap),
          member(EscapeChar-PrintChar, EscapeMap) }.
json_escape(EscapeChar) -->
        "u",
        /*  Logic: Define the domain of the escape character as well as the relationship between the escape character
            and the four hexes */
        { [H1, H2, H3, H4] ins 0..15,
          EscapeCharCode in 0..65535,
          EscapeCharCode #= H1 * 16^3 + H2 * 16^2 + H3 * 16 + H4,
          /*  Control: Get the code of the escape character if we can. Otherwise we'll end up backtracking over 65,536
              possible hex values. 
              Logic: Only the first 32 Unicode characters not escaped in the escape map are eligible for \u-escaping
              when generating. However, we want to be able to parse any of the 65,536 \u-escaped values when parsing. */
          (   nonvar(EscapeChar) ->
              char_code(EscapeChar, EscapeCharCode),
              EscapeCharCode in 0..31,
              escape_map(EscapeMap),
              \+ member(EscapeChar-_, EscapeMap)
          ;   true
          )
        },
        json_hex(H1),
        json_hex(H2),
        json_hex(H3),
        json_hex(H4),
        /*  Control + Logic: Get the escape character atom from the character code computed from the hexes. */
        { (   var(EscapeChar) ->
              char_code(EscapeChar, EscapeCharCode)
          ;   true
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

/*  Here we are going to write completely different DCGs for parsing and generating, and rely on built-in
    predicates. However, the underlying logic remains the same. */
json_number(Number) -->
    { (   nonvar(Number) ->
          number_chars(Number, NumberChars)
      ;   false
      ) },
    NumberChars.
json_number(Number) -->
    { var(Number) },
    json_sign_noplus(Sign),
    json_integer(Integer),
    json_fraction(Fraction),
    json_exponent(Exponent),
    { Number is Sign * (Integer + Fraction) * 10.0 ^ Exponent }.

json_integer(Digit)      --> json_digit(Digit).
json_integer(TotalValue) -->
    json_onenine(FirstDigit),
    json_digits(RemainingValue, Power),
    { TotalValue #= FirstDigit * 10 ^ (Power + 1) + RemainingValue }.

json_digits(Digit, 0)     --> json_digit(Digit).
json_digits(Value, Power) -->
    json_digit(FirstDigit),
    json_digits(RemainingValue, NextPower),
    { Power #= NextPower + 1,
      Value #= FirstDigit * 10^Power + RemainingValue }.

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
    { Fraction is Value / 10 ^ (Power + 1) }.

json_exponent(0)        --> "".
json_exponent(Exponent) -->
    json_exponent_signifier,
    json_sign(Sign),
    json_digits(Value, _),
    { Exponent #= Sign * Value }.

json_exponent_signifier --> "E".
json_exponent_signifier --> "e".

json_sign_noplus(1)  --> "".
json_sign_noplus(-1) --> "-".

json_sign(Sign) --> json_sign_noplus(Sign).
json_sign(1)    --> "+".

json_ws --> "".
json_ws --> " ", json_ws.
json_ws --> "\n", json_ws.
json_ws --> "\r", json_ws.
json_ws --> "\t", json_ws.
