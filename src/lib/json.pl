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
                 json_whitespace//0,
                 json_string//1
                ]).

:- use_module(library(charsio)).
:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(error)).
:- use_module(library(lists)).

char_uniontypes(Char, Types) :-
    must_be(list, Types),
    bagof(Type, (char_type(Char, Type), member(Type, Types)), [_|_]).

json_whitespace --> "".
json_whitespace --> " ", json_whitespace.
json_whitespace --> "\n", json_whitespace.
json_whitespace --> "\r", json_whitespace.
json_whitespace --> "\t", json_whitespace.

escape_map([
    '"' - '"',
    ('\\') - ('\\'),
    ('/') - ('/'),
    '\b' - 'b',
    '\f' - 'f',
    '\n' - 'n',
    '\r' - 'r',
    '\t' - 't'
]).

hex(0) --> "0".
hex(1) --> "1".
hex(2) --> "2".
hex(3) --> "3".
hex(4) --> "4".
hex(5) --> "5".
hex(6) --> "6".
hex(7) --> "7".
hex(8) --> "8".
hex(9) --> "9".
hex(10) --> "a".
hex(11) --> "b".
hex(12) --> "c".
hex(13) --> "d".
hex(14) --> "e".
hex(15) --> "f".

inner_string("") --> "".
inner_string([PrintChar | Tail]) -->
    [PrintChar],
    {
        escape_map(EscapeMap),
        \+ member(PrintChar-_, EscapeMap),
        (
            PrintChar = ' '
            ; char_uniontypes(PrintChar, [alphanumeric, ascii_graphic])
        )
    },
    inner_string(Tail).
inner_string([EscapeChar | Tail]) -->
    "\\",
    [PrintChar],
    {
        escape_map(EscapeMap),
        member(EscapeChar-PrintChar, EscapeMap)
    },
    inner_string(Tail).
inner_string([NonPrintChar | Tail]) -->
    "\\u",
    {
        [H1, H2, H3, H4] ins 0..15,
        NonPrintCharCode in 0..65535,
        NonPrintCharCode #= H1 * 16^3 + H2 * 16^2 + H3 * 16 + H4,
        (
            ground(NonPrintChar) ->
            escape_map(EscapeMap),
            \+ member(NonPrintChar-_, EscapeMap),
            dif(NonPrintChar, ' '),
            \+ char_uniontypes(NonPrintChar, [alphanumeric, ascii_graphic]),
            char_code(NonPrintChar, NonPrintCharCode)
            ; true
        )
    },
    hex(H1),
    hex(H2),
    hex(H3),
    hex(H4),
    {
        \+ ground(NonPrintChar) ->
        char_code(NonPrintChar, NonPrintCharCode)
        ; true
    },
    inner_string(Tail).

json_string(Inner) --> "\"", inner_string(Inner), "\"".
