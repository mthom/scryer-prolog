/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written Apr 2021 by Aram Panasenco (panasenco@ucla.edu)
   Part of Scryer Prolog.

   [Core Rules](https://tools.ietf.org/html/rfc5234#appendix-B.1) of the
   Augmented Backus-Naur Form specification (ABNF - RFC 5234). ABNF commonly
   serves as the definition language for IETF communication protocols, so
   having these DCGs can be extremely useful for reasoning about most IETF
   syntaxes. The DCGs are presented in the order they appear in the RFC.
   While some DCGs below use `char_type/2`, the most common ones are defined
   manually in order to take advantage of Prolog's first-argument indexing.

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

:- module(abnf, [abnf_alpha//1,
                 abnf_bit//1,
                 abnf_char//1,
                 abnf_cr//0,
                 abnf_crlf//0,
                 abnf_ctl//1,
                 abnf_digit//1,
                 abnf_dquote//0,
                 abnf_hexdig//1,
                 abnf_htab//0,
                 abnf_lf//0,
                 abnf_lwsp//0,
                 abnf_octet//1,
                 abnf_sp//0,
                 abnf_vchar//1,
                 abnf_wsp//0 ]).

:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(lists)).

abnf_alpha('a') --> "a".
abnf_alpha('b') --> "b".
abnf_alpha('c') --> "c".
abnf_alpha('d') --> "d".
abnf_alpha('e') --> "e".
abnf_alpha('f') --> "f".
abnf_alpha('g') --> "g".
abnf_alpha('h') --> "h".
abnf_alpha('i') --> "i".
abnf_alpha('j') --> "j".
abnf_alpha('k') --> "k".
abnf_alpha('l') --> "l".
abnf_alpha('m') --> "m".
abnf_alpha('n') --> "n".
abnf_alpha('o') --> "o".
abnf_alpha('p') --> "p".
abnf_alpha('q') --> "q".
abnf_alpha('r') --> "r".
abnf_alpha('s') --> "s".
abnf_alpha('t') --> "t".
abnf_alpha('u') --> "u".
abnf_alpha('v') --> "v".
abnf_alpha('w') --> "w".
abnf_alpha('x') --> "x".
abnf_alpha('y') --> "y".
abnf_alpha('z') --> "z".
abnf_alpha('A') --> "A".
abnf_alpha('B') --> "B".
abnf_alpha('C') --> "C".
abnf_alpha('D') --> "D".
abnf_alpha('E') --> "E".
abnf_alpha('F') --> "F".
abnf_alpha('G') --> "G".
abnf_alpha('H') --> "H".
abnf_alpha('I') --> "I".
abnf_alpha('J') --> "J".
abnf_alpha('K') --> "K".
abnf_alpha('L') --> "L".
abnf_alpha('M') --> "M".
abnf_alpha('N') --> "N".
abnf_alpha('O') --> "O".
abnf_alpha('P') --> "P".
abnf_alpha('Q') --> "Q".
abnf_alpha('R') --> "R".
abnf_alpha('S') --> "S".
abnf_alpha('T') --> "T".
abnf_alpha('U') --> "U".
abnf_alpha('V') --> "V".
abnf_alpha('W') --> "W".
abnf_alpha('X') --> "X".
abnf_alpha('Y') --> "Y".
abnf_alpha('Z') --> "Z".

abnf_bit('0') --> "0".
abnf_bit('1') --> "1".

abnf_char(Char) --> [Char], { dif(Char, '\x0000\'), char_type(Char, ascii) }. %'

abnf_cr --> "\r".

abnf_crlf --> "\r\n".

abnf_ctl(Char) --> [Char], { char_type(Char, ascii), char_type(Char, control) }.

abnf_digit('0') --> "0".
abnf_digit('1') --> "1".
abnf_digit('2') --> "2".
abnf_digit('3') --> "3".
abnf_digit('4') --> "4".
abnf_digit('5') --> "5".
abnf_digit('6') --> "6".
abnf_digit('7') --> "7".
abnf_digit('8') --> "8".
abnf_digit('9') --> "9".

abnf_dquote --> "\"".

abnf_hexdig(Char) --> abnf_digit(Char).
abnf_hexdig('A') --> "A".
abnf_hexdig('B') --> "B".
abnf_hexdig('C') --> "C".
abnf_hexdig('D') --> "D".
abnf_hexdig('E') --> "E".
abnf_hexdig('F') --> "F".

abnf_htab --> "\t".

abnf_lf --> "\n".

abnf_lwsp --> "".
abnf_lwsp --> abnf_wsp, abnf_lwsp.
abnf_lwsp --> abnf_crlf, abnf_wsp, abnf_lwsp.

abnf_octet(Char) --> [Char], char_type(Char, octet).

abnf_sp --> " ".

abnf_vchar(Char) --> [Char], char_type(Char, ascii_graphic).

abnf_wsp --> abnf_sp.
abnf_wsp --> abnf_htab.
