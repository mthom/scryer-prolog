:- module(charsio, [char_type/2,
                    chars_utf8bytes/2,
                    get_single_char/1,
                    read_line_to_chars/3,
                    read_term_from_chars/2,
                    write_term_to_chars/3,
                    chars_base64/3,
                    abnf_alpha//1,
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

:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(lists)).

fabricate_var_name(VarType, VarName, N) :-
    char_code('A', AC),
    LN is N mod 26 + AC,
    char_code(LC, LN),
    NN is N // 26,
    (  NN =:= 0 ->
       (  VarType == fabricated ->
          atom_chars(VarName, ['_', LC])
       ;  VarType == numbervars ->
          atom_chars(VarName, [LC])
       )
    ;  number_chars(NN, NNChars),
       (  VarType == fabricated ->
          atom_chars(VarName, ['_', LC | NNChars])
       ;  VarType == numbervars ->
          atom_chars(VarName, [LC | NNChars])
       )
    ).

var_list_contains_name([VarName = _ | VarList], VarName0) :-
    (  VarName == VarName0 -> true
    ;  var_list_contains_name(VarList, VarName0)
    ).

var_list_contains_variable([_ = Var | VarList], Var0) :-
    (  Var == Var0 -> true
    ;  var_list_contains_variable(VarList, Var0)
    ).

make_new_var_name(VarType, V, VarName, N, N1, VarList) :-
    fabricate_var_name(VarType, VarName0, N),
    (  var_list_contains_name(VarList, VarName0) ->
       N0 is N + 1,
       make_new_var_name(VarType, V, VarName, N0, N1, VarList)
    ;  VarName = VarName0,
       N1 is N + 1
    ).

extend_var_list(Vars, VarList, NewVarList, VarType) :-
    extend_var_list_(Vars, 0, VarList, NewVarList0, VarType),
    append(VarList, NewVarList0, NewVarList).

extend_var_list_([], _, _, [], _).
extend_var_list_([V|Vs], N, VarList, NewVarList, VarType) :-
    (  var_list_contains_variable(VarList, V) ->
       extend_var_list_(Vs, N, VarList, NewVarList, VarType)
    ;  make_new_var_name(VarType, V, VarName, N, N1, VarList),
       NewVarList = [VarName = V | NewVarList0],
       extend_var_list_(Vs, N1, VarList, NewVarList0, VarType)
    ).


char_type(Char, Type) :-
    (   var(Char) -> instantiation_error(char_type/2)
    ;   atom_length(Char, 1) ->
        (   ground(Type) ->
            (   ctype(Type) ->
                '$char_type'(Char, Type)
            ;   domain_error(char_type, Type, char_type/2)
            )
        ;   ctype(Type),
            '$char_type'(Char, Type)
        )
    ;   type_error(in_character, Char, char_type/2)
    ).


ctype(alnum).
ctype(alpha).
ctype(alphabetic).
ctype(alphanumeric).
ctype(ascii).
ctype(ascii_graphic).
ctype(ascii_punctuation).
ctype(binary_digit).
ctype(control).
ctype(decimal_digit).
ctype(exponent).
ctype(graphic).
ctype(graphic_token).
ctype(hexadecimal_digit).
ctype(layout).
ctype(lower).
ctype(meta).
ctype(numeric).
ctype(octal_digit).
ctype(octet).
ctype(prolog).
ctype(sign).
ctype(solo).
ctype(symbolic_control).
ctype(symbolic_hexadecimal).
ctype(upper).
ctype(whitespace).


get_single_char(C) :-
    (  var(C) -> '$get_single_char'(C)
    ;  atom_length(C, 1) -> '$get_single_char'(C)
    ;  type_error(in_character, C, get_single_char/1)
    ).


read_term_from_chars(Chars, Term) :-
    (  var(Chars) ->
       instantiation_error(read_term_from_chars/2)
    ;  nonvar(Term) ->
       throw(error(uninstantiation_error(Term), read_term_from_chars/2))
    ;  '$skip_max_list'(_, -1, Chars, Chars0),
       Chars0 == [],
       partial_string(Chars) ->
       true
    ;
       type_error(complete_string, Chars, read_term_from_chars/2)
    ),
    '$read_term_from_chars'(Chars, Term).


write_term_to_chars(_, Options, _) :-
    var(Options), instantiation_error(write_term_to_chars/3).
write_term_to_chars(Term, Options, Chars) :-
    builtins:parse_write_options(Options,
                                 [IgnoreOps, MaxDepth, NumberVars, Quoted, VNNames],
                                 write_term_to_chars/3),
    (  nonvar(Chars)  ->
       throw(error(uninstantiation_error(Chars), write_term_to_chars/3))
    ;
       true
    ),
    term_variables(Term, Vars),
    extend_var_list(Vars, VNNames, NewVarNames, numbervars),
    '$write_term_to_chars'(Chars, Term, IgnoreOps, NumberVars, Quoted, NewVarNames, MaxDepth).

% Encodes Ch character to list of Bytes.
char_utf8bytes(Ch, Bytes) :-
  char_code(Ch, Code),
  phrase(code_to_utf8(Code), Bytes).

code_to_utf8(Code) --> {Code @< 0x80},     [Code], !.
code_to_utf8(Code) --> {Code @< 0x800},    encode(Code, 0xC0, 2), !.
code_to_utf8(Code) --> {Code @< 0x10000},  encode(Code, 0xE0, 3), !.
code_to_utf8(Code) --> {Code @< 0x110000}, encode(Code, 0xF0, 4), !.

encode(_, _, 0) --> !.
encode(Code, Prefix, Nb) -->
  { Nb1 is Nb - 1, Byte is Prefix \/ ((Code >> (6 * Nb1)) /\ 0x3F) },
  [Byte], encode(Code, 0x80, Nb1).

% Maps characters and UTF-8 bytes.
% If Cs is a variable, parses Bs as a list of UTF-8 bytes.
% Otherwise, transform the list of characters Cs to UTF-8 bytes.
chars_utf8bytes(Cs, Bs) :-
  var(Cs), must_be(list, Bs) ->
    once(phrase(decode_utf8(Cs), Bs))
  ; (must_be(list, Cs),
     maplist(must_be(atom), Cs),
     maplist(char_utf8bytes, Cs, Bss),
     append(Bss, Bs)).

decode_utf8([]) --> [].
decode_utf8(Chars) --> leading(Nb, Code), continuation(Code, Chars, Nb).

leading(1, Byte) --> [Byte], {Byte /\ 0x80 =:= 0}.
leading(2, Code) --> [Byte], {Byte /\ 0xE0 =:= 0xC0, Code is Byte - 0xC0}.
leading(3, Code) --> [Byte], {Byte /\ 0xF0 =:= 0xE0, Code is Byte - 0xE0}.
leading(4, Code) --> [Byte], {Byte /\ 0xF8 =:= 0xF0, Code is Byte - 0xF0}.
leading(1, 0xFFFD) --> [_]. % invalid first byte

continuation(Code, [H|T], 1) --> {char_code(H, Code)}, decode_utf8(T).
continuation(Code, Chars, Nb) --> [Byte],
  {Nb1 is Nb - 1, Byte /\ 0xC0 =:= 0x80, NextCode is (Code << 6) \/ (Byte - 0x80)},
  continuation(NextCode, Chars, Nb1).

% invalid continuation byte
% each remaining continuation byte (if any) will raise 0xFFFD too
continuation(_, ['\xFFFD\'|T], _) --> [_], decode_utf8(T).


read_line_to_chars(Stream, Cs0, Cs) :-
        '$get_n_chars'(Stream, 1, Char), % this also works for binary streams
        (   Char == [] -> Cs0 = Cs
        ;   Char = [C],
            Cs0 = [C|Rest],
            (   C == '\n' -> Rest = Cs
            ;   read_line_to_chars(Stream, Rest, Cs)
            )
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Relation between a list of characters Cs and its Base64 encoding Bs,
   also a list of characters.

   At least one of the arguments must be instantiated.

   Options are:

      - padding(Boolean)
        Whether to use padding: true (the default) or false.
      - charset(C)
        Either 'standard' (RFC 4648 §4, the default) or 'url' (RFC 4648 §5).

   Example:

      ?- chars_base64("hello", Bs, []).
         Bs = "aGVsbG8=".
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

chars_base64(Cs, Bs, Options) :-
        must_be(list, Options),
        (   member(O, Options), var(O) ->
            instantiation_error(chars_base64/3)
        ;   (   member(padding(Padding), Options) -> true
            ;   Padding = true
            ),
            (   member(charset(Charset), Options) -> true
            ;   Charset = standard
            )
        ),
        must_be(boolean, Padding),
        must_be(atom, Charset),
        (   member(Charset, [standard,url]) -> true
        ;   domain_error(charset, Charset, chars_base64/3)
        ),
        (   var(Cs) ->
            must_be(list, Bs),
            maplist(must_be(character), Bs),
            '$chars_base64'(Cs, Bs, Padding, Charset)
        ;   must_be(list, Cs),
            maplist(must_be(character), Cs),
            '$chars_base64'(Cs, Bs, Padding, Charset)
        ).

/*  [Core Rules](https://tools.ietf.org/html/rfc5234#appendix-B.1) of the
    Augmented Backus-Naur Form specification (ABNF - RFC 5234). ABNF commonly
    serves as the definition language for IETF communication protocols, so
    having these DCGs can be extremely useful for reasoning about most IETF
    syntaxes. The DCGs are presented in the order they appear in the RFC.
    While some DCGs below use `char_type/2`, the most common ones are defined
    manually in order to take advantage of Prolog's first-argument indexing. */
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

abnf_bit(0) --> "0".
abnf_bit(1) --> "1".

abnf_char(C) --> [C], { dif(C, '\x0000\'), char_type(C, ascii) }. %'

abnf_cr --> "\r".

abnf_crlf --> "\r\n".

abnf_ctl(C) --> [C], { char_type(C, ascii), char_type(C, control) }.

abnf_digit(0) --> "0".
abnf_digit(1) --> "1".
abnf_digit(2) --> "2".
abnf_digit(3) --> "3".
abnf_digit(4) --> "4".
abnf_digit(5) --> "5".
abnf_digit(6) --> "6".
abnf_digit(7) --> "7".
abnf_digit(8) --> "8".
abnf_digit(9) --> "9".

abnf_dquote --> "\"".

abnf_hexdig(Digit) --> abnf_digit(Digit).
abnf_hexdig(10) --> "A".
abnf_hexdig(11) --> "B".
abnf_hexdig(12) --> "C".
abnf_hexdig(13) --> "D".
abnf_hexdig(14) --> "E".
abnf_hexdig(15) --> "F".

abnf_htab --> "\t".

abnf_lf --> "\n".

abnf_lwsp --> "".
abnf_lwsp --> abnf_wsp, abnf_lwsp.
abnf_lwsp --> abnf_clrf, abnf_wsp, abnf_lwsp.

abnf_octet(C) --> [C], char_type(C, octet).

abnf_sp --> " ".

abnf_vchar(C) --> [C], char_type(C, ascii_graphic).

abnf_wsp --> abnf_sp.
abnf_wsp --> abnf_htab.
