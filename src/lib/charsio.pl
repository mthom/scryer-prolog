/** High-level predicates to work with chars and strings

This module contains predicates that relates strings of chars
to other representations, as well as high-level predicates to
read and write chars.

*/

:- module(charsio, [char_type/2,
                    chars_utf8bytes/2,
                    get_single_char/1,
                    get_n_chars/3,
                    get_line_to_chars/3,
                    read_from_chars/2,
                    write_term_to_chars/3,
                    chars_base64/3]).

:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(iso_ext), [partial_string/1,partial_string/3]).

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


%% char_type(+Char, -Type).
%
% Given a Char, Type is one of the categories that char fits in.
% Possible categories are:
%
% - `alnum`
% - `alpha`
% - `alphabetic`
% - `alphanumeric`
% - `ascii`
% - `ascii_graphic`
% - `ascii_punctuation`
% - `binary_digit`
% - `control`
% - `decimal_digit`
% - `exponent`
% - `graphic`
% - `graphic_token`
% - `hexadecimal_digit`
% - `layout`
% - `lower`
% - `meta`
% - `numeric`
% - `octal_digit`
% - `octet`
% - `prolog`
% - `sign`
% - `solo`
% - `symbolic_control`
% - `symbolic_hexadecimal`
% - `upper`
% - `to_lower(Lower)`
% - `to_upper(Upper)`
% - `whitespace`
%
% An example:
%
% ```
% ?- char_type(a, Type).
%    Type = alnum
% ;  Type = alpha
% ;  Type = alphabetic
% ;  Type = alphanumeric
% ;  Type = ascii
% ;  Type = ascii_graphic
% ;  Type = hexadecimal_digit
% ;  Type = lower
% ;  Type = octet
% ;  Type = prolog
% ;  Type = symbolic_control
% ;  Type = to_lower("a")
% ;  Type = to_upper("A")
% ;  false.
% ```
%
% Note that uppercase and lowercase transformations use a string. This is because
% some characters do not map 1:1 between lowercase and uppercase.
char_type(Char, Type) :-
        must_be(character, Char),
        (   ground(Type) ->
            (   ctype(Type) ->
                '$char_type'(Char, Type)
            ;   domain_error(char_type, Type, char_type/2)
            )
        ;   ctype(Type),
            '$char_type'(Char, Type)
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
ctype(to_lower(_)).
ctype(to_upper(_)).
ctype(upper).
ctype(whitespace).


%% get_single_char(-Char).
%
% Gets a single char from the current input stream.
get_single_char(C) :-
    (  var(C) -> '$get_single_char'(C)
    ;  atom_length(C, 1) -> '$get_single_char'(C)
    ;  type_error(in_character, C, get_single_char/1)
    ).

%% read_from_chars(+Chars, -Term).
%
% Given a string made of chars which contains a representation of
% a Prolog term, Term is the Prolog term represented. Example:
%
% ```
% ?- read_from_chars("f(x,y).", X).
%    X = f(x,y).
% ```
read_from_chars(Chars, Term) :-
    must_be(chars, Chars),
    must_be(var, Term),
    '$read_term_from_chars'(Chars, Term).

%% write_term_to_chars(+Term, +Options, -Chars).
%
% Given a Term which is a Prolog term and a set of options, Chars is
% string representation of that term. Options available are:
%
%  * `ignore_ops(+Boolean)` if `true`, the generic term representation is used everywhere. In `false`
%    (default), operators do not use that generic term representation.
%  * `max_depth(+N)` if the term is nested deeper than N, print the reminder as ellipses.
%    If N = 0 (default), there's no limit.
%  * `numbervars(+Boolean)` if true, replaces `$VAR(N)` variables with letters, in order. Default is false.
%  * `quoted(+Boolean)` if true, strings and atoms that need quotes to be valid Prolog syntax, are quoted. Default is false.
%  * `variable_names(+List)` assign names to variables in term. List should be a list of terms of format `Name=Var`.
%  * `double_quotes(+Boolean)` if true, strings are printed in double quotes rather than with list notation. Default is false.
write_term_to_chars(_, Options, _) :-
    var(Options), instantiation_error(write_term_to_chars/3).
write_term_to_chars(Term, Options, Chars) :-
    builtins:parse_write_options(Options,
                                 [DoubleQuotes, IgnoreOps, MaxDepth, NumberVars, Quoted, VNNames],
                                 write_term_to_chars/3),
    (  nonvar(Chars)  ->
       throw(error(uninstantiation_error(Chars), write_term_to_chars/3))
    ;
       true
    ),
    term_variables(Term, Vars),
    extend_var_list(Vars, VNNames, NewVarNames, numbervars),
    '$write_term_to_chars'(Chars, Term, IgnoreOps, NumberVars, Quoted, NewVarNames, MaxDepth, DoubleQuotes).

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

%% chars_utf8bytes(?Chars, ?Bytes).
%
% Maps a string made of chars with a list of UTF-8 bytes. Some examples:
%
% ```
% ?- chars_utf8bytes("Prolog", X).
%   X = [80,114,111,108,111,103].
% ?- chars_utf8bytes(X, [226, 136, 145]).
%    X = "∑".
% ```
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

%% get_line_to_chars(+Stream, -Chars, +InitialChars).
%
% Reads chars from stream Stream until it finds a `\n` character.
% InitialChars will be appended at the end of Chars
get_line_to_chars(Stream, Cs0, Cs) :-
        '$get_n_chars'(Stream, 1, Char), % this also works for binary streams
        (   Char == [] -> Cs0 = Cs
        ;   Char = [C],
            Cs0 = [C|Rest],
            (   C == '\n' -> Rest = Cs
            ;   get_line_to_chars(Stream, Rest, Cs)
            )
        ).

%% get_n_chars(+Stream, ?N, -Chars).
%
% Read N chars from stream Stream. N can be an integer, in that case
% only N chars are read, or a variable, unifying N with the number of chars
% read until it found EOF.
get_n_chars(Stream, N, Cs) :-
        can_be(integer, N),
        (   var(N) ->
            get_to_eof(Stream, Cs),
            length(Cs, N)
        ;   N >= 0,
            '$get_n_chars'(Stream, N, Cs)
        ).

get_to_eof(Stream, Cs) :-
        '$get_n_chars'(Stream, 512, Cs0),
        (   Cs0 == [] -> Cs = []
        ;   partial_string(Cs0, Cs, Rest),
            get_to_eof(Stream, Rest)
        ).

%% chars_base64(?Chars, ?Base64, +Options).
%
% Relation between a list of characters Cs and its Base64 encoding Bs,
% also a list of characters.
%
% At least one of the arguments must be instantiated.
%
% Options are:
%
% - `padding(Boolean)`
%   Whether to use padding: true (the default) or false.
% - `charset(C)`
%   Either 'standard' (RFC 4648 §4, the default) or 'url' (RFC 4648 §5).
%
% Example:
%
% ```
% ?- chars_base64("hello", Bs, []).
%    Bs = "aGVsbG8=".
% ```

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
            must_be(chars, Bs),
            '$chars_base64'(Cs, Bs, Padding, Charset)
        ;   must_be(chars, Cs),
            (   '$first_non_octet'(Cs, N) ->
                domain_error(octet_character, N, chars_base64/3)
            ;   '$chars_base64'(Cs, Bs, Padding, Charset)
            )
        ).
