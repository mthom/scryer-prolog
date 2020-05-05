:- module(charsio, [char_type/2, get_single_char/1,
                    read_term_from_chars/2,
                    write_term_to_chars/3]).

:- use_module(library(iso_ext)).
:- use_module(library(error)).
:- use_module(library(lists), [append/3]).

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

extend_var_list_([], _, VarList, [], _).
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
ctype(ascii).
ctype(ascii_graphic).
ctype(ascii_punctuation).
ctype(binary_digit).
ctype(control).
ctype(decimal_digit).
ctype(exponent).
ctype(graphic).
ctype(hexadecimal_digit).
ctype(layout).
ctype(lower).
ctype(meta).
ctype(numeric).
ctype(octal_digit).
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
    extend_var_list(Vars, VarNames, NewVarNames, numbervars),
    '$write_term_to_chars'(Chars, Term, IgnoreOps, NumberVars, Quoted, NewVarNames, MaxDepth).
