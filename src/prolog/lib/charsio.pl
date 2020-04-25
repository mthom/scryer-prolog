:- module(charsio, [char_type/2, get_single_char/1,
                    read_term_from_chars/2,
                    write_term_to_chars/3]).

:- use_module(library(iso_ext)).


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

extend_var_list(Value, VarList, NewVarList, VarType) :-
    term_variables(Value, Vars),
    extend_var_list_(Vars, 0, VarList, NewVarList, VarType).

extend_var_list_([], _, VarList, VarList, _).
extend_var_list_([V|Vs], N, VarList, NewVarList, VarType) :-
    (  var_list_contains_variable(VarList, V) ->
       extend_var_list_(Vs, N, VarList, NewVarList, VarType)
    ;  make_new_var_name(VarType, V, VarName, N, N1, VarList),
       NewVarList = [VarName = V | NewVarList0],
       extend_var_list_(Vs, N1, VarList, NewVarList0, VarType)
    ).


char_type(Char, Type) :-
    (   var(Char) -> throw(error(instantiation_error, char_type/2))
    ;   atom_length(Char, 1) ->
        (   ground(Type) -> '$char_type'(Char, Type)
        ;   Type = symbolic_control, '$char_type'(Char, Type)
        ;   Type = layout, '$char_type'(Char, Type)
        ;   Type = symbolic_hexadecimal, Char = x
        ;   Type = octal_digit, '$char_type'(Char, Type)
        ;   Type = binary_digit, '$char_type'(Char, Type)
        ;   Type = hexadecimal_digit, '$char_type'(Char, Type)
        ;   Type = exponent, '$char_type'(Char, Type)
        ;   Type = sign, '$char_type'(Char, Type)
        ;   Type = upper, '$char_type'(Char, Type)
        ;   Type = lower, '$char_type'(Char, Type)
        ;   Type = graphic, '$char_type'(Char, Type)
        ;   Type = alpha, '$char_type'(Char, Type)
        ;   Type = decimal_digit, '$char_type'(Char, Type)
        ;   Type = alnum, '$char_type'(Char, Type)
        ;   Type = meta, '$char_type'(Char, Type)
        ;   Type = solo, '$char_type'(Char, Type)
        ;   Type = prolog, '$char_type'(Char, Type)
        ;   Type = alphabetic, '$char_type'(Char, Type)
        ;   Type = whitespace, '$char_type'(Char, Type)
        ;   Type = control, '$char_type'(Char, Type)
        ;   Type = numeric, '$char_type'(Char, Type)
        ;   Type = ascii, '$char_type'(Char, Type)
        ;   Type = ascii_punctuation, '$char_type'(Char, Type)
        ;   Type = ascii_graphic, '$char_type'(Char, Type)
        )
    ;   throw(error(type_error(in_character, Char), char_type/2))
    ).


get_single_char(C) :-
    (  var(C) -> '$get_single_char'(C)
    ;  atom_length(C, 1) -> '$get_single_char'(C)
    ;  throw(error(type_error(in_character, C), get_single_char/1))
    ).


read_term_from_chars(Chars, Term) :-
    (  var(Chars) ->
       throw(error(instantiation_error, read_term_from_chars/2))
    ;  nonvar(Term) ->
       throw(error(uninstantiation_error(Term), read_term_from_chars/2))
    ;  '$skip_max_list'(_, -1, Chars, Chars0),
       Chars0 == [],
       partial_string(Chars) ->
       true
    ;
       throw(error(type_error(complete_string, Chars), read_term_from_chars/2))
    ),
    '$read_term_from_chars'(Chars, Term).


write_term_to_chars(_, Options, _) :-
    var(Options), throw(error(instantiation_error, write_term_to_chars/3)).
write_term_to_chars(Term, Options, Chars) :-
    '$skip_max_list'(_, -1, Options, Options0),
    (  var(Options0)  ->
       throw(error(instantiation_error, write_term_to_chars/3))
    ;  nonvar(Chars)  ->
       throw(error(uninstantiation_error(Chars), write_term_to_chars/3))
    ;  Options0 == [] ->
       true
    ;
       throw(error(type_error(list, Options), write_term_to_chars/3))
    ),
    builtins:inst_member_or(Options, ignore_ops(IgnoreOps), ignore_ops(false)),
    builtins:inst_member_or(Options, numbervars(NumberVars), numbervars(false)),
    builtins:inst_member_or(Options, quoted(Quoted), quoted(false)),
    builtins:inst_member_or(Options, variable_names(VarNames), variable_names([])),
    builtins:inst_member_or(Options, max_depth(MaxDepth), max_depth(0)),
    extend_var_list(Term, VarNames, NewVarNames, numbervars),
    '$write_term_to_chars'(Term, IgnoreOps, NumberVars, Quoted, NewVarNames, MaxDepth, Chars).
