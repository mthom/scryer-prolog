:- module(charsio, [read_term_from_chars/2,
                    write_term_to_chars/3]).

:- use_module(library(iso_ext)).


fabricate_var_name(VarName, N) :-
    char_code('A', AC),
    LN is N mod 26 + AC,
    char_code(LC, LN),
    NN is N // 26,
    (  NN =:= 0 ->
       atom_chars(VarName, ['_', LC])
    ;  number_chars(NN, NNChars),
       atom_chars(VarName, ['_', LC | NNChars])
    ).

var_list_contains_name([VarName = _ | VarList], VarName0) :-
    (  VarName == VarName0 -> true
    ;  var_list_contains_name(VarList, VarName0)
    ).

var_list_contains_variable([_ = Var | VarList], Var0) :-
    (  Var == Var0 -> true
    ;  var_list_contains_variable(VarList, Var0)
    ).

make_new_var_name(V, VarName, N, N1, VarList) :-
    fabricate_var_name(VarName0, N),
    (  var_list_contains_name(VarList, VarName0) ->
       N0 is N + 1,
       make_new_var_name(V, VarName, N0, N1, VarList)
    ;  VarName = VarName0,
       N1 is N + 1
    ).

extend_var_list(Value, VarList, NewVarList) :-
    term_variables(Value, Vars),
    extend_var_list_(Vars, 0, VarList, NewVarList).

extend_var_list_([], N, VarList, VarList).
extend_var_list_([V|Vs], N, VarList, NewVarList) :-
    (  var_list_contains_variable(VarList, V) ->
       extend_var_list_(Vs, N, VarList, NewVarList)
    ;  make_new_var_name(V, VarName, N, N1, VarList),
       NewVarList = [VarName = V | NewVarList0],
       extend_var_list_(Vs, N1, VarList, NewVarList0)
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
    extend_var_list(Term, VarNames, NewVarNames),
    '$write_term_to_chars'(Term, IgnoreOps, NumberVars, Quoted, NewVarNames, MaxDepth, Chars).
