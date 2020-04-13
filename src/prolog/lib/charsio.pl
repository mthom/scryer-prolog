:- module(charsio, [read_term_from_chars/2,
                    write_term_to_chars/3]).

:- use_module(library(iso_ext)).

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
    '$write_term_to_chars'(Term, IgnoreOps, NumberVars, Quoted, VarNames, MaxDepth, Chars).
