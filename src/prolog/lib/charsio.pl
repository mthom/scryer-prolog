:- module(charsio, [write_term_to_chars/3]).

write_term_to_chars(_, Options, _) :-
    var(Options), throw(error(instantiation_error, write_term_to_chars/3)).
write_term_to_chars(Term, Options, Chars) :-
    '$skip_max_list'(_, -1, Options, Options0),
    (  var(Options0)  ->
       throw(error(instantiation_error, write_term_to_chars/3))
    ;  var(Term) ->
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
