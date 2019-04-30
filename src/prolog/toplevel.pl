repl :-
    catch(read_and_match, E, '$print_exception'(E)),
    false. %% this is for GC, until we get actual GC.
repl :- repl.
    
read_and_match :-
    write_term('?- ', [quoted(false)]),
    read_term(Term, [variable_names(VarList)]),
    '$instruction_match'(Term, VarList).

'$instruction_match'([user], []) :-
    !, '$compile_batch'.
'$instruction_match'(Term, VarList) :-
    '$submit_query_and_print_results'(Term, VarList),
    !.

'$print_exception'(E) :-
    write_term('caught: ', [quoted(false)]),
    writeq(E),
    nl.
