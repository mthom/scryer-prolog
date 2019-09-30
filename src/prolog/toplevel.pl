/* 
 *  inserting the modules should not result in the insertion of
 *  code. this is because they're already loaded by this point -- see
 *  Machine::new.
*/

:- use_module(library(lists)).
:- use_module(library(si)).

'$repl'(ListOfModules) :-
    maplist('$use_list_of_modules', ListOfModules),
    false.
'$repl'(_) :- '$repl'.

'$use_list_of_modules'(Module) :-
    catch(use_module(Module), E, '$print_exception'(E)).

'$repl' :-
    catch('$read_and_match', E, '$print_exception'(E)),
    false. %% this is for GC, until we get actual GC.
'$repl' :- '$repl'.

'$read_and_match' :-
    '$read_query_term'(Term, VarList),
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

'$predicate_indicator'(Source, PI) :-
    (  nonvar(PI) ->
       (  PI = Name / Arity ->
	  (  var(Name) -> throw(error(instantiation_error, Source))
	  ;  integer(Arity) ->
	     (  \+ atom(Name) -> throw(error(type_error(atom, Name), Source))
	     ;  Arity < 0 -> throw(error(domain_error(not_less_than_zero, Arity), Source))
	     ;  true
	     )
	  ;  throw(error(type_error(integer, Arity), Source))
	  )
       ;  throw(error(type_error(predicate_indicator, PI), Source))
       )
    ;  throw(error(instantiation_error, Source))
    ).

use_module(Module) :-
    (  nonvar(Module) ->
       (  Module = library(Filename) -> '$use_module'(Filename)
       ;  atom(Module) -> '$use_module_from_file'(Module)
       ;  throw(error(invalid_module_specifier, use_module/1))
       )
    ;  throw(error(instantiation_error, use_module/1))
    ).

use_module(Module, QualifiedExports) :-
    (  nonvar(Module) ->
       (  list_si(QualifiedExports) ->
	  maplist('$predicate_indicator'(use_module/2), QualifiedExports), !,
	  (  Module = library(Filename) -> '$use_qualified_module'(Filename, QualifiedExports)
	  ;  atom(Module) -> '$use_qualified_module_from_file'(Module, QualifiedExports)
	  ;  throw(error(invalid_module_specifier, use_module/2))
	  )
       ;  throw(error(type_error(list, QualifiedExports), use_module/2))
       )
    ;  throw(error(instantiation_error, use_module/2))
    ).
