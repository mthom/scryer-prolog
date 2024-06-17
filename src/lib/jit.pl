:- module(jit, [jit_compile/1]).

jit_compile(Clause) :-
    (  nonvar(Clause) ->
       (  Clause = Name / Arity ->
	  '$jit_compile'(user, Name, Arity)
       ;  Clause = Module : (Name / Arity) ->
	  '$jit_compile'(Module, Name, Arity)
       )
    ;  throw(error(instantiation_error, jit_compile/1))
    ).
