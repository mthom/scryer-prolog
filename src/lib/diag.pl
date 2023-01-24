:- module(diag, [wam_instructions/2]).

/** Diagnostics library

  The predicate `wam_instructions/2` _decompiles_ a predicate so that
  we can inspect its Warren Abstract Machine (WAM) instructions.
  In this way, we can verify and reason about compiled programs,
  and detect opportunities for optimization.

  For example, we have:

```
?- use_module(library(lists)).
   true.
?- use_module(library(diag)).
   true.
?- use_module(library(format)).
   true.
?- wam_instructions(append/3, Is),
   maplist(portray_clause, Is).
switch_on_term(1,external(1),external(2),external(6),fail).
try_me_else(4).
get_constant(level(shallow),[],x(1)).
get_value(x(2),3).
proceed.
trust_me(0).
get_list(level(shallow),x(1)).
unify_variable(x(4)).
unify_variable(x(1)).
get_list(level(shallow),x(3)).
unify_value(x(4)).
unify_variable(x(3)).
execute(append,3).
   Is = [switch_on_term(1,external(1),external(2),external(6),fail)|...].
```
*/


:- use_module(library(error)).

%% wam_instructions(+PI, -Instrs)
%
%  _Instrs_ are the WAM instructions corresponding to predicate indicator _PI_.

wam_instructions(Clause, Listing) :-
    (  nonvar(Clause) ->
       (  Clause = Name / Arity ->
          fetch_instructions(user, Name, Arity, Listing)
       ;  Clause = Module : (Name / Arity) ->
          fetch_instructions(Module, Name, Arity, Listing)
       )
    ;  throw(error(instantiation_error, wam_instructions/2))
    ).


fetch_instructions(Module, Name, Arity, Listing) :-
    must_be(atom, Module),
    must_be(atom, Name),
    must_be(integer, Arity),
    (  Arity >= 0 ->
       '$wam_instructions'(Module, Name, Arity, Listing)
    ;  throw(error(domain_error(not_less_than_zero, Arity), wam_instructions/2))
    ).
