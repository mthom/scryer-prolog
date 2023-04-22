:- module(diag, [wam_instructions/2, inlined_instructions/2]).

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

  `inlined_instructions/2` decompiles predicates at the code offset in
  its first argument.

  For example, given the program

```
?- [user].
:- use_module(library(clpz)).

all_eq(Vs, E) :- maplist(#=(E), Vs).

```

  we inspect the code of `all_eqs/2` using `wam_instructions/2`,
  revealing:

```
?- wam_instructions(all_eq/2, Is),
   maplist(portray_clause, Is).
put_structure('$aux',2,x(3)).
set_local_value(x(2)).
set_void(1).
set_constant('$index_ptr'(115334)).
get_variable(x(4),1).
put_structure(:,2,x(1)).
set_constant(user).
set_local_value(x(3)).
get_variable(x(5),2).
put_value(x(4),2).
execute(maplist,2).
   Is = [put_structure('$aux',2,x(3)),set_local_value(x(2)),set_void(1),set_constant('$index_ptr'(115334)),get_variable(x(4),1),put_structure(:,2,x(1)),set_constant(user),set_local_value(x(3)),get_variable(x(5),2),put_value(x(4),2),execute(maplist,2)].
```

  The `'$index_ptr(115334)` functor gives a code offset to an inlined
  predicate compiled for the use of maplist/2. `inlined_instructions/2`
  can be used to decompile its source code:

```
?- inlined_instructions(115334, Is),
   maplist(portray_clause, Is).
allocate(1).
get_level(y(1)).
get_variable(x(5),2).
put_value(x(3),2).
get_variable(x(6),3).
put_value(x(5),3).
put_unsafe_value(1,4).
deallocate.
jmp_by_execute(1).
try_me_else(8).
call(integer,1).
neck_cut.
get_variable(x(5),1).
put_value(x(2),1).
get_variable(x(6),2).
put_value(x(5),2).
jmp_by_execute(7).
try_me_else(12).
allocate(3).
get_level(y(1)).
get_variable(y(3),1).
get_variable(y(2),2).
call_default(true,0).
call(var,1).
cut(y(1)).
put_unsafe_value(3,1).
put_unsafe_value(2,2).
deallocate.
execute_default(is,2).
default_retry_me_else(4).
call(integer,1).
neck_cut.
execute(=:=,2).
default_trust_me(0).
allocate(2).
get_variable(y(1),1).
get_variable(y(2),3).
put_value(y(2),1).
call_default(is,2).
put_unsafe_value(2,1).
put_unsafe_value(1,2).
deallocate.
execute_default(clpz_equal,2).
default_retry_me_else(4).
call(integer,1).
neck_cut.
jmp_by_execute(29).
try_me_else(12).
allocate(3).
get_level(y(1)).
get_variable(y(3),1).
get_variable(y(2),2).
call_default(true,0).
call(var,1).
cut(y(1)).
put_unsafe_value(3,1).
put_unsafe_value(2,2).
deallocate.
execute_default(is,2).
default_trust_me(0).
allocate(2).
get_variable(y(2),1).
get_variable(y(1),3).
put_value(y(1),1).
call_default(is,2).
put_unsafe_value(2,1).
put_unsafe_value(1,2).
deallocate.
execute_default(clpz_equal,2).
default_trust_me(0).
execute_default(clpz_equal,2).
   Is = [allocate(1),get_level(y(1)),get_variable(x(5),2),put_value(x(3),2),get_variable(x(6),3),put_value(x(5),3),put_unsafe_value(1,4),deallocate,jmp_by_execute(1),try_me_else(8),call(integer,1),neck_cut,get_variable(x(5),1),put_value(x(2),1),get_variable(x(6),2),put_value(x(5),2),jmp_by_execute(7),try_me_else(12),allocate(3),get_level(...),...].
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

%% inlined_instructions(+IndexPtr, -Instrs)
%
%  _Instrs_ are the WAM instructions corresponding to code offset _IndexPtr_.

inlined_instructions(IndexPtr, Listing) :-
    must_be(integer, IndexPtr),
    (  IndexPtr >= 0 ->
       '$inlined_instructions'(IndexPtr, Listing)
    ;  throw(error(domain_error(not_less_than_zero, IndexPtr), inlined_instructions/2))
    ).

fetch_instructions(Module, Name, Arity, Listing) :-
    must_be(atom, Module),
    must_be(atom, Name),
    must_be(integer, Arity),
    (  Arity >= 0 ->
       '$wam_instructions'(Module, Name, Arity, Listing)
    ;  throw(error(domain_error(not_less_than_zero, Arity), wam_instructions/2))
    ).
