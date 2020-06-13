:- module(diag, [wam_instructions/2]).

:- use_module(library(error)).

wam_instructions(Clause, Listing) :-
    (  nonvar(Clause) ->
       Clause = Name / Arity,
       must_be(atom, Name),
       must_be(integer, Arity),
       (  Arity >= 0 -> '$wam_instructions'(Name, Arity, Listing)
       ;  throw(error(domain_error(not_less_than_zero, Arity), wam_instructions/2))
       )
    ;  throw(error(instantiation_error, wam_instructions/2))
    ).
