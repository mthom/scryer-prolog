:- module(atts, [op(1199, fx, attribute),
                 term_attributed_variables/2]).

:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(terms)).

/* represent the list of attributes belonging to a variable,
   of a particular module, as a list of terms of the form
   Module:put_atts(V, ListOfAtts). */
'$default_attr_list'(Module, V) -->
    (  { Module:get_atts(V, Attributes) } ->
       '$default_attr_list'(Attributes, Module, V)
    ;  []
    ).

'$default_attr_list'([PG | PGs], Module, AttrVar) -->
    [Module:put_atts(AttrVar, PG)],
    '$default_attr_list'(PGs, Module, AttrVar).
'$default_attr_list'([], _, _) --> [].

'$absent_attr'(V, Module, Attr) :-
    (  '$get_from_attr_list'(V, Module, Attr) ->
       false
    ;  true
    ).

'$copy_attr_list'(L, _Module, []) :- var(L), !.
'$copy_attr_list'([Module0:Att|Atts], Module, CopiedAtts) :-
    (  Module0 == Module ->
       CopiedAtts = [Att|CopiedAtts0],
       '$copy_attr_list'(Atts, Module, CopiedAtts0)
    ;  '$copy_attr_list'(Atts, Module, CopiedAtts)
    ).

user:term_expansion(Term0, Terms) :-
    nonvar(Term0),
    Term0 = (:- attribute Atts),
    nonvar(Atts),
    prolog_load_context(module, Module),
    phrase(expand_terms(Atts, Module), Terms).

expand_terms(Atts, Module) -->
    put_attrs_var_check,
    put_attrs(Atts, Module),
    get_attrs_var_check(Module),
    get_attrs(Atts, Module).

put_attrs_var_check -->
    [(put_atts(Var, Attr) :- nonvar(Var),
                             throw(error(uninstantiation_error(Var), put_atts/2))),
     (put_atts(Var, Attr) :- var(Attr),
                             throw(error(instantiation_error, put_atts/2)))].

get_attrs_var_check(Module) -->
    [(get_atts(Var, Attr) :- nonvar(Var),
                             throw(error(uninstantiation_error(Var), get_atts/2))),
     (get_atts(Var, Attr) :- var(Attr),
                             !,
                             '$get_attr_list'(Var, Ls),
                             nonvar(Ls),
			                 atts:'$copy_attr_list'(Ls, Module, Attr))].

put_attrs(Name/Arity, Module) -->
    put_attr(Name, Arity, Module),
    [(put_atts(Var, Attr) :- lists:maplist(Module:put_atts(Var), Attr), !)].
put_attrs((Name/Arity, Atts), Module) -->
    { nonvar(Atts) },
    put_attr(Name, Arity, Module),
    put_attrs(Atts, Module).

get_attrs(Name/Arity, Module) -->
    get_attr(Name, Arity, Module).
get_attrs((Name/Arity, Atts), Module) -->
    { nonvar(Atts) },
    get_attr(Name, Arity, Module),
    get_attrs(Atts, Module).

put_attr(Name, Arity, Module) -->
    { functor(Attr, Name, Arity) },
    [(put_atts(V, +Attr) :-
          !,
          '$put_to_attr_list'(V, Module, Attr)),
     (put_atts(V, Attr) :-
          !,
          '$put_to_attr_list'(V, Module, Attr)),
     (put_atts(V, -Attr) :-
          !,
          '$del_from_attr_list'(V, Module, Attr))].

get_attr(Name, Arity, Module) -->
    { functor(Attr, Name, Arity) },
    [(get_atts(V, +Attr) :-
          !,
          functor(Attr, _, _),
          atts:'$get_from_attr_list'(V, Module, Attr)),
     (get_atts(V,  Attr) :-
          !,
          functor(Attr, _, _),
          atts:'$get_from_attr_list'(V, Module, Attr)),
     (get_atts(V, -Attr) :-
          !,
          functor(Attr, _, _),
          atts:'$absent_attr'(V, Module, Attr))].

user:goal_expansion(Term, M:put_atts(Var, Attr)) :-
    nonvar(Term),
    Term = put_atts(Var, M, Attr).
user:goal_expansion(Term, M:get_atts(Var, Attr)) :-
    nonvar(Term),
    Term = get_atts(Var, M, Attr).

term_attributed_variables(Term, Vars) :-
    '$term_attributed_variables'(Term, Vars).
