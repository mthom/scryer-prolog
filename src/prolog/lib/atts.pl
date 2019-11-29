:- module(atts, [op(1199, fx, attribute), call_residue_vars/2,
		 '$absent_attr'/2, '$copy_attr_list'/2, '$get_attr'/2,
		 '$put_attr'/2, '$absent_from_list'/2,
		 '$get_from_list'/3, '$add_to_list'/3, '$del_attr'/3,
		 '$del_attr_step'/3, '$del_attr_buried'/4,
		 '$default_attr_list'/4]).

:- use_module(library(dcgs)).
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
    (  { '$module_of'(Module, PG) } -> [Module:put_atts(AttrVar, PG)]
    ;  { true }
    ),
    '$default_attr_list'(PGs, Module, AttrVar).
'$default_attr_list'([], _, _) --> [].

'$absent_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls),
    '$absent_from_list'(Ls, Attr).

'$absent_from_list'(X, _) :-
    var(X), !.
'$absent_from_list'([L|Ls], Attr) :-
    ( L \= Attr -> '$absent_from_list'(Ls, Attr) ).

'$get_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls), nonvar(Ls), '$get_from_list'(Ls, V, Attr).

'$get_from_list'([L|Ls], V, Attr) :-
    nonvar(L),
    ( L \= Attr -> nonvar(Ls), '$get_from_list'(Ls, V, Attr)
    ; L = Attr -> '$enqueue_attr_var'(V)
    ; '$get_from_list'(Ls, V, Attr)
    ).

'$put_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls), '$add_to_list'(Ls, V, Attr).

'$add_to_list'(Ls, V, Attr) :-
    ( var(Ls) -> Ls = [Attr | _], '$enqueue_attr_var'(V)
    ; Ls = [_ | Ls0], '$add_to_list'(Ls0, V, Attr)
    ).

'$del_attr'(Ls0, _, _) :-
    var(Ls0), !.
'$del_attr'(Ls0, V, Attr) :-
    Ls0 = [Att | Ls1],
    nonvar(Att),
    ( Att \= Attr -> '$del_attr_buried'(Ls0, Ls1, V, Attr)
    ; '$enqueue_attr_var'(V), '$del_attr_head'(V), '$del_attr'(Ls1, V, Attr)
    ).

'$del_attr_step'(Ls1, V, Attr) :-
    ( nonvar(Ls1) -> Ls1 = [_ | Ls2], '$del_attr_buried'(Ls1, Ls2, V, Attr)
    ; true ).

%% assumptions: Ls0 is a list, Ls1 is its tail;
%%              the head of Ls0 can be ignored.
'$del_attr_buried'(Ls0, Ls1, V, Attr) :-
    Ls0 = [_, Att | _],
    nonvar(Att),
    !,
    ( Att \= Attr -> '$del_attr_step'(Ls1, V, Attr)
    ; '$enqueue_attr_var'(V),
      '$del_attr_non_head'(Ls0), %% set tail of Ls0 = tail of Ls1. can be undone by backtracking.
      '$del_attr_step'(Ls1, V, Attr)
    ).
'$del_attr_buried'(_, _, _, _).

'$copy_attr_list'(L, []) :- var(L), !.
'$copy_attr_list'([Att|Atts], [Att|CopiedAtts]) :-
    '$copy_attr_list'(Atts, CopiedAtts).

user:term_expansion(Term0, Terms) :-
    nonvar(Term0),
    Term0 = (:- attribute Atts),
    nonvar(Atts),
    phrase(expand_terms(Atts), Terms).

expand_terms(Atts) -->
    put_attrs_var_check,
    put_attrs(Atts),
    get_attrs_var_check,
    get_attrs(Atts).

put_attrs_var_check -->
    { numbervars([Var, Attr], 0, _) },
    [(put_atts(Var, Attr) :- nonvar(Var), throw(error(type_error(variable, Var), put_atts/2))),
     (put_atts(Var, Attr) :- var(Attr), throw(error(instantiation_error, put_atts/2)))].

get_attrs_var_check -->
    { numbervars([Var, Ls, Attr], 0, _) },
    [(get_atts(Var, Attr) :- nonvar(Var), throw(error(type_error(variable, Var), get_atts/2))),
     (get_atts(Var, Attr) :- var(Attr), !, '$get_attr_list'(Var, Ls), nonvar(Ls),
			     '$copy_attr_list'(Ls, Attr))].

put_attrs(Name/Arity) -->
    put_attr(Name, Arity),
    { numbervars([Var, Attr], 0, _) },
    [(put_atts(Var, Attr) :- lists:maplist(put_atts(Var), Attr), !)].
put_attrs((Name/Arity, Atts)) -->
    { nonvar(Atts) },
    put_attr(Name, Arity),
    put_attrs(Atts).

get_attrs(Name/Arity) -->
    get_attr(Name, Arity).
get_attrs((Name/Arity, Atts)) -->
    { nonvar(Atts) },
    get_attr(Name, Arity),
    get_attrs(Atts).

put_attr(Name, Arity) -->
    { functor(Attr, Name, Arity),
      numbervars(Attr, 0, Arity),
      V = '$VAR'(Arity) },
    [(put_atts(V, +Attr) :- !, functor(Attr, Head, Arity), functor(AttrForm, Head, Arity),
			    '$get_attr_list'(V, Ls), '$del_attr'(Ls, V, AttrForm), '$put_attr'(V, Attr)),
     (put_atts(V,  Attr) :- !, functor(Attr, Head, Arity), functor(AttrForm, Head, Arity),
			    '$get_attr_list'(V, Ls), '$del_attr'(Ls, V, AttrForm), '$put_attr'(V, Attr)),
     (put_atts(V, -Attr) :- !, functor(Attr, _, _), '$get_attr_list'(V, Ls), '$del_attr'(Ls, V, Attr))].

get_attr(Name, Arity) -->
    { functor(Attr, Name, Arity),
      numbervars(Attr, 0, Arity),
      V = '$VAR'(Arity) },
    [(get_atts(V, +Attr) :- !, functor(Attr, _, _), '$get_attr'(V, Attr)),
     (get_atts(V,  Attr) :- !, functor(Attr, _, _), '$get_attr'(V, Attr)),
     (get_atts(V, -Attr) :- !, functor(Attr, _, _), '$absent_attr'(V, Attr))].

user:goal_expansion(Term, M:put_atts(Var, Attr)) :-
    nonvar(Term),
    Term = put_atts(Var, M, Attr).
user:goal_expansion(Term, M:get_atts(Var, Attr)) :-
    nonvar(Term),
    Term = get_atts(Var, M, Attr).

call_residue_vars(Goal, Vars) :-
    '$get_attr_var_queue_delim'(B),
    call(Goal),
    '$get_attr_var_queue_beyond'(B, Vars).
