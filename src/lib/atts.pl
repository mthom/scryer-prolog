:- module(atts, [op(1199, fx, attribute),
                 call_residue_vars/2,
                 term_attributed_variables/2,
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
    [Module:put_atts(AttrVar, PG)],
    '$default_attr_list'(PGs, Module, AttrVar).
'$default_attr_list'([], _, _) --> [].

'$absent_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls),
    '$absent_from_list'(Ls, Attr).

'$absent_from_list'(X, Attr) :-
    (  var(X) -> true
    ;  X = [L|Ls], L \= Attr -> '$absent_from_list'(Ls, Attr)
    ).

'$get_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls), nonvar(Ls), '$get_from_list'(Ls, V, Attr).

'$get_from_list'([L|Ls], V, Attr) :-
    nonvar(L),
    (  L \= Attr -> nonvar(Ls), '$get_from_list'(Ls, V, Attr)
    ;  L = Attr, '$enqueue_attr_var'(V)
    ).

'$put_attr'(V, Attr) :-
    '$get_attr_list'(V, Ls), '$add_to_list'(Ls, V, Attr).

'$add_to_list'(Ls, V, Attr) :-
    ( var(Ls) ->
      Ls = [Attr | _], '$enqueue_attr_var'(V)
    ; Ls = [_ | Ls0], '$add_to_list'(Ls0, V, Attr)
    ).

'$del_attr'(Ls0, _, _) :-
    var(Ls0), !.
'$del_attr'(Ls0, V, Attr) :-
    Ls0 = [Att | Ls1],
    nonvar(Att),
    (  Att \= Attr ->
       '$del_attr_buried'(Ls0, Ls1, V, Attr)
    ;  '$enqueue_attr_var'(V),
       '$del_attr_head'(V),
       '$del_attr'(Ls1, V, Attr)
    ).

'$del_attr_step'(Ls1, V, Attr) :-
    (  nonvar(Ls1) -> Ls1 = [_ | Ls2], '$del_attr_buried'(Ls1, Ls2, V, Attr)
    ;  true
    ).

%% assumptions: Ls0 is a list, Ls1 is its tail;
%%              the head of Ls0 can be ignored.
'$del_attr_buried'(Ls0, Ls1, V, Attr) :-
    (  var(Ls1) -> true
    ;  Ls1 = [Att | Ls2] ->
       (  Att \= Attr -> '$del_attr_buried'(Ls1, Ls2, V, Attr)
       ;  '$enqueue_attr_var'(V),
	      '$del_attr_non_head'(Ls0), %% set tail of Ls0 = tail of Ls1. can be undone by backtracking.
	      '$del_attr_step'(Ls1, V, Attr)
       )
    ).

'$copy_attr_list'(L, []) :- var(L), !.
'$copy_attr_list'([Att|Atts], [Att|CopiedAtts]) :-
    '$copy_attr_list'(Atts, CopiedAtts).

user:term_expansion(Term0, Terms) :-
    nonvar(Term0),
    Term0 = (:- attribute Atts),
    nonvar(Atts),
    loader:prolog_load_context(module, Module),
    phrase(expand_terms(Atts, Module), Terms).

expand_terms(Atts, Module) -->
    put_attrs_var_check,
    put_attrs(Atts, Module),
    get_attrs_var_check,
    get_attrs(Atts, Module).

put_attrs_var_check -->
    [(put_atts(Var, Attr) :- nonvar(Var), throw(error(type_error(variable, Var), put_atts/2))),
     (put_atts(Var, Attr) :- var(Attr), throw(error(instantiation_error, put_atts/2)))].

get_attrs_var_check -->
    [(get_atts(Var, Attr) :- nonvar(Var), throw(error(type_error(variable, Var), get_atts/2))),
     (get_atts(Var, Attr) :- var(Attr), !, '$get_attr_list'(Var, Ls), nonvar(Ls),
			     '$copy_attr_list'(Ls, Attr))].

put_attrs(Name/Arity, Module) -->
    put_attr(Name, Arity, Module),
    [(put_atts(Var, Attr) :- lists:maplist(put_atts(Var), Attr), !)].
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
          functor(Attr, Head, Arity),
		  functor(AttrForm, Head, Arity),
		  '$get_attr_list'(V, Ls),
		  '$del_attr'(Ls, V, Module:AttrForm),
		  '$put_attr'(V, Module:Attr)),
     (put_atts(V,  Attr) :-
          !,
          functor(Attr, Head, Arity),
		  functor(AttrForm, Head, Arity),
		  '$get_attr_list'(V, Ls),
		  '$del_attr'(Ls, V, Module:AttrForm),
		  '$put_attr'(V, Module:Attr)),
     (put_atts(V, -Attr) :-
          !,
          functor(Attr, _, _),
		  '$get_attr_list'(V, Ls),
		  '$del_attr'(Ls, V, Module:Attr))].

get_attr(Name, Arity, Module) -->
    { functor(Attr, Name, Arity) },
    [(get_atts(V, +Attr) :- !, functor(Attr, _, _), '$get_attr'(V, Module:Attr)),
     (get_atts(V,  Attr) :- !, functor(Attr, _, _), '$get_attr'(V, Module:Attr)),
     (get_atts(V, -Attr) :- !, functor(Attr, _, _), '$absent_attr'(V, Module:Attr))].

user:goal_expansion(Term, M:put_atts(Var, Attr)) :-
    nonvar(Term),
    Term = put_atts(Var, M, Attr).
user:goal_expansion(Term, M:get_atts(Var, Attr)) :-
    nonvar(Term),
    Term = get_atts(Var, M, Attr).

:- meta_predicate call_residue_vars(0, ?).

call_residue_vars(Goal, Vars) :-
    '$get_attr_var_queue_delim'(B),
    call(Goal),
    '$get_attr_var_queue_beyond'(B, Vars).

term_attributed_variables(Term, Vars) :-
    '$term_attributed_variables'(Term, Vars).
