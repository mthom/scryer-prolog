pub static VERIFY_ATTRS: &str = "
iterate([Var-Value|Bindings]) :-
    '$get_attr_list'(Var, Ls),
    call_verify_attributes(Ls, Var, Value),
    iterate(Bindings),
    '$restore_p_from_sfcp'.
iterate([]).

call_verify_attributes(Attrs, _, _) :-
    var(Attrs), !.
call_verify_attributes([Attr|Attrs], Var, Value) :-
    '$module_of'(M, Attr), % write the owning module Attr to M.
    catch(M:verify_attribute(Var, Value, Goals), error(existence_error(procedure, _), _), true),
    call_verify_attribute_goals(Goals),
    call_verify_attributes(Attrs, Var, Value).

call_verify_attribute_goals(Goals) :-
    var(Goals), throw(error(instantiation_error, call_verify_attribute_goals/1)).
call_verify_attribute_goals([Goal|Goals]) :-
    call(Goal),
    call_verify_attribute_goals(Goals).
call_verify_attribute_goals([]).
";

