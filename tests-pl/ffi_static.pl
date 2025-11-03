test :-
    (current_predicate(ffi:'get_example_struct'/1) -> write(is_current); write(is_not_current)),
    nl,
    ffi:'get_example_struct'(Example),
    write(Example).

:- initialization(test).
