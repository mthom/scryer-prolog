:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, [
        %% should be void instead of c_void
        'ffi_invalid_type'([], c_void)
    ]).

:- initialization(test).
