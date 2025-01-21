:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    getenv("ffi_invalid_type_LIB", LIB),    
    use_foreign_module(LIB, [
        'ffi_invalid_type'([], c_void)
    ]).

:- initialization(test).
