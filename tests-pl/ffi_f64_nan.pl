:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    getenv("ffi_f64_nan_LIB", LIB),    
    use_foreign_module(LIB, ['ffi_f64_nan'([], f64)]),
    ffi:'ffi_f64_nan'(N),
    _ is round(N).

:- initialization(test).
