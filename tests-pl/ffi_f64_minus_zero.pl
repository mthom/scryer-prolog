:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, ['ffi_f64_minus_zero'([], f64), 'signum'([f64], f64)]),
    ffi:'ffi_f64_minus_zero'(N),
    A is max(0.0, N),
    B is max(N, 0.0),
    ffi:'signum'(A, SA),
    ffi:'signum'(B, SB),
    write((SA, SB)),
    1.0 is SA,
    1.0 is SB.

:- initialization(test).
