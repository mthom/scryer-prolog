:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, [
        'ffi_cstr_len'([cstr], u64),
        'ffi_example_cstr'([], cstr)
    ]),
    ffi:'ffi_cstr_len'("Scryer Prolog", Len),
    ffi:'ffi_example_cstr'(Str),
    write((Len-Str)).

:- initialization(test).
