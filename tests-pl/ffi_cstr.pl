:- use_module(library(os)).
:- use_module(library(ffi)).

init :-
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, [
        'ffi_cstr_len'([cstr], u64),
        'ffi_example_cstr'([], cstr),
        'ffi_null_cstr'([], cstr)
    ]).

test :-
    ffi:'ffi_cstr_len'("Scryer Prolog", Len),
    ffi:'ffi_example_cstr'(Str),
    ffi:'ffi_null_cstr'(Null),
    ffi:'ffi_cstr_len'(0, MaxU64),
    write((Len-Str-Null-MaxU64)).

:- initialization((init,test)).
