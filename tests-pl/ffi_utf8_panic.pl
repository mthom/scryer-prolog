:- use_module(library(os)).
:- use_module(library(ffi)).

init :-
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, [
        'ffi_invalid_utf8_cstr'([], cstr)
    ]).

test :-
    ffi:'ffi_invalid_utf8_cstr'(Str),
    write(Str), nl.

:- initialization((init,test)).
