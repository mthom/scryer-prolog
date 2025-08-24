:- use_module(library(os)).
:- use_module(library(ffi)).

init :-
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    use_foreign_module(LIB, [
        'ffi_set_u64'([ptr], void)
    ]).

test :-
    ffi:allocate(rust, u64, 0, Ptr),
    ffi:'ffi_set_u64'(Ptr),
    ffi:read_ptr(u64, Ptr, Val),
    ffi:deallocate(rust, u64, Ptr),
    write((Val)).

:- initialization((init,test)).
