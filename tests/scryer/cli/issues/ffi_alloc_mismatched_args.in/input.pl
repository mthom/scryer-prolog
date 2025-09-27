:- use_module(library(ffi)).


test :- ffi:array_type(u8, 2, Type), ffi:allocate(rust, Type, [Type, 0], _ArrayPtr).

?- test.
   error(system_error,'$ffi_allocate'/4).