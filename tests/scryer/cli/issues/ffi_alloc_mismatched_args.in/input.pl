:- use_module(library(ffi)).


test :- ffi:array_type(u8, 2, Type), ffi:allocate(rust, Type, [Type, 0], _ArrayPtr).

?- test.
   error(existence_error(ffi_struct_constructor,'$[u8;2]'/1),'$ffi_allocate'/4).