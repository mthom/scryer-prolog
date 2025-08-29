:- use_module(library(ffi)).
:- use_module(library(format)).

test :-
    ffi:array_type(u64, 1, ArrayType1),
    ffi:with_locals(
        [
            let(_Local1, ArrayType1, [ArrayType1 , 42])
        ],
        format("With Locals 1~n", [])
    ),
    ffi:array_type(u8, 4, ArrayType2),
    ffi:with_locals(
        [
            let(_Local2, ArrayType2, [ArrayType2 , 42, 13, 4, 12])
        ],
        format("With Locals 2~n", [])
    ),
    ffi:array_type(u64, 1, ArrayType3),
    ffi:with_locals(
        [
            let(_Local3, ArrayType3, [ArrayType3 , 42])
        ],
        format("With Locals 3~n", [])
    ).

:- initialization(test).
