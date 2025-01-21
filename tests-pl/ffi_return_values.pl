:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    getenv("ffi_return_values_LIB", LIB),    
    use_foreign_module(LIB, [
        'ffi_return_values_true'([], bool), 
        'ffi_return_values_false'([], bool), 
        'ffi_return_values_i8'([], sint8),
        'ffi_return_values_u8'([], uint8),
        'ffi_return_values_i16'([], sint16),
        'ffi_return_values_u16'([], uint16),
        'ffi_return_values_i32'([], sint32),
        'ffi_return_values_u32'([], uint32),
        'ffi_return_values_i64'([], sint64),
        'ffi_return_values_u64'([], uint64),
        'ffi_return_values_f32'([], f32),
        'ffi_return_values_f64'([], f64)
    ]),
    ffi:'ffi_return_values_true',
    (\+ ffi:'ffi_return_values_false'),
    ffi:'ffi_return_values_i8'(I8),
    ffi:'ffi_return_values_u8'(U8),
    ffi:'ffi_return_values_i16'(I16),
    ffi:'ffi_return_values_u16'(U16),
    ffi:'ffi_return_values_i32'(I32),
    ffi:'ffi_return_values_u32'(U32),
    ffi:'ffi_return_values_i64'(I64),
    ffi:'ffi_return_values_u64'(U64),
    ffi:'ffi_return_values_f32'(F32),
    ffi:'ffi_return_values_f64'(F64),
    write((i8-I8, u8-U8, i16-I16, u16-U16, i32-I32, u32-U32, i64-I64, u64-U64, f32-F32, f64-F64)).

:- initialization(test).
