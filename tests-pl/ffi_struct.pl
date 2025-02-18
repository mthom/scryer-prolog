:- use_module(library(os)).
:- use_module(library(ffi)).

test :- 
    read(Body),
    term_variables(Body, [LIB]),
    Body,
    foreign_struct(pg, [uint8, uint16, uint32, uint64, uint8, f32, f64]),
    use_foreign_module(LIB, ['construct'([uint8, uint16, uint32, uint64, uint8, f32, f64], pg), 'modify'([pg], pg)]),
    ffi:'construct'(8, 12, 46, 40, 127, 1.368, -4.587, PG),
    write(("PG"-PG)), nl,
    ffi:'modify'(PG, [pg, A, B, C, D, A2, E, F]),
    write(("PG2"-[pg, A, B, C, D, A2, E, F])), nl.

:- initialization(test).
