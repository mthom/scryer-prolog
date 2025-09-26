:- use_module(library(files)).

main :-
    current_input(UserStream),
    open('./input', read, InputStream),
    set_input(InputStream),
    read_term(T, []), write(T),
    set_input(UserStream).

:- initialization(main).
