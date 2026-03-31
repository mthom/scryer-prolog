:- initialization(main).
main :- ( current_prolog_flag(X, X) -> write(true) ; write(false) ).
