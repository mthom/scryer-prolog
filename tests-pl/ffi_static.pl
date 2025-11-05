test :-
    ffi:assert_predicate('get_example_struct'([], 'ExampleCStructOuter')), % this shouldn't be necessary
    ffi:'get_example_struct'(Example),
    write(Example).

:- initialization(test).
