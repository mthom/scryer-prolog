:- use_module(library(dcgs)).
:- use_module(library(reif)).

animals([animal(dog, [is_true('has fur'), is_true('says woof')]),
         animal(cat, [is_true('has fur'), is_true('says meow')]),
         animal(duck, [is_true('has feathers'), is_true('says quack')])]).

animal(A) :-
    animals(Animals),
    Known0 = [],
    phrase(any_animal(Animals, A), [Known0], _).

any_animal([Animal|Animals], A) -->
    any_animal_(Animal, Animals, A).

any_animal_(animal(A0, []), Animals, A) -->
    (   { A0 = A }
    ;   any_animal(Animals, A)
    ).
any_animal_(animal(A0, [C|Cs]), Animals, A) -->
    state0_state(Known0, Known),
    { condition_truth(C, T, Known0, Known) },
    next_animal(T, animal(A0,Cs), Animals, A).

next_animal(yes, Animal, Animals, A)  --> any_animal([Animal|Animals], A).
next_animal(no, _, Animals, A)        --> any_animal(Animals, A).

state0_state(S0, S), [S] --> [S0].

condition_truth(is_true(Q), Answer, Known0, Known) :-
    if_(known_(Q,Answer,Known0),
        Known0 = Known,
        ( writeq([Q, ?]), nl,
	  read(Answer),
          Known = [known(Q,Answer)|Known0])).

known_(What, Answer, Known, Truth) :-
    if_(memberd_t(known(What,yes), Known),
        ( Answer = yes, Truth = true ),
        if_(memberd_t(known(What,no), Known),
            ( Answer = no, Truth = true),
            Truth = false)).
