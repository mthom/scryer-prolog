:- use_module(library(format)).
:- use_module(library(files)).
:- use_module(library(iso_ext)).

w(T) :-
   open("consult_update_terms.pl", write, S),
   format(S, "~s", [T]),
   close(S),
   consult(consult_update_terms).

test :-
   call_cleanup((
    w("a :- b."),
    current_predicate(a/0),
    \+ current_predicate(a/1),
    w("a(1) :- b."),
    \+ current_predicate(a/0),
    current_predicate(a/1)
   ),
   delete_file("consult_update_terms.pl")).

?- test.
   false, unexpected.
   true.