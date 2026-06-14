:- use_module(library(format)).
:- use_module(library(files)).
:- use_module(library(iso_ext)).

w(T) :-
   open("consult_dynamic_update_terms.pl", write, S),
   format(S, "~s", [T]),
   close(S),
   consult(consult_dynamic_update_terms).

test :-
   call_cleanup((
    w(":- dynamic(a/1)."),
    current_predicate(a/1),
    \+ current_predicate(a/2),
    w(":- dynamic(a/2)."),
    \+ current_predicate(a/1),
    current_predicate(a/2)
   ),
   delete_file("consult_dynamic_update_terms.pl")).

?- test.
   false, unexpected.
   true.