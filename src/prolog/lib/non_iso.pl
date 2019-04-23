%% for builtins that are not part of the ISO standard.
%% must be loaded at the REPL with

%% ?- use_module(library(non_iso)).

:- module(non_iso, [bb_b_put/2, bb_get/2, bb_put/2, call_cleanup/2,
		    forall/2]).

forall(Generate, Test) :-
    \+ (Generate, \+ Test).

%% (non-)backtrackable global variables.

bb_put(Key, Value) :- atom(Key), !, '$store_global_var'(Key, Value).
bb_put(Key, _) :- throw(error(type_error(atom, Key), bb_put/2)).

bb_b_put(Key, NewValue) :-
    (  bb_get(Key, OldValue) ->
       call_cleanup((store_global_var(Key, NewValue) ; false), store_global_var(Key, OldValue))
    ;  call_cleanup((store_global_var(Key, NewValue) ; false), reset_global_var_at_key(Key))
    ).

store_global_var(Key, Value) :- '$store_global_var'(Key, Value).

reset_global_var_at_key(Key) :- '$reset_global_var_at_key'(Key).

bb_get(Key, Value) :- atom(Key), !, '$fetch_global_var'(Key, Value).
bb_get(Key, _) :- throw(error(type_error(atom, Key), bb_get/2)).

call_cleanup(G, C) :- setup_call_cleanup(true, G, C).
