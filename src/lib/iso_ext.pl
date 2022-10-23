:- module(iso_ext, [bb_b_put/2,
                    bb_get/2,
                    bb_put/2,
                    call_cleanup/2,
                    call_with_inference_limit/3,
                    forall/2,
                    partial_string/1,
                    partial_string/3,
                    partial_string_tail/2,
                    setup_call_cleanup/3,
                    call_nth/2,
                    copy_term_nat/2]).

:- use_module(library(error), [can_be/2,
                               domain_error/3,
                               instantiation_error/1,
                               type_error/3]).

:- use_module(library(lists), [maplist/3]).

:- meta_predicate(forall(0, 0)).

forall(Generate, Test) :-
    \+ (Generate, \+ Test).

%% (non-)backtrackable global variables.

bb_put(Key, Value) :-
    (  atom(Key) ->
       '$store_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_put/2)
    ).

%% backtrackable global variables.

bb_b_put(Key, Value) :-
    (  atom(Key) ->
       '$store_backtrackable_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_b_put/2)
    ).

bb_get(Key, Value) :-
    (  atom(Key) ->
       '$fetch_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_get/2)
    ).


% setup_call_cleanup.

:- meta_predicate(call_cleanup(0, 0)).

call_cleanup(G, C) :- setup_call_cleanup(true, G, C).

:- meta_predicate(setup_call_cleanup(0, 0, 0)).

:- non_counted_backtracking setup_call_cleanup/3.

setup_call_cleanup(S, G, C) :-
    '$get_b_value'(B),
    '$call_with_inference_counting'(call(S)),
    '$set_cp_by_default'(B),
    '$get_current_block'(Bb),
    (  C = _:CC,
       var(CC) ->
       instantiation_error(setup_call_cleanup/3)
    ;  scc_helper(C, G, Bb)
    ).

:- meta_predicate(scc_helper(?,0,?)).

:- non_counted_backtracking scc_helper/3.

scc_helper(C, G, Bb) :-
    '$get_cp'(Cp),
    '$install_scc_cleaner'(C, NBb),
    '$call_with_inference_counting'(call(G)),
    (  '$check_cp'(Cp) ->
       '$reset_block'(Bb),
       run_cleaners_without_handling(Cp)
    ;  true
    ;  '$reset_block'(NBb),
       '$fail'
    ).
scc_helper(_, _, Bb) :-
    '$reset_block'(Bb),
    '$push_ball_stack',
    run_cleaners_with_handling,
    '$pop_from_ball_stack',
    '$unwind_stack'.
scc_helper(_, _, _) :-
    '$get_cp'(Cp),
    run_cleaners_without_handling(Cp),
    '$fail'.

:- non_counted_backtracking run_cleaners_with_handling/0.

run_cleaners_with_handling :-
    '$get_scc_cleaner'(C),
    '$get_level'(B),
    catch(C, _, true),
    '$set_cp_by_default'(B),
    run_cleaners_with_handling.
run_cleaners_with_handling :-
    '$restore_cut_policy'.

:- non_counted_backtracking run_cleaners_without_handling/1.

run_cleaners_without_handling(Cp) :-
    '$get_scc_cleaner'(C),
    '$get_level'(B),
    call(C),
    '$set_cp_by_default'(B),
    run_cleaners_without_handling(Cp).
run_cleaners_without_handling(Cp) :-
    '$set_cp_by_default'(Cp),
    '$restore_cut_policy'.

% call_with_inference_limit

:- non_counted_backtracking end_block/4.

end_block(_, Bb, NBb, _L) :-
    '$clean_up_block'(NBb),
    '$reset_block'(Bb).
end_block(B, _Bb, NBb, L) :-
    '$install_inference_counter'(B, L, _),
    '$reset_block'(NBb),
    '$fail'.

:- non_counted_backtracking handle_ile/3.

handle_ile(B, inference_limit_exceeded(B), inference_limit_exceeded) :-
    !,
    '$pop_ball_stack'.
handle_ile(B, _, _) :-
    '$remove_call_policy_check'(B),
    '$pop_from_ball_stack',
    '$unwind_stack'.

:- meta_predicate(call_with_inference_limit(0, ?, ?)).

:- non_counted_backtracking call_with_inference_limit/3.

call_with_inference_limit(G, L, R) :-
    (  integer(L) ->
       (  L < 0 ->
          domain_error(not_less_than_zero, L, call_with_inference_limit/3)
       ;  true
       )
    ;  var(L) ->
       instantiation_error(call_with_inference_limit/3)
    ;  type_error(integer, L, call_with_inference_limit/3)
    ),
    '$get_current_block'(Bb),
    '$get_b_value'(B),
    call_with_inference_limit(G, L, R, Bb, B),
    '$remove_call_policy_check'(B).

install_inference_counter(B, L, Count0) :-
    '$install_inference_counter'(B, L, Count0).

:- meta_predicate(call_with_inference_limit(0,?,?,?,?)).

:- non_counted_backtracking call_with_inference_limit/5.

call_with_inference_limit(G, L, R, Bb, B) :-
    '$install_new_block'(NBb),
    '$install_inference_counter'(B, L, Count0),
    '$call_with_inference_counting'(call(G)),
    '$inference_level'(R, B),
    '$remove_inference_counter'(B, Count1),
    Diff is L - (Count1 - Count0),
    end_block(B, Bb, NBb, Diff).
call_with_inference_limit(_, _, R, Bb, B) :-
    '$reset_block'(Bb),
    '$remove_inference_counter'(B, _),
    (  '$get_ball'(Ball),
       '$push_ball_stack',
       '$get_level'(Cp),
       '$set_cp_by_default'(Cp)
    ;  '$remove_call_policy_check'(B),
       '$fail'
    ),
    handle_ile(B, Ball, R).

partial_string(String, L, L0) :-
    (  String == [] ->
       L = L0
    ;  catch(atom_chars(Atom, String),
             error(E, _),
             throw(error(E, partial_string/3))),
       '$create_partial_string'(Atom, L, L0)
    ).

partial_string(String) :-
    '$is_partial_string'(String).

partial_string_tail(String, Tail) :-
    (  partial_string(String) ->
       '$partial_string_tail'(String, Tail)
    ;  throw(error(type_error(partial_string, String), partial_string_tail/2))
    ).

:- dynamic(i_call_nth_nesting/2).
:- dynamic(i_call_nth_counter/1).

:- meta_predicate(call_nth(0, ?)).

call_nth(Goal, N) :-
    can_be(integer, N),
    (   integer(N) ->
        (   N < 0 ->
            domain_error(not_less_than_zero, N, call_nth/2)
        ;   N > 0
        )
    ;   true
    ),
    setup_call_cleanup(call_nth_nesting(C, ID),
                       (   Goal,
                           bb_get(ID, N0),
                           N1 is N0 + 1,
                           bb_put(ID, N1),
                           (   integer(N) ->
                               N = N1,
                               !
                           ;   N = N1
                           )
                       ),
                       (   bb_get(i_call_nth_counter, C) ->
                           C1 is C - 1,
                           bb_put(i_call_nth_counter, C1)
                       ;   true
                       )).

call_nth_nesting(C, ID) :-
    (   bb_get(i_call_nth_counter, C0) ->
        C is C0 + 1
    ;   C = 0
    ),
    number_chars(C, Cs),
    atom_chars(Atom, Cs),
    atom_concat(i_call_nth_nesting_, Atom, ID),
    bb_put(ID, 0),
    bb_put(i_call_nth_counter, C).


copy_term_nat(Source, Dest) :-
    '$copy_term_without_attr_vars'(Source, Dest).
