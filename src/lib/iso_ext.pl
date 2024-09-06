/** Useful general predicates that are not ISO standard yet

Predicates available here are similar to the ones defined in builtin.pl,
but they're not part of the ISO Prolog standard at the moment.
*/

:- module(iso_ext, [bb_b_put/2,
                    bb_get/2,
                    bb_put/2,
                    call_cleanup/2,
                    call_with_inference_limit/3,
                    call_residue_vars/2,
                    forall/2,
                    partial_string/1,
                    partial_string/3,
                    partial_string_tail/2,
                    setup_call_cleanup/3,
                    succ/2,
                    call_nth/2,
                    countall/2,
                    copy_term_nat/2,
		    copy_term/3]).

:- use_module(library(error), [can_be/2,
                               domain_error/3,
                               instantiation_error/1,
                               type_error/3]).

:- use_module(library(lists), [maplist/3]).

:- use_module(library('$project_atts')).

:- meta_predicate(forall(0, 0)).

%% forall(Generate, Test).
%
% For all bindings possible by Generate, Test must be true.
%
% In this example, it checks that all numbers are even:
%
% ```
% ?- Ns = [2,4,6], forall(member(N, Ns), 0 is N mod 2).
%    Ns = [2,4,6].
% ```
forall(Generate, Test) :-
    \+ (Generate, \+ Test).

% (non-)backtrackable global variables.

%% bb_put(+Key, +Value).
%
% Sets a global variable named Key (must be an atom) with value Value.
% The global variable isn't backtrackable. Check `bb_b_put/2` for the
% backtrackable version.
%
% ```
% ?- bb_put(city, "Valladolid").
%    true.
% ?- bb_get(city, X).
%    X = "Valladolid".
% ```
%
% In this example one can understand the difference between `bb_put/2` and
% `bb_b_put/2`:
%
% ```
% ?- bb_put(city, "Valladolid"), (bb_put(city, "Salamanca"), false);(bb_get(city, X)).
%    X = "Salamanca".
% ?- bb_put(city, "Valladolid"), (bb_b_put(city, "Salamanca"), false);(bb_get(city, X)).
%    X = "Valladolid".
% ```
bb_put(Key, Value) :-
    (  atom(Key) ->
       '$store_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_put/2)
    ).

% backtrackable global variables.

%% bb_b_put(+Key, +Value).
%
% Sets a global variable named Key (must be an atom) with value Value.
% The global variable is backtrackable. Check `bb_put/2` for the
% non-backtrackable version.
%
% ```
% ?- bb_b_put(city, "Valladolid").
%    true.
% ?- bb_get(city, X).
%    X = "Valladolid".
% ```
%
% In this example one can understand the difference between `bb_put/2` and
% `bb_b_put/2`:
%
% ```
% ?- bb_put(city, "Valladolid"), (bb_put(city, "Salamanca"), false);(bb_get(city, X)).
%    X = "Salamanca".
% ?- bb_put(city, "Valladolid"), (bb_b_put(city, "Salamanca"), false);(bb_get(city, X)).
%    X = "Valladolid".
% ```
bb_b_put(Key, Value) :-
    (  atom(Key) ->
       '$store_backtrackable_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_b_put/2)
    ).

%% bb_get(+Key, -Value).
%
% Gets the value Value of a global variable named Key (must be an atom)
bb_get(Key, Value) :-
    (  atom(Key) ->
       '$fetch_global_var'(Key, Value)
    ;  type_error(atom, Key, bb_get/2)
    ).


%% succ(?I, ?S).
%
% True iff S is the successor of the non-negative integer I.
% At least one of the arguments must be instantiated.

succ(I, S) :-
    can_be(not_less_than_zero, I),
    can_be(not_less_than_zero, S),
    (   integer(S) ->
        S > 0,
        I is S-1
    ;   integer(I) ->
        S is I+1
    ;   instantiation_error(succ/2)
    ).


% setup_call_cleanup.

:- meta_predicate(call_cleanup(0, 0)).

%% call_cleanup(Goal, Cleanup).
%
% Executes Goal and then, either on success or failure, executes Cleanup.
% The success or failure of Cleanup is ignored and choice points created inside are destroyed.
call_cleanup(G, C) :- setup_call_cleanup(true, G, C).

:- meta_predicate(setup_call_cleanup(0, 0, 0)).

:- non_counted_backtracking setup_call_cleanup/3.

%% setup_call_cleanup(Setup, Goal, Cleanup).
%
% If Setup succeeds, Cleanup will be called after the execution of Goal. Goal itself can succeed or not.
%
% In this example, we use the predicate to always close an open file:
%
% ```
% ?- setup_call_cleanup(open(File, read, Stream), do_something_with_stream(Stream), close(Stream)).
% ```
setup_call_cleanup(S, G, C) :-
    '$get_b_value'(B),
    '$call_with_inference_counting'(call(S)),
    '$set_cp_by_default'(B),
    '$get_current_scc_block'(Bb),
    (  C = _:CC,
       var(CC) ->
       instantiation_error(setup_call_cleanup/3)
    ;  scc_helper(C, G, Bb)
    ).

:- meta_predicate(scc_helper(?,0,?)).

:- non_counted_backtracking scc_helper/3.

scc_helper(C, G, Bb) :-
    '$get_cp'(Cp),
    '$install_scc_cleaner'(C),
    '$call_with_inference_counting'(call(G)),
    (  '$check_cp'(Cp) ->
       '$reset_scc_block'(Bb),
       run_cleaners_without_handling(Cp)
    ;  true
    ;  '$fail'
    ).
scc_helper(_, _, Bb) :-
    '$reset_scc_block'(Bb),
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
    '$get_cp'(B),
    catch(C, _, true),
    '$set_cp_by_default'(B),
    run_cleaners_with_handling.
run_cleaners_with_handling :-
    '$restore_cut_policy'.

:- non_counted_backtracking run_cleaners_without_handling/1.

run_cleaners_without_handling(Cp) :-
    '$get_scc_cleaner'(C),
    '$get_cp'(B),
    call(C),
    '$set_cp_by_default'(B),
    run_cleaners_without_handling(Cp).
run_cleaners_without_handling(Cp) :-
    '$set_cp_by_default'(Cp),
    '$restore_cut_policy'.

% call_with_inference_limit

:- meta_predicate(call_with_inference_limit(0, ?, ?)).

:- non_counted_backtracking call_with_inference_limit/3.

%% call_with_inference_limit(Goal, Limit, Result).
%
% Similar to `call(Goal)` but it limits the number of inferences for each solution of Goal.
% Calls to it may be nested, but only the last limit will be in power.
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


:- meta_predicate(call_with_inference_limit(0,?,?,?,?)).

:- non_counted_backtracking call_with_inference_limit/5.

call_with_inference_limit(G, L, R, Bb, B) :-
    '$install_new_block'(NBb),
    '$install_inference_counter'(NBb, L, Count0),
    '$call_with_inference_counting'(call(G)),
    '$inference_level'(R, B),
    '$remove_inference_counter'(NBb, Count1),
    Diff is L - (Count1 - Count0),
    (  '$clean_up_block'(NBb),
       '$reset_block'(Bb)
    ;  '$install_inference_counter'(NBb, Diff, _),
       '$reset_block'(NBb),
       '$fail'
    ).
call_with_inference_limit(_, _, R, Bb, B) :-
    (  '$inference_limit_exceeded' ->
       R = inference_limit_exceeded
    ;  true
    ),
    '$get_current_block'(NBb),
    '$remove_inference_counter'(NBb, _),
    '$reset_block'(Bb),
    '$remove_call_policy_check'(B),
    (  '$get_ball'(_),
       '$push_ball_stack',
       '$get_cp'(Cp),
       '$set_cp_by_default'(Cp),
       '$pop_from_ball_stack',
       '$unwind_stack'
    ;  nonvar(R)
    ).

%% partial_string(String, L, L0)
%
% Explicitly construct a partial string "manually". It can be used as an optimized append/3.
% It's not recommended to use this predicate in application code.
partial_string(String, L, L0) :-
    (  String == [] ->
       L = L0
    ;  catch(atom_chars(Atom, String),
             error(E, _),
             throw(error(E, partial_string/3))),
       '$create_partial_string'(Atom, L, L0)
    ).

%% partial_string(+String)
%
% Succeeds if String is a _partial string_. A partial string is a string composed of several smaller
% strings, even just one. That means all strings in Scryer are partial strings.
partial_string(String) :-
    '$is_partial_string'(String).

%% partial_string_tail(+String, -Tail).
%
% Unifies Tail with the last section of the partial string.
% It's not recommended to use this predicate in application code.
partial_string_tail(String, Tail) :-
    (  partial_string(String) ->
       '$partial_string_tail'(String, Tail)
    ;  throw(error(type_error(partial_string, String), partial_string_tail/2))
    ).

:- dynamic(i_call_nth_nesting/2).
:- dynamic(i_call_nth_counter/1).

:- meta_predicate(call_nth(0, ?)).

%% call_nth(Goal, N).
%
% Succeeds when Goal succeeded for the Nth time (there are at least N solutions)
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

%% countall(G_0, N).
%
% countall(G_0, N) is true iff N unifies with the total number of
% answers of call(G_0).

:- meta_predicate(countall(0, ?)).

countall(Goal, N) :-
    can_be(integer, N),
    (   integer(N) ->
        (   N < 0 ->
            domain_error(not_less_than_zero, N, countall/2)
        ;   true
        )
    ;   true
    ),
    setup_call_cleanup(call_nth_nesting(C, ID),
                       (   (   Goal,
                               bb_get(ID, N0),
                               N1 is N0 + 1,
                               bb_put(ID, N1),
                               false
                           ;   bb_get(ID, N)
                           )
                       ),
                       (   bb_get(i_call_nth_counter, C) ->
                           C1 is C - 1,
                           bb_put(i_call_nth_counter, C1)
                       ;   true
                       )).

%% copy_term_nat(Source, Dest)
%
% Similar to `copy_term/2` but without attribute variables
copy_term_nat(Source, Dest) :-
    '$copy_term_without_attr_vars'(Source, Dest).

%% copy_term(+Term, -Copy, -Gs).
%
% Produce a deep copy of Term and unify it to Copy, without attributes.
% Unify Gs with a list of goals that represent the attributes of Term.
% Similar to `copy_term/2` but splitting the attributes.
copy_term(Term, Copy, Gs) :-
   can_be(list, Gs),
   findall(Term-Rs, '$project_atts':term_residual_goals(Term,Rs), [Copy-Gs]),
   (  var(Gs) ->
      Gs = []
   ;  true
   ).

:- meta_predicate call_residue_vars(0, ?).

call_residue_vars(Goal, Vars) :-
    can_be(list, Vars),
    '$get_attr_var_queue_delim'(B),
    call(Goal),
    '$get_attr_var_queue_beyond'(B, Vars).
