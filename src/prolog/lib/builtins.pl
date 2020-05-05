:- op(400, yfx, /).

% module resolution operator.
:- op(600, xfy, :).

user:term_expansion((:- op(Pred, Spec, [Op | OtherOps])), OpResults) :-
    '$expand_op_list'([Op | OtherOps], Pred, Spec, OpResults).

'$expand_op_list'([], _, _, []).
'$expand_op_list'([Op | OtherOps], Pred, Spec, [(:- op(Pred, Spec, Op)) | OtherResults]) :-
    '$expand_op_list'(OtherOps, Pred, Spec, OtherResults).

/* this is an implementation specific declarative operator used to implement call_with_inference_limit/3
   and setup_call_cleanup/3. switches to the default trust_me and retry_me_else. Indexing choice
   instructions are unchanged. */
:- op(700, fx, non_counted_backtracking).

% arithmetic operators.
:- op(700, xfx, is).
:- op(500, yfx, [+, -]).
:- op(400, yfx, *).
:- op(200, xfy, [**, ^]).
:- op(500, yfx, [/\, \/, xor]).
:- op(400, yfx, [div, //, rdiv, <<, >>, mod, rem]).
:- op(200, fy, [+, -, \]).

% arithmetic comparison operators.
:- op(700, xfx, [>, <, =\=, =:=, >=, =<]).

% term comparison.
:- op(700, xfx, [==, \==, @=<, @>=, @<, @>]).

% conditional operators.
:- op(1050, xfy, ->).
:- op(1100, xfy, ;).

% control.
:- op(700, xfx, [=, =.., \=]).
:- op(900, fy, \+).

:- module(builtins, [(=)/2, (\=)/2, (\+)/1, (',')/2, (->)/2, (;)/2,
                     (=..)/2, (:)/2, (:)/3, (:)/4, (:)/5, (:)/6,
                     (:)/7, (:)/8, (:)/9, (:)/10, (:)/11, (:)/12,
                     abolish/1, asserta/1, assertz/1, atom_chars/2,
                     atom_codes/2, atom_concat/3, atom_length/2,
                     bagof/3, catch/3, char_code/2, clause/2, close/1,
                     close/2, current_input/1, current_output/1,
                     current_op/3, current_predicate/1,
                     current_prolog_flag/2, expand_goal/2,
                     expand_term/2, fail/0, false/0, findall/3,
                     findall/4, get_char/1, halt/0, max_arity/1,
                     number_chars/2, number_codes/2, once/1, op/3,
                     open/3, open/4, read_term/2, read_term/3,
                     repeat/0, retract/1, set_prolog_flag/2,
                     set_input/1, set_output/1, setof/3, sub_atom/5,
                     subsumes_term/2, term_variables/2, throw/1,
                     true/0, unify_with_occurs_check/2, write/1,
                     write_canonical/1, write_term/2, write_term/3,
                     writeq/1]).


% the maximum arity flag. needs to be replaced with
% current_prolog_flag(max_arity, MAX_ARITY).
max_arity(255).

% unify.
X = X.

true.

false :- '$fail'.

% dynamic module resolution.

Module : Predicate :-
    ( atom(Module) -> '$module_call'(Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1) :-
    ( atom(Module) -> '$module_call'(A1, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2) :-
    ( atom(Module) -> '$module_call'(A1, A2, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5, A6) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, A6, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5, A6, A7) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, A6, A7, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5, A6, A7, A8) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, A6, A7, A8, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5, A6, A7, A8, A9) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, A6, A7, A8, A9, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).

:(Module, Predicate, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10) :-
    ( atom(Module) -> '$module_call'(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, Module, Predicate)
    ; throw(error(type_error(atom, Module), (:)/2))
    ).


% flags.

current_prolog_flag(Flag, false) :- Flag == bounded, !.
current_prolog_flag(bounded, false).
current_prolog_flag(Flag, toward_zero) :- Flag == integer_rounding_function, !.
current_prolog_flag(integer_rounding_function, toward_zero).
current_prolog_flag(Flag, Value) :- Flag == double_quotes, !, '$get_double_quotes'(Value).
current_prolog_flag(double_quotes, Value) :- '$get_double_quotes'(Value).
current_prolog_flag(Flag, _) :- Flag == max_integer, !, '$fail'.
current_prolog_flag(Flag, _) :- Flag == min_integer, !, '$fail'.
current_prolog_flag(Flag, _) :-
    atom(Flag),
    throw(error(domain_error(prolog_flag, Flag), current_prolog_flag/2)). % 8.17.2.3 b
current_prolog_flag(Flag, _) :-
    nonvar(Flag),
    throw(error(type_error(atom, Flag), current_prolog_flag/2)). % 8.17.2.3 a

set_prolog_flag(Flag, Value) :-
    (var(Flag) ; var(Value)),
    throw(error(instantiation_error, set_prolog_flag/2)). % 8.17.1.3 a, b
set_prolog_flag(bounded, false) :- !. % 7.11.1.1
set_prolog_flag(bounded, true)  :- !, '$fail'. % 7.11.1.1
set_prolog_flag(bounded, Value) :-
    throw(error(domain_error(flag_value, bounded + Value), set_prolog_flag/2)). % 8.17.1.3 e
set_prolog_flag(max_integer, Value) :- integer(Value), !, '$fail'. % 7.11.1.2
set_prolog_flag(max_integer, Value) :-
    throw(error(domain_error(flag_value, max_integer + Value), set_prolog_flag/2)). % 8.17.1.3 e
set_prolog_flag(min_integer, Value) :- integer(Value), !, '$fail'. % 7.11.1.3
set_prolog_flag(min_integer, Value) :-
    throw(error(domain_error(flag_value, min_integer + Value), set_prolog_flag/2)). % 8.17.1.3 e
set_prolog_flag(integer_rounding_function, down) :- !. % 7.11.1.4
set_prolog_flag(integer_rounding_function, Value) :-
    throw(error(domain_error(flag_value, integer_rounding_function + Value),
		set_prolog_flag/2)). % 8.17.1.3 e
set_prolog_flag(double_quotes, chars) :-
    !, '$set_double_quotes'(chars). % 7.11.2.5, list of one-char atoms.
set_prolog_flag(double_quotes, atom) :-
    !, '$set_double_quotes'(atom). % 7.11.2.5, list of char codes (UTF8).
set_prolog_flag(double_quotes, codes) :-
    !, '$set_double_quotes'(codes).
set_prolog_flag(double_quotes, Value) :-
    throw(error(domain_error(flag_value, double_quotes + Value),
		set_prolog_flag/2)). % 8.17.1.3 e
set_prolog_flag(Flag, _) :-
    atom(Flag),
    throw(error(domain_error(prolog_flag, Flag), set_prolog_flag/2)). % 8.17.1.3 d
set_prolog_flag(Flag, _) :-
    throw(error(type_error(atom, Flag), set_prolog_flag/2)). % 8.17.1.3 c

% control operators.

fail :- '$fail'.

\+ G :- call(G), !, false.
\+ _.

X \= X :- !, false.
_ \= _.

once(G) :- call(G), !.

repeat.
repeat :- repeat.

','(G1, G2) :- '$get_b_value'(B), '$call_with_default_policy'(comma_errors(G1, G2, B)).

:- non_counted_backtracking comma_errors/3.
comma_errors(G1, G2, B) :- var(G1), throw(error(instantiation_error, (',')/2)).
comma_errors(G1, G2, B) :- '$call_with_default_policy'(','(G1, G2, B)).

:- non_counted_backtracking (',')/3.
','(!, CF, B) :- compound(CF),
		 '$call_with_default_policy'(CF = ','(G1, G2)),
		 '$set_cp'(B),
		 '$call_with_default_policy'(comma_errors(G1, G2, B)).
','(!, Atom, B) :- Atom == !, '$set_cp'(B).
','(!, G, B)  :- '$set_cp'(B), call(G).
','(G, CF, B) :- compound(CF),
		 '$call_with_default_policy'(CF = ','(G1, G2)),
		 !,
		 call(G),
		 '$call_with_default_policy'(comma_errors(G1, G2, B)).
','(G, Atom, B) :- Atom == !, !, call(G), '$set_cp'(B).
','(G1, G2, _)  :- call(G1), call(G2).

;(G1, G2) :- '$get_b_value'(B), ;(G1, G2, B).

:- non_counted_backtracking semicolon_compound_selector/3.
semicolon_compound_selector(->(G2, G3), G4, B) :-
    (  call(G2) ->
       call(G3)
    ;  '$set_cp'(B),
       call(G4)
    ).
semicolon_compound_selector(','(G2, G3), G4, B) :-
    (  ','(G2, G3, B)
    ;  '$set_cp'(B),
       call(G4)
    ).
semicolon_compound_selector(';'(G2, G3), G4, B) :-
    (  ';'(G2, G3, B)
    ;  '$set_cp'(B),
       call(G4)
    ).

:- non_counted_backtracking (;)/3.
;(G1, G4, B) :-
    ( (  G1 = (_ -> _)
      ;  G1 = (_ , _)
      ;  G1 = (_ ; _) 
      ) ->
      !,
      semicolon_compound_selector(G1, G4, B)
    ).
;(G1, G2, B) :-
    G1 == !, !, '$set_cp'(B), call(G2).
;(G1, G2, B) :-
    G2 == !, !, call(G1), '$set_cp'(B).
;(G, _, _) :-
    call(G).
;(_, G, _) :-
    call(G).

G1 -> G2 :- '$get_b_value'(B), '$call_with_default_policy'(->(G1, G2, B)).

:- non_counted_backtracking (->)/3.
->(G1, G2, B) :- G2 == !, call(G1), '$set_cp'(B).
->(G1, G2, B) :- call(G1), '$set_cp'(B), call(G2).

% univ.

:- non_counted_backtracking univ_errors/3.
univ_errors(Term, List, N) :-
    '$skip_max_list'(N, -1, List, R),
    ( var(R)        ->
       (  var(Term), throw(error(instantiation_error, (=..)/2))      % 8.5.3.3 a)
       ;  true
       )
    ;  R \== []     ->
       throw(error(type_error(list, List), (=..)/2))                % 8.5.3.3 b)
    ;  List = [H|T] ->
       (  var(H), var(Term), % R == [] => List is a proper list.
       	  throw(error(instantiation_error, (=..)/2))                 % 8.5.3.3 c)
       ;  T \== [], nonvar(H), \+ atom(H),
       	  throw(error(type_error(atom, H), (=..)/2))                 % 8.5.3.3 d)
       ;  compound(H), T == [],
       	  throw(error(type_error(atomic, H), (=..)/2))               % 8.5.3.3 e)
       ;  var(Term), max_arity(M), N - 1 > M,
       	  throw(error(representation_error(max_arity), (=..)/2))     % 8.5.3.3 g)
       ;  true
       )
    ;  var(Term)    ->
       throw(error(domain_error(non_empty_list, List), (=..)/2))    % 8.5.3.3 f)
    ;  true
    ).

Term =.. List :- '$call_with_default_policy'(univ_errors(Term, List, N)),
		 '$call_with_default_policy'(univ_worker(Term, List, N)).


:- non_counted_backtracking univ_worker/3.

univ_worker(Term, List, _) :-
    atomic(Term), !, '$call_with_default_policy'(List = [Term]).
univ_worker(Term, [Name|Args], N) :-
    var(Term), !,
    '$call_with_default_policy'(Arity is N-1),
    '$call_with_default_policy'(functor(Term, Name, Arity)),
    '$call_with_default_policy'(get_args(Args, Term, 1, Arity)).
univ_worker(Term, List, _) :-
    '$call_with_default_policy'(functor(Term, Name, Arity)),
    '$call_with_default_policy'(get_args(Args, Term, 1, Arity)),
    '$call_with_default_policy'(List = [Name|Args]).


:- non_counted_backtracking get_args/4.

get_args(Args, _, _, 0) :-
    !, '$call_with_default_policy'(Args = []).
get_args([Arg], Func, N, N) :-
    !, '$call_with_default_policy'(arg(N, Func, Arg)).
get_args([Arg|Args], Func, I0, N) :-
    '$call_with_default_policy'(arg(I0, Func, Arg)),
    '$call_with_default_policy'(I1 is I0 + 1),
    '$call_with_default_policy'(get_args(Args, Func, I1, N)).

parse_write_options(Options, OptionValues, Stub) :-
    DefaultOptions = [ignore_ops-false, max_depth-0, numbervars-false,
                      quoted-false, variable_names-[]],
    parse_options_list(Options, parse_write_options_, DefaultOptions, OptionValues, Stub).

parse_write_options_(ignore_ops(IgnoreOps), ignore_ops-IgnoreOps) :-
    (  nonvar(IgnoreOps), lists:member(IgnoreOps, [true, false])
    ;
       throw(error(domain_error(write_option, ignore_ops(IgnoreOps)), _))
    ).
parse_write_options_(quoted(Quoted), quoted-Quoted) :-
    (  nonvar(Quoted), lists:member(Quoted, [true, false])
    ;
       throw(error(domain_error(write_option, quoted(Quoted)), _))
    ).
parse_write_options_(numbervars(NumberVars), numbervars-NumberVars) :-
    (  nonvar(NumberVars), lists:member(NumberVars, [true, false])
    ;
       throw(error(domain_error(write_option, numbervars(NumberVars)), _))
    ).
parse_write_options_(variable_names(VNNames), variable_names-VNNames) :-
    must_be_var_names_list(VNNames).
parse_write_options_(max_depth(MaxDepth), max_depth-MaxDepth) :-
    (  integer(MaxDepth), MaxDepth >= 0
    ;
       throw(error(domain_error(write_option, max_depth(MaxDepth)), _))
    ).

must_be_var_names_list(VarNames) :-
    '$skip_max_list'(_, -1, VarNames, Tail),
    (  Tail == [] -> must_be_var_names_list_(VarNames, VarNames)
    ;  var(Tail)  -> throw(error(instantiation_error, write_term/2))
    ;  throw(error(domain_error(write_option, variable_names(VarNames)), write_term/2))
    ).

must_be_var_names_list_([], List).
must_be_var_names_list_([VarName | VarNames], List) :-
    (  nonvar(VarName) ->
       (  VarName = (Atom = _) ->
	      (  atom(Atom) -> must_be_var_names_list_(VarNames, List)
	      ;  var(Atom)  -> throw(error(instantiation_error, write_term/2))
	      ;  throw(error(domain_error(write_option, variable_names(List)), write_term/2))
	      )
       ;  throw(error(domain_error(write_option, variable_names(List)), write_term/2))
       )
    ;  throw(error(instantiation_error, write_term/2))
    ).


write_term(Term, Options) :-
    current_output(Stream),
    write_term(Stream, Term, Options).

write_term(Stream, Term, Options) :-
    parse_write_options(Options, [IgnoreOps, MaxDepth, NumberVars, Quoted, VNNames], write_term/3),
    '$write_term'(Stream, Term, IgnoreOps, NumberVars, Quoted, VNNames, MaxDepth).


write(Term) :-
    current_output(Stream),
    '$write_term'(Stream, Term, false, true, false, [], 0).

write_canonical(Term) :-
    current_output(Stream),
    '$write_term'(Stream, Term, true, false, true, [], 0).

writeq(Term) :-
    current_output(Stream),
    '$write_term'(Stream, Term, false, true, true, [], 0).



select_rightmost_options([Option-Value | OptionPairs], OptionValues) :-
    (  pairs:same_key(Option, OptionPairs, OtherValues, _),
       OtherValues == []  ->
       OptionValues = [Value | OptionValues0],
       select_rightmost_options(OptionPairs, OptionValues0)
    ;
       select_rightmost_options(OptionPairs, OptionValues)
    ).
select_rightmost_options([], []).


parse_options_list(Options, Selector, DefaultPairs, OptionValues, Stub) :-
    '$skip_max_list'(_, -1, Options, Tail),
    (  Tail == [] ->
       true
    ;  var(Tail) ->
       throw(error(instantiation_error, Stub))       % 8.11.5.3c)
    ;  Tail \== [] ->
       throw(error(type_error(list, Options), Stub)) % 8.11.5.3e)
    ),
    (  lists:maplist(nonvar, Options),
       catch(lists:maplist(Selector, Options, OptionPairs0),
             error(E, _),
             throw(error(E, Stub))) ->
       lists:append(DefaultPairs, OptionPairs0, OptionPairs1),
       keysort(OptionPairs1, OptionPairs),
       select_rightmost_options(OptionPairs, OptionValues)
    ;
       throw(error(instantiation_error, Stub))       % 8.11.5.3c)
    ).


parse_read_term_options(Options, OptionValues, Stub) :-
    DefaultOptions = [singletons-_, variables-_, variable_names-_],
    parse_options_list(Options, parse_read_term_options_, DefaultOptions, OptionValues, Stub).


parse_read_term_options_(singletons(Vars), singletons-Vars).
parse_read_term_options_(variables(Vars), variables-Vars).
parse_read_term_options_(variable_names(Vars), variable_names-Vars).
parse_read_term_options_(E,_) :-
    throw(error(domain_error(read_option, E), _)).



read_term(Stream, Term, Options) :-
    parse_read_term_options(Options, [Singletons, VariableNames, Variables], read_term/3),
    '$read_term'(Stream, Term, Singletons, Variables, VariableNames).

read_term(Term, Options) :-
    current_input(Stream),
    read_term(Stream, Term, Options).


% expand_goal.

expand_goal(Term0, Term) :- '$expand_goal'(Term0, Term).

% expand_term.

expand_term(Term0, Term) :- '$expand_term'(Term0, Term).

% term_variables.

% ensures List is either a variable or a list.
can_be_list(List, _)  :- var(List), !.
can_be_list(List, _)  :- '$skip_max_list'(_, -1, List, Tail), ( var(Tail) -> true ; Tail == []), !.
can_be_list(List, PI) :- throw(error(type_error(list, List), PI)).

term_variables(Term, Vars) :-
    can_be_list(Vars, term_variables/2),
    '$term_variables'(Term, Vars).

% exceptions.

catch(G,C,R) :- '$get_current_block'(Bb), '$call_with_default_policy'(catch(G,C,R,Bb)).

:- non_counted_backtracking catch/4.
catch(G,C,R,Bb) :-
    '$install_new_block'(NBb),
    call(G),
    '$call_with_default_policy'(end_block(Bb, NBb)).
catch(G,C,R,Bb) :-
    '$reset_block'(Bb),
    '$get_ball'(Ball),
    '$call_with_default_policy'(handle_ball(Ball, C, R)).

:- non_counted_backtracking end_block/2.
end_block(Bb, NBb) :- '$clean_up_block'(NBb), '$reset_block'(Bb).
end_block(Bb, NBb) :- '$reset_block'(NBb), '$fail'.

:- non_counted_backtracking handle_ball/3.
handle_ball(C, C, R) :- !, '$erase_ball', call(R).
handle_ball(_, _, _) :- '$unwind_stack'.

throw(Ball) :- '$set_ball'(Ball), '$unwind_stack'.

:- non_counted_backtracking '$iterate_find_all'/4.
'$iterate_find_all'(Template, Goal, _, LhOffset) :-
    call(Goal),
    '$copy_to_lh'(LhOffset, Template),
    '$fail'.
'$iterate_find_all'(_, _, Solutions, LhOffset) :-
    '$truncate_if_no_lh_growth'(LhOffset),
    '$get_lh_from_offset'(LhOffset, Solutions).

truncate_lh_to(LhLength) :- '$truncate_lh_to'(LhLength).

findall(Template, Goal, Solutions) :-
    error:can_be(list, Solutions),
    '$lh_length'(LhLength),
    '$call_with_default_policy'(catch('$iterate_find_all'(Template, Goal, Solutions, LhLength),
				      Error,
				      ( truncate_lh_to(LhLength), throw(Error) ))).

:- non_counted_backtracking '$iterate_find_all_diff'/5.
'$iterate_find_all_diff'(Template, Goal, _, _, LhOffset) :-
    call(Goal),
    '$copy_to_lh'(LhOffset, Template),
    '$fail'.
'$iterate_find_all_diff'(_, _, Solutions0, Solutions1, LhOffset) :-
    '$truncate_if_no_lh_growth_diff'(LhOffset, Solutions1),
    '$get_lh_from_offset_diff'(LhOffset, Solutions0, Solutions1).


findall(Template, Goal, Solutions0, Solutions1) :-
    error:can_be(list, Solutions0),
    error:can_be(list, Solutions1),
    '$lh_length'(LhLength),
    '$call_with_default_policy'(catch('$iterate_find_all_diff'(Template, Goal, Solutions0,
							       Solutions1, LhLength),
				      Error,
				      ( truncate_lh_to(LhLength), throw(Error) ))).

set_difference([X|Xs], [Y|Ys], Zs) :-
    X == Y, !, set_difference(Xs, [Y|Ys], Zs).
set_difference([X|Xs], [Y|Ys], [X|Zs]) :-
    X @< Y, !, set_difference(Xs, [Y|Ys], Zs).
set_difference([X|Xs], [Y|Ys], Zs) :-
    X @> Y, !, set_difference([X|Xs], Ys, Zs).
set_difference([], _, []) :- !.
set_difference(Xs, [], Xs).

group_by_variant([V2-S2 | Pairs], V1-S1, [S2 | Solutions], Pairs0) :-
    iso_ext:variant(V1, V2), !, V1 = V2, group_by_variant(Pairs, V2-S2, Solutions, Pairs0).
group_by_variant(Pairs, _, [], Pairs).

group_by_variants([V-S|Pairs], [V-Solution|Solutions]) :-
    group_by_variant([V-S|Pairs], V-S, Solution, Pairs0),
    group_by_variants(Pairs0, Solutions).
group_by_variants([], []).

iterate_variants([V-Solution|GroupSolutions], V, Solution) :-
    (  GroupSolutions == [] -> !
    ;  true
    ).
iterate_variants([_|GroupSolutions], Ws, Solution) :-
    iterate_variants(GroupSolutions, Ws, Solution).

rightmost_power(Term, FinalTerm, Xs) :-
    (  Term = X ^ Y
    -> (  var(Y) -> FinalTerm = Y, Xs = [X]
       ;  Xs = [X | Xss], rightmost_power(Y, FinalTerm, Xss)
       )
    ;  Xs = [], FinalTerm = Term
    ).

findall_with_existential(Template, Goal, PairedSolutions, Witnesses0, Witnesses) :-
    (  nonvar(Goal), Goal = _ ^ _ ->
       rightmost_power(Goal, Goal1, ExistentialVars0),
       term_variables(ExistentialVars0, ExistentialVars),
       sort(Witnesses0, Witnesses1),
       sort(ExistentialVars, ExistentialVars1),
       set_difference(Witnesses1, ExistentialVars1, Witnesses),
       findall(Witnesses-Template, Goal1, PairedSolutions)
    ;  Witnesses = Witnesses0,
       findall(Witnesses-Template, Goal, PairedSolutions)
    ).

bagof(Template, Goal, Solution) :-
    error:can_be(list, Solution),
    term_variables(Template, TemplateVars0),
    term_variables(Goal, GoalVars0),
    sort(TemplateVars0, TemplateVars),
    sort(GoalVars0, GoalVars),
    set_difference(GoalVars, TemplateVars, Witnesses0),
    findall_with_existential(Template, Goal, PairedSolutions0, Witnesses0, Witnesses),
    keysort(PairedSolutions0, PairedSolutions),
    group_by_variants(PairedSolutions, GroupedSolutions),
    iterate_variants(GroupedSolutions, Witnesses, Solution).

iterate_variants_and_sort([V-Solution0|GroupSolutions], V, Solution) :-
    sort(Solution0, Solution),
    (  GroupSolutions == [] -> !
    ;  true
    ).
iterate_variants_and_sort([_|GroupSolutions], Ws, Solution) :-
    iterate_variants_and_sort(GroupSolutions, Ws, Solution).

setof(Template, Goal, Solution) :-
    error:can_be(list, Solution),
    term_variables(Template, TemplateVars0),
    term_variables(Goal, GoalVars0),
    sort(TemplateVars0, TemplateVars),
    sort(GoalVars0, GoalVars),
    set_difference(GoalVars, TemplateVars, Witnesses0),
    findall_with_existential(Template, Goal, PairedSolutions0, Witnesses0, Witnesses),
    keysort(PairedSolutions0, PairedSolutions),
    group_by_variants(PairedSolutions, GroupedSolutions),
    iterate_variants_and_sort(GroupedSolutions, Witnesses, Solution).

% Clause retrieval and information.

'$clause_body_is_valid'(B) :-
    (  var(B) -> true
    ;  functor(B, Name, _) -> (  atom(Name), Name \== '.' -> true
			      ;  throw(error(type_error(callable, B), clause/2))
			      )
    ;  throw(error(type_error(callable, B), clause/2))
    ).

'$module_clause'(H, B, Module) :-
    (  var(H) -> throw(error(instantiation_error, clause/2))
    ;  functor(H, Name, Arity) -> (  Name == '.' -> throw(error(type_error(callable, H), clause/2))
				  ;  '$module_head_is_dynamic'(H, Module) ->
				     '$clause_body_is_valid'(B),
				     '$get_module_clause'(H, B, Module)
				  ;  throw(error(permission_error(access, private_procedure, Name/Arity),
						 clause/2))
				  )
    ;  throw(error(type_error(callable, H), clause/2))
    ).

clause(H, B) :-
    (  var(H) -> throw(error(instantiation_error, clause/2))
    ;  functor(H, Name, Arity) ->
       (  Name == '.' -> throw(error(type_error(callable, H), clause/2))
	   ;  Name == (:), Arity =:= 2 ->
		  arg(1, H, Module),
		  arg(2, H, F),
		  '$module_clause'(F, B, Module)
	   %% '$no_such_predicate' fails if H is not callable.
	   ;  '$no_such_predicate'(H) -> '$fail'
	   ;  '$head_is_dynamic'(H) -> '$clause_body_is_valid'(B),
							       '$get_clause'(H, B)
	   ;  throw(error(permission_error(access, private_procedure, Name/Arity),
					  clause/2))
	   )
    ;  throw(error(type_error(callable, H), clause/2))
    ).

call_module_asserta(Head, Body, Name, Arity, Module) :-
    '$clause_body_is_valid'(Body),
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(Module:VarHead, VarBody), Clauses),
    '$module_asserta'((Head :- Body), Clauses, Name, Arity, Module).

call_asserta(Head, Body, Name, Arity) :-
    '$clause_body_is_valid'(Body),
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(VarHead, VarBody), Clauses),
    '$asserta'((Head :- Body), Clauses, Name, Arity).

module_asserta_clause(Head, Body, Module) :-
    (  var(Head) -> throw(error(instantiation_error, asserta/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       (  '$module_head_is_dynamic'(Head, Module) -> call_module_asserta(Head, Body, Name, Arity, Module)
       ;  throw(error(permission_error(modify, static_procedure, Name/Arity), asserta/1))
       )
    ;  throw(error(type_error(callable, Head), asserta/1))
    ).

asserta_clause(Head, Body) :-
    (  var(Head) -> throw(error(instantiation_error, asserta/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       ( Name == (:), Arity =:= 2 ->
	 arg(1, Head, Module),
	 arg(2, Head, F),
	 module_asserta_clause(F, Body, Module)
       ; '$no_such_predicate'(Head) -> call_asserta(Head, Body, Name, Arity)
       ; '$head_is_dynamic'(Head) -> call_asserta(Head, Body, Name, Arity)
       ;  throw(error(permission_error(modify, static_procedure, Name/Arity), asserta/1))
       )
    ;  throw(error(type_error(callable, Head), asserta/1))
    ).

asserta(Clause) :-
    (  Clause \= (_ :- _) -> Head = Clause, Body = true, asserta_clause(Head, Body)
    ;  Clause = (Head :- Body) -> asserta_clause(Head, Body)
    ).

call_module_assertz(Head, Body, Name, Arity, Module) :-
    '$clause_body_is_valid'(Body),
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(Module:VarHead, VarBody), Clauses),
    '$module_assertz'((Head :- Body), Clauses, Name, Arity, Module).

call_assertz(Head, Body, Name, Arity) :-
    '$clause_body_is_valid'(Body),
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(VarHead, VarBody), Clauses),
    '$assertz'((Head :- Body), Clauses, Name, Arity).

module_assertz_clause(Head, Body, Module) :-
    (  var(Head) -> throw(error(instantiation_error, assertz/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       (  '$module_head_is_dynamic'(Head, Module) -> call_module_assertz(Head, Body, Name, Arity, Module)
       ;  throw(error(permission_error(modify, static_procedure, Name/Arity), assertz/1))
       )
    ;  throw(error(type_error(callable, Head), assertz/1))
    ).

assertz_clause(Head, Body) :-
    (  var(Head) -> throw(error(instantiation_error, assertz/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       ( Name == (:), Arity =:= 2 ->
	 arg(1, Head, Module),
	 arg(2, Head, F),
	 module_assertz_clause(F, Body, Module)
       ; '$no_such_predicate'(Head) ->
	 call_assertz(Head, Body, Name, Arity)
       ; '$head_is_dynamic'(Head) ->
	 call_assertz(Head, Body, Name, Arity)
       ; throw(error(permission_error(modify, static_procedure, Name/Arity), assertz/1))
       )
    ;  throw(error(type_error(callable, Head), assertz/1))
    ).

assertz(Clause) :-
    (  Clause \= (_ :- _) -> Head = Clause, Body = true, assertz_clause(Head, Body)
    ;  Clause = (Head :- Body) -> assertz_clause(Head, Body)
    ).

first_match_index([Clause0 | Clauses], Clause1, N0, N) :-
    (  Clause0 \= Clause1 ->
       N1 is N0 + 1,
       first_match_index(Clauses, Clause1, N1, N)
    ;  N0 = N, Clause0 = Clause1
    ).

retract_clauses([Clause | Clauses0], Head, Body, Name, Arity) :-
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(VarHead, VarBody), Clauses1),
    first_match_index(Clauses1, (Head :- Body), 0, N),
    (  Clauses0 == [] -> !
    ;  true
    ),
    '$retract_clause'(Name, Arity, N, Clauses1).
retract_clauses([_ | Clauses0], Head, Body, Name, Arity) :-
    retract_clauses(Clauses0, Head, Body, Name, Arity).

call_retract(Head, Body, Name, Arity) :-
    findall((Head :- Body), clause(Head, Body), Clauses),
    retract_clauses(Clauses, Head, Body, Name, Arity).

module_retract_clauses([Clause|Clauses0], Head, Body, Name, Arity, Module) :-
    functor(VarHead, Name, Arity),
    findall((VarHead :- VarBody), clause(Module:VarHead, VarBody), Clauses1),
    first_match_index(Clauses1, (Head :- Body), 0, N),
    (  Clauses0 == [] -> !
    ;  true
    ),
    '$module_retract_clause'(Name, Arity, N, Clauses1, Module).
module_retract_clauses([_|Clauses0], Head, Body, Name, Arity, Module) :-
    module_retract_clauses(Clauses0, Head, Body, Name, Arity, Module).

call_module_retract(Head, Body, Name, Arity, Module) :-
    findall((Head :- Body), clause(Module:Head, Body), Clauses),
    module_retract_clauses(Clauses, Head, Body, Name, Arity, Module).

retract_module_clause(Head, Body, Module) :-
    (  var(Head) -> throw(error(instantiation_error, retract/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       ( '$module_head_is_dynamic'(Head, Module) ->
	 call_module_retract(Head, Body, Name, Arity, Module)
       ; throw(error(permission_error(modify, static_procedure, Name/Arity), retract/1))
       )
    ;  throw(error(type_error(callable, Head), retract/1))
    ).

retract_clause(Head, Body) :-
    (  var(Head) -> throw(error(instantiation_error, retract/1))
    ;  functor(Head, Name, Arity), atom(Name), Name \== '.' ->
       ( Name == (:), Arity =:= 2 ->
	 arg(1, Head, Module),
	 arg(2, Head, F),
	 retract_module_clause(F, Body, Module)
       ; '$head_is_dynamic'(Head) -> call_retract(Head, Body, Name, Arity)
       ; '$no_such_predicate'(Head) -> '$fail'
       ; throw(error(permission_error(modify, static_procedure, Name/Arity), retract/1))
       )
    ;  throw(error(type_error(callable, Head), retract/1))
    ).

retract(Clause) :-
    (  Clause \= (_ :- _) -> Head = Clause, Body = true, retract_clause(Head, Body)
    ;  Clause = (Head :- Body) -> retract_clause(Head, Body)
    ).

module_abolish(Pred, Module) :-
    (  var(Pred) -> throw(error(instantiation_error), abolish/1)
    ;  Pred = Name/Arity ->
       (  var(Name)  -> throw(error(instantiation_error, abolish/1))
       ;  integer(Arity) ->
	  ( \+ atom(Name) -> throw(error(type_error(atom, Name), abolish/1))
	  ; Arity < 0 -> throw(error(domain_error(not_less_than_zero, Arity), abolish/1))
	  ; max_arity(N), Arity > N -> throw(error(representation_error(max_arity), abolish/1))
	  ; functor(Head, Name, Arity) ->
	    (  '$module_head_is_dynamic'(Head, Module) ->
	       '$abolish_module_clause'(Name, Arity, Module)
	    ;  throw(error(permission_error(modify, static_procedure, Pred), abolish/1))
	    )
	  )
       ;  throw(error(type_error(integer, Arity), abolish/1))
       )
    ; throw(error(type_error(predicate_indicator, Module:Pred), abolish/1))
    ).

abolish(Pred) :-
    (  var(Pred) -> throw(error(instantiation_error), abolish/1)
    ;  Pred = Module:InnerPred -> module_abolish(InnerPred, Module)
    ;  Pred = Name/Arity ->
       (  var(Name)  -> throw(error(instantiation_error, abolish/1))
       ;  var(Arity) -> throw(error(instantiation_error, abolish/1))
       ;  integer(Arity) ->
	  ( \+ atom(Name) -> throw(error(type_error(atom, Name), abolish/1))
	  ; Arity < 0 -> throw(error(domain_error(not_less_than_zero, Arity), abolish/1))
	  ; max_arity(N), Arity > N -> throw(error(representation_error(max_arity), abolish/1))
	  ; functor(Head, Name, Arity) ->
	    (  '$no_such_predicate'(Head) -> true
	    ;  '$head_is_dynamic'(Head) -> '$abolish_clause'(Name, Arity)
	    ;  throw(error(permission_error(modify, static_procedure, Pred), abolish/1))
	    )
	  )
       ;  throw(error(type_error(integer, Arity), abolish/1))
       )
    ;  throw(error(type_error(predicate_indicator, Pred), abolish/1))
    ).

'$iterate_db_refs'(Ref, Name/Arity) :-
    '$lookup_db_ref'(Ref, Name, Arity).
'$iterate_db_refs'(Ref, Name/Arity) :-
    '$get_next_db_ref'(Ref, NextRef),
    '$iterate_db_refs'(NextRef, Name/Arity).

current_predicate(Pred) :-
    (  nonvar(Pred), Pred \= _ / _
    -> throw(error(type_error(predicate_indicator, Pred), current_predicate/1))
    ;  '$get_next_db_ref'(Ref, _),
       '$iterate_db_refs'(Ref, Pred)
    ).

'$iterate_op_db_refs'(Ref, Priority, Spec, Op) :-
    '$lookup_op_db_ref'(Ref, Priority, Spec, Op).
'$iterate_op_db_refs'(Ref, Priority, Spec, Op) :-
    '$get_next_op_db_ref'(Ref, NextRef),
    '$iterate_op_db_refs'(NextRef, Priority, Spec, Op).

can_be_op_priority(Priority) :- var(Priority).
can_be_op_priority(Priority) :- op_priority(Priority).

can_be_op_specifier(Spec) :- var(Spec).
can_be_op_specifier(Spec) :- op_specifier(Spec).

current_op(Priority, Spec, Op) :-
    (  can_be_op_priority(Priority), can_be_op_specifier(Spec), error:can_be(atom, Op)
    -> '$get_next_op_db_ref'(Ref, _),
       '$iterate_op_db_refs'(Ref, Priority, Spec, Op)
    ).

list_of_op_atoms(Var) :-
    var(Var), throw(error(instantiation_error, op/3)). % 8.14.3.3 c)
list_of_op_atoms([Atom|Atoms]) :-
    ( valid_op(Atom) -> list_of_op_atoms(Atoms) % 8.14.3.3 k).
    ; var(Atom) -> throw(error(instantiation_error, op/3)) % 8.14.3.3 c)
    ; throw(error(type_error(atom, Atom), op/3)) % 8.14.3.3 g)
    ).
list_of_op_atoms([]).

op_priority(Priority) :-
    integer(Priority), !,
    (  ( Priority < 0 ; Priority > 1200 ) ->
       throw(error(domain_error(operator_priority, Priority))) % 8.14.3.3 h)
    ;  true
    ).
op_priority(Priority) :-
    throw(error(type_error(integer, Priority), op/3)). % 8.14.3.3 d)

op_specifier(OpSpec) :- atom(OpSpec),
    (  lists:member(OpSpec, [yfx, xfy, xfx, yf, fy, xf, fx]), !
    ;  throw(error(domain_error(operator_specifier, OpSpec), op/3)) % 8.14.3.3 i)
    ).
op_specifier(OpSpec) :- throw(error(type_error(atom, OpSpec), op/3)).

valid_op(Op) :- atom(Op),
    (  Op == (',') -> throw(error(permission_error(modify, operator, (',')), op/3)) % 8.14.3.3 j), k).
    ;  Op == {} -> throw(error(permission_error(create, operator, {}), op/3))
    ;  Op == [] -> throw(error(permission_error(create, operator, []), op/3))
    ;  true
    ).

op_(Priority, OpSpec, Op) :- '$op'(Priority, OpSpec, Op).

op(Priority, OpSpec, Op) :-
    (  var(Priority) -> throw(error(instantiation_error, op/3)) % 8.14.3.3 a)
    ;  var(OpSpec)   -> throw(error(instantiation_error, op/3)) % 8.14.3.3 b)
    ;  var(Op)       -> throw(error(instantiation_error, op/3)) % 8.14.3.3 c)
    ;  Op == '|'     -> (  op_priority(Priority), op_specifier(OpSpec),
			   lists:member(OpSpec, [xfx, xfy, yfx]), ( Priority >= 1001 ; Priority == 0 )
			-> '$op'(Priority, OpSpec, Op)
			;  throw(error(permission_error(create, operator, (|)), op/3))) % www.complang.tuwien.ac.at/ulrich/iso-prolog/conformity_testing#72
    ;  valid_op(Op), op_priority(Priority), op_specifier(OpSpec) ->
       '$op'(Priority, OpSpec, Op)
    ;  list_of_op_atoms(Op), op_priority(Priority), op_specifier(OpSpec) ->
       lists:maplist(op_(Priority, OpSpec), Op), !
    ;  throw(error(type_error(list, Op), op/3)) % 8.14.3.3 f)
    ).

halt :- '$halt'.

atom_length(Atom, Length) :-
    (  var(Atom)  -> throw(error(instantiation_error, atom_length/2)) % 8.16.1.3 a)
    ;  atom(Atom) -> (  var(Length) -> '$atom_length'(Atom, Length)
		     ;  integer(Length), Length >= 0 -> '$atom_length'(Atom, Length)
		     ;  integer(Length) -> throw(error(domain_error(not_less_than_zero, Length), atom_length/2))
		     % 8.16.1.3 d)
		     ;  throw(error(type_error(integer, Length), atom_length/2)) % 8.16.1.3 c)
		     )
    ;  throw(error(type_error(atom, Atom), atom_length/2)) % 8.16.1.3 b)
    ).

atom_chars(Atom, List) :-
    '$skip_max_list'(_, -1, List, Tail),
    (  ( Tail == [] ; var(Tail) ) -> true
    ;  throw(error(type_error(list, List), atom_chars/2))
    ),
    (  var(Atom) ->
       (  var(Tail) -> throw(error(instantiation_error, atom_chars/2))
       ;  ground(List), Tail == [] -> '$atom_chars'(Atom, List)
       ;  throw(error(instantiation_error, atom_chars/2))
       )
    ;  atom(Atom) -> can_be_chars_or_vars(List, atom_chars/2), '$atom_chars'(Atom, List)
    ;  throw(error(type_error(atom, Atom), atom_chars/2))
    ).

atom_codes(Atom, List) :-
    '$skip_max_list'(_, -1, List, Tail),
    (  ( Tail == [] ; var(Tail) ) -> true
    ;  throw(error(type_error(list, List), atom_codes/2))
    ),
    (  var(Atom) ->
       (  var(Tail) -> throw(error(instantiation_error, atom_codes/2))
       ;  ground(List), Tail == [] -> '$atom_codes'(Atom, List)
       ;  throw(error(instantiation_error, atom_codes/2))
       )
    ;  atom(Atom) -> can_be_codes_or_vars(List, atom_codes/2), '$atom_codes'(Atom, List)
    ;  throw(error(type_error(atom, Atom), atom_codes/2))
    ).

atom_concat(Atom_1, Atom_2, Atom_12) :-
    error:can_be(atom, Atom_1),
    error:can_be(atom, Atom_2),
    error:can_be(atom, Atom_12),
    (  var(Atom_1) ->
       (  var(Atom_12) -> throw(error(instantiation_error, atom_concat/3))
       ;  atom_chars(Atom_12, Atom_12_Chars),
	  lists:append(BeforeChars, AfterChars, Atom_12_Chars),
	  atom_chars(Atom_1, BeforeChars),
	  atom_chars(Atom_2, AfterChars)
       )
    ;  var(Atom_2) ->
       (  var(Atom_12) -> throw(error(instantiation_error, atom_concat/3))
       ;  atom_chars(Atom_1, Atom_1_Chars),
	  atom_chars(Atom_12, Atom_12_Chars),
	  lists:append(Atom_1_Chars, Atom_2_Chars, Atom_12_Chars),
	  atom_chars(Atom_2, Atom_2_Chars)
       )
    ;  atom_chars(Atom_1, Atom_1_Chars),
       atom_chars(Atom_2, Atom_2_Chars),
       lists:append(Atom_1_Chars, Atom_2_Chars, Atom_12_Chars),
       atom_chars(Atom_12, Atom_12_Chars)
    ).

sub_atom(Atom, Before, Length, After, Sub_atom) :-
    error:must_be(atom, Atom),
    error:can_be(atom, Sub_atom),
    error:can_be(integer, Before),
    error:can_be(integer, Length),
    error:can_be(integer, After),
    (  integer(Before), Before < 0 -> throw(error(domain_error(not_less_than_zero, Before), sub_atom/5))
    ;  integer(Length), Length < 0 -> throw(error(domain_error(not_less_than_zero, Length), sub_atom/5))
    ;  integer(After), After < 0 -> throw(error(domain_error(not_less_than_zero, After), sub_atom/5))
    ;  atom_chars(Atom, AtomChars),
       lists:append(BeforeChars, LengthAndAfterChars, AtomChars),
       lists:append(LengthChars, AfterChars, LengthAndAfterChars),
       '$skip_max_list'(Before, -1, BeforeChars, []),
       '$skip_max_list'(Length, -1, LengthChars, []),
       '$skip_max_list'(After, -1, AfterChars, []),
       atom_chars(Sub_atom, LengthChars)
    ).

char_code(Char, Code) :-
    (  var(Char) ->
       (  var(Code) -> throw(error(instantiation_error, char_code/2))
       ;  integer(Code) -> '$char_code'(Char, Code)
       ;  throw(error(type_error(integer, Code), char_code/2))
       )
    ;  atom_length(Char, 1) -> '$char_code'(Char, Code)
    ;  throw(error(type_error(character, Char), char_code/2))
    ).

get_char(C) :-
    (  var(C) -> '$get_char'(C)
    ;  C == end_of_file  -> '$get_char'(C)
    ;  atom_length(C, 1) -> '$get_char'(C)
    ;  throw(error(type_error(in_character, C), get_char/1))
    ).

can_be_number(N, PI) :-
    (  var(N) -> true
    ;  must_be_number(N, PI)
    ).

must_be_number(N, _) :-
    (  integer(N)
    ;  float(N)
    ),
    !.
must_be_number(N, PI) :-
    (  nonvar(N) -> throw(error(type_error(number, N), PI))
    ;  throw(error(instantiation_error, PI))
    ).

can_be_chars_or_vars(Cs, _)  :- var(Cs), !.
can_be_chars_or_vars(Cs, PI) :-
    (  string(Cs) ->
       current_prolog_flag(double_quotes, chars)
    ;  chars_or_vars(Cs, PI)
    ).

chars_or_vars([], _).
chars_or_vars([C|Cs], PI) :-
    (  nonvar(C) ->
       (  catch(atom_length(C, 1), _, false) ->
	  (  nonvar(Cs) -> chars_or_vars(Cs, PI)
	  ;  false
	  )
       ;  throw(error(type_error(character, C), PI))
       )
    ;  chars_or_vars(Cs, PI)
    ).

can_be_codes_or_vars(Cs, _)  :- var(Cs), !.
can_be_codes_or_vars(Cs, PI) :-
    (  string(Cs) ->
       current_prolog_flag(double_quotes, codes)
    ;  codes_or_vars(Cs, PI)
    ).

codes_or_vars([], _).
codes_or_vars([C|Cs], PI) :-
    (  nonvar(C) ->
       (  catch(char_code(_, C), _, false) ->
	  (  nonvar(Cs) -> codes_or_vars(Cs, PI)
	  ;  false
	  )
       ;  integer(C) -> throw(error(representation_error(character_code), PI))
       ;  throw(error(type_error(integer, C), PI))
       )
    ;  codes_or_vars(Cs, PI)
    ).

number_chars(N, Chs) :-
   (  ground(Chs)
   -> can_be_number(N, number_chars/2),
      can_be_list(Chs, number_chars/2),
      '$chars_to_number'(Chs, Nx),
      Nx = N
   ;  must_be_number(N, number_chars/2),
      (  var(Chs) -> true
      ;  can_be_list(Chs, number_chars/2)
      ,  chars_or_vars(Chs, number_chars/2)
      ),
      '$number_to_chars'(N, Chsx),
      Chsx = Chs
    ).

number_codes(N, Chs) :-
   (  ground(Chs)
   -> can_be_number(N, number_codes/2),
      can_be_list(Chs, number_codes/2),
      '$codes_to_number'(Chs, Nx),
      Nx = N
   ;  must_be_number(N, number_codes/2),
      (  var(Chs) -> true
      ;  can_be_list(Chs, number_codes/2)
      ,  codes_or_vars(Chs, number_codes/2)
      ),
      '$number_to_codes'(N, Chsx),
      Chsx = Chs
    ).

subsumes_term(General, Specific) :-
   \+ \+ (
      term_variables(Specific, SVs1),
      General = Specific,
      term_variables(SVs1, SVs2),
      SVs1 == SVs2
   ).

unify_with_occurs_check(X, Y) :- '$unify_with_occurs_check'(X, Y).

current_input(S) :- '$current_input'(S).

current_output(S) :- '$current_output'(S).

set_input(S) :-
    (  var(S) ->
       throw(error(instantiation_error, set_input/1))
    ;  '$set_input'(S)
    ).

set_output(S) :-
    (  var(S) ->
       throw(error(instantiation_error, set_output/1))
    ;  '$set_output'(S)
    ).


parse_stream_options(Options, OptionValues, Stub) :-
    DefaultOptions = [alias-[], eof_action-eof_code, reposition-false, type-text],
    parse_options_list(Options, parse_stream_options_, DefaultOptions, OptionValues, Stub).


parse_stream_options_(type(Type), type-Type) :-
    (  nonvar(Type), lists:member(Type, [text, binary]), !, true
    ;
       throw(error(domain_error(stream_option, type(Type)), _))
    ).
parse_stream_options_(reposition(Bool), reposition-Bool) :-
    (  nonvar(Bool), lists:member(Bool, [true, false]), !, true
    ;
       throw(error(domain_error(stream_option, reposition(Bool)), _))
    ).
parse_stream_options_(alias(A), alias-A) :-
    (  atom(A), A \== [], !, true
    ;
       throw(error(domain_error(stream_option, alias(A)), _))
    ).
parse_stream_options_(eof_action(Action), eof_action-Action) :-
    (  nonvar(Action), lists:member(Action, [eof_code, error, reset]), !, true
    ;
       throw(error(domain_error(stream_option, eof_action(Action)), _))
    ).
parse_stream_options_(E, _) :-
    throw(error(domain_error(stream_option, E), _)). % 8.11.5.3i)


open(SourceSink, Mode, Stream) :-
    open(SourceSink, Mode, Stream, []).

open(SourceSink, Mode, Stream, StreamOptions) :-
    (  var(SourceSink) ->
       throw(error(instantiation_error, open/4)) % 8.11.5.3a)
    ;  var(Mode) ->
       throw(error(instantiation_error, open/4)) % 8.11.5.3b)
    ;  \+ atom(Mode) ->
       throw(error(type_error(atom, Mode), open/4)) % 8.11.5.3d)
    ;  nonvar(Stream) ->
       throw(error(type_error(variable, Stream), open/4)) % 8.11.5.3f)
    ;
       parse_stream_options(StreamOptions, [Alias, EOFAction, Reposition, Type], open/4),
       '$open'(SourceSink, Mode, Stream, Alias, EOFAction, Reposition, Type)
    ).


parse_close_options(Options, OptionValues, Stub) :-
    DefaultOptions = [force-false],
    parse_options_list(Options, parse_close_options_, DefaultOptions, OptionValues, Stub).

parse_close_options_(force(Force), force-Force) :-
    (  nonvar(Force), lists:member(Force, [true, false]), !
    ;
       throw(error(domain_error(close_option, force(Force)), _))
    ).
parse_close_options_(E, _) :-
    throw(error(domain_error(close_option, E), _)).


close(Stream, CloseOptions) :-
    parse_close_options(CloseOptions, [Force], close/2),
    '$close'(Stream, CloseOptions).

close(Stream) :-
    close(Stream, []).
