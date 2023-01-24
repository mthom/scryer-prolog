:- module(builtins, [(=)/2, (\=)/2, (\+)/1, !/0, (',')/2, (->)/2,
                     (;)/2, (=..)/2, abolish/1, asserta/1, assertz/1,
                     at_end_of_stream/0, at_end_of_stream/1,
                     atom_chars/2, atom_codes/2, atom_concat/3,
                     atom_length/2, bagof/3, call/1, call/2, call/3,
                     call/4, call/5, call/6, call/7, call/8, call/9,
                     callable/1, catch/3, char_code/2, clause/2,
                     close/1, close/2, current_input/1,
                     current_output/1, current_op/3,
                     current_predicate/1, current_prolog_flag/2,
                     error/2, fail/0, false/0, findall/3, findall/4,
                     flush_output/0, flush_output/1, get_byte/1,
                     get_byte/2, get_char/1, get_char/2, get_code/1,
                     get_code/2, halt/0, halt/1, nl/0, nl/1,
                     number_chars/2, number_codes/2, once/1, op/3,
                     open/3, open/4, peek_byte/1, peek_byte/2,
                     peek_char/1, peek_char/2, peek_code/1,
                     peek_code/2, put_byte/1, put_byte/2, put_code/1,
                     put_code/2, put_char/1, put_char/2, read/1,
                     read_term/2, read_term/3, repeat/0, retract/1,
                     retractall/1, set_prolog_flag/2, set_input/1,
                     set_stream_position/2, set_output/1, setof/3,
                     stream_property/2, sub_atom/5, subsumes_term/2,
                     term_variables/2, throw/1, true/0,
                     unify_with_occurs_check/2, write/1, write/2,
                     write_canonical/1, write_canonical/2,
                     write_term/2, write_term/3, writeq/1, writeq/2]).


% unify.
X = X.

true.

false :- '$fail'.


% These are stub versions of call/{1-9} defined for bootstrapping.
% Once Scryer is bootstrapped, each is replaced with a version that
% uses expand_goal to pass the expanded goal along to '$call'.

call(_).

call(_, _).

call(_, _, _).

call(_, _, _, _).

call(_, _, _, _, _).

call(_, _, _, _, _, _).

call(_, _, _, _, _, _, _).

call(_, _, _, _, _, _, _, _).

call(_, _, _, _, _, _, _, _, _).


:- meta_predicate catch(0, ?, 0).

% flags.

current_prolog_flag(Flag, Value) :- Flag == max_arity, !, Value = 1023.
current_prolog_flag(max_arity, 1023).
current_prolog_flag(Flag, Value) :- Flag == bounded, !, Value = false.
current_prolog_flag(bounded, false).
current_prolog_flag(Flag, Value) :- Flag == integer_rounding_function, !, Value == toward_zero.
current_prolog_flag(integer_rounding_function, toward_zero).
current_prolog_flag(Flag, Value) :- Flag == double_quotes, !, '$get_double_quotes'(Value).
current_prolog_flag(double_quotes, Value) :- '$get_double_quotes'(Value).
current_prolog_flag(Flag, _) :- Flag == max_integer, !, '$fail'.
current_prolog_flag(Flag, _) :- Flag == min_integer, !, '$fail'.
current_prolog_flag(Flag, OccursCheckEnabled) :-
    Flag == occurs_check,
    !,
    '$is_sto_enabled'(OccursCheckEnabled).
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
set_prolog_flag(occurs_check, true) :-
    !, '$set_sto_as_unify'.
set_prolog_flag(occurs_check, false) :-
    !, '$set_nsto_as_unify'.
set_prolog_flag(occurs_check, error) :-
    !, '$set_sto_with_error_as_unify'.
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


:- meta_predicate \+(0).

\+ G :- call(G), !, false.
\+ _.


X \= X :- !, false.
_ \= _.


:- meta_predicate once(0).

once(G) :- call(G), !.


repeat.
repeat :- repeat.


:- meta_predicate ','(0,0).

:- meta_predicate ;(0,0).

:- meta_predicate ->(0,0).


G1 -> G2 :- control_entry_point((G1 -> G2)).


:- non_counted_backtracking staggered_if_then/2.

staggered_if_then(G1, G2) :-
    call(G1),
    !,
    call(G2).

G1 ; G2 :- control_entry_point((G1 ; G2)).


:- non_counted_backtracking staggered_sc/2.

staggered_sc(G, _) :-
    (  nonvar(G),
       G = '$call'(builtins:staggered_if_then(G1, G2)) ->
       call(G1),
       !,
       call(G2)
    ;  call(G)
    ).
staggered_sc(_, G) :- call(G).

!.

:- non_counted_backtracking set_cp/1.

set_cp(B) :- '$set_cp'(B).

','(G1, G2) :- control_entry_point((G1, G2)).


:- non_counted_backtracking control_entry_point/1.

control_entry_point(G) :-
    functor(G, Name, Arity),
    catch(builtins:control_entry_point_(G),
          dispatch_prep_error,
          builtins:throw(error(type_error(callable, G), Name/Arity))).


:- non_counted_backtracking control_entry_point_/1.

control_entry_point_(G) :-
    '$get_cp'(B),
    dispatch_prep(G,B,Conts),
    dispatch_call_list(Conts).


:- non_counted_backtracking cont_list_to_goal/2.

cont_list_goal([Cont], Cont) :- !.
cont_list_goal(Conts, '$call'(builtins:dispatch_call_list(Conts))).


:- non_counted_backtracking dispatch_prep/3.

dispatch_prep(Gs, B, [Cont|Conts]) :-
    (  callable(Gs) ->
       strip_module(Gs, M, Gs0),
       (  nonvar(Gs0),
          dispatch_prep_(Gs0, B, [Cont|Conts]) ->
          true
       ;  Gs0 == ! ->
          Cont = '$call'(builtins:set_cp(B)),
          Conts = []
       ;  Cont = Gs,
          Conts = []
       )
    ;  var(Gs) ->
       Cont = Gs,
       Conts = []
    ;  throw(dispatch_prep_error)
    ).


:- non_counted_backtracking dispatch_prep_/3.

dispatch_prep_((G1, G2), B, [Cont|Conts]) :-
    dispatch_prep(G1, B, IConts1),
    cont_list_goal(IConts1, Cont),
    dispatch_prep(G2, B, Conts).
dispatch_prep_((G1 ; G2), B, [Cont|Conts]) :-
    dispatch_prep(G1, B, IConts0),
    dispatch_prep(G2, B, IConts1),
    cont_list_goal(IConts0, Cont0),
    cont_list_goal(IConts1, Cont1),
    Cont = '$call'(builtins:staggered_sc(Cont0, Cont1)),
    Conts = [].
dispatch_prep_((G1 -> G2), B, [Cont|Conts]) :-
    dispatch_prep(G1, B, IConts1),
    dispatch_prep(G2, B, IConts2),
    cont_list_goal(IConts1, Cont1),
    cont_list_goal(IConts2, Cont2),
    Cont = '$call'(builtins:staggered_if_then(Cont1, Cont2)),
    Conts = [].


:- non_counted_backtracking dispatch_call_list/1.

dispatch_call_list([]).
dispatch_call_list([G1,G2,G3,G4,G5,G6,G7,G8|Gs]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)),
    '$call_with_inference_counting'(call(G4)),
    '$call_with_inference_counting'(call(G5)),
    '$call_with_inference_counting'(call(G6)),
    '$call_with_inference_counting'(call(G7)),
    '$call_with_inference_counting'(call(G8)),
    dispatch_call_list(Gs).
dispatch_call_list([G1,G2,G3,G4,G5,G6,G7]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)),
    '$call_with_inference_counting'(call(G4)),
    '$call_with_inference_counting'(call(G5)),
    '$call_with_inference_counting'(call(G6)),
    '$call_with_inference_counting'(call(G7)).
dispatch_call_list([G1,G2,G3,G4,G5,G6]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)),
    '$call_with_inference_counting'(call(G4)),
    '$call_with_inference_counting'(call(G5)),
    '$call_with_inference_counting'(call(G6)).
dispatch_call_list([G1,G2,G3,G4,G5]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)),
    '$call_with_inference_counting'(call(G4)),
    '$call_with_inference_counting'(call(G5)).
dispatch_call_list([G1,G2,G3,G4]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)),
    '$call_with_inference_counting'(call(G4)).
dispatch_call_list([G1,G2,G3]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)),
    '$call_with_inference_counting'(call(G3)).
dispatch_call_list([G1,G2]) :-
    !,
    '$call_with_inference_counting'(call(G1)),
    '$call_with_inference_counting'(call(G2)).
dispatch_call_list([G1]) :-
    '$call_with_inference_counting'(call(G1)).


% univ.

:- non_counted_backtracking univ_errors/3.

univ_errors(Term, List, N) :-
    '$skip_max_list'(N, _, List, R),
    (  var(R)        ->
       (  var(Term),
          throw(error(instantiation_error, (=..)/2))      % 8.5.3.3 a)
       ;  true
       )
    ;  R \== []     ->
       throw(error(type_error(list, List), (=..)/2))                % 8.5.3.3 b)
    ;  List = [H|T] ->
       (  var(H),
          var(Term), % R == [] => List is a proper list.
          throw(error(instantiation_error, (=..)/2))                 % 8.5.3.3 c)
       ;  T \== [],
          nonvar(H),
          \+ atom(H),
          throw(error(type_error(atom, H), (=..)/2))                 % 8.5.3.3 d)
       ;  compound(H),
          T == [],
          throw(error(type_error(atomic, H), (=..)/2))               % 8.5.3.3 e)
       ;  var(Term),
          current_prolog_flag(max_arity, M),
          N - 1 > M,
          throw(error(representation_error(max_arity), (=..)/2))     % 8.5.3.3 g)
       ;  true
       )
    ;  var(Term)    ->
       throw(error(domain_error(non_empty_list, List), (=..)/2))    % 8.5.3.3 f)
    ;  true
    ).

:- non_counted_backtracking (=..)/2.

Term =.. List :-
    univ_errors(Term, List, N),
    univ_worker(Term, List, N).


:- non_counted_backtracking univ_worker/3.

univ_worker(Term, List, _) :-
    atomic(Term),
    !,
    List = [Term].
univ_worker(Term, [Name|Args], N) :-
    var(Term),
    !,
    Arity is N-1,
    functor(Term, Name, Arity), % Term = {var}, Name = nonvar, Arity = 0.
    get_args(Args, Term, 1, Arity).
univ_worker(Term, List, _) :-
    functor(Term, Name, Arity),
    get_args(Args, Term, 1, Arity),
    List = [Name|Args].


:- non_counted_backtracking get_args/4.

get_args(Args, _, _, 0) :-
    !,
    Args = [].
get_args([Arg], Func, N, N) :-
    !,
    arg(N, Func, Arg).
get_args([Arg|Args], Func, I0, N) :-
    arg(I0, Func, Arg),
    I1 is I0 + 1,
    get_args(Args, Func, I1, N).


:- meta_predicate parse_options_list(?, 2, ?, ?, ?).

parse_options_list(Options, Selector, DefaultPairs, OptionValues, Stub) :-
    '$skip_max_list'(_, _, Options, Tail),
    (  Tail == [] ->
       true
    ;  var(Tail) ->
       throw(error(instantiation_error, Stub))       % 8.11.5.3c)
    ;  Tail \== [] ->
       throw(error(type_error(list, Options), Stub)) % 8.11.5.3e)
    ),
    (  lists:maplist('$call'(nonvar), Options), % need '$call' because
                                                % maplist isn't
                                                % declared as a
                                                % meta-predicate yet
       catch(lists:maplist(Selector, Options, OptionPairs0),
             error(E, _),
             builtins:throw(error(E, Stub))) ->
       lists:append(DefaultPairs, OptionPairs0, OptionPairs1),
       keysort(OptionPairs1, OptionPairs),
       select_rightmost_options(OptionPairs, OptionValues)
    ;
       throw(error(instantiation_error, Stub))       % 8.11.5.3c)
    ).


parse_write_options(Options, OptionValues, Stub) :-
    DefaultOptions = [ignore_ops-false, max_depth-0, numbervars-false,
                      quoted-false, variable_names-[]],
    parse_options_list(Options, builtins:parse_write_options_, DefaultOptions, OptionValues, Stub).

parse_write_options_(ignore_ops(IgnoreOps), ignore_ops-IgnoreOps) :-
    (  nonvar(IgnoreOps),
       lists:member(IgnoreOps, [true, false]),
       !
    ;
       throw(error(domain_error(write_option, ignore_ops(IgnoreOps)), _))
    ).
parse_write_options_(quoted(Quoted), quoted-Quoted) :-
    (  nonvar(Quoted),
       lists:member(Quoted, [true, false]),
       !
    ;
       throw(error(domain_error(write_option, quoted(Quoted)), _))
    ).
parse_write_options_(numbervars(NumberVars), numbervars-NumberVars) :-
    (  nonvar(NumberVars),
       lists:member(NumberVars, [true, false]),
       !
    ;
       throw(error(domain_error(write_option, numbervars(NumberVars)), _))
    ).
parse_write_options_(variable_names(VNNames), variable_names-VNNames) :-
    must_be_var_names_list(VNNames),
    !.
parse_write_options_(max_depth(MaxDepth), max_depth-MaxDepth) :-
    (  integer(MaxDepth),
       MaxDepth >= 0,
       !
    ;
       throw(error(domain_error(write_option, max_depth(MaxDepth)), _))
    ).
parse_write_options_(E, _) :-
    throw(error(domain_error(write_option, E), _)).

must_be_var_names_list(VarNames) :-
    '$skip_max_list'(_, _, VarNames, Tail),
    (  Tail == [] ->
       must_be_var_names_list_(VarNames, VarNames)
    ;  var(Tail)  ->
       throw(error(instantiation_error, write_term/2))
    ;  throw(error(domain_error(write_option, variable_names(VarNames)), write_term/2))
    ).

must_be_var_names_list_([], List).
must_be_var_names_list_([VarName | VarNames], List) :-
    (  nonvar(VarName) ->
       (  VarName = (Atom = _) ->
          (  atom(Atom) ->
             must_be_var_names_list_(VarNames, List)
          ;  var(Atom)  ->
             throw(error(instantiation_error, write_term/2))
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

write(Stream, Term) :-
    '$write_term'(Stream, Term, false, true, false, [], 0).

write_canonical(Term) :-
    current_output(Stream),
    '$write_term'(Stream, Term, true, false, true, [], 0).

write_canonical(Stream, Term) :-
    '$write_term'(Stream, Term, true, false, true, [], 0).

writeq(Term) :-
    current_output(Stream),
    '$write_term'(Stream, Term, false, true, true, [], 0).

writeq(Stream, Term) :-
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


parse_read_term_options(Options, OptionValues, Stub) :-
    DefaultOptions = [singletons-_, variables-_, variable_names-_],
    parse_options_list(Options, builtins:parse_read_term_options_, DefaultOptions, OptionValues, Stub).


parse_read_term_options_(singletons(Vars), singletons-Vars) :- !.
parse_read_term_options_(variables(Vars), variables-Vars) :- !.
parse_read_term_options_(variable_names(Vars), variable_names-Vars) :- !.
parse_read_term_options_(E,_) :-
    throw(error(domain_error(read_option, E), _)).



read_term(Stream, Term, Options) :-
    parse_read_term_options(Options, [Singletons, VariableNames, Variables], read_term/3),
    '$read_term'(Stream, Term, Singletons, Variables, VariableNames).

read_term(Term, Options) :-
    current_input(Stream),
    read_term(Stream, Term, Options).

read(Term) :-
    current_input(Stream),
    read(Stream, Term).

% ensures List is either a variable or a list.
can_be_list(List, _)  :-
    var(List),
    !.
can_be_list(List, _)  :-
    '$skip_max_list'(_, _, List, Tail),
    (  var(Tail) ->
       true
    ;  Tail == []
    ),
    !.
can_be_list(List, PI) :-
    throw(error(type_error(list, List), PI)).

% term_variables.

term_variables(Term, Vars) :-
    can_be_list(Vars, term_variables/2),
    '$term_variables'(Term, Vars).

% exceptions.

:- non_counted_backtracking catch/3.

catch(G,C,R) :-
    '$get_current_block'(Bb),
    catch(G,C,R,Bb).

:- meta_predicate catch(0, ?, 0, ?).

:- non_counted_backtracking catch/4.

catch(G,C,R,Bb) :-
    '$install_new_block'(NBb),
    '$call_with_inference_counting'(call(G)),
    end_block(Bb, NBb).
catch(G,C,R,Bb) :-
    '$reset_block'(Bb),
    '$get_ball'(Ball),
    '$push_ball_stack', % move ball to ball stack.
    handle_ball(Ball, C, R).


:- non_counted_backtracking end_block/2.

end_block(Bb, NBb) :-
    '$clean_up_block'(NBb),
    '$reset_block'(Bb).
end_block(Bb, NBb) :-
    '$reset_block'(NBb),
    '$fail'.

:- non_counted_backtracking handle_ball/3.

handle_ball(C, C, R) :-
    !,
    '$pop_ball_stack', % remove ball from ball stack.
    call(R).
handle_ball(_, _, _) :-
    '$pop_from_ball_stack', % restore ball from ball stack.
    '$unwind_stack'.

:- non_counted_backtracking throw/1.

throw(Ball) :-
    (   var(Ball) ->
        '$set_ball'(error(instantiation_error,throw/1))
    ;   '$set_ball'(Ball)
    ),
    '$unwind_stack'.

:- non_counted_backtracking '$iterate_find_all'/4.

'$iterate_find_all'(Template, Goal, _, LhOffset) :-
    '$call_with_inference_counting'(call(Goal)),
    '$copy_to_lh'(LhOffset, Template),
    '$fail'.
'$iterate_find_all'(_, _, Solutions, LhOffset) :-
    '$truncate_if_no_lh_growth'(LhOffset),
    '$get_lh_from_offset'(LhOffset, Solutions).


truncate_lh_to(LhLength) :- '$truncate_lh_to'(LhLength).


:- meta_predicate findall(?, 0, ?).

:- non_counted_backtracking findall_cleanup/2.

findall_cleanup(LhLength, Error) :-
    truncate_lh_to(LhLength),
    throw(Error).

:- non_counted_backtracking findall/3.

findall(Template, Goal, Solutions) :-
    error:can_be(list, Solutions),
    '$lh_length'(LhLength),
    catch(builtins:'$iterate_find_all'(Template, Goal, Solutions, LhLength),
          Error,
          builtins:findall_cleanup(LhLength, Error)
         ).

:- non_counted_backtracking '$iterate_find_all_diff'/5.

'$iterate_find_all_diff'(Template, Goal, _, _, LhOffset) :-
    '$call_with_inference_counting'(call(Goal)),
    '$copy_to_lh'(LhOffset, Template),
    '$fail'.
'$iterate_find_all_diff'(_, _, Solutions0, Solutions1, LhOffset) :-
    '$truncate_if_no_lh_growth_diff'(LhOffset, Solutions1),
    '$get_lh_from_offset_diff'(LhOffset, Solutions0, Solutions1).


:- meta_predicate findall(?, 0, ?, ?).

:- non_counted_backtracking findall/4.

findall(Template, Goal, Solutions0, Solutions1) :-
    error:can_be(list, Solutions0),
    error:can_be(list, Solutions1),
    '$lh_length'(LhLength),
    catch(builtins:'$iterate_find_all_diff'(Template, Goal, Solutions0,
                                            Solutions1, LhLength),
          Error,
          builtins:findall_cleanup(LhLength, Error)
         ).

:- non_counted_backtracking set_difference/3.

set_difference([X|Xs], [Y|Ys], Zs) :-
    X == Y, !, set_difference(Xs, [Y|Ys], Zs).
set_difference([X|Xs], [Y|Ys], [X|Zs]) :-
    X @< Y, !, set_difference(Xs, [Y|Ys], Zs).
set_difference([X|Xs], [Y|Ys], Zs) :-
    X @> Y, !, set_difference([X|Xs], Ys, Zs).
set_difference([], _, []) :- !.
set_difference(Xs, [], Xs).

:- non_counted_backtracking group_by_variant/4.

group_by_variant([V2-S2 | Pairs], V1-S1, [S2 | Solutions], Pairs0) :-
    V1 = V2, % \+ \+ (V1 = V2), % (2) % iso_ext:variant(V1, V2), % (1)
    !,
    % V1 = V2, % (3)
    group_by_variant(Pairs, V2-S2, Solutions, Pairs0).
group_by_variant(Pairs, _, [], Pairs).

:- non_counted_backtracking group_by_variants/2.

group_by_variants([V-S|Pairs], [V-Solution|Solutions]) :-
    group_by_variant([V-S|Pairs], V-S, Solution, Pairs0),
    group_by_variants(Pairs0, Solutions).
group_by_variants([], []).

:- non_counted_backtracking iterate_variants/3.

iterate_variants([V-Solution|GroupSolutions], V, Solution) :-
    (  GroupSolutions == [] -> !
    ;  true
    ).
iterate_variants([_|GroupSolutions], Ws, Solution) :-
    iterate_variants(GroupSolutions, Ws, Solution).

:- non_counted_backtracking rightmost_power/3.

rightmost_power(Term, FinalTerm, Xs) :-
    (  Term = X ^ Y
    -> (  var(Y) -> FinalTerm = Y, Xs = [X]
       ;  Xs = [X | Xss], rightmost_power(Y, FinalTerm, Xss)
       )
    ;  Term = M : X ^ Y
    -> (  var(Y) -> FinalTerm = M:Y, Xs = [X]
       ;  Xs = [X | Xss], rightmost_power(M:Y, FinalTerm, Xss)
       )
    ;  Xs = [], FinalTerm = Term
    ).

:- non_counted_backtracking findall_with_existential/5.

findall_with_existential(Template, Goal, PairedSolutions, Witnesses0, Witnesses) :-
    (  nonvar(Goal),
       loader:strip_module(Goal, M, Goal1),
       (  Goal1 = _ ^ _  ) ->
       rightmost_power(Goal1, Goal2, ExistentialVars0),
       term_variables(ExistentialVars0, ExistentialVars),
       sort(Witnesses0, Witnesses1),
       sort(ExistentialVars, ExistentialVars1),
       set_difference(Witnesses1, ExistentialVars1, Witnesses),
       expand_goal(M:Goal2, M, Goal3),
       findall(Witnesses-Template, Goal3, PairedSolutions)
    ;  Witnesses = Witnesses0,
       findall(Witnesses-Template, Goal, PairedSolutions)
    ).


:- meta_predicate bagof(?, 0, ?).

:- non_counted_backtracking bagof/3.

bagof(Template, Goal, Solution) :-
    error:can_be(list, Solution),
    term_variables(Template, TemplateVars),
    term_variables(Goal, GoalVars),
    term_variables(TemplateVars+GoalVars, TGVs),
    lists:append(TemplateVars, Witnesses0, TGVs),
    findall_with_existential(Template, Goal, PairedSolutions0, Witnesses0, Witnesses),
    keysort(PairedSolutions0, PairedSolutions),
    group_by_variants(PairedSolutions, GroupedSolutions),
    iterate_variants(GroupedSolutions, Witnesses, Solution).

:- non_counted_backtracking iterate_variants_and_sort/3.

iterate_variants_and_sort([V-Solution0|GroupSolutions], V, Solution) :-
    sort(Solution0, Solution1),
    Solution1 = Solution,
    (  GroupSolutions == [] -> !
    ;  true
    ).
iterate_variants_and_sort([_|GroupSolutions], Ws, Solution) :-
    iterate_variants_and_sort(GroupSolutions, Ws, Solution).


:- meta_predicate setof(?, 0, ?).

:- non_counted_backtracking setof/3.

setof(Template, Goal, Solution) :-
    error:can_be(list, Solution),
    term_variables(Template, TemplateVars),
    term_variables(Goal, GoalVars),
    term_variables(TemplateVars+GoalVars, TGVs),
    lists:append(TemplateVars, Witnesses0, TGVs),
    findall_with_existential(Template, Goal, PairedSolutions0, Witnesses0, Witnesses),
    keysort(PairedSolutions0, PairedSolutions),
    group_by_variants(PairedSolutions, GroupedSolutions),
    iterate_variants_and_sort(GroupedSolutions, Witnesses, Solution).

% Clause retrieval and information.


'$clause_body_is_valid'(B) :-
    (  var(B) -> true
    ;  functor(B, Name, _) ->
       (  atom(Name), Name \== '.' -> true
       ;  throw(error(type_error(callable, B), clause/2))
       )
    ;  throw(error(type_error(callable, B), clause/2))
    ).

'$module_clause'(H, B, Module) :-
    (  var(H) ->
       throw(error(instantiation_error, clause/2))
    ;  callable(H), functor(H, Name, Arity) ->
       (  '$no_such_predicate'(Module, H) ->
          '$fail'
       ;  '$head_is_dynamic'(Module, H) ->
          '$clause_body_is_valid'(B),
          Module:'$clause'(H, B)
       ;  throw(error(permission_error(access, private_procedure, Name/Arity),
                      clause/2))
       )
    ;  throw(error(type_error(callable, H), clause/2))
    ).

clause(H, B) :-
    (  var(H) ->
       throw(error(instantiation_error, clause/2))
    ;  callable(H), functor(H, Name, Arity) ->
       (  Name == (:),
          Arity =:= 2 ->
          arg(1, H, Module),
          arg(2, H, F),
          '$module_clause'(F, B, Module)
       ;  '$no_such_predicate'(user, H) ->
          '$fail'
       ;  '$head_is_dynamic'(user, H) ->
          '$clause_body_is_valid'(B),
          '$clause'(H, B)
       ;  throw(error(permission_error(access, private_procedure, Name/Arity),
                      clause/2))
       )
    ;  throw(error(type_error(callable, H), clause/2))
    ).


:- meta_predicate asserta(:).

asserta(Clause0) :-
    loader:strip_subst_module(Clause0, user, Module, Clause),
    iso_ext:asserta(Module, Clause).


:- meta_predicate assertz(:).

assertz(Clause0) :-
    loader:strip_subst_module(Clause0, user, Module, Clause),
    iso_ext:assertz(Module, Clause).


:- meta_predicate retract(:).

retract(Clause0) :-
    loader:strip_module(Clause0, Module, Clause),
    (  Clause \= (_ :- _) ->
       loader:strip_module(Clause, Module, Head),
       (  var(Module) -> Module = user
       ;  true
       ),
       Body = true,
       retract_module_clause(Head, Body, Module)
    ;  Clause = (Head :- Body) ->
       retract_module_clause(Head, Body, Module)
    ).

retract_clauses([L-P | Ps], Head, Body, Name, Arity, Module) :-
    '$invoke_clause_at_p'(Head, Body, L, P, N, Module),
    (  integer(N) ->
       '$retract_clause'(Name, Arity, N, Module)
    ;  true % the clause at index N has already been retracted in this
            % case but unify (Head :- Body) anyway.
    ),
    (  Ps == [] -> !
    ;  true
    ).
retract_clauses([_ | Ps], Head, Body, Name, Arity, Module) :-
    retract_clauses(Ps, Head, Body, Name, Arity, Module).

call_retract_helper(Head, Body, P, Module) :-
    (  Module == user ->
       ClauseQualifier = builtins
    ;  ClauseQualifier = Module
    ),
    ClauseQualifier:'$clause'(Head, Body),
    '$get_clause_p'(Head, P, Module).

call_retract(Head, Body, Name, Arity, Module) :-
    findall(P, builtins:call_retract_helper(Head, Body, P, Module), Ps),
    retract_clauses(Ps, Head, Body, Name, Arity, Module).

retract_clause(Head, Body) :-
    (  var(Head) ->
       throw(error(instantiation_error, retract/1))
    ;  callable(Head),
       functor(Head, Name, Arity) ->
       (  Name == (:),
          Arity =:= 2 ->
          arg(1, Head, Module),
          arg(2, Head, Head1),
          retract_module_clause(Head1, Body, Module)
       ;  '$no_such_predicate'(user, Head) ->
          '$fail'
       ;  '$head_is_dynamic'(user, Head) ->
          call_retract(Head, Body, Name, Arity, user)
       ;  throw(error(permission_error(modify, static_procedure, Name/Arity), retract/1))
       )
    ;  throw(error(type_error(callable, Head), retract/1))
    ).

retract_module_clause(Head, Body, Module) :-
    (  var(Head) ->
       throw(error(instantiation_error, retract/1))
    ;  callable(Head),
       functor(Head, Name, Arity) ->
       (  '$no_such_predicate'(Module, Head) ->
          '$fail'
       ;  '$head_is_dynamic'(Module, Head) ->
          call_retract(Head, Body, Name, Arity, Module)
       ;  throw(error(permission_error(modify, static_procedure, Name/Arity), retract/1))
       )
    ;  throw(error(type_error(callable, Head), retract/1))
    ).

:- meta_predicate retractall(:).

retractall(Head) :-
   retract_clause(Head, _),
   false.
retractall(_).


module_abolish(Pred, Module) :-
    (  var(Pred) ->
       throw(error(instantiation_error, abolish/1))
    ;  Pred = Name/Arity ->
       (  var(Name)  ->
          throw(error(instantiation_error, abolish/1))
       ;  var(Arity) ->
          throw(error(instantiation_error, abolish/1))
       ;  integer(Arity) ->
          (\+ atom(Name) ->
             throw(error(type_error(atom, Name), abolish/1))
          ;  Arity < 0 ->
             throw(error(domain_error(not_less_than_zero, Arity), abolish/1))
          ;  current_prolog_flag(max_arity, N), Arity > N ->
             throw(error(representation_error(max_arity), abolish/1))
          ;  functor(Head, Name, Arity) ->
             (  '$head_is_dynamic'(Module, Head) ->
                '$abolish_clause'(Module, Name, Arity)
             ;  '$no_such_predicate'(Module, Head) ->
                true
             ;  throw(error(permission_error(modify, static_procedure, Pred), abolish/1))
             )
          )
       ;  throw(error(type_error(integer, Arity), abolish/1))
       )
    ;  throw(error(type_error(predicate_indicator, Module:Pred), abolish/1))
    ).


:- meta_predicate abolish(:).

abolish(Pred) :-
    (  var(Pred) ->
       throw(error(instantiation_error, abolish/1))
    ;  Pred = Module:InnerPred ->
       (  var(Module) -> Module = user
       ;  true
       ),
       module_abolish(InnerPred, Module)
    ;  Pred = Name/Arity ->
       (  var(Name)  ->
          throw(error(instantiation_error, abolish/1))
       ;  var(Arity) ->
          throw(error(instantiation_error, abolish/1))
       ;  integer(Arity) ->
          (  \+ atom(Name) ->
             throw(error(type_error(atom, Name), abolish/1))
          ;  Arity < 0 ->
             throw(error(domain_error(not_less_than_zero, Arity), abolish/1))
          ;  current_prolog_flag(max_arity, N), Arity > N ->
             throw(error(representation_error(max_arity), abolish/1))
          ;  functor(Head, Name, Arity) ->
             (  '$head_is_dynamic'(user, Head) ->
                '$abolish_clause'(user, Name, Arity)
             ;  '$no_such_predicate'(user, Head) ->
                true
             ;  throw(error(permission_error(modify, static_procedure, Pred), abolish/1))
             )
          )
       ;  throw(error(type_error(integer, Arity), abolish/1))
       )
    ;  throw(error(type_error(predicate_indicator, Pred), abolish/1))
    ).


'$iterate_db_refs'(Name, Arity, Name/Arity). % :-
%   '$lookup_db_ref'(Ref, Name, Arity).
'$iterate_db_refs'(RName, RArity, Name/Arity) :-
    '$get_next_db_ref'(RName, RArity, RRName, RRArity),
    '$iterate_db_refs'(RRName, RRArity, Name/Arity).


current_predicate(Pred) :-
    (  var(Pred) ->
       '$get_next_db_ref'(RN, RA, _, _),
       '$iterate_db_refs'(RN, RA, Pred)
    ;  Pred \= _/_ ->
       throw(error(type_error(predicate_indicator, Pred), current_predicate/1))
    ;  Pred = Name/Arity,
       (  nonvar(Name), \+ atom(Name)
       ;  nonvar(Arity), \+ integer(Arity)
       ;  integer(Arity), Arity < 0
       ) ->
       throw(error(type_error(predicate_indicator, Pred), current_predicate/1))
    ;  '$get_next_db_ref'(RN, RA, _, _),
       '$iterate_db_refs'(RN, RA, Pred)
    ).


'$iterate_op_db_refs'(RPriority, RSpec, ROp, _, RPriority, RSpec, ROp).
'$iterate_op_db_refs'(RPriority, RSpec, ROp, OssifiedOpDir, Priority, Spec, Op) :-
    '$get_next_op_db_ref'(RPriority, RSpec, ROp, OssifiedOpDir, RRPriority, RRSpec, RROp),
    '$iterate_op_db_refs'(RRPriority, RRSpec, RROp, OssifiedOpDir, Priority, Spec, Op).


can_be_op_priority(Priority) :- var(Priority).
can_be_op_priority(Priority) :- op_priority(Priority).

can_be_op_specifier(Spec) :- var(Spec).
can_be_op_specifier(Spec) :- op_specifier(Spec).


current_op(Priority, Spec, Op) :-
    (  can_be_op_priority(Priority),
       can_be_op_specifier(Spec),
       error:can_be(atom, Op) ->
       '$get_next_op_db_ref'(RPriority, RSpec, ROp, OssifiedOpDir, _, _, Op),
       '$iterate_op_db_refs'(RPriority, RSpec, ROp, OssifiedOpDir, Priority, Spec, Op)
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
       throw(error(domain_error(operator_priority, Priority), op/3)) % 8.14.3.3 h)
    ;  true
    ).
op_priority(Priority) :-
    throw(error(type_error(integer, Priority), op/3)). % 8.14.3.3 d)


op_specifier(OpSpec) :-
    atom(OpSpec),
    (  lists:member(OpSpec, [yfx, xfy, xfx, yf, fy, xf, fx]), !
    ;  throw(error(domain_error(operator_specifier, OpSpec), op/3)) % 8.14.3.3 i)
    ).
op_specifier(OpSpec) :-
    throw(error(type_error(atom, OpSpec), op/3)).


valid_op(Op) :-
    atom(Op),
    (  Op == (',') ->
       throw(error(permission_error(modify, operator, (',')), op/3)) % 8.14.3.3 j), k).
    ;  Op == {} ->
       throw(error(permission_error(create, operator, {}), op/3))
    ;  Op == [] ->
       throw(error(permission_error(create, operator, []), op/3))
    ;  true
    ).


op_(Priority, OpSpec, Op) :-
    '$op'(Priority, OpSpec, Op).


op(Priority, OpSpec, Op) :-
    (  var(Priority) ->
       throw(error(instantiation_error, op/3)) % 8.14.3.3 a)
    ;  var(OpSpec)   ->
       throw(error(instantiation_error, op/3)) % 8.14.3.3 b)
    ;  var(Op)       ->
       throw(error(instantiation_error, op/3)) % 8.14.3.3 c)
    ;  Op == '|'     ->
       (  op_priority(Priority),
          op_specifier(OpSpec),
          lists:member(OpSpec, [xfx, xfy, yfx]),
          ( Priority >= 1001 ; Priority == 0 )
       -> '$op'(Priority, OpSpec, Op)
       ;  throw(error(permission_error(create, operator, (|)), op/3))) % www.complang.tuwien.ac.at/ulrich/iso-prolog/conformity_testing#72
    ;  valid_op(Op), op_priority(Priority), op_specifier(OpSpec) ->
       '$op'(Priority, OpSpec, Op)
    ;  list_of_op_atoms(Op), op_priority(Priority), op_specifier(OpSpec) ->
       lists:maplist(builtins:op_(Priority, OpSpec), Op),
       !
    ;  throw(error(type_error(list, Op), op/3)) % 8.14.3.3 f)
    ).

halt :- halt(0).

halt(N) :-
    (   var(N) ->
        throw(error(instantiation_error, halt/1)) % 8.17.4.3 a)
    ;   \+ integer(N) ->
        throw(error(type_error(integer, N), halt/1)) % 8.17.4.3 b)
    ;   -2^31 =< N, N =< 2^31 - 1 ->
        '$halt'(N)
    ;   throw(error(domain_error(exit_code, N), halt/1))
    ).


atom_length(Atom, Length) :-
    (  var(Atom)  ->
       throw(error(instantiation_error, atom_length/2)) % 8.16.1.3 a)
    ;  atom(Atom) ->
       (  var(Length) ->
          '$atom_length'(Atom, Length)
       ;  integer(Length), Length >= 0 ->
          '$atom_length'(Atom, Length)
       ;  integer(Length) ->
          throw(error(domain_error(not_less_than_zero, Length), atom_length/2))
       % 8.16.1.3 d)
       ;  throw(error(type_error(integer, Length), atom_length/2)) % 8.16.1.3 c)
       )
    ;  throw(error(type_error(atom, Atom), atom_length/2)) % 8.16.1.3 b)
    ).


atom_chars(Atom, List) :-
    '$skip_max_list'(_, _, List, Tail),
    (  ( Tail == [] ; var(Tail) ) ->
       true
    ;  throw(error(type_error(list, List), atom_chars/2))
    ),
    (  var(Atom) ->
       (  var(Tail) ->
          throw(error(instantiation_error, atom_chars/2))
       ;  ground(List) ->
          chars_or_vars(List, atom_chars/2),
          '$atom_chars'(Atom, List)
       ;  throw(error(instantiation_error, atom_chars/2))
       )
    ;  atom(Atom) ->
       chars_or_vars(List, atom_chars/2),
       '$atom_chars'(Atom, List)
    ;  throw(error(type_error(atom, Atom), atom_chars/2))
    ).

atom_codes(Atom, List) :-
    '$skip_max_list'(_, _, List, Tail),
    (  ( Tail == [] ; var(Tail) ) ->
       true
    ;  throw(error(type_error(list, List), atom_codes/2))
    ),
    (  var(Atom) ->
       (  var(Tail) ->
          throw(error(instantiation_error, atom_codes/2))
       ;  ground(List) ->
          codes_or_vars(List, atom_codes/2),
          '$atom_codes'(Atom, List)
       ;  throw(error(instantiation_error, atom_codes/2))
       )
    ;  atom(Atom) ->
       codes_or_vars(List, atom_codes/2),
       '$atom_codes'(Atom, List)
    ;  throw(error(type_error(atom, Atom), atom_codes/2))
    ).


atom_concat(Atom_1, Atom_2, Atom_12) :-
    error:can_be(atom, Atom_1),
    error:can_be(atom, Atom_2),
    error:can_be(atom, Atom_12),
    (  var(Atom_1) ->
       (  var(Atom_12) ->
          throw(error(instantiation_error, atom_concat/3))
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
    (  integer(Before), Before < 0 ->
       throw(error(domain_error(not_less_than_zero, Before), sub_atom/5))
    ;  integer(Length), Length < 0 ->
       throw(error(domain_error(not_less_than_zero, Length), sub_atom/5))
    ;  integer(After), After < 0 ->
       throw(error(domain_error(not_less_than_zero, After), sub_atom/5))
    ;  atom_chars(Atom, AtomChars),
       lists:append(BeforeChars, LengthAndAfterChars, AtomChars),
       lists:append(LengthChars, AfterChars, LengthAndAfterChars),
       '$skip_max_list'(Before, _, BeforeChars, []),
       '$skip_max_list'(Length, _, LengthChars, []),
       '$skip_max_list'(After, _, AfterChars, []),
       atom_chars(Sub_atom, LengthChars)
    ).


char_code(Char, Code) :-
    (  var(Char) ->
       (  var(Code) ->
          throw(error(instantiation_error, char_code/2))
       ;  integer(Code) ->
          '$char_code'(Char, Code)
       ;  throw(error(type_error(integer, Code), char_code/2))
       )
    ;  \+ atom(Char) ->
       throw(error(type_error(character, Char), char_code/2))
    ;  atom_length(Char, 1) ->
       (  var(Code) ->
          '$char_code'(Char, Code)
       ;  integer(Code) ->
          '$char_code'(Char, Code)
       ;  throw(error(type_error(integer, Code), char_code/2))
       )
    ;  throw(error(type_error(character, Char), char_code/2))
    ).

get_char(C) :-
    error:can_be(in_character, C),
    current_input(S),
    '$get_char'(S, C).

get_char(S, C) :-
    error:can_be(in_character, C),
    '$get_char'(S, C).

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
    (  nonvar(N) ->
       throw(error(type_error(number, N), PI))
    ;  throw(error(instantiation_error, PI))
    ).


chars_or_vars(Cs, _) :-
    (  var(Cs) ->
       !
    ;  Cs == [] ->
       !
    ).
chars_or_vars([C|Cs], PI) :-
    (  nonvar(C) ->
       (  atom(C),
          atom_length(C, 1) ->
          chars_or_vars(Cs, PI)
       ;  throw(error(type_error(character, C), PI))
       )
    ;  chars_or_vars(Cs, PI)
    ).


codes_or_vars(Cs, _) :-
    (  var(Cs) ->
       !
    ;  Cs == [] ->
       !
    ).
codes_or_vars([C|Cs], PI) :-
    (  nonvar(C) ->
       (  catch(builtins:char_code(_, C), _, false) ->
          codes_or_vars(Cs, PI)
       ;  integer(C) ->
          throw(error(representation_error(character_code), PI))
       ;  throw(error(type_error(integer, C), PI))
       )
    ;  codes_or_vars(Cs, PI)
    ).


number_chars(N, Chs) :-
    (  ground(Chs) ->
       can_be_number(N, number_chars/2),
       catch(error:must_be(chars, Chs),
             error(E, _),
             builtins:throw(error(E, number_chars/2))
            ),
       '$chars_to_number'(Chs, N)
    ;  must_be_number(N, number_chars/2),
       (  var(Chs) -> true
       ;  can_be_list(Chs, number_chars/2),
          chars_or_vars(Chs, number_chars/2)
       ),
       '$number_to_chars'(N, Chs)
    ).


list_of_ints(Ns) :-
    error:must_be(list, Ns),
    lists:maplist(error:must_be(integer), Ns).


number_codes(N, Chs) :-
   (  ground(Chs) ->
      can_be_number(N, number_codes/2),
      catch(builtins:list_of_ints(Chs),
            error(E, _),
            builtins:throw(error(E, number_codes/2))
           ),
      '$codes_to_number'(Chs, N)
   ;  must_be_number(N, number_codes/2),
      (  var(Chs) -> true
      ;  can_be_list(Chs, number_codes/2),
         codes_or_vars(Chs, number_codes/2)
      ),
      '$number_to_codes'(N, Chs)
   ).


subsumes_term(General, Specific) :-
   \+ \+ (
      term_variables(Specific, SVs1),
      unify_with_occurs_check(General, Specific),
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
    parse_options_list(Options, builtins:parse_stream_options_, DefaultOptions, OptionValues, Stub).


parse_stream_options_(type(Type), type-Type) :-
    (  var(Type) ->
       throw(error(instantiation_error, open/4)) % 8.1.3 7)
    ;
       lists:member(Type, [text, binary]), !
    ;
       throw(error(domain_error(stream_option, type(Type)), _))
    ).
parse_stream_options_(reposition(Bool), reposition-Bool) :-
    (  nonvar(Bool), lists:member(Bool, [true, false]), !
    ;
       throw(error(domain_error(stream_option, reposition(Bool)), _))
    ).
parse_stream_options_(alias(A), alias-A) :-
    (  var(A) ->
       throw(error(instantiation_error, open/4)) % 8.1.3 7)
    ;
       atom(A), A \== [] -> true
    ;
       throw(error(domain_error(stream_option, alias(A)), _))
    ).
parse_stream_options_(eof_action(Action), eof_action-Action) :-
    (  nonvar(Action), lists:member(Action, [eof_code, error, reset]), !
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
       throw(error(uninstantiation_error(Stream), open/4)) % 8.11.5.3f)
    ;
       parse_stream_options(StreamOptions, [Alias, EOFAction, Reposition, Type], open/4),
       (   SourceSink = stream(S0) ->
           '$set_stream_options'(S0, Alias, EOFAction, Reposition, Type),
           Stream = S0
       ;   (
                atom(SourceSink) ->
                atom_chars(SourceSink, SourceSinkString)
           ;    SourceSink = SourceSinkString
           ),
           '$open'(SourceSinkString, Mode, Stream, Alias, EOFAction, Reposition, Type)
       )
    ).


parse_close_options(Options, OptionValues, Stub) :-
    DefaultOptions = [force-false],
    parse_options_list(Options, builtins:parse_close_options_, DefaultOptions, OptionValues, Stub).


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
    '$close'(Stream, []).



flush_output(S) :-
    '$flush_output'(S).

flush_output :-
    current_output(S),
    '$flush_output'(S).


get_byte(S, B) :-
    '$get_byte'(S, B).

get_byte(B) :-
    current_input(S),
    '$get_byte'(S, B).


put_char(C) :-
    current_output(S),
    '$put_char'(S, C).

put_char(S, C) :-
    '$put_char'(S, C).


put_byte(C) :-
    current_output(S),
    '$put_byte'(S, C).

put_byte(S, C) :-
    '$put_byte'(S, C).


put_code(C) :-
    current_output(S),
    '$put_code'(S, C).

put_code(S, C) :-
    '$put_code'(S, C).


get_code(C) :-
    current_input(S),
    '$get_code'(S, C).

get_code(S, C) :-
    '$get_code'(S, C).


peek_byte(S, B) :-
    '$peek_byte'(S, B).

peek_byte(B) :-
    current_input(S),
    '$peek_byte'(S, B).


peek_code(C) :-
    current_input(S),
    '$peek_code'(S, C).

peek_code(S, C) :-
    '$peek_code'(S, C).


peek_char(C) :-
    current_input(S),
    '$peek_char'(S, C).

peek_char(S, C) :-
    '$peek_char'(S, C).


is_stream_position(position_and_lines_read(P, L)) :-
    ( var(P) ; integer(P), P >= 0 ),
    ( var(L) ; integer(L), L >= 0 ),
    !.

check_stream_property(D, direction, D) :-
    ( var(D) -> true ; lists:member(D, [input, output, input_output]), ! ).
check_stream_property(file_name(F), file_name, F) :-
    ( var(F) -> true ; atom(F) ).
check_stream_property(mode(M), mode, M) :-
    ( var(M) -> true ; lists:member(M, [read, write, append]) ).
check_stream_property(alias(A), alias, A) :-
    ( var(A) -> true ; atom(A) ).
check_stream_property(position(P), position, P) :-
    ( var(P) -> true ; is_stream_position(P)).
check_stream_property(end_of_stream(E), end_of_stream, E) :-
    ( var(E) -> true ; lists:member(E, [not, at, past]) ).
check_stream_property(eof_action(A), eof_action, A) :-
    ( var(A) -> true ; lists:member(A, [error, eof_code, reset]) ).
check_stream_property(reposition(B), reposition, B) :-
    ( var(B) -> true ; lists:member(B, [true, false]) ).
check_stream_property(type(T), type, T) :-
    ( var(T) -> true ; lists:member(T, [text, binary]) ).


stream_iter_(S, S).
stream_iter_(S, S1) :-
    '$next_stream'(S, S0),
    stream_iter_(S0, S1).

stream_iter(S) :-
    (  nonvar(S) ->
       true
    ;  '$first_stream'(S0),
       stream_iter_(S0, S)
    ).


stream_property(S, P) :-
    (  nonvar(P), \+ check_stream_property(P, _, _) ->
       throw(error(domain_error(stream_property, P), stream_property/2))
    ;  stream_iter(S),
       check_stream_property(P, PropertyName, PropertyValue),
       '$stream_property'(S, PropertyName, PropertyValue)
    ).


at_end_of_stream(S_or_a) :-
    (  var(S_or_a) ->
       throw(error(instantiation_error, at_end_of_stream/1))
    ;  atom(S_or_a) ->
       stream_property(S, alias(S_or_a))
    ;  S = S_or_a
    ),
    stream_property(S, end_of_stream(E)),
    ( E = at -> true ; E = past ).

at_end_of_stream :-
    current_input(S),
    stream_property(S, end_of_stream(E)),
    !,
    ( E = at ; E = past ).


set_stream_position(S_or_a, Position) :-
    (  var(Position) ->
       throw(error(instantiation_error, set_stream_position/2))
    ;  Position = position_and_lines_read(P, _),
       is_stream_position(Position) ->
       '$set_stream_position'(S_or_a, P)
    ;  throw(error(domain_error(stream_position, Position), set_stream_position/2))
    ).

callable(X) :-
    (  nonvar(X), functor(X, F, _), atom(F) ->
       true
    ;  false
    ).

nl :-
    current_output(Stream),
    nl(Stream).

nl(Stream) :-
    put_char(Stream, '\n').

error(Error_term, Imp_def) :-
   throw(error(Error_term, Imp_def)).
