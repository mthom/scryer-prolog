:- module('$toplevel', [argv/1,
                        copy_term/3]).

:- use_module(library(atts), [call_residue_vars/2]).
:- use_module(library(charsio)).
:- use_module(library(files)).
:- use_module(library(format), [format/2]).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(si)).

:- use_module(library('$project_atts')).
:- use_module(library('$atts')).

load_scryerrc :-
    (  '$home_directory'(HomeDir) ->
       append(HomeDir, "/.scryerrc", ScryerrcFile),
       (  file_exists(ScryerrcFile) ->
          atom_chars(ScryerrcFileAtom, ScryerrcFile),
          catch(use_module(ScryerrcFileAtom), E, print_exception(E))
       ;  true
       )
    ;  true
    ).

:- dynamic(argv/1).

'$repl'([_|Args0]) :-
    \+ argv(_),
    (   append(Args1, ["--"|Args2], Args0) ->
        asserta('$toplevel':argv(Args2)),
        Args = Args1
    ;   asserta('$toplevel':argv([])),
        Args = Args0
    ),
    load_scryerrc,
    delegate_task(Args, []),
    repl.
'$repl'(_) :-
    (   \+ argv(_) -> asserta('$toplevel':argv([]))
    ;   true
    ),
    load_scryerrc,
    repl.

delegate_task([], []).
delegate_task([], Goals0) :-
    reverse(Goals0, Goals),
    run_goals(Goals),
    repl.
delegate_task([Arg0|Args], Goals0) :-
    (   member(Arg0, ["-h", "--help"]) -> print_help
    ;   member(Arg0, ["-v", "--version"]) -> print_version
    ;   member(Arg0, ["-g", "--goal"]) -> gather_goal(g, Args, Goals0)
    ;   atom_chars(Mod, Arg0),
        catch(use_module(Mod), E, print_exception(E))
    ),
    delegate_task(Args, Goals0).

print_help :-
    write('Usage: scryer-prolog [OPTIONS] [FILES] [-- ARGUMENTS]'),
    nl, nl,
    write('Options:'), nl,
    write('   -h, --help           '),
    write('Display this message'), nl,
    write('   -v, --version        '),
    write('Print version information and exit'), nl,
    write('   -g, --goal GOAL      '),
    write('Run the query GOAL'), nl,
    % write('                        '),
    halt.

print_version :-
    '$scryer_prolog_version'(Version),
    write(Version), nl,
    halt.

gather_goal(Type, Args0, Goals) :-
    length(Args0, N),
    (   N < 1 -> print_help, halt
    ;   true
    ),
    [Gs1|Args] = Args0,
    Gs =.. [Type, Gs1],
    delegate_task(Args, [Gs|Goals]).

arg_type(g).
arg_type(t).
arg_type(g(_)).
arg_type(t(_)).

ends_with_dot(Ls0) :-
    reverse(Ls0, Ls),
    layout_and_dot(Ls).

layout_and_dot(['.'|_]).
layout_and_dot([C|Cs]) :-
    char_type(C, layout),
    layout_and_dot(Cs).

run_goals([]).
run_goals([g(Gs0)|Goals]) :-
    (   ends_with_dot(Gs0) -> Gs1 = Gs0
    ;   append(Gs0, ".", Gs1)
    ),
    read_term_from_chars(Gs1, Goal),
    (   catch(
            user:Goal,
            Exception,
            (write(Goal), write(' causes: '), write(Exception), nl) % halt?
        )
    ;   write('Warning: initialization failed for '),
        write(Gs0), nl
    ),
    run_goals(Goals).
run_goals([Goal|_]) :-
    write('caught: '),
    write(error(domain_error(arg_type, Goal), run_goals/1)), nl,
    halt.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  REPL.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

%% Enable op declarations with lists of operands, i.e.,
%% :- op(900, fy, [$,@]).

user:term_expansion((:- op(Pred, Spec, [Op | OtherOps])), OpResults) :-
    expand_op_list([Op | OtherOps], Pred, Spec, OpResults).

expand_op_list([], _, _, []).
expand_op_list([Op | OtherOps], Pred, Spec, [(:- op(Pred, Spec, Op)) | OtherResults]) :-
    expand_op_list(OtherOps, Pred, Spec, OtherResults).


repl :-
    catch(read_execute, E, print_exception(E)),
    false. %% This is for GC, until we get actual GC.
repl :-
    repl.

print_exception(E) :-
    (   E == error('$interrupt_throw', repl/0) ->
        nl  % Print the exception on a new line to evade "^C".
    ;   true
    ),
    write_term('caught: ', [quoted(false), max_depth(20)]),
    writeq(E), nl. % Fail-safe.

print_exception_with_check(E) :-
    (   E = error(_, _:_) ->
        % If the error source contains a line number, a GNU-style error
        % message is expected to be printed instead.
        true
    ;   print_exception(E)
    ).

read_execute :-
    '$read_query_term'(_, Term, _, AllInitVs, Eqs0),
    (   var(Term) ->
        throw(error(instantiation_error, repl/0))
    ;   Term = end_of_file ->
        halt
    ;   Term = [File] -> !,
        (   atom(File) ->
            (   File == user ->
                catch(load(user_input), E, print_exception_with_check(E))
            ;   consult(File)
            )
        ;   catch(
                throw(error(type_error(atom, File), repl/0)),
                E,
                print_exception_with_check(E)
            )
        )
    ;   execute_query(Term, Eqs0, AllInitVs)
    ).

% :- meta_predicate execute_query(0, ?, ?).
execute_query(Goal, Eqs0, AllInitVs) :-
    term_variables(Eqs0, InterestVs), % Must show it.
    list_filter(not(in(InterestVs)), AllInitVs, AnonVs),
    setup_call_cleanup(
        true,
        (   catch(call_residue_vars(user:Goal, ResVs), E, true),
            (   var(E) ->
                Succeed = true
            ;   NoError = false
            )
        ),
        (   (   NoError \== false, Succeed \== true ->
                format("    false.\n", [])
            ;   Last = true
            )
        )
    ),
    (   nonvar(E) ->
        throw(E)
    ;   true
    ),
    term_variables(Goal, NewVs),
    terms_equations(Eqs0, AllInitVs, InterestVs, AnonVs, ResVs, NewVs, Terms, AllEqs),
    (   print_and_read_input_if_not_last(Last, 20, Terms, AllEqs) ->
        true
    % ;   !       % Bug, this doesn't cut.
    % ;   !, true % Bug, this also doesn't cut.
    ;   true, ! % End query.
    ).

print_and_read_input_if_not_last(Last, MaxDepth, Terms, AllEqs) :-
    print_goal(Terms, AllEqs, MaxDepth, Cs),
    format("    ~s", [Cs]),
    (   Last == true ->
        (   list_last(Cs, C), char_type(C, graphic_token) ->
            write(' .'), nl
        ;   write('.'), nl
        )
    ;   read_input_and_print_(MaxDepth, Terms, AllEqs)
    ).

read_input_and_print_(MaxDepth, Terms, AllEqs) :-
    get_single_char(C),
    nl,
    (   member(C, [;, ' ', n]) ->
        write(;), nl
    ;   member(C, ['\n', .]) ->
        write(';   ...'), nl,
        false
    ;   C = h ->
        help_message,
        read_input_and_print_(MaxDepth, Terms, AllEqs)
    ;   C = p ->
        print_goal(Terms, AllEqs, MaxDepth, Cs),
        format("    ~s", [Cs]),
        read_input_and_print_(MaxDepth, Terms, AllEqs)
    ;   C = w ->
        print_goal(Terms, AllEqs, 0, Cs),
        format("    ~s", [Cs]),
        read_input_and_print_(MaxDepth, Terms, AllEqs)
    ;   read_input_and_print_(MaxDepth, Terms, AllEqs)
    ).

help_message :-
    nl, nl,
    write('SPACE, "n" or ";": next solution, if any\n'),
    write('RETURN or ".": stop enumeration\n'),
    write('"h": display this help message\n'),
    write('"w": write terms without depth limit\n'),
    write('"p": print terms with depth limit\n\n').

terms_equations(Eqs0, AllInitVs, InterestVs0, AnonVs0, ResVs0, NewVs0, Terms, AllEqs) :-
    % Include new variables of interest, possibly some anonymous variables.
    term_variables(InterestVs0, InterestVs),

    % Include new anonymous variables. New variables of anonymous origin are
    % new anonymous variables.
    term_variables(AnonVs0, AnonVs1),

    % Anonymous variables that are "inside" a variable of interest isn't
    % anonymous.
    list_filter(not(in(InterestVs)), AnonVs1, AnonVs),

    % Get the attributed variables only.
    '$term_attributed_variables'(ResVs0, ResVs1), % Not enough.
    list_filter(not(in(AnonVs)), ResVs1, ResVs2),

    term_variables([AllInitVs, ResVs1], AllVs),

    list_filter(not(in(AnonVs)), AllVs, AttrVs0),

    term_variables(AllInitVs, AllVs0),

    % '$term_attributed_variables'(AttrVs0, AttrVs1),
    '$project_atts':project_attributes(AllVs0, AttrVs0),
    copy_term(AttrVs0, AttrVs0, AttrGs),

    % Truly useful attributed variables.
    term_variables(AttrGs, AttrVs1),
    % '$term_attributed_variables'(AttrGs, AttrVs1), % Bad.
    list_filter(both(ResVs2, AttrVs1), ResVs2, ResVs3),

    % New hidden variables in attributed variables have to be revealed.
    term_variables(AttrGs, HiddenVs0),
    list_filter(not(in(AllVs)), HiddenVs0, Hs),

    % Reorder: normal variables then attributed variables.
    list_filter(not(in(AnonVs)), NewVs0, NewVs1),
    list_filter(not(in(NewVs1)), ResVs3, ResVs4),

    append([NewVs1, ResVs4, Hs], NewVs),
    charsio:extend_var_list(NewVs, Eqs0, AllEqs, fabricated),

    append(AllEqs, AttrGs, Terms0),
    reverse(Terms0, RevTerms0),
    seen(RevTerms0, [], Terms1),

    (   Terms1 = [] ->
        Terms = [true]
    ;   Terms = Terms1
    ).

print_goal(Terms, AllEqs, MaxDepth, Cs) :-
    maplist(print_goal_(AllEqs, MaxDepth, ", "), Terms, Css),
    append(Css, Cs0),
    append(Cs, ", ", Cs0).

print_goal_(AllEqs, MaxDepth, Append, Term, Cs) :-
    Settings = [variable_names(AllEqs), max_depth(MaxDepth)],
    write_term_to_chars(Term, Settings, Cs0), % Not good enough for REPL.
    append(Cs0, Append, Cs).

:- meta_predicate list_filter(1, ?, ?).
list_filter(_, [], []).
list_filter(G, [L|Ls0], Ls1) :-
    (   call('$toplevel':G, L) ->
        Ls1 = [L|Ls2]
    ;   Ls1 = Ls2
    ),
    list_filter(G, Ls0, Ls2).

% Warning: This isn't pure.
:- meta_predicate not(1, ?).
not(G, L) :-
    \+ call('$toplevel':G, L).

diff(Ls0, Ls1, L) :-
    eq_member(L, Ls0),
    \+ eq_member(L, Ls1).

in(Ls0, L) :-
    eq_member(L, Ls0).

both(Ls0, Ls1, L) :-
    eq_member(L, Ls0),
    eq_member(L, Ls1).

either(Ls0, Ls1, L) :-
    (   eq_member(L, Ls0)
    ;   eq_member(L, Ls1)
    ).

/*
 * This predicate removes the first equations like `'A'=A` and permutes the
 * second equation if it's the second occurrence of the variable `A`.
 */
% FIXME: Find a better name.
seen([], Eqs, Eqs).
seen([Eq0|Eqs0], Eqs1, Eqs) :-
    (   Eq0 = (N = V), var(V), occurrences(is_eq(V), Eqs0, N0) ->
        (   N0 =:= 0 ->
            % Remove singleton.
            Eqs2 = Eqs1
        ;   N0 =:= 1,
            maplist(term_variables, Eqs0, Vss),
            append(Vss, Vs),
            occurrences(==(V), Vs, N1),
            N1 =:= 1 ->
            % The singleton is the only one that remains.
            % So this equation is permuted.
            Eqs2 = [V = N|Eqs1]
        ;   Eqs2 = [N = V|Eqs1]
        )
    ;   Eqs2 = [Eq0|Eqs1]
    ),
    seen(Eqs0, Eqs2, Eqs).

is_eq(V0, _ = V) :-
    V0 == V.

:- meta_predicate occurrences(1, ?, ?).
occurrences(G, Ls, N) :-
    occurrences_(G, Ls, 0, N).

:- meta_predicate occurrences_(1, ?, ?, ?).
occurrences_(_, [], N, N).
occurrences_(G, [Eq|Eqs], N0, N) :-
    (   call('$toplevel':G, Eq) ->
        N1 is N0 + 1
    ;   N1 = N0
    ),
    occurrences_(G, Eqs, N1, N).

list_last([L0|Ls], L) :-
    list_last(Ls, L0, L).

list_last([], L, L).
list_last([L0|Ls], _, L) :-
    list_last(Ls, L0, L).

eq_member(X, [Y|Ls]) :-
    (   Ls == [] ->
        X == Y
    ;   X == Y
    ;   eq_member(X, Ls)
    ).
