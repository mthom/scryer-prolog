:- module('$toplevel', [argv/1, copy_term/3]).

:- use_module(library(atts), [call_residue_vars/2]).
:- use_module(library(charsio), [
    char_type/2,
    get_single_char/1,
    read_term_from_chars/2,
    write_term_to_chars/3
]).
:- use_module(library(dcgs)).
:- use_module(library(files), [file_exists/1]).
:- use_module(library(format), [format/2, format_//2]).
:- use_module(library(iso_ext), [bb_get/2, bb_put/2, setup_call_cleanup/3]).
:- use_module(library(lists), [
    append/2,
    append/3,
    length/2,
    maplist/2,
    maplist/3,
    member/2,
    reverse/2,
    select/3
]).

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

'$repl'(Args0) :-
    (   nonvar(Args0), Args0 = [_|Args1] ->
        (   append(Args2, ["--"|Args3], Args1) ->
            true
        ;   Args2 = Args1,
            Args3 = []
        )
    ;   Args2 = [],
        Args3 = []
    ),
    (   \+ argv(_) ->
        asserta('$toplevel':argv(Args3))
    ;   % Unexpected what to do?
        argv(Args), write('Found unexpected arguments: '), write(Args), nl
    ),
    load_scryerrc,
    % Loads modules first.
    gather_goals_and_load_modules(Args2, Goals, Toplevels0),
    append(Toplevels0, ['$toplevel':repl], Toplevels),
    maplist(execute_goal, Goals),
    [Toplevel|_] = Toplevels,
    % The top-level isn't supposed to fail or end.
    call(Toplevel).
'$repl'(_) :-
    repeat.

gather_goals_and_load_modules(Args, Goals, Toplevels) :-
    gather_goals_and_load_modules(Args, [], Goals0, [], Toplevels0),
    reverse(Goals0, Goals),
    reverse(Toplevels0, Toplevels).

gather_goals_and_load_modules([], Goals, Goals, Toplevels, Toplevels).
gather_goals_and_load_modules([Arg0|Args0], Goals0, Goals, Toplevels0, Toplevels) :-
    (   member(Arg0, ["-h", "--help"]) ->
        print_help,
        halt
    ;   member(Arg0, ["-v", "--version"]) ->
        print_version,
        halt
    ;   member(Arg0, ["-g", "--goal"]) ->
        Toplevels1 = Toplevels0,
        (   [Arg1|Args1] = Args0 ->
            % Only the first term needs to be valid.
            append(Arg1, "\n.", Arg2),
            catch(read_term_from_chars(Arg2, Goal), Exception, true),
            (   nonvar(Exception) ->
                format("~q causes: ~q\n", [Arg1, Exception])
            ;   Goals1 = [Goal|Goals0]
            )
        ;   print_help % Argument is missing.
        )
    ;   member(Arg0, ["-t", "--top-level"]) ->
        Goals1 = Goals0,
        (   [Arg1|Args1] = Args0 ->
            % Only the first term needs to be valid.
            append(Arg1, "\n.", Arg2),
            catch(read_term_from_chars(Arg2, Goal), Exception, true),
            (   nonvar(Exception) ->
                format("~q causes: ~q\n", [Arg1, Exception])
            ;   Toplevels1 = [Goal|Toplevels0]
            )
        ;   print_help % Argument is missing.
        )
    ;   % Load file as a module.
        Args1 = Args0,
        Toplevels1 = Toplevels0,
        Goals1 = Goals0,
        atom_chars(Mod, Arg0),
        % Goals1 = [use_module(Mod)|Goals0]
        catch(use_module(Mod), E, print_exception(E))
    ),
    gather_goals_and_load_modules(Args1, Goals1, Goals, Toplevels1, Toplevels).

execute_goal(G) :-
    (   catch(call(user:G), Exception, true) ->
        (   nonvar(Exception) ->
            % write(G), write(' causes: '), write(Exception), nl % Fail-safe.
            format("\"~q\" causes: ~q\n", [G, Exception])
        ;   true
        )
    ;   true
    ).

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
    write('   -t, --top-level GOAL '),
    write('Launch the top-level GOAL'), nl,
    % write('                        '),
    halt.

print_version :-
    '$scryer_prolog_version'(Version),
    % write(Version), nl, % Fail-safe.
    format("~s\n", [Version]),
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
        bb_put('$first_answer', true), % true,
        (   catch(call_residue_vars(user:Goal, ResVs), E, true),
            (   var(E) ->
                Succeed = true
            ;   NoError = false
            )
        ),
        (   (   NoError \== false, Succeed \== true ->
                (   bb_get('$first_answer', true) ->
                    write('   ')
                ;   true
                ),
                format("false.\n", [])
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
    (   bb_get('$first_answer', true) ->
        write('   '),
        bb_put('$first_answer', false)
    ;   true
    ),
    (   print_and_read_input_if_not_last(Last, 20, Terms, AllEqs) ->
        true
    ;   !
    ).

print_and_read_input_if_not_last(Last, MaxDepth, Terms, AllEqs) :-
    print_goal(Terms, AllEqs, MaxDepth, Cs),
    format("~s", [Cs]),
    (   Last == true ->
        (   list_last(Cs, C), char_type(C, graphic_token) ->
            write(' .'), nl
        ;   write('.'), nl
        )
    ;   read_input_and_print_(MaxDepth, Terms, AllEqs)
    ).

read_input_and_print_(MaxDepth, Terms, AllEqs) :-
    get_single_char(C),
    (   member(C, [;, ' ', n]) ->
        % write(' ;'), nl
        nl, write(';  ')
    ;   member(C, ['\n', .]) ->
        nl, write(';  ...'), nl,
        false
        % write(' ;\n   ...'), nl,
        % false
    ;   C = h ->
        nl,
        help_message,
        read_input_and_print_(MaxDepth, Terms, AllEqs)
    ;   C = p ->
        nl,
        print_goal(Terms, AllEqs, MaxDepth, Cs),
        format("~s", [Cs]),
        read_input_and_print_(MaxDepth, Terms, AllEqs)
    ;   C = w ->
        nl,
        print_goal(Terms, AllEqs, 0, Cs),
        format("~s", [Cs]),
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
    % write_term_to_chars(Term, Settings, Cs0), % Not good enough for REPL.
    phrase(print_(Term, Settings, [], _, _), Cs0),
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

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Prolog printer.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

chars(V) :- var(V), !, false.
chars([]).
chars([C|Cs]) :- atom(C), atom_length(C, 1), chars(Cs).

spec_arity(fx, 1).
spec_arity(fy, 1).
spec_arity(xf, 1).
spec_arity(yf, 1).
spec_arity(xfx, 2).
spec_arity(xfy, 2).
spec_arity(yfx, 2).

symbolic_control('\a', "\\a").
symbolic_control('\b', "\\b").
symbolic_control('\f', "\\f").
symbolic_control('\n', "\\n").
symbolic_control('\r', "\\f").
symbolic_control('\t', "\\t").
symbolic_control('\v', "\\v").
% symbolic_control('\x0\', "\x0\"). % '.

print_double_quoted([]) --> [].
print_double_quoted([C|Cs]) -->
    (   { symbolic_control(C, Cs0) } ->
        Cs0
    % ;   { write_term_to_chars(C, [], Cs0) }, Cs0
    ;   format_("~w", [C])
    ),
    print_double_quoted(Cs).

print_quoted([]) --> [].
print_quoted([C|Cs]) -->
    (   { C = '''' } ->
        "''"
    ;   { symbolic_control(C, Cs0) } ->
        Cs0
    % ;   { write_term_to_chars(C, [], Cs0) }, Cs0
    ;   format_("~w", [C])
    ),
    print_quoted(Cs).

print_args([A|As], Settings, Ps) --> print_args(As, A, Settings, Ps).

print_args([], A0, Settings, Ps) -->
    (   { nonvar(A0),
          functor(A0, F, N),
          N >= 1, N =< 2,
          current_op(Pri, S, F),
          spec_arity(S, N),
          Pri > 1000 } ->
        "(", print_(A0, Settings, Ps, '(', _), ")"
    ;   print_(A0, Settings, Ps, _, _)
    ).
print_args([A1|As], A0, Settings, Ps) -->
    (   { nonvar(A0),
          functor(A0, F, N),
          N >= 1, N =< 2,
          current_op(Pri, S, F),
          spec_arity(S, N),
          Pri > 1000 } ->
        "(", print_(A0, Settings, Ps, '(', _), ")"
    ;   print_(A0, Settings, Ps, _, _)
    ),
    ",", print_args(As, A1, Settings, Ps).

print_list(List, Settings, Ps, MaxDepth0) -->
    % { format("List: ~q ~q ~q\n", [Settings, Ps, MaxDepth0]) },
    {   (   var(MaxDepth0) ->
            (   member(max_depth(MaxDepth0), Settings) ->
                true
            ;   MaxDepth0 = 0 % Infinite
            )
        ;   true
        )  ,
        (   MaxDepth0 == none ->
            true
        ;   MaxDepth0 > 1 ->
            MaxDepth is MaxDepth0 - 1
        ;   MaxDepth0 =:= 1 ->
            MaxDepth = none
        ;   MaxDepth0 =:= 0 ->
            MaxDepth = 0
        )
    },
    (   { MaxDepth0 \== none } ->
        (   { [L0|Ls] = List } ->
            (   { nonvar(L0),
                  functor(L0, F, N),
                  N >= 1, N =< 2,
                  current_op(Pri, S, F),
                  spec_arity(S, N),
                  Pri > 1000 } ->
                { Parentheses = true, C0 = '(' },
                "("
            ;   { Parentheses = false }
            ),
            (   { var(Ls) } ->
                print_(L0, Settings, Ps, C0, _),
                (   { Parentheses } ->
                    ")"
                ;   []
                ),
                "|", print_(Ls, Settings, Ps, '|', _)
            ;   { Ls = [] } ->
                print_(L0, Settings, Ps, C0, _),
                (   { Parentheses } ->
                    ")"
                ;   []
                )
            ;   { Ls = [_|_] } ->
                print_(L0, Settings, Ps, C0, _),
                (   { Parentheses } ->
                    ")"
                ;   []
                ),
                (   { eq_member(Ls, Ps) } ->
                    (   { member(variable_names(Eqs), Settings) } ->
                        (   { member(Name = V, Eqs), V == Ls } ->
                            { atom_chars(Name, Cs) }, "|", Cs
                        ;   { true } -> "_0"
                        ;   { throw(error(instantiation_error, print_//5)) }
                        )
                    ;   { true } -> "_1"
                    ;   { throw(error(instantiation_error, print_//5)) }
                    )
                ;   ",", print_list(Ls, Settings, Ps, MaxDepth)
                )
            ;   print_(L0, Settings, Ps, C0, _),
                (   { Parentheses } ->
                    ")"
                ;   []
                ),
                "|", print_(Ls, Settings, Ps, C0, _)
            )
        ;   { [] = List } ->
            print_(List, Settings, Ps, _, _)
        ;   { throw(error(is_not_list(List), print_list//5)) }
        )
    ;   "..."
    ).

print_(Var, Settings, _Ps, L0, L) -->
    { var(Var) }, !,
    % { format("Variable: ~q\n", [Settings]) },
    (   { member(variable_names(Eqs), Settings) } ->
        (   { member(Name = V, Eqs), V == Var } ->
            { atom_chars(Name, Cs), list_last(Cs, L) },
            (   { nonvar(L0), char_type(L0, alnum) } ->
                " "
            ;   []
            ),
            Cs
        ;   { true } ->
            { L = '2' },
            "_2"
        ;   { throw(error(instantiation_error, print_//5)) }
        )
    ;   { true } ->
        { L = '3' },
        "_3"
    ;   { throw(error(instantiation_error, print_//5)) }
    ).
print_(Number, _Settings, _Ps, L0, L) -->
    { number(Number) ; rational(Number) }, !,
    % { format("Number: ~q ~q\n", [Number, _Settings]) },
    { number_chars(Number, Cs), list_last(Cs, L) },
    (   { nonvar(L0),
        ( char_type(L0, alnum)
        ; Number < 0, char_type(L0, graphic_token)
        ) } ->
        " "
    ;   []
    ),
    Cs.
print_(Atom, _Settings, _Ps, L0, L) -->
    { atom(Atom) }, !,
    % { format("Atom: ~q ~q ~q ~q\n", [Atom, _Settings, _Ps, L0]) },
    { atom_chars(Atom, Cs) },
    (   { Cs = [] } ->
        { member(Atom, ['']) } ->
        { L = '''' },
        "'", print_quoted(Cs), "'"
    ;   { list_last(Cs, L1) },
        (   { member(Atom, [!, ;, [], {}]) } ->
            { L = L1 },
            Cs
        % ;   { Atom == (\) } -> % Not nice.
        %     { L = L1 },
        %     "\\"
        ;   { member(Atom, [.]) } ->
            (   { nonvar(L0),
                  ( char_type(L0, graphic_token)
                  ; char_type(L0, whitespace)
                  ) } ->
                { L = '''' },
                "'.'"
            ;   { L = L1 },
                "."
            )
        ;   { [C|_] = Cs, char_type(C, numeric) } ->
            % Quote is always required.
            { L = '''' },
            "'", print_quoted(Cs), "'"
        % ;   { member(C, Cs), char_type(C, meta), C \= (\) } ->
        %     { L = '''' },
        %     "'", print_quoted(Cs), "'"
        ;   { member(C, Cs), member(T, [solo, whitespace]), char_type(C, T) } ->
            % Quote is always required.
            { L = '''' },
            "'", print_quoted(Cs), "'"
        ;   { setof(
                T,
                C^(
                    lists:member(C, Cs),
                    lists:member(T, [alnum, graphic_token]),
                    charsio:char_type(C, T)
                ),
                Ts
              ),
              length(Ts, N),
              N > 1 } ->
            % There is a mixture.
            { L = '''' },
            "'", print_quoted(Cs), "'"
        ;   { member(C, Cs),
              \+ ( member(T, [alnum, graphic_token]), char_type(C, T)) } ->
            % There is an unknown character.
            { L = '''' },
            "'", print_quoted(Cs), "'"
        ;   { L = L1 },
            (   { nonvar(L0), [C|_] = Cs, member(T, [alnum, graphic_token]),
                  char_type(C, T), char_type(L0, T) } ->
                " "
            ;   []
            ),
            Cs
        )
    ).
print_(Compound, Settings0, Ps0, L0, L) -->
    { Compound =.. [F|Args] }, !,
    % { format("Compound: ~q ~q\n", [Compound, Settings]) },
    { ( select(max_depth(MaxDepth0), Settings0, Settings1) ->
        (   MaxDepth0 == none ->
            Settings = Settings0
        ;   MaxDepth0 > 1 ->
            MaxDepth is MaxDepth0 - 1,
            Settings = [max_depth(MaxDepth)|Settings1]
        ;   MaxDepth0 =:= 1 ->
            Settings = [max_depth(none)|Settings1]
        ;   MaxDepth0 =:= 0 ->
            Settings = [max_depth(0)|Settings1],
            MaxDepth = 0
        )
      ; Settings = Settings0
      )
    },
    (   { MaxDepth0 \== none } ->
        (   { eq_member(Compound, Ps0) } ->
            (   { member(variable_names(Eqs), Settings) } ->
                (   { member(Name = V, Eqs), V == Compound } ->
                    { atom_chars(Name, Cs), list_last(Cs, L) },
                    (   { nonvar(L0), char_type(L0, alnum) } ->
                        " "
                    ;   []
                    ),
                    Cs
                ;   { true } ->
                    { L = '4' },
                    "_4"
                ;   { throw(error(instantiation_error, print_//5)) }
                )
            ;   { true } ->
                { L = '5' },
                "_5"
            ;   { throw(error(instantiation_error, print_//5)) }
            )
        ;   { length(Args, N), Ps = [Compound|Ps0] },
            % TODO: What happens if for example fx and xf is defined?
            (   { N =:= 1, current_op(P, Spec, F), spec_arity(Spec, N) } ->
                { [A] = Args, ( nonvar(A), functor(A, F1, N1) -> true ; true ) },
                (   { member(Spec, [fx, fy]) } ->
                    (   { number(A), A > 0, F = (-) } ->
                        { L = ')' },
                        print_(F, Settings, Ps, L0, _),
                        " (", print_(A, Settings, Ps, '(', _), ")"
                    ;   { atom(A), current_op(_, _, F1) } ->
                        { L = ')' },
                        print_(F, Settings, Ps, L0, _),
                        " (", print_(A, Settings, Ps, '(', _), ")"
                    ;   { compound(A), % N > 0,
                          N1 >= 1, N1 =< 2,
                          current_op(P1, S1, F1),
                          spec_arity(S1, N1),
                          ( Spec = fy, P < P1 -> true
                          ; Spec = fx, P =< P1
                          ) } ->
                        { L = ')' },
                        print_(F, Settings, Ps, L0, _),
                        " (", print_(A, Settings, Ps, '(', _), ")"
                    ;   print_(F, Settings, Ps, L0, L1),
                        print_(A, Settings, Ps, L1, L)
                    )
                ;   { member(Spec, [xf, yf]) } ->
                    (   { atom(A), current_op(_, _, F1) } ->
                        "(", print_(A, Settings, Ps, '(', _), ")",
                        print_(F, Settings, Ps, ')', L)
                    ;   { compound(A),
                          N1 >= 1, N1 =< 2,
                          current_op(P1, S1, F1),
                          spec_arity(S1, N1),
                          ( Spec = yf, P < P1 -> true
                          ; Spec = xf, P =< P1
                          ) } ->
                        "(", print_(A, Settings, Ps, '(', _), ") ",
                        print_(F, Settings, Ps, ')', L)
                    ;   print_(A, Settings, Ps, L0, L1),
                        print_(F, Settings, Ps, L1, L)
                    )
                )
            ;   { N =:= 2, current_op(P, Spec, F), spec_arity(Spec, N) } ->
                (   { [A, B] = Args,
                      ( nonvar(A), functor(A, F1, N1) -> true ; true),
                      ( nonvar(B), functor(B, F2, N2) -> true ; true) },
                    (   { atom(A), current_op(_, _, F1) } ->
                        { L1 = ')' },
                        "(", print_(A, Settings, Ps, '(', _), ")"
                    ;   { compound(A),
                          N1 >= 1, N1 =< 2,
                          current_op(P1, S1, F1),
                          spec_arity(S1, N1),
                          ( Spec = yfx, P < P1 ->
                            true
                          ; ( Spec = xfx -> true ; Spec = xfy ), P =< P1
                          ) } ->
                        { L1 = ')' },
                        "(", print_(A, Settings, Ps, '(', _), ")"
                    ;   print_(A, Settings, Ps, L0, L1)
                    ),
                    (   { F = (',') } ->
                        { L2 = (',') },
                        ","
                    /*
                    ;   { member(F, [., :, /]) } ->
                        print_(F, Settings, Ps, L1, L2)
                    ;   { member(F, [-, +, *, /, **, ^, //, <<, >>, ..]) } ->
                        print_(F, Settings, Ps, L1, L2)
                    ;   { L2 = ' ' },
                        " ", print_(F, Settings, Ps, ' ', _), " "
                    % */
                    ;   { false, member(F, [=]) } ->
                        { L2 = ' ' },
                        " ", print_(F, Settings, Ps, ' ', _), " "
                    ;   print_(F, Settings, Ps, L1, L2)
                    ),
                    (   { atom(B), current_op(_, _, F2) } ->
                        { L = ')' },
                        "(", print_(B, Settings, Ps, '(', _), ")"
                    ;   { compound(B),
                          N2 >= 1, N2 =< 2,
                          current_op(P2, S2, F2),
                          spec_arity(S2, N2),
                          ( Spec = xfy, P < P2 ->
                            true
                          ; ( Spec = xfx -> true ; Spec = yfx ), P =< P2
                          ) } ->
                        { L = ')' },
                        "(", print_(B, Settings, Ps, '(', _), ")"
                    ;   print_(B, Settings, Ps, L2, L)
                    )
                )
            ;   { F = '.', N =:= 2 } ->
                (   { ground(Compound),
                      length(Compound, Cn),
                      chars(Compound) } ->
                    { L = '"' },
                    {   (   MaxDepth > 0 ->
                            (   Cn > MaxDepth ->
                                Cut = true,
                                Cn0 is max(MaxDepth - 4, 0),
                                length(Cs, Cn0)
                            ;   Cut = false,
                                length(Cs, Cn)
                            ),
                            append(Cs, _, Compound)
                        ;   Cs = Compound
                        )
                    },
                    "\"",
                    print_double_quoted(Cs),
                    (   { Cut == true } ->
                        " ..."
                    ;   []
                    ),
                    "\""
                ;   { L = ']' },
                    "[", print_list(Compound, Settings, Ps, _), "]"
                )
            ;   { F = '{}', N =:= 1 } ->
                { L = '}' },
                "{", print_list(Args, Settings, Ps, _), "}"
            ;   { L = ')' },
                print_(F, Settings, Ps, L0, _),
                "(", print_args(Args, Settings, Ps), ")"
            )
        )
    ;   "..."
    ).
