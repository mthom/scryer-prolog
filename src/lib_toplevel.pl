:- module('$toplevel', [argv/1,
                        copy_term/3]).

:- use_module(library(atts), [call_residue_vars/2]).
:- use_module(library(charsio)).
:- use_module(library(error)).
:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lambda)).
:- use_module(library(lists)).
:- use_module(library(si)).

:- use_module(library('$project_atts')).
:- use_module(library('$atts')).

:- dynamic(disabled_init_file/0).

:- dynamic(argv/1).


arg_type(g).
arg_type(t).
arg_type(g(_)).
arg_type(t(_)).




print_exception(E) :-
    (  E == error('$interrupt_thrown', repl) -> nl % print the
                                                   % exception on a
                                                   % newline to evade
                                                   % "^C".
    ;  true
    ),
    loader:write_error(E),
    nl.


run_input_once :-
    bb_put('$report_all', true),
    catch(read_and_match_all_results, E, print_exception(E)).

read_and_match_all_results :-
    '$read_query_term'(_, Term, _, _, VarList),
    bb_put('$answer_count', 0),
    submit_query_and_print_all_results(Term, VarList).

submit_query_and_print_all_results(Term, VarList) :-
    '$get_b_value'(B),
    bb_put('$report_all', true),
    bb_put('$report_n_more', 0),
    call(user:Term),
    write_eqs_and_read_input(B, VarList),
    !.
submit_query_and_print_all_results(_, _) :-
    (   bb_get('$answer_count', 0) ->
        write('   ')
    ;   true
    ),
    write('false.'),
    nl.
