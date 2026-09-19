% Tests for the double bar || operator in codes mode
% Spec: https://www.complang.tuwien.ac.at/ulrich/iso-prolog/double_bar
%
% Abstract syntax (from spec):
%   term = double quoted list, bar, bar, term ;
%   Priority: 0, 0, 0
%
% The LEFT side must be a double quoted list.
% The RIGHT side (tail) can be any term at priority 0, including:
%   - Variables: "abc"||K
%   - Strings (chained): "a"||"b"||"c"
%   - Atoms: "abc"||xyz (valid per abstract syntax)
%   - Numbers: "abc"||123
%
% WG17 2025-06-02: Accepts option 1 (only after double quotes)
%
% Note: Format helpers defined BEFORE set_prolog_flag so format strings
% are parsed as chars (format/2 requires char lists, not code lists).

:- use_module(library(format)).

run_test(Name, Goal) :-
    copy_term(Goal, GoalCopy),
    (   call(GoalCopy) ->
        true
    ;   format("FAILED: ~q~n", [Name]),
        fail
    ).

report_success :- format("All tests passed", []).
report_failure :- format("Some tests failed", []).

:- set_prolog_flag(double_quotes, codes).

all_tests :-
    run_test(basic, (
        L = "abc"||K,
        L = [97,98,99|K]
    )),
    run_test(empty_string, (
        L = ""||K,
        L == K
    )),
    run_test(chain, (
        L = "a"||"b"||"c",
        L = [97,98,99]
    )),
    run_test(unification, (
        "abc"||X = [97,98,99,100,101],
        X = [100,101]
    )),
    run_test(mixed_empty, (
        L = ""||"hello"||""||world,
        L = [104,101,108,108,111|world]
    )),
    run_test(atom_tail, (
        L = "abc"||xyz,
        L = [97,98,99|xyz]
    )),
    run_test(multiline_line_comment, (
        L = "a"|| % multiple lines
            "b"||
            "c",
        L = [97,98,99]
    )),
    run_test(multiline_block_comment, (
        L = "a"||"b"|| /* with comments */ "c",
        L = [97,98,99]
    )),
    run_test(multiline_complex, (
        L = "a"|| % first line
            "b"|| /* second */
            "c",
        L = [97,98,99]
    )),
    run_test(spaced_syntax, (
        L = "abc" | | K,
        L = [97,98,99|K]
    )),
    run_test(spaced_chain, (
        L = "a" | | "b" | | "c",
        L = [97,98,99]
    )),
    run_test(block_comment_between_bars, (
        L = "a" | /* comment */ | "b",
        L = [97,98]
    )),
    run_test(line_comment_between_bars, (
        L = "a" | % line comment
            | "b",
        L = [97,98]
    )),
    run_test(block_comment_in_spaced_bar_with_tail, (
        L = "abc" |/* comment */| K,
        L = [97,98,99|K]
    )),
    run_test(comment_before_double_bar, (
        L = "a" /* before */ || "b",
        L = [97,98]
    )),
    run_test(comment_after_double_bar, (
        L = "a" || /* after */ "b",
        L = [97,98]
    )),
    run_test(comment_before_spaced_bars, (
        L = "a" /* before */ | | "b",
        L = [97,98]
    )),
    run_test(comment_after_spaced_bars, (
        L = "a" | | /* after */ "b",
        L = [97,98]
    )),
    run_test(multiple_comments_around_bars, (
        L = "a" /* before */ | /* between */ | /* after */ "b",
        L = [97,98]
    )),
    run_test(empty_at_start_of_chain, (
        L = ""||"abc"||"de",
        L = [97,98,99,100,101]
    )),
    run_test(empty_in_middle_of_chain, (
        L = "ab"||""||"cd",
        L = [97,98,99,100]
    )),
    run_test(empty_at_end_of_chain, (
        L = "abc"||"de"||"",
        L = [97,98,99,100,101]
    )),
    run_test(single_character_strings, (
        L = "x"||"y"||"z",
        L = [120,121,122]
    )),
    run_test(unicode_characters, (
        L = "α"||"β"||tail,
        L = [945,946|tail]
    )),
    run_test(longer_strings, (
        L = "hello"||"world",
        L = [104,101,108,108,111,119,111,114,108,100]
    )),
    run_test(nested_unification, (
        "a"||"b"||X = [97,98,99],
        X = [99]
    )),
    run_test(numeric_tail, (
        L = "abc"||123,
        L = [97,98,99|123]
    )).

main :-
    (   all_tests ->
        report_success
    ;   report_failure
    ),
    halt.
