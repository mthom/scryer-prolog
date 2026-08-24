:- module(issue_7_bar_parens_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).

setup :-
    op(1105, xfy, '|').

throws_syntax_error(Input) :-
    catch(
        (read_from_chars(Input, _), fail),
        error(syntax_error(_), _),
        true
    ).

test("(|) alone should error", throws_syntax_error("(|).")).
test("(|) in curly with space before }", throws_syntax_error("{1*!(|). }.")).
test("(|) in curly no space", throws_syntax_error("{1*!(|).}.")).
test("(|) without braces", throws_syntax_error("1*!(|).")).
test("(|) with + operator", throws_syntax_error("1+!(|).")).
test("(|) nested in parens", throws_syntax_error("(!(|)).")).
test("(|) as argument", throws_syntax_error("foo((|)).")).
