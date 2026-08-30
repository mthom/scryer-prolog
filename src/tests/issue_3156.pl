:- module(issue_3156_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).

throws_syntax_error(Input) :-
    catch(
        (read_from_chars(Input, _), fail),
        error(syntax_error(_), _),
        true
    ).

test("((>)(1) throws syntax error", throws_syntax_error("((>)(1).")).
test("((a)(b) throws syntax error", throws_syntax_error("((a)(b).")).
test("(a) (b) throws syntax error", throws_syntax_error("(a) (b).")).
test("a(b) parses correctly", (read_from_chars("a(b).", T), T == a(b))).
test("(a) parses correctly", (read_from_chars("(a).", T), T == a)).
test("((>)) parses correctly", (read_from_chars("((>)).", T), T == (>))).
