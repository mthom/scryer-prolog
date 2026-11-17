:- module(issue_5_bar_list_tests, []).
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

test("[|] in curly with space before }", throws_syntax_error("{1*[|]. }.")).
test("[|] in curly with spaces throughout", throws_syntax_error("{ ! * [ | ] * ! }.")).
test("[|] in curly no spaces", throws_syntax_error("{!*[|]*!}.")).
test("[|] without braces", throws_syntax_error("!*[|]*!.")).
test("[|] with parens", throws_syntax_error("(!*[|]*!).")).
test("[|] ending with number", throws_syntax_error("!*[|]*1.")).
test("[|] ending with variable", throws_syntax_error("!*[|]*A.")).
test("[|] simple case with space", throws_syntax_error("{1*[|]. }.")).
test("[|] simple case no space", throws_syntax_error("{1*[|].}.")).
