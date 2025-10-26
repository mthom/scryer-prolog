:- module(syntax_errors_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).

% Test for issue #3138
% ([) and ({) should be syntax errors when reading
% See: https://github.com/mthom/scryer-prolog/issues/3138
test("read of ([). should produce syntax_error", (
    catch(
        (read_from_chars("([).", _), false),
        error(syntax_error(_), _),
        true
    )
)).

% Test that writeq(([)) produces syntax error when reading
test("read of writeq(([)). should produce syntax_error", (
    catch(
        (read_from_chars("writeq(([)).", _), false),
        error(syntax_error(_), _),
        true
    )
)).

% Test that ({) should be a syntax error (similar to ([)
test("read of ({). should produce syntax_error", (
    catch(
        (read_from_chars("({).", _), false),
        error(syntax_error(_), _),
        true
    )
)).
