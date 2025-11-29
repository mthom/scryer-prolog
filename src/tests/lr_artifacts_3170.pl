%% Issue #3170: LR artifacts
%% https://github.com/mthom/scryer-prolog/issues/3170
%%
%% ISO 6.3.4: Operators require operands per specifier
%% ISO 6.3.6: {term} requires valid term inside

:- module(lr_artifacts_3170_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).

%% Issue #3170: Parser produced garbage {/} instead of error for unreduced operators
test("issue_3170_unreduced_op_in_curly_errors", (
    op(1105, xfy, '|'),
    catch(read_from_chars("{!*!(|)/}.", _), _, true),
    op(0, xfy, '|')
)).

%% Bare operators in curlies must error (no operands)
test("bare_slash_in_curly_errors", (
    catch(read_from_chars("{/}.", _), _, true)
)).

test("bare_plus_in_curly_errors", (
    catch(read_from_chars("{+}.", _), _, true)
)).

test("bare_star_in_curly_errors", (
    catch(read_from_chars("{*}.", _), _, true)
)).

%% Incomplete operator expressions must error
test("trailing_slash_errors", (
    catch(read_from_chars("{a/}.", _), _, true)
)).

test("leading_slash_errors", (
    catch(read_from_chars("{/b}.", _), _, true)
)).

test("juxtaposed_terms_error", (
    catch(read_from_chars("{!*!a}.", _), _, true)
)).

%% Quoted operators in curlies must succeed
test("quoted_slash_in_curly_succeeds", (
    read_from_chars("{(/)}.", T),
    T == '{}'(/)
)).

test("quoted_plus_in_curly_succeeds", (
    read_from_chars("{(+)}.", T),
    T == '{}'(+)
)).

%% Valid expressions in curlies must succeed
test("valid_multiplication_succeeds", (
    read_from_chars("{a*b}.", T),
    T == '{}'(a*b)
)).

test("valid_addition_succeeds", (
    read_from_chars("{1+2}.", T),
    T == '{}'(1+2)
)).

test("atom_bang_succeeds", (
    read_from_chars("{!}.", T),
    T == '{}'(!)
)).

test("bang_star_bang_succeeds", (
    read_from_chars("{!*!}.", T),
    T == '{}'(!*!)
)).

%% Bar operator cases (with | defined as operator)
test("bar_incomplete_left_errors", (
    op(1105, xfy, '|'),
    catch(read_from_chars("{a|}.", _), _, true),
    op(0, xfy, '|')
)).

test("bar_incomplete_right_errors", (
    op(1105, xfy, '|'),
    catch(read_from_chars("{|b}.", _), _, true),
    op(0, xfy, '|')
)).

test("quoted_bar_in_curly_succeeds", (
    op(1105, xfy, '|'),
    read_from_chars("{(|)}.", T),
    op(0, xfy, '|'),
    T == '{}'('|')
)).

test("valid_bar_expression_succeeds", (
    op(1105, xfy, '|'),
    read_from_chars("{a|b}.", T),
    op(0, xfy, '|'),
    T == '{}'('|'(a,b))
)).

test("quoted_bar_in_expression_succeeds", (
    op(1105, xfy, '|'),
    read_from_chars("{a*(|)}.", T),
    op(0, xfy, '|'),
    T == '{}'(a*'|')
)).

%% Nested curlies
test("nested_curly_with_bare_op_errors", (
    catch(read_from_chars("{{/}}.", _), _, true)
)).

test("nested_curly_with_quoted_op_succeeds", (
    read_from_chars("{{(/)}}.", T),
    T == '{}'('{}'(/))
)).
