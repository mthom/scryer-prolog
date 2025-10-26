:- module(iso_syntax_errors_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).

% ISO/IEC 13211-1 Technical Corrigendum 2, Section C2
% See https://www.complang.tuwien.ac.at/ulrich/iso-prolog/dtc2#C2

test("single_bar_in_parens_should_error", (
    % see https://github.com/mthom/scryer-prolog/issues/3140
    % (|) should cause a syntax error when parsed
    catch(
        (read_from_chars("(|).", _), false),
        error(syntax_error(_), _),
        true
    )
)).

test("op_create_empty_curly_should_error", (
    catch(
        op(500, xfy, {}),
        error(permission_error(create, operator, {}), _),
        true
    )
)).

test("op_create_empty_curly_in_list_should_error", (
    catch(
        op(500, xfy, [{}]),
        error(permission_error(create, operator, {}), _),
        true
    )
)).

test("op_create_bar_priority_1000_should_error", (
    catch(
        op(1000, xfy, '|'),
        error(permission_error(create, operator, '|'), _),
        true
    )
)).

test("op_create_bar_in_list_priority_1000_should_error", (
    catch(
        op(1000, xfy, ['|']),
        error(permission_error(create, operator, '|'), _),
        true
    )
)).

test("op_create_bar_prefix_should_error", (
    catch(
        op(1150, fx, '|'),
        error(permission_error(create, operator, '|'), _),
        true
    )
)).

test("op_create_bar_priority_1105_should_succeed", (
    op(1105, xfy, '|'),
    % Clean up
    op(0, xfy, '|')
)).

test("op_remove_bar_should_succeed", (
    op(1105, xfy, '|'),
    op(0, xfy, '|')
)).
