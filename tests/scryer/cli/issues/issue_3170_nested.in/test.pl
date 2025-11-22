% Comprehensive test cases for issue #3170
% Testing nested parentheses and mixed contexts with op(1105,xfy,'|')
% All tests should throw syntax_error when the operator is declared

:- use_module(library(charsio)).
:- op(1105,xfy,'|').

%% Category 1: Nested parentheses with increasing depth
%% These test (|) wrapped in multiple layers of parentheses

test1 :-
    % Double nested: ((|))
    catch(
        read_from_chars("((|)).", _T),
        error(syntax_error(_), _),
        true
    ).

test2 :-
    % Triple nested: (((|)))
    catch(
        read_from_chars("(((|))).", _T),
        error(syntax_error(_), _),
        true
    ).

test3 :-
    % Quadruple nested: ((((|))))
    catch(
        read_from_chars("((((|)))).", _T),
        error(syntax_error(_), _),
        true
    ).

test4 :-
    % Quintuple nested: (((((|)))))
    catch(
        read_from_chars("(((((|))))).", _T),
        error(syntax_error(_), _),
        true
    ).

%% Category 2: Mixed bracket contexts
%% These test (|) inside combinations of [], {}, and ()

test5 :-
    % List containing curly braces with (|): [{(|)}]
    catch(
        read_from_chars("[{(|)}].", _T),
        error(syntax_error(_), _),
        true
    ).

test6 :-
    % Curly braces containing list with (|): {[(|)]}
    catch(
        read_from_chars("{[(|)]}.", _T),
        error(syntax_error(_), _),
        true
    ).

test7 :-
    % Parentheses containing curly with list: ({[(|)]})
    catch(
        read_from_chars("({[(|)]}).", _T),
        error(syntax_error(_), _),
        true
    ).

test8 :-
    % List containing nested parens: [((|))]
    catch(
        read_from_chars("[((|))].", _T),
        error(syntax_error(_), _),
        true
    ).

test9 :-
    % Curly braces containing nested parens: {((|))}
    catch(
        read_from_chars("{((|))}.", _T),
        error(syntax_error(_), _),
        true
    ).

%% Category 3: Function arguments
%% These test (|) as or within function arguments

test10 :-
    % Function with nested parens as argument: foo((|))
    catch(
        read_from_chars("foo((|)).", _T),
        error(syntax_error(_), _),
        true
    ).

test11 :-
    % Function with multiple args, middle is nested parens: bar(a,(|),b)
    catch(
        read_from_chars("bar(a,(|),b).", _T),
        error(syntax_error(_), _),
        true
    ).

test12 :-
    % Function with double nested parens: baz(((|)))
    catch(
        read_from_chars("baz(((|))).", _T),
        error(syntax_error(_), _),
        true
    ).

test13 :-
    % Multiple functions nested: foo(bar((|)))
    catch(
        read_from_chars("foo(bar((|))).", _T),
        error(syntax_error(_), _),
        true
    ).

%% Category 4: Complex nesting with operators and structures
%% These test (|) in complex nested structures with operators

test14 :-
    % Curly braces with function containing list: {foo([bar((|))])}
    catch(
        read_from_chars("{foo([bar((|))])}.", _T),
        error(syntax_error(_), _),
        true
    ).

test15 :-
    % List with multiple elements and operators: [a,{b+(|)*c}]
    catch(
        read_from_chars("[a,{b+(|)*c}].", _T),
        error(syntax_error(_), _),
        true
    ).

test16 :-
    % Deeply nested structure: {[((|))]}
    catch(
        read_from_chars("{[((|))]}.", _T),
        error(syntax_error(_), _),
        true
    ).

test17 :-
    % List with arithmetic expression: [1+((|))*2]
    catch(
        read_from_chars("[1+((|))*2].", _T),
        error(syntax_error(_), _),
        true
    ).

test18 :-
    % Curly braces with comparison: {x =:= ((|))}
    catch(
        read_from_chars("{x =:= ((|))}.", _T),
        error(syntax_error(_), _),
        true
    ).

%% Category 5: Multiple instances and mixed depths
%% These test multiple occurrences and asymmetric nesting

test19 :-
    % List with two nested instances: [(|),((|))]
    catch(
        read_from_chars("[(|),((|))].", _T),
        error(syntax_error(_), _),
        true
    ).

test20 :-
    % Function with nested list and curly: func([a,{((|))}])
    catch(
        read_from_chars("func([a,{((|))}]).", _T),
        error(syntax_error(_), _),
        true
    ).

test21 :-
    % Deeply nested in list context: [[[(|)]]]
    catch(
        read_from_chars("[[[(|)]]].", _T),
        error(syntax_error(_), _),
        true
    ).

test22 :-
    % Mixed with unification: X = {[(|)]}
    catch(
        read_from_chars("X = {[(|)]}.", _T),
        error(syntax_error(_), _),
        true
    ).

%% Category 6: Edge cases with other constructs

test23 :-
    % As part of compound term: term(((|)),data)
    catch(
        read_from_chars("term(((|)),data).", _T),
        error(syntax_error(_), _),
        true
    ).

test24 :-
    % In nested compound: outer(inner((|)))
    catch(
        read_from_chars("outer(inner((|))).", _T),
        error(syntax_error(_), _),
        true
    ).

test25 :-
    % Very deep nesting (6 levels): ((((((|))))))
    catch(
        read_from_chars("((((((|)))))).", _T),
        error(syntax_error(_), _),
        true
    ).

%% Run all tests
run :-
    test1, test2, test3, test4, test5, test6, test7, test8, test9, test10,
    test11, test12, test13, test14, test15, test16, test17, test18, test19, test20,
    test21, test22, test23, test24, test25,
    halt.

%% Note: To test VALID cases (without operator declaration),
%% remove the op/3 directive and these should parse successfully:
%%
%% valid_test1 :- read_from_chars("((|)).", T), write(T), nl.
%% valid_test2 :- read_from_chars("{[(|)]}.", T), write(T), nl.
%% valid_test3 :- read_from_chars("foo((|)).", T), write(T), nl.
%%
%% These would parse (|) as a regular atom in parentheses.
