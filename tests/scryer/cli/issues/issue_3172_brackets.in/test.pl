%% Test file for issue #3172: Mismatched bracket detection
%%
%% GitHub: https://github.com/mthom/scryer-prolog/pull/3172#issuecomment-3574685968
%%
%% Bug Report:
%% - read_from_chars("([).", T) was returning T = '[' instead of syntax_error
%% - read_from_chars("{([)}.", T) was returning T = {[} instead of syntax_error
%%
%% ISO/IEC 13211-1:1995 References:
%% - Section 6.3: Brackets must be properly matched
%%   - ( must close with )
%%   - [ must close with ]
%%   - { must close with }

:- use_module(library(charsio)).

%% ============================================================================
%% TESTS FOR MISMATCHED BRACKETS (should all throw syntax_error)
%% ============================================================================

%% Test 1-12: Various mismatched bracket patterns
test1 :- catch((read_from_chars("([).", _), fail), error(syntax_error(_), _), true).
test2 :- catch((read_from_chars("({).", _), fail), error(syntax_error(_), _), true).
test3 :- catch((read_from_chars("{([)}.", _), fail), error(syntax_error(_), _), true).
test4 :- catch((read_from_chars("[(]).", _), fail), error(syntax_error(_), _), true).
test5 :- catch((read_from_chars("{(}).", _), fail), error(syntax_error(_), _), true).
test6 :- catch((read_from_chars("{[}.", _), fail), error(syntax_error(_), _), true).
test7 :- catch((read_from_chars("[{].", _), fail), error(syntax_error(_), _), true).
test8 :- catch((read_from_chars("((]).", _), fail), error(syntax_error(_), _), true).
test9 :- catch((read_from_chars("[).", _), fail), error(syntax_error(_), _), true).
test10 :- catch((read_from_chars("{).", _), fail), error(syntax_error(_), _), true).
test11 :- catch((read_from_chars("(].", _), fail), error(syntax_error(_), _), true).
test12 :- catch((read_from_chars("(}.", _), fail), error(syntax_error(_), _), true).

%% ============================================================================
%% TESTS FOR VALID NESTED BRACKETS (should all succeed)
%% ============================================================================

test13 :- read_from_chars("([]).", T), T = [].
test14 :- read_from_chars("({}).", T), T = {}.
test15 :- read_from_chars("{[]}.", T), T = '{}'([]).
test17 :- read_from_chars("{([])}.", T), T = '{}'([]).
test18 :- read_from_chars("[{}].", T), T = [{}].
test19 :- read_from_chars("([a]).", T), T = [a].
test20 :- read_from_chars("({a}).", T), T = '{}'(a).
test21 :- read_from_chars("{[a,b]}.", T), T = '{}'([a,b]).
test22 :- read_from_chars("[a,[b],c].", T), T = [a,[b],c].
test23 :- read_from_chars("{a,{b},c}.", T), T = '{}'(','(a,','('{}'(b),c))).

%% Run all tests (silent success pattern)
run :-
    test1, test2, test3, test4, test5, test6, test7, test8, test9, test10,
    test11, test12, test13, test14, test15, test17, test18, test19, test20,
    test21, test22, test23,
    halt.
