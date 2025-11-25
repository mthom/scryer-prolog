%% Test file for issue #3172: Mismatched bracket detection
%%
%% GitHub: https://github.com/mthom/scryer-prolog/pull/3172#issuecomment-3574685968
%%
%% Bug Report:
%% - read_from_chars("([).", T) returns T = '[' instead of syntax_error
%% - read_from_chars("{([)}.", T) returns T = {[} instead of syntax_error
%%
%% ISO/IEC 13211-1:1995 References:
%% - Section 6.3: Brackets must be properly matched
%%   - ( must close with )
%%   - [ must close with ]
%%   - { must close with }
%% - Section 6.3.4: List notation - [items] denotes list
%% - Section 6.3.6: Curly bracketed term - {term} == '{}'(term)
%%
%% Mismatched brackets should always result in syntax_error.

:- use_module(library(charsio)).

%% ============================================================================
%% TESTS FOR MISMATCHED BRACKETS (should all fail with syntax_error)
%% ============================================================================

%% Test 1: ([) - paren containing unclosed list, closed with paren
%% Expected: syntax_error (mismatched: [ not closed with ])
test1 :-
    catch(
        (read_from_chars("([).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 2: ({) - paren containing unclosed curly, closed with paren
%% Expected: syntax_error (mismatched: { not closed with })
test2 :-
    catch(
        (read_from_chars("({).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 3: {([)} - curly containing mismatched inner brackets
%% Expected: syntax_error (mismatched: [ not closed with ])
test3 :-
    catch(
        (read_from_chars("{([)}.", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 4: [(]) - list containing mismatched parens
%% Expected: syntax_error (mismatched: ( not closed with ))
test4 :-
    catch(
        (read_from_chars("[(]).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 5: {(}) - curly containing mismatched parens
%% Expected: syntax_error (mismatched: ( not closed with ))
test5 :-
    catch(
        (read_from_chars("{(}).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 6: {[} - curly containing unclosed list
%% Expected: syntax_error (mismatched: [ not closed with ])
test6 :-
    catch(
        (read_from_chars("{[}.", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 7: [{] - list containing unclosed curly
%% Expected: syntax_error (mismatched: { not closed with })
test7 :-
    catch(
        (read_from_chars("[{].", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 8: ((]) - nested parens with mismatched list closer
%% Expected: syntax_error
test8 :-
    catch(
        (read_from_chars("((]).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 9: [) - bare list closed with paren
%% Expected: syntax_error
test9 :-
    catch(
        (read_from_chars("[).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 10: {) - bare curly closed with paren
%% Expected: syntax_error
test10 :-
    catch(
        (read_from_chars("{).", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 11: (] - bare paren closed with list closer
%% Expected: syntax_error
test11 :-
    catch(
        (read_from_chars("(].", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% Test 12: (} - bare paren closed with curly closer
%% Expected: syntax_error
test12 :-
    catch(
        (read_from_chars("(}.", _), fail),
        error(syntax_error(_), _),
        true
    ).

%% ============================================================================
%% TESTS FOR VALID NESTED BRACKETS (should all succeed)
%% ============================================================================

%% Test 13: ([]) - paren containing empty list
%% Expected: T = []
test13 :-
    read_from_chars("([]).", T),
    T = [].

%% Test 14: ({}) - paren containing empty curly
%% Expected: T = {}
test14 :-
    read_from_chars("({}).", T),
    T = {}.

%% Test 15: {[]} - curly containing empty list
%% Expected: T = {[]}
test15 :-
    read_from_chars("{[]}.", T),
    T = '{}'([]).

%% Test 17: {([])} - curly containing paren containing list
%% Expected: T = {[]}
test17 :-
    read_from_chars("{([])}.", T),
    T = '{}'([]).

%% Test 18: [{}] - list containing empty curly
%% Expected: T = [{}]
test18 :-
    read_from_chars("[{}].", T),
    T = [{}].

%% Test 19: ([a]) - paren containing list with element
%% Expected: T = [a]
test19 :-
    read_from_chars("([a]).", T),
    T = [a].

%% Test 20: ({a}) - paren containing curly with element
%% Expected: T = {a}
test20 :-
    read_from_chars("({a}).", T),
    T = '{}'(a).

%% Test 21: {[a,b]} - curly containing list with elements
%% Expected: T = {[a,b]}
test21 :-
    read_from_chars("{[a,b]}.", T),
    T = '{}'([a,b]).

%% Test 22: [a,[b],c] - list containing nested list
%% Expected: T = [a,[b],c]
test22 :-
    read_from_chars("[a,[b],c].", T),
    T = [a,[b],c].

%% Test 23: {a,{b},c} - curly containing nested curly
%% Expected: T = {','(a,','({b},c))}
test23 :-
    read_from_chars("{a,{b},c}.", T),
    T = '{}'(','(a,','('{}'(b),c))).

%% ============================================================================
%% MAIN TEST RUNNER
%% ============================================================================

run :-
    write('Test 1 (([) should error): '),
    (test1 -> write('PASS') ; write('FAIL')), nl,

    write('Test 2 (({) should error): '),
    (test2 -> write('PASS') ; write('FAIL')), nl,

    write('Test 3 ({([)} should error): '),
    (test3 -> write('PASS') ; write('FAIL')), nl,

    write('Test 4 ([(]) should error): '),
    (test4 -> write('PASS') ; write('FAIL')), nl,

    write('Test 5 ({(}) should error): '),
    (test5 -> write('PASS') ; write('FAIL')), nl,

    write('Test 6 ({[} should error): '),
    (test6 -> write('PASS') ; write('FAIL')), nl,

    write('Test 7 ([{] should error): '),
    (test7 -> write('PASS') ; write('FAIL')), nl,

    write('Test 8 (((]) should error): '),
    (test8 -> write('PASS') ; write('FAIL')), nl,

    write('Test 9 ([) should error): '),
    (test9 -> write('PASS') ; write('FAIL')), nl,

    write('Test 10 ({) should error): '),
    (test10 -> write('PASS') ; write('FAIL')), nl,

    write('Test 11 ((] should error): '),
    (test11 -> write('PASS') ; write('FAIL')), nl,

    write('Test 12 ((} should error): '),
    (test12 -> write('PASS') ; write('FAIL')), nl,

    write('Test 13 (([]) valid): '),
    (test13 -> write('PASS') ; write('FAIL')), nl,

    write('Test 14 (({}) valid): '),
    (test14 -> write('PASS') ; write('FAIL')), nl,

    write('Test 15 ({[]} valid): '),
    (test15 -> write('PASS') ; write('FAIL')), nl,

    write('Test 17 ({([])} valid): '),
    (test17 -> write('PASS') ; write('FAIL')), nl,

    write('Test 18 ([{}] valid): '),
    (test18 -> write('PASS') ; write('FAIL')), nl,

    write('Test 19 (([a]) valid): '),
    (test19 -> write('PASS') ; write('FAIL')), nl,

    write('Test 20 (({a}) valid): '),
    (test20 -> write('PASS') ; write('FAIL')), nl,

    write('Test 21 ({[a,b]} valid): '),
    (test21 -> write('PASS') ; write('FAIL')), nl,

    write('Test 22 ([a,[b],c] valid): '),
    (test22 -> write('PASS') ; write('FAIL')), nl,

    write('Test 23 ({a,{b},c} valid): '),
    (test23 -> write('PASS') ; write('FAIL')), nl.

:- initialization(run).
