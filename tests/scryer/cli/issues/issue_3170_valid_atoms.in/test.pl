%% Test cases for issue #3170: VALID atom cases
%% Testing that (|) patterns work correctly WITHOUT op(1105,xfy,'|') declaration
%% These should all SUCCEED, parsing '|' as a regular atom
%%
%% ISO/IEC 13211-1:1995 References:
%% - §6.3.1.3: Atoms - '|' is a valid atom name
%% - §6.3.3.1: Arguments - atoms that are operators can appear as args
%% - §6.3.5: List Notation - '|' as regular atom vs ht_sep
%% - §6.3.6: Curly Bracketed Term - {atom} is valid
%%
%% Without op declaration:
%% - '|' is just an atom (§6.3.1.3)
%% - (|) = atom in parentheses = valid term
%% - [(|)] = list containing atom '|' = valid
%% - {(|)} = curly term with atom '|' = valid
%%
%% This file validates backward compatibility: the fix for issue #3170
%% ONLY affects the case where op(1105,xfy,'|') is declared, and does
%% NOT break normal usage of '|' as an atom.

:- use_module(library(charsio)).

%% NOTE: NO op(1105,xfy,'|') declaration here!

%% Category 1: Simple atom cases
test1 :-
    % (|) as atom
    read_term_from_chars("(|).", T, []),
    T = '|'.

test2 :-
    % Double parentheses
    read_term_from_chars("((|)).", T, []),
    T = '|'.

test3 :-
    % Triple parentheses
    read_term_from_chars("(((|))).", T, []),
    T = '|'.

%% Category 2: Curly brace cases
test4 :-
    % {(|)} - curly with atom
    read_from_chars("{(|)}.", T),
    T = '{}'('|').

test5 :-
    % {((|))} - curly with nested parens
    read_from_chars("{((|))}.", T),
    T = '{}'('|').

test6 :-
    % {a,(|),b} - curly with comma and atom
    read_from_chars("{a,(|),b}.", T),
    T = '{}'((a,('|'),b)).

%% Category 3: List cases
test7 :-
    % [(|)] - list containing atom
    read_term_from_chars("[(|)].", T, []),
    T = ['|'].

test8 :-
    % [a,(|),b] - list with multiple elements
    read_term_from_chars("[a,(|),b].", T, []),
    T = [a,'|',b].

test9 :-
    % [((|))] - list with nested parens
    read_term_from_chars("[((|))].", T, []),
    T = ['|'].

test10 :-
    % [[{(|)}]] - deeply nested
    read_term_from_chars("[[{(|)}]].", T, []),
    T = [['{}'('|')]].

%% Category 4: Function argument cases
test11 :-
    % foo((|)) - function with atom arg
    read_term_from_chars("foo((|)).", T, []),
    T = foo('|').

test12 :-
    % bar(a,(|),b) - multiple args
    read_term_from_chars("bar(a,(|),b).", T, []),
    T = bar(a,'|',b).

test13 :-
    % baz(((|))) - nested parens in arg
    read_term_from_chars("baz(((|))).", T, []),
    T = baz('|').

%% Category 5: Mixed contexts
test14 :-
    % {foo([bar((|))])} - deeply nested mix
    read_term_from_chars("{foo([bar((|))])}.", T, []),
    T = '{}'(foo([bar('|')])).

test15 :-
    % [a,{b,(|),c}] - list with curly
    read_term_from_chars("[a,{b,(|),c}].", T, []),
    T = [a,'{}'((b,('|'),c))].

test16 :-
    % func([{(|)}]) - function with list containing curly
    read_term_from_chars("func([{(|)}]).", T, []),
    T = func(['{}'('|')]).

%% Category 6: Verify distinction from ht_sep
test17 :-
    % [a|b] - uses ht_sep, not affected
    read_term_from_chars("[a|b].", T, []),
    T = [a|b].

test18 :-
    % [(|)] vs [a|b] - different syntax
    read_term_from_chars("[(|)].", T1, []),
    read_term_from_chars("[a|b].", T2, []),
    T1 = ['|'],
    T2 = [a|b],
    T1 \= T2.

test19 :-
    % Can have both in same list
    read_term_from_chars("[x,(|),y|tail].", T, []),
    T = [x,'|',y|tail].

%% Category 7: Operator-like usage (but as atoms)
test20 :-
    % '|' can appear in operator-like positions when it's an atom
    read_term_from_chars("a + (|).", T, []),
    T = +(a,'|').

test21 :-
    % Multiple '|' atoms
    read_term_from_chars("[(|),(|)].", T, []),
    T = ['|','|'].

test22 :-
    % As functor-like usage
    read_term_from_chars("'|'(a,b).", T, []),
    T = '|'(a,b).

%% Run all tests
run :-
    test1, test2, test3, test4, test5, test6, test7, test8, test9, test10,
    test11, test12, test13, test14, test15, test16, test17, test18, test19, test20,
    test21, test22,
    halt.
