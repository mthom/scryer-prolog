:- module(double_bar_tests, []).

:- use_module(test_framework).

% Tests for the double bar || operator
% Based on: https://www.complang.tuwien.ac.at/ulrich/iso-prolog/double_bar

test("basic double bar with variable tail", (
    L = "abc"||K,
    L = [a,b,c|K]
)).

test("double bar chain", (
    L = "a"||"b"||"c",
    L = [a,b,c]
)).

test("empty string double bar unifies with tail", (
    L = ""||K,
    L == K
)).

test("double bar with atom tail", (
    L = "hello"||world,
    L = [h,e,l,l,o|world]
)).

test("unification with double bar", (
    "abc"||X = [a,b,c,d,e],
    X = [d,e]
)).

test("empty string unification", (
    ""||Y = hello,
    Y == hello
)).

test("multiple chained empty strings", (
    L = ""||""||""||X,
    L == X
)).

test("mixed empty and non-empty strings", (
    L = ""||"hello"||""||world,
    L = [h,e,l,l,o|world]
)).

test("multi-line double bar with line comment", (
    L = "a"|| % multiple lines
        "b"||
        "c",
    L = [a,b,c]
)).

test("multi-line double bar with block comment", (
    L = "a"||"b"|| /* with comments */ "c",
    L = [a,b,c]
)).

test("multi-line double bar complex", (
    L = "a"|| % first line
        "b"|| /* second */
        "c",
    L = [a,b,c]
)).

% Note: These invalid cases are tested at parse time, not runtime
% They cannot be included as test/2 predicates because they fail at read_term
% The parser correctly rejects them with syntax_error(incomplete_reduction)
%
% Invalid cases (verified separately):
% - [1,2,3]||K => syntax_error
% - [_]||Rs => syntax_error
% - K||[] => syntax_error
% - ("a")||[] => syntax_error
