:- module(double_bar_tests, []).

:- use_module(test_framework).

% Tests for the double bar || operator
% Spec: https://www.complang.tuwien.ac.at/ulrich/iso-prolog/double_bar
%
% Abstract syntax (from spec):
%   term = double quoted list, bar, bar, term ;
%   Priority: 0, 0, 0
%
% The LEFT side must be a double quoted list.
% The RIGHT side (tail) can be any term at priority 0, including:
%   - Variables: "abc"||K
%   - Strings (chained): "a"||"b"||"c"
%   - Atoms: "hello"||world (valid per abstract syntax)
%   - Numbers: "abc"||123
%
% WG17 2025-06-02: Accepts option 1 (only after double quotes)

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

% Atom tail: valid per abstract syntax "term = dql, bar, bar, term"
% The right-hand term can be any term at priority 0, including atoms.
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

test("spaced double bar syntax", (
    L = "abc" | | K,
    L = [a,b,c|K]
)).

test("spaced double bar chain", (
    L = "a" | | "b" | | "c",
    L = [a,b,c]
)).

test("block comment between bars", (
    L = "a" | /* comment */ | "b",
    L = [a,b]
)).

test("line comment between bars", (
    L = "a" | % line comment
        | "b",
    L = [a,b]
)).

test("block comment in spaced bar with tail", (
    L = "abc" |/* comment */| K,
    L = [a,b,c|K]
)).

test("comment before double bar", (
    L = "a" /* before */ || "b",
    L = [a,b]
)).

test("comment after double bar", (
    L = "a" || /* after */ "b",
    L = [a,b]
)).

test("comment before spaced bars", (
    L = "a" /* before */ | | "b",
    L = [a,b]
)).

test("comment after spaced bars", (
    L = "a" | | /* after */ "b",
    L = [a,b]
)).

test("multiple comments around bars", (
    L = "a" /* before */ | /* between */ | /* after */ "b",
    L = [a,b]
)).

% Note: These invalid cases are tested at parse time, not runtime
% They cannot be included as test/2 predicates because they fail at read_term
% The parser correctly rejects them with syntax_error(incomplete_reduction)
%
% Invalid cases (verified separately):
% - [1,2,3]||K => syntax_error
% - [_]||Rs => syntax_error
% - [a,b,c]||S => syntax_error
% - K||[] => syntax_error
% - ("a")||[] => syntax_error



test("double bar chars mode empty at start of chain", (
    L = ""||"abc"||"de",
    L = [a,b,c,d,e]
)).

test("double bar chars mode empty in middle of chain", (
    L = "ab"||""||"cd",
    L = [a,b,c,d]
)).

test("double bar chars mode empty at end of chain", (
    L = "abc"||"de"||"",
    L = [a,b,c,d,e]
)).

test("double bar chars mode single character strings", (
    L = "x"||"y"||"z",
    L = [x,y,z]
)).

test("double bar chars mode unicode characters", (
    L = "α"||"β"||tail,
    L = [α,β|tail]
)).

test("double bar chars mode longer strings", (
    L = "hello"||"world",
    L = [h,e,l,l,o,w,o,r,l,d]
)).

test("double bar chars mode nested unification", (
    "a"||"b"||X = [a,b,c],
    X = [c]
)).

% Numeric tail: valid per abstract syntax (right-hand term can be any term)
test("double bar chars mode with numeric tail", (
    L = "abc"||123,
    L = [a,b,c|123]
)).
