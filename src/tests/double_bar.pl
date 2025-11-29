:- module(double_bar_tests, []).

:- use_module(test_framework).
:- discontiguous(test/2).

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

test("double bar chars mode with numeric tail", (
    L = "abc"||123,
    L = [a,b,c|123]
)).
% Tests for double bar with double_quotes set to codes
% These must be in a separate section with the flag set at parse time

:- set_prolog_flag(double_quotes, codes).

test("double bar with codes mode basic", (
    L = "abc"||K,
    L = [97,98,99|K]
)).

test("double bar with codes mode empty string", (
    L = ""||K,
    L == K
)).

test("double bar with codes mode chain", (
    L = "a"||"b"||"c",
    L = [97,98,99]
)).

test("double bar with codes mode unification", (
    "abc"||X = [97,98,99,100,101],
    X = [100,101]
)).

test("double bar with codes mode mixed empty and non-empty", (
    L = ""||"hello"||""||world,
    L = [104,101,108,108,111|world]
)).

test("double bar with codes mode with atom tail", (
    L = "abc"||xyz,
    L = [97,98,99|xyz]
)).


test("double bar with codes mode multi-line with line comment", (
    L = "a"|| % multiple lines
        "b"||
        "c",
    L = [97,98,99]
)).

test("double bar with codes mode multi-line with block comment", (
    L = "a"||"b"|| /* with comments */ "c",
    L = [97,98,99]
)).

test("double bar with codes mode multi-line complex", (
    L = "a"|| % first line
        "b"|| /* second */
        "c",
    L = [97,98,99]
)).

test("double bar with codes mode spaced syntax", (
    L = "abc" | | K,
    L = [97,98,99|K]
)).

test("double bar with codes mode spaced chain", (
    L = "a" | | "b" | | "c",
    L = [97,98,99]
)).

test("double bar with codes mode block comment between bars", (
    L = "a" | /* comment */ | "b",
    L = [97,98]
)).

test("double bar with codes mode line comment between bars", (
    L = "a" | % line comment
        | "b",
    L = [97,98]
)).

test("double bar with codes mode block comment in spaced bar with tail", (
    L = "abc" |/* comment */| K,
    L = [97,98,99|K]
)).

test("double bar with codes mode comment before double bar", (
    L = "a" /* before */ || "b",
    L = [97,98]
)).

test("double bar with codes mode comment after double bar", (
    L = "a" || /* after */ "b",
    L = [97,98]
)).

test("double bar with codes mode comment before spaced bars", (
    L = "a" /* before */ | | "b",
    L = [97,98]
)).

test("double bar with codes mode comment after spaced bars", (
    L = "a" | | /* after */ "b",
    L = [97,98]
)).

test("double bar with codes mode multiple comments around bars", (
    L = "a" /* before */ | /* between */ | /* after */ "b",
    L = [97,98]
)).

test("double bar with codes mode empty at start of chain", (
    L = ""||"abc"||"de",
    L = [97,98,99,100,101]
)).

test("double bar with codes mode empty in middle of chain", (
    L = "ab"||""||"cd",
    L = [97,98,99,100]
)).

test("double bar with codes mode empty at end of chain", (
    L = "abc"||"de"||"",
    L = [97,98,99,100,101]
)).

test("double bar with codes mode single character strings", (
    L = "x"||"y"||"z",
    L = [120,121,122]
)).

test("double bar with codes mode unicode characters", (
    L = "α"||"β"||tail,
    L = [945,946|tail]
)).

test("double bar with codes mode longer strings", (
    L = "hello"||"world",
    L = [104,101,108,108,111,119,111,114,108,100]
)).

test("double bar with codes mode nested unification", (
    "a"||"b"||X = [97,98,99],
    X = [99]
)).


test("double bar with codes mode with numeric tail", (
    L = "abc"||123,
    L = [97,98,99|123]
)).


:- set_prolog_flag(double_quotes, chars).
