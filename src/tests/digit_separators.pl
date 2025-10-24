:- module(digit_separators_tests, []).
:- use_module(test_framework).

test("decimal with single underscore", (
    X = 1_000,
    X =:= 1000
)).

test("decimal with multiple underscores", (
    X = 1_000_000,
    X =:= 1000000
)).

test("decimal with underscore and whitespace", (
    X = 123_ 456,
    X =:= 123456
)).

test("decimal with underscore and comment", (
    X = 123_ /* comment */ 456,
    X =:= 123456
)).

test("hexadecimal with single underscore", (
    X = 0xDE_AD,
    X =:= 0xDEAD
)).

test("hexadecimal with multiple underscores", (
    X = 0x1_2_3_4,
    X =:= 0x1234
)).

test("hexadecimal with underscore and whitespace", (
    X = 0xFF_ 00,
    X =:= 0xFF00
)).

test("hexadecimal with underscore and comment", (
    X = 0xDE_ /* test */ AD,
    X =:= 0xDEAD
)).

test("octal with single underscore", (
    X = 0o7_6,
    X =:= 0o76
)).

test("octal with multiple underscores", (
    X = 0o1_2_3,
    X =:= 0o123
)).

test("octal with underscore and whitespace", (
    X = 0o77_ 00,
    X =:= 0o7700
)).

test("octal with underscore and comment", (
    X = 0o1_ /* octal */ 23,
    X =:= 0o123
)).

test("binary with single underscore", (
    X = 0b10_11,
    X =:= 0b1011
)).

test("binary with multiple underscores", (
    X = 0b1_0_1_0,
    X =:= 0b1010
)).

test("binary with underscore and whitespace", (
    X = 0b1111_ 0000,
    X =:= 0b11110000
)).

test("binary with underscore and comment", (
    X = 0b10_ /* binary */ 11,
    X =:= 0b1011
)).

test("large decimal number with separators", (
    X = 999_999_999,
    X =:= 999999999
)).

test("hexadecimal case insensitive", (
    X1 = 0xAB_CD,
    X2 = 0xab_cd,
    X1 =:= X2
)).
