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

% Tests for number_chars/2 with different number bases
test("number_chars with hex", (
    number_chars(N, "0xa"),
    N =:= 10
)).

test("number_chars with hex and separator", (
    number_chars(N, "0xDE_AD"),
    N =:= 57005
)).

test("number_chars with octal", (
    number_chars(N, "0o76"),
    N =:= 62
)).

test("number_chars with octal and separator", (
    number_chars(N, "0o7_6"),
    N =:= 62
)).

test("number_chars with binary", (
    number_chars(N, "0b1011"),
    N =:= 11
)).

test("number_chars with binary and separator", (
    number_chars(N, "0b10_11"),
    N =:= 11
)).

test("number_chars with decimal separator", (
    number_chars(N, "1_000"),
    N =:= 1000
)).

% Option 9: Reject digit separators in float (before decimal point)
test("number_chars rejects float with separator before decimal", (
    catch(
        (number_chars(_, "1_0.0"), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

test("number_chars rejects float separator via atom_chars", (
    catch(
        (atom_chars('1_0.0', Cs), number_chars(_, Cs), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

test("number_chars rejects float separator via char list", (
    % Test with explicit character list to ensure syntax_error, not type_error
    catch(
        (number_chars(_, ['1','_','0','.','0']), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

% Reject trailing underscore with layout
test("number_chars rejects trailing underscore with layout", (
    catch(
        (number_chars(_, "0_ "), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

% Reject trailing underscore without layout
test("number_chars rejects trailing underscore decimal", (
    catch(
        (number_chars(_, "123_"), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

test("number_chars rejects trailing underscore hex", (
    catch(
        (number_chars(_, "0xFF_"), fail),
        error(syntax_error(unexpected_end_of_file), _),
        true
    )
)).

test("number_chars rejects trailing underscore octal", (
    catch(
        (number_chars(_, "0o77_"), fail),
        error(syntax_error(unexpected_end_of_file), _),
        true
    )
)).

test("number_chars rejects trailing underscore binary", (
    catch(
        (number_chars(_, "0b11_"), fail),
        error(syntax_error(unexpected_end_of_file), _),
        true
    )
)).

% Option 2: Double underscores are rejected (undecided in spec)
test("number_chars rejects double underscore", (
    catch(
        (number_chars(_, "1__000"), fail),
        error(syntax_error(cannot_parse_big_int), _),
        true
    )
)).

% Option 10: Reject digit separators in float (after decimal point)
test("number_chars rejects float with separator after decimal", (
    catch(
        (number_chars(_, "11.2_5"), fail),
        error(syntax_error(unexpected_char), _),
        true
    )
)).

% Option 11: Reject digit separators in float exponent
test("number_chars rejects float with separator in exponent", (
    catch(
        (number_chars(_, "1.0e1_0"), fail),
        error(syntax_error(unexpected_char), _),
        true
    )
)).
