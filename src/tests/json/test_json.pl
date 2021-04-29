:- module(test_json, [test_json/0]).

:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os)).
:- use_module(library(pio)).
:- use_module(library(serialization/json)).
:- use_module(library(time)).

test_path(TestName, TestPath) :-
    getenv("SCRYER_JSON_TESTS_PATH", JsonPath),
    append(JsonPath, TestName, TestPathChars),
    atom_chars(TestPath, TestPathChars).

name_parse(Name, Json) :-
    test_path(Name, Path),
    once(phrase_from_file(json_chars(Json), Path)).

test_json_read :-
    name_parse("pass_null.json", null),
    name_parse("pass_alnum.json", string("ABCDEFGHIJKLMNOPQRSTUVWYZabcdefghijklmnopqrstuvwyz0123456789")),
    name_parse("pass_special.json", string("`1~!@#$%^&*()_+-={':[,]}|;.</>?")),
    name_parse("pass_mandatory_escapes.json", string(" \" \\ \b\f\n\r\t ")),
    name_parse("pass_forward_slash.json", string("/ & /")),
    name_parse("pass_hex.json", string("ģ\x4567\\x89ab\\xcdef\\xabcd\\xef4a\")),
    name_parse("pass_smallfloat.json", number(0.000000000000123456789)),
    name_parse("pass_bigfloat.json", number(12345678900000000000000000000000000.0)),
    time(name_parse("pass_everything.json", _)).

minify_sample_json :-
    name_parse("pass_everything.json", Json),
    time(once(phrase(json_chars(Json), MinChars))),
    test_path("pass_everything.min.json", MinPath),
    setup_call_cleanup(
        open(MinPath, write, Stream),
        format(Stream, "~s~n", [MinChars]),
        close(Stream)
    ).

test_json_minify :-
    test_path("pass_everything.min.json", MinPath),
    once(phrase_from_file(seq(RefChars), MinPath)),
    name_parse("pass_everything.json", Json),
    time(once(phrase(json_chars(Json), MinChars))),
    append(MinChars, "\n", MinFileChars),
    RefChars = MinFileChars.

test_json_int_float :-
    once(phrase(json_chars(number(ZeroInt)), "0")),
    integer(ZeroInt),
    once(phrase(json_chars(number(ZeroFloat)), "0.0")),
    \+ integer(ZeroFloat),
    once(phrase(json_chars(number(BigInt)), "32E5")),
    integer(BigInt),
    once(phrase(json_chars(number(BigFloat)), "32.2E5")),
    \+ integer(BigFloat),
    once(phrase(json_chars(number(SmallFloat)), "32E-5")),
    \+ integer(SmallFloat).

test_json :-
    test_json_read,
    test_json_minify,
    test_json_int_float.
