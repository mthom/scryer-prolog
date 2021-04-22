:- module(test_json, [test_json/0]).

:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(json)).
:- use_module(library(lists)).
:- use_module(library(os)).
:- use_module(library(pio)).
:- use_module(library(time)).

test_path(TestName, TestPath) :-
    getenv("SCRYER_JSON_TESTS_PATH", JsonPath),
    append(JsonPath, TestName, TestPathChars),
    atom_chars(TestPath, TestPathChars).

name_parse(Name, Json) :-
    test_path(Name, Path),
    once(phrase_from_file(json_chars(Json), Path)).

test_json_read :-
    name_parse("pass_null.json", _),
    name_parse("pass_alnum.json", _),
    name_parse("pass_special.json", _),
    name_parse("pass_mandatory_escapes.json", _),
    name_parse("pass_forward_slash.json", _),
    name_parse("pass_hex.json", _),
    name_parse("pass_smallfloat.json", _),
    name_parse("pass_bigfloat.json", _),
    time(name_parse("pass_everything.json", _)).

test_json_minify :-
    test_path("pass_everything.min.json", MinPath),
    open(MinPath, read, RefMin),
    read_line_to_chars(RefMin, RefChars, []),
    close(RefMin),
    name_parse("pass_everything.json", Json),
    time(phrase(json_chars(Json), MinChars)),
    RefChars = MinChars.

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
