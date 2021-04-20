:- module(test_json, [test_json_read/0]).

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
