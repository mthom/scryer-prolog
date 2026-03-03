:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(serialization/json)).
:- use_module(library(lists)).

% Helper to parse JSON output
parse_json_output(Output, JsonTerm) :-
    atom_chars(Output, OutputChars),
    phrase(json_chars(JsonTerm), OutputChars).

% Test that triggers segfault
run :-
    Output = '{"hash":"c24463f5e352da20cb79a43f97436cce57344911e1d0ec0008cbedb5fabcca33"}',
    parse_json_output(Output, pairs(Obj)),
    FieldStr = "hash",
    ExpValStr = "c24463f5e352da20cb79a43f97436cce57344911e1d0ec0008cbedb5fabcca33",
    member(string(FieldStr)-string(ActualValue), Obj),
    (ActualValue = ExpValStr -> write('ok') ; write('failed_value_match')).

:- initialization(run).
