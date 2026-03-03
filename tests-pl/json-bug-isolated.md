# Segmentation Fault in library(serialization/json) - Bug Report for Scryer Prolog

## Environment

- **Scryer Prolog Version**: Built from source
- **OS**: macOS (Darwin)
- **Date**: 2026-03-03

## Issue Summary

A segmentation fault occurs when using `library(serialization/json)` with `phrase/2` to parse valid JSON strings containing larger hexadecimal strings, or when attempting simple extraction of JSON fields via `atom_chars/2` and `phrase/2`.

## Minimal Reproduction

The following isolated test case triggers the segmentation fault:

```prolog
:- use_module(library(serialization/json)).
:- use_module(library(lists)).

% Helper to parse JSON output
parse_json_output(Output, JsonTerm) :-
    atom_chars(Output, OutputChars),
    phrase(json(JsonTerm), OutputChars).

% Helper to check JSON field value
check_json_field(Output, Field, ExpectedValue) :-
    parse_json_output(Output, json(Obj)),
    atom_string(Field, FieldStr),
    atom_string(ExpectedValue, ExpValStr),
    member(FieldStr=ActualValue, Obj),
    (atom(ActualValue) -> atom_string(ActualValue, ActualStr) ; ActualStr = ActualValue),
    ActualStr = ExpValStr.

% Test that triggers segfault
test_json_segfault :-
    Output = '{"hash":"c24463f5e352da20cb79a43f97436cce57344911e1d0ec0008cbedb5fabcca33"}',
    check_json_field(Output, "hash", "c24463f5e352da20cb79a43f97436cce57344911e1d0ec0008cbedb5fabcca33"),
    write('ok').

:- initialization(test_json_segfault).
```

## Steps to Reproduce

1. Create a file `tests-pl/serialization-json-segfault.pl` with the code above.
2. Run it with the scryer-prolog release binary: 
   `./target/release/scryer-prolog tests-pl/serialization-json-segfault.pl`
3. **Result**: Segmentation fault.

## Expected Behavior

The JSON string `{"hash":"c24463f5e352da20cb79a43f97436cce57344911e1d0ec0008cbedb5fabcca33"}` should be parsed successfully, and the script should output `ok`.

## Workaround

Using simple `sub_atom/5` or `sub_string/5` for string matching avoids the crash, but avoids JSON parsing entirely.

```prolog
check_json_field(Output, Field, ExpectedValue) :-
    atom_string(Output, OutStr),
    atom_string(Field, FieldStr),
    atom_string(ExpectedValue, ExpValStr),
    sub_string(OutStr, _, _, _, FieldStr),
    sub_string(OutStr, _, _, _, ExpValStr).
```

## Possible Causes

1. Potential memory corruption or stack overflow in `library(serialization/json)` when constructing deeply nested terms or long character lists during `json//1` parsing.
2. An issue with `phrase/2` execution on specific sequence lengths in the WAM.
3. String allocation mismanagement during the conversion from `atom_chars` output inside the DCG.

## Request

Please investigate the crash in `library(serialization/json)` related to string parsing. This bug prevents using the standard library for parsing standard API/FFI JSON payloads.
