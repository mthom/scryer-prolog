:- module(get_n_chars_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).
:- use_module(library(process)).
:- use_module(library(format)).
:- use_module(library(lists)).

% Test 1: timeout=0 should behave exactly like get_n_chars/3
test("timeout=0 equals get_n_chars/3", (
    atom_chars('/bin/echo', Echo),
    atom_chars('ABCDEFGHIJ', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    get_n_chars(Out1, 5, Chars1),
    get_n_chars(Out2, 5, Chars2, 0),

    Chars1 = Chars2,
    close(Out1),
    close(Out2)
)).

% Test 2: Variable N with timeout=0
test("variable N with timeout=0", (
    atom_chars('/bin/echo', Echo),
    atom_chars('Testing', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    get_n_chars(Out1, N1, Chars1),
    get_n_chars(Out2, N2, Chars2, 0),

    N1 = N2,
    Chars1 = Chars2,
    N1 = 8,
    Chars1 = "Testing\n",
    close(Out1),
    close(Out2)
)).

% Test 3: Negative timeout should also mean no timeout
test("negative timeout equals no timeout", (
    atom_chars('/bin/echo', Echo),
    atom_chars('NegativeTest', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    get_n_chars(Out1, N1, Chars1),
    get_n_chars(Out2, N2, Chars2, -100),

    N1 = N2,
    Chars1 = Chars2,
    close(Out1),
    close(Out2)
)).

% Test 4: Positive timeout should timeout on slow output
test("positive timeout stops reading", (
    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; [print(c,end="",flush=True) or time.sleep(1) for c in "ABCDEFGH"]', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    get_n_chars(Out, N, _Chars, 2500),

    N >= 2,
    N =< 3,
    close(Out)
)).

% Test 5: infinity atom means no timeout
test("infinity atom means no timeout", (
    atom_chars('/bin/echo', Echo),
    atom_chars('InfinityTest', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    get_n_chars(Out, N, _Chars, infinity),

    N > 0,
    close(Out)
)).

% Test 6: Stream remains usable after timeout
test("stream usable after timeout", (
    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; print("A",end="",flush=True); time.sleep(2); print("B",end="",flush=True)', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    get_n_chars(Out, N1, Chars1, 100),
    get_n_chars(Out, N2, Chars2, 3000),

    N1 = 1,
    Chars1 = "A",
    N2 = 1,
    Chars2 = "B",
    close(Out)
)).

% Test 7: Timeout returns partial data, not EOF
test("timeout returns partial data not EOF", (
    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; print("ABC",end="",flush=True); time.sleep(5); print("DEF",end="",flush=True)', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    get_n_chars(Out, N1, Chars1, 1000),
    get_n_chars(Out, N2, Chars2, 6000),

    N1 = 3,
    Chars1 = "ABC",
    N2 = 3,
    Chars2 = "DEF",
    close(Out)
)).

% Test 8: Multiple reads with timeout=0
test("multiple reads with timeout=0", (
    atom_chars('/bin/echo', Echo),
    atom_chars('ABCDEFGHIJKLMNOP', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    get_n_chars(Out, 4, Chars1, 0),
    get_n_chars(Out, 4, Chars2, 0),
    get_n_chars(Out, 4, Chars3, 0),

    Chars1 = "ABCD",
    Chars2 = "EFGH",
    Chars3 = "IJKL",
    close(Out)
)).

% Test 9: Reading more than available with timeout=0
test("read more than available with timeout=0", (
    atom_chars('/bin/echo', Echo),
    atom_chars('Short', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    get_n_chars(Out, N, _Chars, 0),

    N >= 5,
    N =< 7,
    close(Out)
)).

% Test 10: Variable N unifies with actual character count
test("variable N unifies with actual count", (
    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; [print(c,end="",flush=True) or time.sleep(0.5) for c in "ABCD"]', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    get_n_chars(Out, N, Chars, 1300),
    length(Chars, ActualLength),

    N = ActualLength,
    close(Out)
)).
