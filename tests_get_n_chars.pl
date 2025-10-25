:- use_module(library(charsio)).
:- use_module(library(process)).
:- use_module(library(format)).
:- use_module(library(lists)).

% Test 1: get_n_chars/4 with timeout=0 should behave exactly like get_n_chars/3
test_timeout_zero_equals_no_timeout :-
    write('Test 1: timeout=0 equals get_n_chars/3'), nl,

    % Create a test file with known content
    atom_chars('/bin/echo', Echo),
    atom_chars('ABCDEFGHIJ', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    % Read with get_n_chars/3
    get_n_chars(Out1, 5, Chars1),

    % Read with get_n_chars/4, timeout=0
    get_n_chars(Out2, 5, Chars2, 0),

    % Should be identical
    (Chars1 = Chars2 ->
        write('  PASS: Both returned same result'), nl
    ;   write('  FAIL: Results differ'), nl,
        format("    get_n_chars/3: ~s~n", [Chars1]),
        format("    get_n_chars/4 timeout=0: ~s~n", [Chars2])
    ),

    close(Out1),
    close(Out2),
    nl.

% Test 2: Variable N with timeout=0 should work like get_n_chars/3
test_variable_n_with_timeout_zero :-
    write('Test 2: Variable N with timeout=0'), nl,

    atom_chars('/bin/echo', Echo),
    atom_chars('Testing', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    % Read all with get_n_chars/3
    get_n_chars(Out1, N1, Chars1),

    % Read all with get_n_chars/4, timeout=0
    get_n_chars(Out2, N2, Chars2, 0),

    % Should be identical
    (N1 = N2, Chars1 = Chars2 ->
        format("  PASS: Both read ~d chars: ~s~n", [N1, Chars1])
    ;   write('  FAIL: Results differ'), nl,
        format("    get_n_chars/3: N=~d, Chars=~s~n", [N1, Chars1]),
        format("    get_n_chars/4: N=~d, Chars=~s~n", [N2, Chars2])
    ),

    close(Out1),
    close(Out2),
    nl.

% Test 3: Negative timeout should also mean no timeout
test_negative_timeout_equals_no_timeout :-
    write('Test 3: Negative timeout equals no timeout'), nl,

    atom_chars('/bin/echo', Echo),
    atom_chars('NegativeTest', Content),
    process_create(Echo, [Content], [stdout(pipe(Out1))]),
    process_create(Echo, [Content], [stdout(pipe(Out2))]),

    get_n_chars(Out1, N1, Chars1),
    get_n_chars(Out2, N2, Chars2, -100),

    (N1 = N2, Chars1 = Chars2 ->
        format("  PASS: Both read ~d chars~n", [N1])
    ;   write('  FAIL: Results differ'), nl
    ),

    close(Out1),
    close(Out2),
    nl.

% Test 4: Positive timeout should timeout on slow output
test_positive_timeout :-
    write('Test 4: Positive timeout stops reading'), nl,

    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; [print(c,end="",flush=True) or time.sleep(1) for c in "ABCDEFGH"]', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    % Read for 2500ms - should get about 2-3 characters
    get_n_chars(Out, N, _Chars, 2500),

    (N >= 2, N =< 3 ->
        format("  PASS: Got ~d chars in 2500ms (expected 2-3)~n", [N])
    ;   format("  FAIL: Got ~d chars, expected 2-3~n", [N])
    ),

    close(Out),
    nl.

% Test 5: infinity atom means no timeout
test_infinity_timeout :-
    write('Test 5: infinity atom means no timeout'), nl,

    atom_chars('/bin/echo', Echo),
    atom_chars('InfinityTest', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    get_n_chars(Out, N, _Chars, infinity),

    (N > 0 ->
        format("  PASS: Read ~d chars with infinity timeout~n", [N])
    ;   write('  FAIL: Read 0 chars'), nl
    ),

    close(Out),
    nl.

% Test 6: Stream reusable after timeout
test_stream_reusable_after_timeout :-
    write('Test 6: Stream remains usable after timeout'), nl,

    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; print("A",end="",flush=True); time.sleep(2); print("B",end="",flush=True)', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    % First read with short timeout - should get 'A'
    get_n_chars(Out, N1, Chars1, 100),

    % Second read with longer timeout - should get 'B'
    get_n_chars(Out, N2, Chars2, 3000),

    ((N1 = 1, Chars1 = "A", N2 = 1, Chars2 = "B") ->
        write('  PASS: Stream worked after timeout'), nl
    ;   write('  FAIL: Unexpected behavior'), nl,
        format("    First read: N=~d, Chars=~s~n", [N1, Chars1]),
        format("    Second read: N=~d, Chars=~s~n", [N2, Chars2])
    ),

    close(Out),
    nl.

% Test 7: Timeout returns partial data, not EOF
test_timeout_not_eof :-
    write('Test 7: Timeout returns partial data, not EOF'), nl,

    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; print("ABC",end="",flush=True); time.sleep(5); print("DEF",end="",flush=True)', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    % Read with timeout - should get immediate output before sleep
    get_n_chars(Out, N1, Chars1, 1000),

    % Try reading again - should not fail and get data after sleep
    get_n_chars(Out, N2, Chars2, 6000),

    ((N1 = 3, Chars1 = "ABC", N2 = 3, Chars2 = "DEF") ->
        write('  PASS: Got partial data, stream not EOF'), nl
    ;   write('  FAIL: Unexpected behavior'), nl,
        format("    First: N=~d, Chars=~s~n", [N1, Chars1]),
        format("    Second: N=~d, Chars=~s~n", [N2, Chars2])
    ),

    close(Out),
    nl.

% Test 8: Multiple reads with timeout=0
test_multiple_reads_timeout_zero :-
    write('Test 8: Multiple reads with timeout=0'), nl,

    atom_chars('/bin/echo', Echo),
    atom_chars('ABCDEFGHIJKLMNOP', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    % Read in chunks
    get_n_chars(Out, 4, Chars1, 0),
    get_n_chars(Out, 4, Chars2, 0),
    get_n_chars(Out, 4, Chars3, 0),

    ((Chars1 = "ABCD", Chars2 = "EFGH", Chars3 = "IJKL") ->
        write('  PASS: Multiple reads work correctly'), nl
    ;   write('  FAIL: Unexpected results'), nl
    ),

    close(Out),
    nl.

% Test 9: Reading more than available with timeout=0
test_read_more_than_available_timeout_zero :-
    write('Test 9: Read more than available with timeout=0'), nl,

    atom_chars('/bin/echo', Echo),
    atom_chars('Short', Content),
    process_create(Echo, [Content], [stdout(pipe(Out))]),

    % Try to read 100 chars from stream with only ~6 chars
    get_n_chars(Out, N, _Chars, 0),

    ((N >= 5, N =< 7) ->
        format("  PASS: Read ~d chars (all available)~n", [N])
    ;   format("  FAIL: Read ~d chars~n", [N])
    ),

    close(Out),
    nl.

% Test 10: Variable N unification with actual count
test_variable_n_unification :-
    write('Test 10: Variable N unifies with actual count'), nl,

    atom_chars('/usr/bin/python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; [print(c,end="",flush=True) or time.sleep(0.5) for c in "ABCD"]', Cmd),
    process_create(Py, [C, Cmd], [stdout(pipe(Out))]),

    % Read for 1300ms - should get about 2-3 chars
    get_n_chars(Out, N, Chars, 1300),

    % Check that N is unified with the actual count
    length(Chars, ActualLength),

    (N = ActualLength ->
        format("  PASS: N unified to ~d (actual count)~n", [N])
    ;   format("  FAIL: N=~d but actual length=~d~n", [N, ActualLength])
    ),

    close(Out),
    nl.

% Run all tests
run_all_tests :-
    write('╔════════════════════════════════════════════════════╗'), nl,
    write('║  get_n_chars/4 Test Suite                         ║'), nl,
    write('╚════════════════════════════════════════════════════╝'), nl, nl,

    test_timeout_zero_equals_no_timeout,
    test_variable_n_with_timeout_zero,
    test_negative_timeout_equals_no_timeout,
    test_positive_timeout,
    test_infinity_timeout,
    test_stream_reusable_after_timeout,
    test_timeout_not_eof,
    test_multiple_reads_timeout_zero,
    test_read_more_than_available_timeout_zero,
    test_variable_n_unification,

    write('╔════════════════════════════════════════════════════╗'), nl,
    write('║  All tests completed!                              ║'), nl,
    write('╚════════════════════════════════════════════════════╝'), nl.

% To run tests: ?- run_all_tests.
