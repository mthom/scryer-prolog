:- module(incomplete_utf8_tests, []).
:- use_module(test_framework).
:- use_module(library(charsio)).
:- use_module(library(iso_ext)).
:- use_module(library(process)).
:- use_module(library(format)).

test("get_char/2 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9cAB\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_char(Out, C1),
            C1 == '💜'
        ),
        close(Out)
    )
)).

test("peek_char/2 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9cAB\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            peek_char(Out, C1),
            C1 == '💜',
            get_char(Out, C2),
            C2 == '💜'
        ),
        close(Out)
    )
)).

test("get_code/2 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9cAB\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_code(Out, Code),
            Code =:= 128156
        ),
        close(Out)
    )
)).

test("peek_code/2 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9cAB\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            peek_code(Out, Code1),
            Code1 =:= 128156,
            get_code(Out, Code2),
            Code2 =:= 128156
        ),
        close(Out)
    )
)).

test("get_n_chars/3 (no timeout) after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9cAB\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_n_chars(Out, 2, Chars2),
            Chars2 == "💜A"
        ),
        close(Out)
    )
)).

test("read_term/3 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9c foo(bar).\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_char(Out, Emoji),
            Emoji == '💜',
            read_term(Out, Term, []),
            Term == foo(bar)
        ),
        close(Out)
    )
)).

test("get_line_to_chars/3 after get_n_chars/4 timeout mid-char", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9ctest\\n\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_line_to_chars(Out, Line, []),
            Line == "💜test\n"
        ),
        close(Out)
    )
)).

test("multiple sequential reads after timeout", (
    atom_chars('python3', Py),
    atom_chars('-c', C),
    atom_chars('import sys,time; sys.stdout.buffer.write(b\"\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x92\\x9c\\xf0\"); sys.stdout.buffer.flush(); time.sleep(0.5); sys.stdout.buffer.write(b\"\\x9f\\x98\\x8a\"); sys.stdout.buffer.flush()', Cmd),
    setup_call_cleanup(
        process_create(Py, [C, Cmd], [stdout(pipe(Out))]),
        (
            get_n_chars(Out, _, Chars1, 100),
            Chars1 == [],
            get_char(Out, C1),
            C1 == '💜',
            get_n_chars(Out, _, Chars2, 100),
            Chars2 == [],
            get_char(Out, C2),
            C2 == '😊'
        ),
        close(Out)
    )
)).
