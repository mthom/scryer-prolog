:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(Dir),
    ground(Dir).

act(Dir) :-
    getenv("TARGET_PATH", Dir),
	\+ path_canonical(Dir, _CanonicalPath),
	throw(system_error).
act(Dir) :-
    getenv("TARGET_PATH", Dir),
	path_canonical(Dir, _CanonicalPath),
    write(path_canonicalized).

main :-
    path_segments(Path, ["path_canonical_test", "..", "path_canonical_test"]),
    call_cleanup(
       (setenv("TARGET_PATH", Path),
        shell("mkdir path_canonical_test", 0),
        check),
       shell("test -d path_canonical_test && rmdir path_canonical_test || true", 0)
    ).

:- initialization(main).
