:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetFile),
    ground(TargetFile).

act(TargetFile) :-
    getenv("TARGET_FILE", TargetFile),
    \+ file_exists(TargetFile),
	throw(existence_error(file,TargetFile)).
act(TargetFile) :-
    getenv("TARGET_FILE", TargetFile),
    file_exists(TargetFile).

main :-
    call_cleanup(
       (setenv("TARGET_FILE", "file_exists_test"),
        shell("touch file_exists_test", 0),
        check),
        shell("rm -f file_exists_test", 0)
    ).

:- initialization(main).
