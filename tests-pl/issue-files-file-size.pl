:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetFile, Size),
    ground(TargetFile),
    integer(Size).

act(TargetFile, Size) :-
    getenv("TARGET_FILE", TargetFile),
	file_size(TargetFile, Size).

main :-
    call_cleanup(
       (setenv("TARGET_FILE", "file_size_test"),
        shell("echo '1' > file_size_test", 0),
        check),
        shell("rm -f file_size_test", 0)
    ).

:- initialization(main).
