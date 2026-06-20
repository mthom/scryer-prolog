:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetFile),
    ground(TargetFile).

act(TargetFile) :-
    getenv("TARGET_FILE", TargetFile),
	delete_file(TargetFile),
	append(["ls ", TargetFile], ListFilesCmd),
	shell(ListFilesCmd, 0),
	throw(system_error).
act(TargetFile) :-
    getenv("TARGET_FILE", TargetFile),
	append(["ls ", TargetFile], ListFilesCmd),
	\+ shell(ListFilesCmd, 0),
    write(file_deleted).

main :-
    call_cleanup(
       (setenv("TARGET_FILE", "delete_file_test"),
        shell("touch delete_file_test", 0),
        check),
        shell("test -e delete_file_test && rm delete_file_test || true", 0)
    ).

:- initialization(main).
