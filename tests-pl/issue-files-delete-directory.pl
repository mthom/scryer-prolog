:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetDir),
    ground(TargetDir).

act(TargetDir) :-
    getenv("TARGET_DIRECTORY", TargetDir),
	delete_directory(TargetDir),
	append(["ls ", TargetDir], ListFilesCmd),
	shell(ListFilesCmd, 0),
	throw(system_error).
act(TargetDir) :-
    getenv("TARGET_DIRECTORY", TargetDir),
	append(["ls ", TargetDir], ListFilesCmd),
	\+ shell(ListFilesCmd, 0),
    write(directory_deleted).

main :-
    call_cleanup(
       (setenv("TARGET_DIRECTORY", "delete_directory_test"),
        shell("mkdir delete_directory_test", 0),
        check),
        shell("test -d delete_directory_test && rmdir delete_directory_test || true", 0)
    ).

:- initialization(main).
