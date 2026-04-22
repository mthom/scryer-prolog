:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetPath),
    ground(TargetPath).

act(TargetPath) :-
    getenv("TARGET_DIRECTORY", TargetPath),
	make_directory_path(TargetPath),
	append(["ls ", TargetPath], ListFilesCmd),
	\+ shell(ListFilesCmd, 0),
	throw(system_error).
act(TargetPath) :-
    getenv("TARGET_DIRECTORY", TargetPath),
	append(["ls ", TargetPath], ListFilesCmd),
	shell(ListFilesCmd, 0),
    write(directory_path_made).

main :-
    call_cleanup(
       (setenv("TARGET_DIRECTORY", "make_directory_test/subdir"),
        check),
       (shell("test -d make_directory_test/subdir && rmdir make_directory_test/subdir || true", 0),
        shell("test -d make_directory_test && rmdir make_directory_test || true", 0))
    ).

:- initialization(main).
