:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(TargetDirectory, Files),
    ground(TargetDirectory),
    length(Files, N),
    write(N).

act(TargetDirectory, Files) :-
    getenv("TARGET_DIRECTORY", TargetDirectory),
    directory_files(TargetDirectory, Files).

main :-
    path_segments(Path, ["directory_files_test_parent", "directory_files_test_file"]),
    call_cleanup(
       (setenv("TARGET_DIRECTORY", "directory_files_test_parent"),
        shell("test -d directory_files_test_parent || mkdir directory_files_test_parent", 0),
        append(["test -e ", Path, " || touch ", Path], Cmd),
        shell(Cmd, 0),
        check),
       (append(["rm -f ", Path, " || true"], Cmd1),
        shell(Cmd1, 0),
        shell("rmdir directory_files_test_parent || true", 0),
        shell("ls directory_files_test_parent", 1))
    ).

:- initialization(main).
