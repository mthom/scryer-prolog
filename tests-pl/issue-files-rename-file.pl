:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check :-
    act(Source, Destination),
    ground(Source),
    ground(Destination).

act(Source, Destination) :-
    getenv("SOURCE", Source),
    getenv("DESTINATION", Destination),
    \+ rename_file(Source, Destination),
    throw(system_error).
act(Source, Destination) :-
    getenv("SOURCE", Source),
    getenv("DESTINATION", Destination),
    append(["ls ", Destination], Cmd),
    shell(Cmd, 0),
    write(file_renamed).

main :-
    call_cleanup(
       (setenv("SOURCE", "rename_file_test"),
        setenv("DESTINATION", "rename_file_test_renamed"),
        shell("touch rename_file_test", 0),
        check),
        shell("rm -f rename_file_test_renamed || rm -f rename_file_test", 0)
    ).

:- initialization(main).
