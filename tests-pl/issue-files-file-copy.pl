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
	append("ls ", Source, Cmd),
	shell(Cmd, 0),
	file_copy(Source, Destination),
	append("ls ", Destination, Cmd),
	\+ shell(Cmd, 0),
	throw(existence_error(directory,Destination)).
act(Source, Destination) :-
    getenv("SOURCE", Source),
    getenv("DESTINATION", Destination),
	append("ls ", Destination, Cmd),
	shell(Cmd, 0),
    write(file_copied).

main :-
    call_cleanup(
       (setenv("SOURCE", "file_copy_test_source"),
        setenv("DESTINATION", "file_copy_test_destination"),
        shell("touch file_copy_test_source", 0),
        check),
        shell("rm -f file_copy_test_source file_copy_test_destination", 0)
    ).

:- initialization(main).
