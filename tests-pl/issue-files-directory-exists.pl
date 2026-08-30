:- use_module(library(files)).
:- use_module(library(os), [setenv/2, getenv/2]).

check :-
    act(TargetDir),
    ground(TargetDir).

act(TargetDir) :-
    getenv("TARGET_DIRECTORY", TargetDir),
	\+ directory_exists(TargetDir),
	throw(existence_error(directory,TargetDir)).
act(TargetDir) :-
    getenv("TARGET_DIRECTORY", TargetDir),
    directory_exists(TargetDir).

main :-
	setenv("TARGET_DIRECTORY", "."),
	check.

:- initialization(main).
