:- use_module(library(files)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(os), [setenv/2, getenv/2, shell/2]).

check(Time) :-
    act(TargetFile, Time),
    ground(TargetFile),
    ground(Time).

act(TargetFile, Time) :-
    getenv("TARGET_FILE", TargetFile),
    (   file_access_time(TargetFile, Time)
    ;   file_creation_time(TargetFile, Time)
    ;   file_modification_time(TargetFile, Time) ).

main :-
    call_cleanup(
       (setenv("TARGET_FILE", "file_time_test"),
        shell("touch file_time_test", 0),
        findall(T, check(T), Ts),
        length(Ts, 3)),
        shell("rm -f file_time_test", 0)
    ).

:- initialization(main).
