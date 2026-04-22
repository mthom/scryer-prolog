% Server
:- use_module(library(process)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(time)).

prolog_path(Prolog) :-
    read(Body),
    term_variables(Body, [Prolog]),
    Body.

main :-
    prolog_path(Prolog),
    append(Prolog, " -g '\
        use_module(library(os)), \
        pid(PID), \
        write(PID), nl, \
        asserta((f :- f)), \
        catch(f, Err, (write(Err),nl)), \
        write(done), nl, \
        halt.'", CMD),
    process_create("script", ["-q", "-c", CMD, "/dev/null"], [stdout(pipe(O))]),
    get_line_to_chars(O, PID0, ""),
    append(PID, "\r\n", PID0),
    process_create("kill", ["-s", "INT", PID], []),
    sleep(5),
    % second kill should fail because process should exit after one kill
    process_create("kill", ["-s", "INT", PID], [stderr(null), process(PK)]),
    process_wait(PK, Status),
    status_report(Status, PID), nl.

status_report(exit(1), _PID) :- write(ok).
status_report(exit(0), PID) :-
    write(not_dead),
    % kill by force to exit cleanly
    process_create("kill", ["-9", PID], []).

:- initialization(main).