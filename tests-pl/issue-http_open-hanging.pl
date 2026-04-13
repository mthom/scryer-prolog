% Server
:- use_module(library(process)).
:- use_module(library(iso_ext)).
:- use_module(library(os)).

prolog_path(Prolog) :-
    read(Body),
    term_variables(Body, [Prolog]),
    Body.

server_start([Process,Out]) :-
    prolog_path(Prolog),
    process_create(Prolog,
        ["tests-pl/issue-http_open-hanging_server", "-t", "server"],
        [process(Process), stdout(pipe(Out))]).

server_wait_start([_Process, Out]) :-
    get_char(Out, _C).

server_stop([Process,_Out]) :-
    process_kill(Process).

% Client 
:- use_module(library(charsio)).
:- use_module(library(http/http_open)).

send_request :-
    Options = [
        method('get'),
        status_code(StatusCode),
        request_headers([]),
        headers(_)
    ],
    http_open("http://localhost:8472", _Stream, Options),
    write_term('received response with status code':StatusCode, []), nl.

main :-
    setup_call_cleanup(
        server_start(Server),
        (
            server_wait_start(Server),
            send_request,
            send_request,
            send_request,
            send_request,
            send_request
        ),
        server_stop(Server)
    ).

:- initialization(main).