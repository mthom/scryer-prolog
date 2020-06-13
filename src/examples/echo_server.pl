:- module(echo_server, [echo_server/0,
                        echo_server/1]).

:- use_module(library(format)).
:- use_module(library(sockets)).


echo_server :-
    echo_server('127.0.0.1').


echo_server(Addr) :-
    socket_server_open(Addr:Port, ServerSocket),
    format("echo_server: connection opened at ~w:~d~n", [Addr, Port]),
    socket_server_accept(ServerSocket, Client, Stream, [eof_action(eof_code)]),
    format("echo_server: connection accepted from ~a~n", [Client]),
    !,
    echo_loop(Stream),
    socket_server_close(ServerSocket).


echo_loop(Stream) :-
    read_term(Stream, Term, []),
    (  Term == end_of_file ->
       true
    ;
       format("received: ~w~n", [Term]),
       !,
       echo_loop(Stream)
    ).

