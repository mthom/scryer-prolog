:- use_module(library(sockets)).
:- use_module(library(time)).
:- use_module(library(format)).

test :-
    Addr = '0.0.0.0',
    Port = 5000,
    once(socket_server_open(Addr:Port, Socket)),
    format("Listening at port ~d\n", [Port]),
    socket_server_accept(Socket, _Client, Stream, [type(binary)]),
    format(Stream, "FIRST\r\n", []),
    sleep(20),
    format(Stream, "SECOND\r\n", []),
    close(Stream).