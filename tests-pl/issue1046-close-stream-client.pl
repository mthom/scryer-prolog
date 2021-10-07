:- use_module(library(sockets)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(charsio)).

test :-
    Addr = '0.0.0.0',
    Port = 5000,
    socket_client_open(Addr:Port, Stream, [type(binary)]),
    read_line_to_chars(Stream, Line, []),
    write(Line),
    close(Stream).
