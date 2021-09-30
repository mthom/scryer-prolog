:- use_module(library(sockets)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(charsio)).

test :-
    Addr = '0.0.0.0',
    Port = 5000,
    socket_client_open(Addr:Port, Stream, [type(binary)]),
    read_line(Stream, Line),
    write(Line),
    close(Stream).


read_line(Stream, Line) :-
    get_byte(Stream, Char),
    ( Char = -1 ->
        Line = []
    ; Char = 13 ->
        read_line(Stream, Line)
    ; Char = 10 ->
        Line = []
    ;   (read_line(Stream, Line0), Line = [Char|Line0])
    ).

read_message(Stream, [Cs|Message]) :-
    read_line(Stream, Bs),
    chars_utf8bytes(Cs, Bs),
    ( Cs = "." ->
        Message = []
    ;   read_message(Stream, Message)
    ).
