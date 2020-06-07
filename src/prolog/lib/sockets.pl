
:- module(sockets, [socket_client_open/3,
                    socket_server_open/2,
                    socket_server_accept/4,
                    socket_server_close/1,
                    current_hostname/1]).

:- use_module(library(error)).
:- use_module(library(lists)).

parse_socket_options_(tls(TLS), tls-TLS) :-
    must_be(boolean, TLS), !.
parse_socket_options_(Option, OptionPair) :-
    builtins:parse_stream_options_(Option, OptionPair).

parse_socket_options(Options, OptionValues, Stub) :-
    DefaultOptions = [alias-[], eof_action-eof_code, reposition-false, tls-false, type-text],
    builtins:parse_options_list(Options, parse_socket_options_, DefaultOptions, OptionValues, Stub).

socket_client_open(Addr, Stream, Options) :-
    (  var(Addr) ->
       throw(error(instantiation_error, socket_client_open/3))
    ;
       true
    ),
    must_be(var, Stream),
    must_be(list, Options),
    (  Addr = Address:Port,
       atom(Address),
       ( atom(Port) ; integer(Port) ) ->
       true
    ;
       throw(error(type_error(socket_address, Addr), socket_client_open/3))
    ),
    parse_socket_options(Options,
                         [Alias, EOFAction, Reposition, TLS, Type],
                         socket_client_open/3),
    '$socket_client_open'(Address, Port, Stream, Alias, EOFAction, Reposition, Type, TLS).


socket_server_open(Addr, ServerSocket) :-
    must_be(var, ServerSocket),
    (  ( integer(Addr) ; var(Addr) ) ->
       '$socket_server_open'([], Addr, ServerSocket)
    ;
       Addr = Address:Port,
       must_be(atom, Address),
       can_be(integer, Port),
       '$socket_server_open'(Address, Port, ServerSocket)
    ).


socket_server_accept(ServerSocket, Client, Stream, Options) :-
    must_be(var, Client),
    must_be(var, Stream),
    builtins:parse_stream_options(Options,
                                  [Alias, EOFAction, Reposition, Type],
                                  socket_server_accept/4),
    '$socket_server_accept'(ServerSocket, Client, Stream, Alias, EOFAction, Reposition, Type).


socket_server_close(ServerSocket) :-
    '$socket_server_close'(ServerSocket).


current_hostname(HostName) :-
    '$current_hostname'(HostName).
