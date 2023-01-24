/**
Predicates for handling network sockets, both as a server and as a client.
As a server, you should open a socket an call `socket_server_accept/4` to get a stream for each connection.
As a client, you should just open a socket and you will receive a stream.
In both cases, with a stream, you can use the usual predicates to read and write to the stream.
*/
:- module(sockets, [socket_client_open/3,
                    socket_server_open/2,
                    socket_server_accept/4,
                    socket_server_close/1,
                    current_hostname/1]).

:- use_module(library(error)).

%% socket_client_open(+Addr, -Stream, +Options).
%
% Open a socket to a server, returning a stream. Addr must satisfy `Addr = Address:Port`.
%
% The following options are available:
%
%  * `alias(+Alias)`: Set an alias to the stream
%  * `eof_action(+Action)`: Defined what happens if the end of the stream is reached. Values: `error`, `eof_code` and `reset`.
%  * `reposition(+Boolean)`: Specifies whether repositioning is required for the stream. `false` is the default.
%  * `type(+Type)`: Type can be `text` or `binary`. Defines the type of the stream, if it's optimized for plain text
%    or just binary
%
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
    builtins:parse_stream_options(Options,
                                  [Alias, EOFAction, Reposition, Type],
                                  socket_client_open/3),
    '$socket_client_open'(Address, Port, Stream, Alias, EOFAction, Reposition, Type).

%% socket_server_open(+Addr, -ServerSocket).
%
% Open a server socket, returning a ServerSocket. Use that ServerSocket to accept incoming connections in
% `socket_server_accept/4`. Addr must satisfy `Addr = Address:Port`. Depending on the operating system
% configuration, some ports might be reserved for superusers.
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

%% socket_server_accept(+ServerSocket, -Client, -Stream, +Options).
%
% Given a ServerSocket and a list of Options, accepts a incoming connection, returning data from the Client and
% a Stream to read or write data.
%
% The following options are available:
%
%  * `alias(+Alias)`: Set an alias to the stream
%  * `eof_action(+Action)`: Defined what happens if the end of the stream is reached. Values: `error`, `eof_code` and `reset`.
%  * `reposition(+Boolean)`: Specifies whether repositioning is required for the stream. `false` is the default.
%  * `type(+Type)`: Type can be `text` or `binary`. Defines the type of the stream, if it's optimized for plain text
%    or just binary
% 
socket_server_accept(ServerSocket, Client, Stream, Options) :-
    must_be(var, Client),
    must_be(var, Stream),
    builtins:parse_stream_options(Options,
                                  [Alias, EOFAction, Reposition, Type],
                                  socket_server_accept/4),
    '$socket_server_accept'(ServerSocket, Client, Stream, Alias, EOFAction, Reposition, Type).

%% socket_server_close(+ServerSocket).
%
% Stops listening on that ServerSocket. It's recommended to always close a ServerSocket once it's no longer needed
socket_server_close(ServerSocket) :-
    '$socket_server_close'(ServerSocket).

%% current_hostname(-HostName).
%
% Returns the current hostname of the computer in which Scryer Prolog is executing right now
current_hostname(HostName) :-
    '$current_hostname'(HostName).
