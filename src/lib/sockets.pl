
:- module(sockets, [socket_client_open/3,
                    socket_server_open/2,
                    socket_server_accept/4,
                    socket_server_close/1,
                    tls_server_context/2,       % tls_server_context(-Context, +Options)
                    tls_server_negotiate/3,     % tls_server_negotiate(+Context, +Stream0, -Stream)
                    current_hostname/1]).

:- use_module(library(error)).
:- use_module(library(lists)).

% a client can negotiate a TLS connection by specifying the option
% tls(true) in socket_client_open/3

parse_socket_options_(tls(TLS), tls-TLS) :-
    must_be(boolean, TLS), !.
parse_socket_options_(Option, OptionPair) :-
    builtins:parse_stream_options_(Option, OptionPair).

parse_socket_options(Options, OptionValues, Stub) :-
    DefaultOptions = [alias-[], eof_action-eof_code, reposition-false, tls-false, type-text],
    builtins:parse_options_list(Options, sockets:parse_socket_options_, DefaultOptions, OptionValues, Stub).

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

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   TLS Servers
   ===========

   Use tls_server_context/2 to create a TLS context, for example with:

   tls_server_context(Context, [pkcs12(Chars)])

   where Chars is a list of characters with the contents of a
   DER-formatted PKCS #12 archive. The option password(Ps) can be used
   to specify the password Ps (also a string) for decrypting the key.
   On some versions of OSX, and potentially also on other platforms,
   empty passwords are not supported.

   The archive should contain a leaf certificate and its private key,
   as well any intermediate certificates that should be sent to
   clients to allow them to build a chain to a trusted root. The chain
   certificates should be in order from the leaf certificate towards
   the root.

   PKCS #12 archives typically have the file extension .p12 or .pfx,
   and can be created with the OpenSSL pkcs12 tool:

   $ openssl pkcs12 -export -out identity.pfx \
                    -inkey key.pem -in cert.pem -certfile chain_certs.pem


   You can use phrase_from_file/3 from library(pio) and seq//1 from
   library(dcgs) to read the contents of "identity.pfx" into a string:

   phrase_from_file(seq(Chars), "identity.pfx", [type(binary)])

   The obtained context should be treated as an opaque Prolog term.

   Using the context and an existing stream S0 (for example, the
   result of socket_server_accept/4), a TLS stream S can be negotiated
   by a Prolog-based server with:

   tls_server_negotiate(Context, S0, S)

   S will be an encrypted and authenticated stream with the client.

   The advantage of separating the creation of the server context from
   negotiating a connection is that the context can be created only
   once, and quickly cloned for every incoming connection. This is
   currently not implemented: In the present implementation, a new context
   is created for every connection, using the specified parameters.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

tls_server_context(tls_context(Cert,Password), Options) :-
        (   member(pcks12(Cert), Options) ->
            must_be(chars, Cert)
        ;   domain_error(contains_pcks12, Options, tls_server_context/2)
        ),
        (   member(password(Password), Options) ->
            must_be(chars, Password)
        ;   Password = ""
        ).

tls_server_negotiate(tls_context(Cert,Password), S0, S) :-
        '$tls_accept_client'(Cert, Password, S0, S).
