/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written Dec. 2021 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(tls, [tls_client_context/2,   % -Context, +Options
                tls_client_negotiate/3, % +Context, +Stream0, -Stream
                tls_server_context/2,   % -Context, +Options
                tls_server_negotiate/3, % +Context, +Stream0, -Stream
                tls_server_negotiate/4  % +Context, +Stream0, -Stream, +Options
               ]).

:- use_module(library(lists)).
:- use_module(library(error)).

/** Negotiation of TLS connections.
*/

%% tls_client_context(-Context, +Options)
%
% Use `tls_client_context/2` to create a TLS context, for example with:
%
% ```
% tls_client_context(Context, [hostname("metalevel.at")])
% ```
%
tls_client_context(tls_context(Host), Options) :-
        must_be(list, Options),
        (   member(hostname(Host), Options) ->
            must_be(chars, Host)
        ;   Host = ""
        ).

%% tls_client_negotiate(+Context, +Stream0, -Stream)
%
% Using the context and an existing stream `S0` (for example, the result of
% `socket_client_open/3`), a TLS stream `S` can be negotiated with:
%
% ```
% tls_client_negotiate(Context, S0, S)
% ```
%
% `S` will be an encrypted and authenticated stream with the server.
%
% The advantage of separating the creation of the client context from
% negotiating a connection is that the context can be created only once, and
% quickly reused if needed. This is currently not implemented: In the present
% implementation, a new internal "Connector" is created for every connection,
% using the specified hostname.
tls_client_negotiate(tls_context(Host), S0, S) :-
        '$tls_client_connect'(Host, S0, S).

%% tls_server_context(-Context, +Options)
%
% Use `tls_server_context/2` to create a TLS context, for example with:
%
% ```
% tls_server_context(Context, [certificate(Cert),key(Key)])
% ```
%
% where `Cert` is a list of characters with the contents of a PEM-encoded
% certificate chain, and `Key` is a list of characters with the contents of the
% corresponding PEM-encoded private key. The private key may be in PKCS #8, PKCS
% #1 (RSA) or SEC1 (EC) format.
%
% The certificate chain should contain a leaf certificate followed by any
% intermediate certificates that should be sent to clients to allow them to build
% a chain to a trusted root. The chain certificates should be in order from the
% leaf certificate towards the root.
%
% You can use `phrase_from_file/3` from `library(pio)` and `seq//1` from `library(dcgs)`
% to read the contents of "cert.pem" and "key.pem" into strings:
%
% ```
% phrase_from_file(seq(Cert), "cert.pem"), phrase_from_file(seq(Key), "key.pem")
% ```
%
% The obtained context should be treated as an opaque Prolog term.
tls_server_context(tls_context(Cert,Key), Options) :-
        (   member(certificate(Cert), Options) ->
            must_be(chars, Cert)
        ;   domain_error(contains_certificate, Options, tls_server_context/2)
        ),
        (   member(key(Key), Options) ->
            must_be(chars, Key)
        ;   domain_error(contains_key, Options, tls_server_context/2)
        ).

%% tls_server_negotiate(+Context, +Stream0, -Stream, +Options)
%
% Using the context and an existing stream `S0` (for example, the result of
% `socket_server_accept/4`), a TLS stream `S` can be negotiated by a
% Prolog-based server with:
%
% ```
% tls_server_negotiate(Context, S0, S, Options)
% ```
%
% `S` will be an encrypted and authenticated stream with the client.
%
% Currently, the only existing option is `client_certificate(Cert)` where `Cert`
% will be unified with the client certificate if the client provides one, or the
% atom `none` if none is provided. To get the client certificate, use `Options =
% [client_certificate(Cert)]`.
%
% The advantage of separating the creation of the server context from
% negotiating a connection is that the context can be created only once, and
% quickly cloned for every incoming connection. This is currently not
% implemented: In the present implementation, a new context is created for every
% connection, using the specified parameters.
tls_server_negotiate(tls_context(Cert,Key), S0, S, Options) :-
    must_be(list, Options),
    ( member(client_certificate(ClientCert), Options) ->
      '$tls_accept_client'(Cert, Key, S0, S, ClientCert)
    ; '$tls_accept_client'(Cert, Key, S0, S, _)
    ).

%% tls_server_negotiate(+Context, +Stream0, -Stream)
%
% Like `tls_server_negotiate/4` with empty options.
tls_server_negotiate(Ctx, S0, S) :-
    tls_server_negotiate(Ctx, S0, S, []).
