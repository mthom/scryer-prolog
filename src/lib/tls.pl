/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Negotiation of TLS connections.
   Written Dec. 2021 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(tls, [tls_client_context/2,   % -Context, +Options
                tls_client_negotiate/3, % +Context, +Stream0, -Stream
                tls_server_context/2,   % -Context, +Options
                tls_server_negotiate/3  % +Context, +Stream0, -Stream
               ]).

:- use_module(library(lists)).
:- use_module(library(error)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   TLS Clients
   ===========

   Use tls_client_context/2 to create a TLS context, for example with:

   tls_client_context(Context, [hostname("metalevel.at")])

   Using the context and an existing stream S0 (for example, the
   result of socket_client_open/3), a TLS stream S can be negotiated
   with:

   tls_client_negotiate(Context, S0, S)

   S will be an encrypted and authenticated stream with the server.

   The advantage of separating the creation of the client context from
   negotiating a connection is that the context can be created only once,
   and quickly reused if needed. This is currently not implemented: In
   the present implementation, a new internal "Connector" is created for
   every connection, using the specified hostname.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

tls_client_context(tls_context(Host), Options) :-
        must_be(list, Options),
        (   member(hostname(Host), Options) ->
            must_be(chars, Host)
        ;   Host = ""
        ).

tls_client_negotiate(tls_context(Host), S0, S) :-
        '$tls_client_connect'(Host, S0, S).

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

