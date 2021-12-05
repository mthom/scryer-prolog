/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2020, 2021 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   http_open(+Address, -Stream, +Options)
   ======================================

   Yields Stream to read the body of an HTTP reply from Address.
   Address is a list of characters, and includes the method. Both HTTP
   and HTTPS are supported. Redirects are followed.

   Currently, Options must be the empty list. Options may be
   added in the future to give more control over the connection.

   We use HTTP/1.0 until we can read chunked transfer-encoding.

   Example:

       ?- http_open("https://github.com/mthom/scryer-prolog", S, []).
       %@    S = '$stream'(0x7fcfc9e00f00).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(http_open, [http_open/3]).

:- use_module(library(sockets)).
:- use_module(library(error)).
:- use_module(library(format)).
:- use_module(library(charsio)).
:- use_module(library(dcgs)).
:- use_module(library(lists), [member/2]).
:- use_module(library(tls)).

http_open(Address, Stream, Options) :-
        must_be(list, Options),
        must_be(list, Address),
        once(phrase((seq(SchemeCs), "://", seq(Rest)), Address)),
        atom_chars(Scheme, SchemeCs),
        chars_host_url(Rest, Host, URL),
        connect(Scheme, Host, Stream0),
        format(Stream0, "\
GET ~s HTTP/1.0\r\n\
Host: ~w\r\n\
User-Agent: Scryer Prolog\r\n\
Connection: close\r\n\r\n\
", [URL,Host]),
        read_line_to_chars(Stream0, StatusLine, []),
        once(phrase(("HTTP/1.",(['0']|['1'])," ",[D1]), StatusLine, _)),
        read_header_lines(Stream0, HeaderLines),
        handle_response(D1, HeaderLines, Stream0, Stream).

handle_response('2', _, Stream, Stream).              % ok
handle_response('3', HeaderLines, Stream0, Stream) :- % redirect
        close(Stream0),
        once((member(Line, HeaderLines),
              phrase(("Location: ",seq(Location),"\r\n"), Line))),
        http_open(Location, Stream, []).

% Status-Line = HTTP-Version SP Status-Code SP Reason-Phrase CRLF

read_header_lines(Stream, Hs) :-
        read_line_to_chars(Stream, Cs, []),
        (   Cs == "" -> Hs = []
        ;   Cs == "\r\n" -> Hs = []
        ;   Hs = [Cs|Rest],
            read_header_lines(Stream, Rest)
        ).

chars_host_url(Cs, Host, [/|Us]) :-
        (   phrase((seq(Hs),"/",seq(Us)), Cs) ->
            true
        ;   Hs = Cs,
            Us = []
        ),
        atom_chars(Host, Hs).

connect(https, Host, Stream) :-
        socket_client_open(Host:443, Stream0, []),
        atom_chars(Host, HostChars),
        tls_client_context(Context, [hostname(HostChars)]),
        tls_client_negotiate(Context, Stream0, Stream).
connect(http, Host, Stream) :-
        socket_client_open(Host:80, Stream, []).

