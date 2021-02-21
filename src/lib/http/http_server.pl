/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written in December 2020 by Adrián Arroyo (adrian.arroyocalle@gmail.com)
   Part of Scryer Prolog

   This library provides an starting point to build HTTP server based applications.
   It currently implements a subset of HTTP/1.0. It is recommended to put a reverse
   proxy like nginx in front of this server to have access to more advanced features
   (gzip compression, HTTPS, ...)

   Usage
   ==========
   The main predicate of the library is http_listen/2, which needs a port number
    (usually 80) and a list of handlers. A handler is created using the http_route/3 predicate
   as one HTTP method (in lowercase) and followed by a Route Match and a predicate
   which will handle the call.

   text_handler(Request, Response) :-
    http_status_code(Response, 200),
    http_body(Response, text("Welcome to Scryer Prolog!")).

   parameter_handler(User, Request, Response) :-
    http_body(Response, text(User)).

   server :-
       http_route(get(echo), text_handler, TextHandler),
       http_route(post(user/User), parameter_handler(User), ParameterHandler),
       http_listen(7890, [
            TextHandler,           % GET /echo
            ParameterHandler % POST /user/<User>
       ]).

   Every handler predicate will have at least 2-arity, with Request and Response.
   Although you can work directly with http_request and http_response terms, it is
   recommeded to use the helper predicates, which are easier to understand and cleaner:
   - http_headers(Response/Request, Headers)
   - http_status_code(Responde, StatusCode)
   - http_body(Response/Request, text(Body))
   - http_body(Response/Request, binary(Body))
   - http_body(Request, form(Form))
   - http_body(Response, file(Filename))
   - http_redirect(Response, Url)
   - http_query(Request, QueryName, QueryValue)

   Some things that are still missing:
   - Read forms in multipart format
   - HTTP Basic Auth
   - Keep-Alive support
   - Session handling via cookies
   - HTML Templating

   I place this code in the public domain. Use it in any way you want.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(http_server, [
    http_route/3,
    http_listen/2,
    http_headers/2,
    http_status_code/2,
    http_body/2,
    http_redirect/2,
    http_query/3,
    url_decode//1
]).

:- meta_predicate http_route(?, 2, ?).

:- use_module(library(sockets)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(time)).
:- use_module(library(crypto)).

http_route(Path, Handler, MetaHandler) :-
    Path =.. [Method, Pattern],
    MetaHandler =.. [Method, Pattern, Handler].

% Server initialization
http_listen(Port, Handlers) :-
    must_be(integer, Port),
    must_be(list, Handlers),
    once(socket_server_open(Port, Socket)),
    format("Listening at port ~d\n", [Port]),
    accept_loop(Socket, Handlers).

% Server loop
accept_loop(Socket, Handlers) :-
    setup_call_cleanup(socket_server_accept(Socket, _Client, Stream, [type(binary)]),
        (
            read_header_lines(Stream, Lines),
            [Request|Headers] = Lines,
            (
                (phrase(parse_request(_Version, Method, Path, Queries), Request), maplist(map_parse_header, Headers, HeadersKV)) -> (
                        (
                            member("content-length"-ContentLength, HeadersKV) ->
                                (number_chars(ContentLengthN, ContentLength), get_bytes(Stream, ContentLengthN, Body))
                                ;true
                        ),
                        current_time(Time),
                        phrase(format_time("%Y-%m-%d (%H:%M:%S)", Time), TimeString),
                        format("~s ~w ~s\n", [TimeString, Method, Path]),
                        (
                            match_handler(Handlers, Method, Path, Handler) ->
                            (
                                HttpRequest = http_request(HeadersKV, binary(Body), Queries),
                                HttpResponse = http_response(_, _, _),
                                (call(Handler, HttpRequest, HttpResponse) ->
                                    send_response(Stream, HttpResponse)
                                ;   format(Stream, "HTTP/1.0 500 Internal Server Error\r\n\r\n", [])
                                )
                            )
                        ;   format(Stream, "HTTP/1.0 404 Not Found\r\n\r\n", [])
                        )
                    );(
                        format(Stream, "HTTP/1.0 400 Bad Request\r\n\r\n", []) % bad format
                    )
            ),
            ! % Remove
        ), close(Stream)),
    accept_loop(Socket, Handlers).

match_handler(Handlers, Method, "/", Handler) :-
    member(H, Handlers),
    H =.. [Method, /, Handler].
match_handler(Handlers, Method, Path, Handler) :-
    member(H, Handlers),
    copy_term(H, H1),
    H1 =.. [Method, Pattern, Handler],
    \+ var(Pattern),
    phrase(path(Pattern), Path).
match_handler(Handlers, Method, Path, Handler) :-
    member(H, Handlers),
    copy_term(H, H1),
    H1 =.. [Method, Var, Handler],
    var(Var),
    Var = Path.


% Helper and recommended predicates

http_headers(http_request(Headers, _, _), Headers).
http_headers(http_response(_, _, Headers), Headers).

http_body(http_request(_, binary(ByteBody), _), text(TextBody)) :- chars_utf8bytes(TextBody, ByteBody).
http_body(http_request(Headers, binary(ByteBody), _), form(FormBody)) :- 
    member("content-type"-"application/x-www-form-urlencoded", Headers),
    chars_utf8bytes(TextBody, ByteBody),
    phrase(parse_queries(FormBody), TextBody).
http_body(http_request(_, Body, _), Body).
http_body(http_response(_, Body, _), Body).

http_status_code(http_response(StatusCode, _, _), StatusCode).

http_redirect(http_response(307, text("Moved Temporarily"), ["Location"-Uri]), Uri).

http_query(http_request(_, _, Queries), Key, Value) :- member(Key-Value, Queries).

% Route matching
path(Pattern) -->
    {
        Pattern =.. Parts,
        length(Parts, 3),
        nth0(1, Parts, Pattern0),
        nth0(2, Parts, PartAtom),
        (var(PartAtom) -> Part = PartAtom; atom_chars(PartAtom, Part))
    },
    path(Pattern0),
    "/",
    string_without("/", Part).

path(Pattern) -->
    {
        Pattern =.. Parts,
        Parts = [PartAtom],
        (var(PartAtom) -> Part = PartAtom; atom_chars(PartAtom, Part))
    },
    "/",
    string_without("/", Part).

path([]) --> [].

% Send responses
send_response(Stream, http_response(StatusCode0, file(Filename), Headers)) :-
    default(StatusCode0, 200, StatusCode),
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("connection"-"Close", Headers, Headers0),
    write_headers(Stream, Headers0),
    format(Stream, "\r\n", []),
    setup_call_cleanup(
        open(Filename, read, FileStream, [type(binary)]),
        pipe_bytes(FileStream, Stream),
        close(FileStream)
    ).

send_response(Stream, http_response(StatusCode0, text(TextResponse), Headers)) :-
    default(StatusCode0, 200, StatusCode),
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("content-type"-"text/plain", Headers, Headers0),
    overwrite_header("connection"-"Close", Headers0, Headers1),
    write_headers(Stream, Headers1),
    format(Stream, "\r\n~s", [TextResponse]).

send_response(Stream, http_response(StatusCode0, binary(BinaryResponse), Headers)) :-
    default(StatusCode0, 200, StatusCode),
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("connection"-"Close", Headers, Headers0),
    write_headers(Stream, Headers0),
    format(Stream, "\r\n", []),
    put_bytes(Stream, BinaryResponse).

default(Var, Default, Out) :-
    (var(Var) -> Out = Default
    ;   Var = Out  
    ).

header([]) --> [].
header([Key-Value|Headers]) -->
    format_("~s: ~s\r\n", [Key, Value]),
    header(Headers).

write_headers(Stream, Headers) :-
    phrase(header(Headers), Cs),
    format(Stream, "~s", [Cs]).

overwrite_header(Key-Value, [], [Key-Value]).
overwrite_header(Key-Value, [Header|Headers], [Header|HeadersOut]) :-
    Header = Key0-_,
    Key0 \= Key,
    overwrite_header(Key-Value, Headers, HeadersOut).
overwrite_header(Key-Value, [Header|Headers], [NewHeader|Headers]) :-
    Header = Key-_,
    NewHeader = Key-Value.

parse_request(http_version(Major, Minor), Method, Path, Queries) -->
    method(Method),
    " ",
    parse_path(Path, Queries),
    " ",
    "HTTP/",
    natural(Major),
    ".",
    natural(Minor),
    "\r\n".

parse_path(Path, Queries) -->
    string_without("?", Path),
    "?",
    parse_queries(Queries).

parse_path(Path, []) -->
    string_without(" ", Path).

parse_queries([Key-Value|Queries]) -->
    string_without("=", Key0),
    {
        phrase(url_decode(Key), Key0)
    },
    "=",
    string_without("&", Value0),
    {
        phrase(url_decode(Value), Value0)
    },
    "&",
    parse_queries(Queries).

parse_queries([Key-Value]) -->
    string_without("=", Key0),
    {
        phrase(url_decode(Key), Key0)
    },
    "=",
    string_without(" ", Value0),
    {
        phrase(url_decode(Value), Value0)  
    }.

map_parse_header(Header, HeaderKV) :-
    phrase(parse_header(HeaderKV), Header).

parse_header(Key-Value) -->
    string_without(":", Key0),
    {
        chars_lower(Key0, Key)
    },
    ": ",
    string_without("\r", Value),
    "\r\n".

method(options) --> "OPTIONS".
method(get) --> "GET".
method(head) --> "HEAD".
method(post) --> "POST".
method(put) --> "PUT".
method(delete) --> "DELETE".

string_without(Not, [Char|String]) -->
    [Char],
    {
        \+ member(Char, Not)
    },
    string_without(Not, String).

string_without(_, []) -->
    [].

natural(Nat) -->
    natural_(NatChars),
    {
        number_chars(Nat, NatChars)
    }.

natural_([Nat|Nats]) -->
    [Nat],
    {
        char_type(Nat, decimal_digit)
    },
    natural_(Nats).

natural_([]) -->
    [].

read_header_lines(Stream, Hs) :-
        read_line_to_chars(Stream, Cs, []),
        (   Cs == "" -> Hs = []
        ;   Cs == "\r\n" -> Hs = []
        ;   Hs = [Cs|Rest],
            read_header_lines(Stream, Rest)
        ).

get_bytes(Stream, Length, Res) :- get_bytes(Stream, Length, [], Res).
get_bytes(Stream, Length, Acc, Res) :-
  (Length > 0 -> (
    get_byte(Stream, B),
    B =\= -1,
    get_bytes(Stream, Length - 1, [B|Acc], Res)
  ); reverse(Acc, Res)).

put_bytes(_, []).
put_bytes(Stream, [Byte|Bytes]) :-
    put_byte(Stream, Byte),
    put_bytes(Stream, Bytes).

pipe_bytes(StreamIn, StreamOut) :-
    get_byte(StreamIn, Byte),
    (
        Byte =\= -1 ->
        (
            put_byte(StreamOut, Byte),
            pipe_bytes(StreamIn, StreamOut)
        )
    ;   true).

% WARNING: This only works for ASCII chars. This code can be modified to support
% Latin1 characters also but a completely different approach is needed for other
% languages. Since HTTP internals are ASCII, this is fine for this usecase.
chars_lower(Chars, Lower) :-
    maplist(char_lower, Chars, Lower).
char_lower(Char, Lower) :-
    char_code(Char, Code),
    ((Code >= 65,Code =< 90) ->
        LowerCode is Code + 32,
        char_code(Lower, LowerCode)
    ;   Char = Lower).

% Decodes a UTF-8 URL Encoded string: RFC-1738
url_decode([Char|Chars]) -->
    [Char],
    {
        Char \= '%'
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A],
    [B],
    {
        hex_bytes([A,B], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 128,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    {
        hex_bytes([A,B,C,D], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 224,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    "%",
    [E, F],
    {
        hex_bytes([A,B,C,D,E,F], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 240,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    "%",
    [E, F],
    "%",
    [H, I],
    {
        hex_bytes([A,B,C,D,E,F,H,I], Bytes),
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).

url_decode([]) --> [].
