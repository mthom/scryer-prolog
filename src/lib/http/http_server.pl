:- module(http_server, [http_listen/2, http_headers/2, http_status_code/2, http_body/2, http_redirect/2, http_query/3]).

:- use_module(library(sockets)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).

% TODO
% - Cookies?
% - HTTP Error Codes
% - Improve code quality
% - Comments
% - Keep-Alive
% - Case insensitive headers
% - HTML
% - Response from file
% - Remove forall
% - Remove !
% - URL Encode

:- dynamic(http_handler/3).

http_listen(Port, Handlers) :-
    must_be(integer, Port),
    must_be(list, Handlers),
    once(socket_server_open(Port, Socket)),
    register_handlers(Handlers),
    format("Listening at port ~d\n", [Port]),
    accept_loop(Socket).

register_handlers([]).
register_handlers([get(Path, Handler)|Handlers]) :-
    asserta(http_handler(get, Path, Handler)),
    register_handlers(Handlers).
register_handlers([post(Path, Handler)|Handlers]) :-
    asserta(http_handler(post, Path, Handler)),
    register_handlers(Handlers).
register_handlers([put(Path, Handler)|Handlers]) :-
    asserta(http_handler(put, Path, Handler)),
    register_handlers(Handlers).
register_handlers([patch(Path, Handler)|Handlers]) :-
    asserta(http_handler(patch, Path, Handler)),
    register_handlers(Handlers).
register_handlers([head(Path, Handler)|Handlers]) :-
    asserta(http_handler(head, Path, Handler)),
    register_handlers(Handlers).
register_handlers([delete(Path, Handler)|Handlers]) :-
    asserta(http_handler(delete, Path, Handler)),
    register_handlers(Handlers).
register_handlers([options(Path, Handler)|Handlers]) :-
    asserta(http_handler(options, Path, Handler)),
    register_handlers(Handlers).

accept_loop(Socket) :-
    setup_call_cleanup(socket_server_accept(Socket, Client, Stream, [type(binary)]),
        (
            read_header_lines(Stream, Lines),
            [Request|Headers] = Lines,
            (
                (phrase(parse_request(Version, Method, Path, Queries), Request), maplist(map_parse_header, Headers, HeadersKV)) -> (
                        (
                            member("Content-Length"-ContentLength, HeadersKV) ->
                                (number_chars(ContentLengthN, ContentLength), get_bytes(Stream, ContentLengthN, Body))
                                ;true
                        ),
                        format("~w ~s\n", [Method, Path]),
                        (
                            (http_handler(Method, Pattern, Handler), phrase(path(Pattern), Path)) ->
                            (
                                HttpRequest = http_request(HeadersKV, binary(Body), Queries),
                                HttpResponse = http_response(_, _, _),
                                (call(Handler, HttpRequest, HttpResponse) ->
                                    send_response(Stream, HttpResponse)
                                ;   format(Stream, "HTTP/1.0 500 Internal Server Error\r\n\r\n")
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
    accept_loop(Socket).

% Helper and recommended predicates

% http_header(Response, HEaderName, Value)
http_headers(http_request(Headers, _, _), Headers).
http_headers(http_response(_, _, Headers), Headers).

http_body(http_request(_, binary(ByteBody), _), text(TextBody)) :- chars_utf8bytes(TextBody, ByteBody).
http_body(http_request(_, Body, _), Body).
http_body(http_response(_, Body, _), Body).

http_status_code(http_response(StatusCode, _, _), StatusCode).

http_redirect(http_response(307, text("Moved Temporarily"), ["Location"-Uri]), Uri).

http_query(http_request(_, _, Queries), Key, Value) :- member(Key-Value, Queries).

path([Part|Pattern]) -->
    "/",
    string_without("/", Part),
    path(Pattern).

path([]) --> [].

send_response(Stream, http_response(StatusCode0, text(TextResponse), Headers)) :-
    default(StatusCode0, 200, StatusCode),
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("Content-Type"-"text/plain", Headers, Headers0),
    overwrite_header("Connection"-"Close", Headers0, Headers1),
    write_headers(Stream, Headers1),
    format(Stream, "\r\n~s", [TextResponse]).

send_response(Stream, http_response(StatusCode0, binary(BinaryResponse), Headers)) :-
    default(StatusCode0, 200, StatusCode),
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("Connection"-"Close", Headers, Headers0),
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
    string_without("=", Key),
    "=",
    string_without("&", Value),
    "&",
    parse_queries(Queries).

parse_queries([Key-Value]) -->
    string_without("=", Key),
    "=",
    string_without(" ", Value).

map_parse_header(Header, HeaderKV) :-
    phrase(parse_header(HeaderKV), Header).

parse_header(Key-Value) -->
    string_without(":", Key),
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
