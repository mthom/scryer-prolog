:- module(http_server, [http_listen/2, http_headers/2, http_status_code/2, http_body/2, http_redirect/2]).

:- use_module(library(sockets)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).

% TODO
% - Query Params
% - Cookies?
% - HTTP Error Codes
% - Improve code quality
% - Comments
% - Keep-Alive
% - Case insensitive headers
% - HTML
% - Response from file

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

accept_loop(Socket) :-
    setup_call_cleanup(socket_server_accept(Socket, Client, Stream, [type(binary)]),
        (
            read_header_lines(Stream, Lines),
            [Request|Headers] = Lines,
            (
                (phrase(parse_request(Version, Method, Path), Request), maplist(map_parse_header, Headers, HeadersKV)) -> (
                        (
                            member("Content-Length"-ContentLength, HeadersKV) ->
                                (number_chars(ContentLengthN, ContentLength), get_bytes(Stream, ContentLengthN, Body))
                                ;true
                        ),
                        format("~w ~s\n", [Method, Path]),
                        (
                            (http_handler(Method, Pattern, Handler), phrase(path(Pattern), Path)) ->
                            (
                                HttpRequest = http_request(HeadersKV, binary(Body)),
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
http_headers(http_request(Headers, _), Headers).
http_headers(http_response(_, _, Headers), Headers).

http_body(http_request(_, binary(ByteBody)), text(TextBody)) :- chars_utf8bytes(TextBody, ByteBody).
http_body(http_request(_, Body), Body).
http_body(http_response(_, Body, _), Body).

http_status_code(http_response(StatusCode, _, _), StatusCode).

http_redirect(http_response(307, text("Moved Temporarily"), ["Location"-Uri]), Uri).

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

write_headers(Stream, Headers) :-
    forall(member(Key-Value, Headers), format(Stream, "~s: ~s\r\n", [Key, Value])).

overwrite_header(Key-Value, [], [Key-Value]).
overwrite_header(Key-Value, [Header|Headers], [Header|HeadersOut]) :-
    Header = Key0-_,
    Key0 \= Key,
    overwrite_header(Key-Value, Headers, HeadersOut).
overwrite_header(Key-Value, [Header|Headers], [NewHeader|Headers]) :-
    Header = Key-_,
    NewHeader = Key-Value.

parse_request(http_version(Major, Minor), Method, Path) -->
    method(Method),
    " ",
    string_without(" ", Path),
    " ",
    "HTTP/",
    natural(Major),
    ".",
    natural(Minor),
    "\r\n".

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
